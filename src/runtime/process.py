"""Capture subprocess output while preserving process-tree cancellation semantics."""

from __future__ import annotations

import math
import os
import select
import signal
import subprocess
import threading
import time
from collections.abc import Buffer
from contextlib import suppress
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Callable, cast


@dataclass(frozen=True)
class CapturedProcess:
    """Expose captured streams and the subprocess exit or interruption outcome."""

    returncode: int | None
    stdout: bytes
    stderr: bytes
    timed_out: bool
    pid: int | None
    process_group_id: int | None
    cancelled: bool = False


@dataclass
class _Collector:
    thread: threading.Thread | None = None
    error: BaseException | None = None


StreamObserver = Callable[[bytes], None]
ProcessStartedObserver = Callable[[subprocess.Popen[bytes], int | None], None]

# How long a cancellable wait sleeps between process-exit checks.
_CANCEL_POLL_INTERVAL_SEC = 0.5


def run_process_capture_bytes(
    argv: list[str],
    *,
    env: dict[str, str],
    cwd: Path | None = None,
    timeout_sec: float | None = None,
    stdout_path: Path | None = None,
    stderr_path: Path | None = None,
    stdout_observer: StreamObserver | None = None,
    stderr_observer: StreamObserver | None = None,
    on_started: ProcessStartedObserver | None = None,
    start_new_session: bool = True,
    timeout_stderr_text: str | None = None,
    cancel_event: threading.Event | None = None,
    cancellation_stderr_text: str | None = None,
    collector_exit_grace_sec: float | None = None,
) -> CapturedProcess:
    """Capture streams, optionally bounding collector drain after the parent exits."""
    if collector_exit_grace_sec is not None and (
        not math.isfinite(collector_exit_grace_sec) or collector_exit_grace_sec <= 0
    ):
        raise ValueError("collector exit grace must be positive and finite")
    stdout_chunks: list[bytes] = []
    stderr_chunks: list[bytes] = []
    stdout_file = None
    stderr_file = None
    try:
        stdout_file = _open_tee(stdout_path)
        stderr_file = _open_tee(stderr_path)
        if cancel_event is not None and cancel_event.is_set():
            if cancellation_stderr_text:
                _append_text(
                    stderr_chunks,
                    stderr_file,
                    stderr_observer,
                    cancellation_stderr_text,
                )
            return CapturedProcess(
                returncode=None,
                stdout=b"",
                stderr=b"".join(stderr_chunks),
                timed_out=False,
                cancelled=True,
                pid=None,
                process_group_id=None,
            )
        process = subprocess.Popen(
            argv,
            cwd=cwd,
            env=env,
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=False,
            start_new_session=start_new_session,
        )
        process_group_id = _process_group_id(process)
        collector_stop = threading.Event() if collector_exit_grace_sec is not None else None
        collectors: list[_Collector] = []
        try:
            if on_started is not None:
                on_started(process, process_group_id)
            if process.stdout is None or process.stderr is None:
                raise RuntimeError("Failed to initialize subprocess pipes")
            collectors.append(
                _start_collector(
                    process.stdout,
                    chunks=stdout_chunks,
                    tee_file=stdout_file,
                    observer=stdout_observer,
                    name="process-stdout-collector",
                    stop_event=collector_stop,
                )
            )
            collectors.append(
                _start_collector(
                    process.stderr,
                    chunks=stderr_chunks,
                    tee_file=stderr_file,
                    observer=stderr_observer,
                    name="process-stderr-collector",
                    stop_event=collector_stop,
                )
            )
            returncode, timed_out, cancelled = _wait_for_process(
                process,
                timeout_sec=timeout_sec,
                cancel_event=cancel_event,
            )
        except BaseException:
            _terminate_process_tree(process)
            raise
        finally:
            try:
                complete_capture = _join_collectors(
                    collectors, stop_event=collector_stop, grace_sec=collector_exit_grace_sec
                )
            finally:
                _close_file(process.stdout)
                _close_file(process.stderr)

        if not complete_capture and not (timed_out or cancelled):
            raise RuntimeError("subprocess output capture did not reach EOF within collector grace")

        if timed_out and timeout_stderr_text:
            _append_text(stderr_chunks, stderr_file, stderr_observer, timeout_stderr_text)
        if cancelled and cancellation_stderr_text:
            _append_text(
                stderr_chunks,
                stderr_file,
                stderr_observer,
                cancellation_stderr_text,
            )
        return CapturedProcess(
            returncode=returncode,
            stdout=b"".join(stdout_chunks),
            stderr=b"".join(stderr_chunks),
            timed_out=timed_out,
            cancelled=cancelled,
            pid=process.pid,
            process_group_id=process_group_id,
        )
    finally:
        _close_observer(stdout_observer)
        _close_observer(stderr_observer)
        _close_file(stdout_file)
        _close_file(stderr_file)


def _open_tee(path: Path | None) -> Any | None:
    if path is None:
        return None
    path.parent.mkdir(parents=True, exist_ok=True)
    return path.open("wb")


def _close_file(file_obj: Any | None) -> None:
    if file_obj is not None:
        file_obj.close()


def _start_collector(
    stream: Any,
    *,
    chunks: list[bytes],
    tee_file: Any | None,
    observer: StreamObserver | None,
    name: str,
    stop_event: threading.Event | None,
) -> _Collector:
    collector = _Collector()
    thread = threading.Thread(
        target=_run_collector,
        kwargs={
            "collector": collector,
            "stream": stream,
            "chunks": chunks,
            "tee_file": tee_file,
            "observer": observer,
            "stop_event": stop_event,
        },
        name=name,
        daemon=True,
    )
    collector.thread = thread
    thread.start()
    return collector


def _join_collectors(
    collectors: list[_Collector],
    *,
    stop_event: threading.Event | None,
    grace_sec: float | None,
) -> bool:
    deadline = None if grace_sec is None else time.monotonic() + grace_sec
    for collector in collectors:
        assert collector.thread is not None
        collector.thread.join(
            timeout=None if deadline is None else max(0, deadline - time.monotonic())
        )
    complete_capture = not any(
        collector.thread is not None and collector.thread.is_alive() for collector in collectors
    )
    if not complete_capture:
        assert stop_event is not None
        stop_event.set()
        for collector in collectors:
            assert collector.thread is not None
            collector.thread.join()
    for collector in collectors:
        if collector.error is not None:
            raise RuntimeError("subprocess output collector failed") from collector.error
    return complete_capture


def _run_collector(*, collector: _Collector, **kwargs: Any) -> None:
    try:
        _collect_stream(**kwargs)
    except BaseException as exc:
        collector.error = exc


def _collect_stream(
    *,
    stream: Any,
    chunks: list[bytes],
    tee_file: Any | None,
    observer: StreamObserver | None,
    stop_event: threading.Event | None,
) -> None:
    try:
        poller = None
        if stop_event is not None:
            poller = select.poll()
            poller.register(stream, select.POLLIN | select.POLLHUP | select.POLLERR)
        while True:
            if stop_event is not None:
                if stop_event.is_set():
                    break
                assert poller is not None
                if not poller.poll(100):
                    continue
            chunk = _read_stream_chunk(stream)
            if not chunk:
                break
            _record_chunk(chunk, chunks=chunks, tee_file=tee_file, observer=observer)
    finally:
        stream.close()


def _read_stream_chunk(stream: Any) -> bytes:
    read1 = getattr(stream, "read1", None)
    if callable(read1):
        chunk = read1(4096)
    else:
        chunk = stream.read(4096)
    return chunk if isinstance(chunk, bytes) else bytes(cast(Buffer, chunk))


def _record_chunk(
    chunk: bytes,
    *,
    chunks: list[bytes],
    tee_file: Any | None,
    observer: StreamObserver | None,
) -> None:
    chunks.append(chunk)
    if tee_file is not None:
        tee_file.write(chunk)
        tee_file.flush()
    _feed_observer(observer, chunk)


def _append_text(
    stderr_chunks: list[bytes],
    stderr_file: Any | None,
    stderr_observer: StreamObserver | None,
    text: str,
) -> None:
    payload = b"".join(stderr_chunks)
    if payload and not payload.endswith(b"\n"):
        _record_chunk(b"\n", chunks=stderr_chunks, tee_file=stderr_file, observer=stderr_observer)
    _record_chunk(
        text.encode("utf-8"),
        chunks=stderr_chunks,
        tee_file=stderr_file,
        observer=stderr_observer,
    )


def _wait_for_process(
    process: subprocess.Popen[bytes],
    *,
    timeout_sec: float | None,
    cancel_event: threading.Event | None,
) -> tuple[int | None, bool, bool]:
    if cancel_event is None:
        try:
            return process.wait(timeout=timeout_sec), False, False
        except subprocess.TimeoutExpired:
            return _terminate_process_tree(process), True, False

    deadline = None if timeout_sec is None else time.monotonic() + timeout_sec
    while True:
        returncode = process.poll()
        if returncode is not None:
            return returncode, False, False
        remaining = None if deadline is None else deadline - time.monotonic()
        if remaining is not None and remaining <= 0:
            return _terminate_process_tree(process), True, False
        interval = (
            _CANCEL_POLL_INTERVAL_SEC
            if remaining is None
            else min(_CANCEL_POLL_INTERVAL_SEC, remaining)
        )
        # Sleep on the event rather than the process: cancellation wakes immediately, and
        # the exit check costs one non-blocking waitpid per interval instead of a spin.
        if cancel_event.wait(timeout=interval):
            return _terminate_process_tree(process), False, True


def _feed_observer(observer: StreamObserver | None, chunk: bytes) -> None:
    if observer is None:
        return
    observer(chunk)


def _close_observer(observer: StreamObserver | None) -> None:
    if observer is None:
        return
    close = getattr(observer, "close", None)
    if callable(close):
        close()


def _process_group_id(process: subprocess.Popen[bytes]) -> int | None:
    if not hasattr(os, "getpgid"):
        return None
    try:
        return os.getpgid(process.pid)
    except (OSError, ProcessLookupError):
        return None


def _terminate_process_tree(process: subprocess.Popen[bytes]) -> int | None:
    pgid = _process_group_id(process)
    if pgid is not None and pgid == process.pid and hasattr(os, "killpg"):
        try:
            os.killpg(pgid, signal.SIGKILL)
        except (OSError, ProcessLookupError):
            _kill_process(process)
    else:
        _kill_process(process)
    return process.wait()


def _kill_process(process: subprocess.Popen[bytes]) -> None:
    with suppress(OSError, ProcessLookupError):
        process.kill()
