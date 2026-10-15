"""Controlled subprocesses exercise capture completion and interrupted pipe drain."""

from __future__ import annotations

import json
import os
import resource
import select
import shlex
import signal
import subprocess
import sys
import threading
import time
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

import pytest

from evaluation.runtime import run_command_capture_bytes
from runtime.process import CapturedProcess, run_process_capture_bytes

pytestmark = pytest.mark.integration


@dataclass
class _Observer:
    chunks: list[bytes] = field(default_factory=list)
    collector_threads: set[threading.Thread] = field(default_factory=set)
    closed: bool = False
    fail: bool = False

    def __call__(self, chunk: bytes) -> None:
        assert not self.closed
        current = threading.current_thread()
        if current.name.startswith("process-"):
            self.collector_threads.add(current)
        if self.fail:
            raise ValueError("public observer failure")
        self.chunks.append(chunk)

    def close(self) -> None:
        assert all(not thread.is_alive() for thread in self.collector_threads)
        self.closed = True


@dataclass
class _DetachedPipeFixture:
    directory: Path
    parent: subprocess.Popen[bytes] | None = None
    child_pidfd: int | None = None

    @property
    def ready(self) -> Path:
        return self.directory / "child-ready"

    @property
    def parent_ready(self) -> Path:
        return self.directory / "parent-ready"

    @property
    def release(self) -> Path:
        return self.directory / "release"

    def argv(self, *, normal_exit: bool) -> list[str]:
        child = f"""
import os, time
from pathlib import Path
os.write(1, b'held-out\\n')
os.write(2, b'held-err\\n')
Path({str(self.ready)!r}).write_text(str(os.getpid()))
while not Path({str(self.release)!r}).exists():
    time.sleep(0.01)
os.write(1, b'late-out\\n')
os.write(2, b'late-err\\n')
"""
        parent = f"""
import subprocess, sys, time
from pathlib import Path
subprocess.Popen([sys.executable, '-c', {child!r}], start_new_session=True)
while not Path({str(self.ready)!r}).exists():
    time.sleep(0.01)
Path({str(self.parent_ready)!r}).touch()
{"" if normal_exit else "time.sleep(60)"}
"""
        return [sys.executable, "-c", parent]

    def on_started(self, process: subprocess.Popen[bytes], _pgid: int | None) -> None:
        self.parent = process
        deadline = time.monotonic() + 5
        while not self.parent_ready.exists():
            if process.poll() is not None or time.monotonic() >= deadline:
                raise RuntimeError("public detached fixture did not become ready")
            time.sleep(0.01)
        self.pin_child()

    def pin_child(self) -> None:
        if self.child_pidfd is None and self.ready.exists():
            try:
                self.child_pidfd = os.pidfd_open(int(self.ready.read_text()))
            except ProcessLookupError:
                pass

    def close(self) -> None:
        self.pin_child()
        if self.child_pidfd is not None:
            try:
                signal.pidfd_send_signal(self.child_pidfd, signal.SIGKILL)
                exited = select.poll()
                exited.register(self.child_pidfd, select.POLLIN)
                assert exited.poll(5000), "owned detached child did not terminate"
            except ProcessLookupError:
                pass
            finally:
                os.close(self.child_pidfd)
                self.child_pidfd = None
        if self.parent is not None and self.parent.poll() is None:
            self.parent.kill()
            self.parent.wait(timeout=5)


@pytest.fixture
def detached_pipe(tmp_path: Path) -> Any:
    if not all(
        (
            hasattr(select, "poll"),
            hasattr(os, "pidfd_open"),
            hasattr(signal, "pidfd_send_signal"),
        )
    ):
        pytest.skip("controlled detached cleanup requires Linux poll and pidfds")
    fixture = _DetachedPipeFixture(tmp_path)
    try:
        yield fixture
    finally:
        fixture.close()


# Complete default capture preserves binary streams, tee bytes, observers and the exit code.
def test_default_capture_preserves_complete_output(tmp_path: Path) -> None:
    stdout = _Observer()
    stderr = _Observer()
    out_path = tmp_path / "out"
    err_path = tmp_path / "err"
    script = "import os,sys; os.write(1,b'raw\\x00\\xff'); os.write(2,b'error'); sys.exit(7)"

    result = run_process_capture_bytes(
        [sys.executable, "-c", script],
        env=dict(os.environ),
        stdout_path=out_path,
        stderr_path=err_path,
        stdout_observer=stdout,
        stderr_observer=stderr,
    )

    assert (result.returncode, result.timed_out, result.cancelled) == (7, False, False)
    assert result.stdout == out_path.read_bytes() == b"".join(stdout.chunks) == b"raw\x00\xff"
    assert result.stderr == err_path.read_bytes() == b"".join(stderr.chunks) == b"error"
    assert stdout.closed and stderr.closed


# Explicit bounded capture drains both streams through EOF on an ordinary successful exit.
def test_bounded_capture_preserves_large_complete_output() -> None:
    script = (
        "import sys; sys.stdout.buffer.write(b'o'*100000); sys.stderr.buffer.write(b'e'*100000)"
    )
    result = run_process_capture_bytes(
        [sys.executable, "-c", script],
        env=dict(os.environ),
        collector_exit_grace_sec=0.2,
    )

    assert (result.returncode, result.timed_out, result.cancelled) == (0, False, False)
    assert result.stdout == b"o" * 100000
    assert result.stderr == b"e" * 100000


# Opting out retains blocking EOF capture even after a parent has exited successfully.
def test_default_capture_waits_for_detached_pipe_eof(detached_pipe: _DetachedPipeFixture) -> None:
    results: list[CapturedProcess] = []
    errors: list[BaseException] = []
    ready = threading.Event()

    def started(process: subprocess.Popen[bytes], pgid: int | None) -> None:
        detached_pipe.on_started(process, pgid)
        ready.set()

    def capture() -> None:
        try:
            results.append(
                run_process_capture_bytes(
                    detached_pipe.argv(normal_exit=True),
                    env=dict(os.environ),
                    on_started=started,
                )
            )
        except BaseException as exc:
            errors.append(exc)

    worker = threading.Thread(target=capture)
    worker.start()
    try:
        assert ready.wait(timeout=5)
        assert detached_pipe.parent is not None
        assert detached_pipe.parent.wait(timeout=5) == 0
        assert worker.is_alive()
        detached_pipe.release.touch()
        worker.join(timeout=5)
        assert not worker.is_alive()
        assert not errors
        assert results[0].stdout == b"held-out\nlate-out\n"
        assert results[0].stderr == b"held-err\nlate-err\n"
    finally:
        detached_pipe.release.touch()
        worker.join(timeout=5)


# Timeout returns captured bytes and honest status while a detached writer still holds both pipes.
def test_bounded_capture_timeout_detached_writer(detached_pipe: _DetachedPipeFixture) -> None:
    stdout = _Observer()
    stderr = _Observer()
    out_path = detached_pipe.directory / "out"
    err_path = detached_pipe.directory / "err"
    start = time.monotonic()

    result = run_process_capture_bytes(
        detached_pipe.argv(normal_exit=False),
        env=dict(os.environ),
        on_started=detached_pipe.on_started,
        timeout_sec=0.05,
        collector_exit_grace_sec=0.05,
        timeout_stderr_text="timeout-record",
        stdout_path=out_path,
        stderr_path=err_path,
        stdout_observer=stdout,
        stderr_observer=stderr,
    )

    assert time.monotonic() - start < 2
    assert result.timed_out and not result.cancelled and result.returncode != 0
    assert result.stdout == out_path.read_bytes() == b"".join(stdout.chunks) == b"held-out\n"
    assert result.stderr == err_path.read_bytes() == b"".join(stderr.chunks)
    assert result.stderr == b"held-err\ntimeout-record"
    assert stdout.closed and stderr.closed


# Cancellation remains cancellation when a detached writer prevents ordinary stream EOF.
def test_bounded_capture_cancelled_detached_writer(detached_pipe: _DetachedPipeFixture) -> None:
    cancelled = threading.Event()

    def started(process: subprocess.Popen[bytes], pgid: int | None) -> None:
        detached_pipe.on_started(process, pgid)
        cancelled.set()

    start = time.monotonic()
    result = run_process_capture_bytes(
        detached_pipe.argv(normal_exit=False),
        env=dict(os.environ),
        on_started=started,
        cancel_event=cancelled,
        cancellation_stderr_text="cancel-record",
        collector_exit_grace_sec=0.05,
    )

    assert time.monotonic() - start < 2
    assert result.cancelled and not result.timed_out and result.returncode != 0
    assert result.stdout == b"held-out\n"
    assert result.stderr == b"held-err\ncancel-record"


# A successful parent cannot turn an incomplete bounded stream capture into a successful result.
def test_bounded_capture_rejects_incomplete_normal_exit(
    detached_pipe: _DetachedPipeFixture,
) -> None:
    stdout = _Observer()
    stderr = _Observer()
    start = time.monotonic()

    with pytest.raises(RuntimeError, match="did not reach EOF"):
        run_process_capture_bytes(
            detached_pipe.argv(normal_exit=True),
            env=dict(os.environ),
            on_started=detached_pipe.on_started,
            collector_exit_grace_sec=0.05,
            stdout_observer=stdout,
            stderr_observer=stderr,
        )

    assert time.monotonic() - start < 2
    assert b"".join(stdout.chunks) == b"held-out\n"
    assert b"".join(stderr.chunks) == b"held-err\n"
    assert stdout.closed and stderr.closed


# Collector failures reach the caller instead of returning a partially captured success.
@pytest.mark.parametrize("grace", [None, 0.05])
def test_capture_propagates_observer_failure(grace: float | None) -> None:
    observer = _Observer(fail=True)
    with pytest.raises(RuntimeError, match="output collector failed") as raised:
        run_process_capture_bytes(
            [sys.executable, "-c", "print('public-output')"],
            env=dict(os.environ),
            stdout_observer=observer,
            collector_exit_grace_sec=grace,
        )

    assert isinstance(raised.value.__cause__, ValueError)
    assert observer.closed


# Invalid grace values fail before spawning a process or creating output files.
@pytest.mark.parametrize("grace", [0, -1, float("inf"), float("nan")])
def test_capture_rejects_invalid_grace(grace: float, tmp_path: Path) -> None:
    output = tmp_path / "output"
    with pytest.raises(ValueError, match="positive and finite"):
        run_process_capture_bytes(
            ["/nonexistent-public-command"],
            env={},
            stdout_path=output,
            collector_exit_grace_sec=grace,
        )

    assert not output.exists()


# Poll-based capture handles descriptors above the select FD_SETSIZE limit.
def test_bounded_capture_supports_high_descriptors() -> None:
    if not hasattr(select, "poll") or resource.getrlimit(resource.RLIMIT_NOFILE)[0] < 1200:
        pytest.skip("high-descriptor poll control requires sufficient descriptor capacity")
    descriptors: list[int] = []
    try:
        while not descriptors or descriptors[-1] < 1100:
            descriptors.append(os.open(os.devnull, os.O_RDONLY))
        result = run_process_capture_bytes(
            [
                sys.executable,
                "-c",
                "import sys; print('high-out'); print('high-err',file=sys.stderr)",
            ],
            env=dict(os.environ),
            collector_exit_grace_sec=0.05,
        )
        assert result.returncode == 0
        assert result.stdout == b"high-out\n"
        assert result.stderr == b"high-err\n"
    finally:
        for descriptor in descriptors:
            os.close(descriptor)


# The evaluation facade forwards bounded capture and records incomplete normal output as failure.
def test_evaluation_capture_records_incomplete_normal_failure(
    detached_pipe: _DetachedPipeFixture,
) -> None:
    trace = detached_pipe.directory / "trace.jsonl"
    with pytest.raises(RuntimeError, match="did not reach EOF"):
        run_command_capture_bytes(
            command=shlex.join(detached_pipe.argv(normal_exit=True)),
            env=dict(os.environ),
            timeout_sec=5,
            live_stdout=False,
            live_stderr=False,
            trace_path=trace,
            collector_exit_grace_sec=0.05,
        )

    events = [json.loads(line) for line in trace.read_text().splitlines()]
    assert [event["event"] for event in events] == [
        "command_spawn_requested",
        "command_process_started",
        "command_spawn_failed",
    ]
    assert events[-1]["error_type"] == "RuntimeError"


# Setup cleanup never signals the caller's process group when the child shares its session.
def test_capture_setup_failure_preserves_caller_process_group() -> None:
    script = """
import os, sys
from runtime.process import run_process_capture_bytes

def failed_setup(process, process_group):
    raise ValueError('public setup failure')

try:
    run_process_capture_bytes(
        [sys.executable, '-c', 'import time; time.sleep(60)'],
        env=dict(os.environ),
        start_new_session=False,
        on_started=failed_setup,
        collector_exit_grace_sec=0.05,
    )
except ValueError as error:
    assert str(error) == 'public setup failure'
    print('caller-survived', flush=True)
else:
    raise AssertionError('setup error was lost')
"""
    caller = subprocess.run(
        [sys.executable, "-c", script],
        env=dict(os.environ),
        start_new_session=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        timeout=5,
        check=False,
    )

    assert caller.returncode == 0, caller.stderr
    assert caller.stdout == b"caller-survived\n"
