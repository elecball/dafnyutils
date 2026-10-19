"""Controlled subprocesses exercise capture completion and interrupted pipe drain."""

from __future__ import annotations

import os
import resource
import select
import subprocess
import sys
import threading
from dataclasses import dataclass, field

import pytest

from runtime.process import run_process_capture_bytes

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
