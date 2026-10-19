"""Candidate lifecycle barriers with controlled execution and archive collection."""

from __future__ import annotations

import subprocess
from types import SimpleNamespace

import pytest

from evaluation.agent import runtime
from evaluation.agent.runtime import (
    AgentLaunchSpec,
    CandidateTerminationError,
)

pytestmark = pytest.mark.integration


# Active candidate containers are stopped and rechecked before archive access.
def test_stop_confirms_no_labeled_container_remains(monkeypatch: pytest.MonkeyPatch) -> None:
    calls: list[list[str]] = []
    responses = iter(("candidate-id\n", "", ""))

    def fake_run(command: list[str], **kwargs):
        calls.append(command)
        return SimpleNamespace(stdout=next(responses), returncode=0)

    monkeypatch.setattr(runtime.subprocess, "run", fake_run)
    runtime.stop_agent_sandbox_containers("controlled", {})
    assert calls[1] == ["docker", "stop", "candidate-id"]
    assert calls[2] == calls[0]


# A candidate still active after Docker stop produces a termination barrier failure.
def test_stop_rejects_remaining_container(monkeypatch: pytest.MonkeyPatch) -> None:
    responses = iter(("candidate-id\n", "", "candidate-id\n"))
    monkeypatch.setattr(
        runtime.subprocess,
        "run",
        lambda *args, **kwargs: SimpleNamespace(stdout=next(responses), returncode=0),
    )
    with pytest.raises(CandidateTerminationError, match="remain active"):
        runtime.stop_agent_sandbox_containers("controlled", {})


# Label-scoped cleanup must verify that only the worker's containers were removed.
def test_label_scoped_cleanup_rechecks_after_removing_worker_containers(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    calls: list[list[str]] = []

    def fake_run(argv: list[str], **_: object) -> subprocess.CompletedProcess[str]:
        calls.append(argv)
        if argv[:3] == ["docker", "ps", "-aq"]:
            stdout = "worker-agent\nworker-evaluator\n" if len(calls) == 1 else ""
            return subprocess.CompletedProcess(argv, 0, stdout=stdout, stderr="")
        if argv[:3] == ["docker", "rm", "-f"]:
            return subprocess.CompletedProcess(argv, 0, stdout="", stderr="")
        raise AssertionError(f"unexpected Docker command: {argv}")

    monkeypatch.setattr(runtime.subprocess, "run", fake_run)

    runtime.cleanup_agent_sandbox_containers("worker-label")

    assert calls == [
        ["docker", "ps", "-aq", "--filter", "label=dafnyutils.eval.run=worker-label"],
        ["docker", "rm", "-f", "worker-agent", "worker-evaluator"],
        ["docker", "ps", "-aq", "--filter", "label=dafnyutils.eval.run=worker-label"],
    ]


# Typed controller identities reject ad hoc users instead of altering container authority.
def test_launch_spec_rejects_untyped_controller_identity() -> None:
    with pytest.raises(TypeError, match="controller_identity must be"):
        AgentLaunchSpec(image="agent:test", controller_identity="0:0")
