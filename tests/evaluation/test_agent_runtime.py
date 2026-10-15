"""Candidate lifecycle barriers with controlled execution and archive collection."""

from __future__ import annotations

import os
import socket
import stat
import subprocess
import tarfile
from dataclasses import replace
from pathlib import Path
from types import SimpleNamespace

import pytest
import yaml

from evaluation.agent import ownership, runtime
from evaluation.agent.runtime import (
    AgentLaunchSpec,
    AgentPreparationContext,
    AgentSandboxContext,
    CandidateExecution,
    CandidateRunContext,
    CandidateTerminationError,
    HarnessExecutionIdentity,
    SandboxProfile,
    build_docker_compose_agent_command,
    prepare_agent_sandbox_context,
    run_candidate_lifecycle,
    write_compose_override,
)
from evaluation.submission.container_mounts import (
    CONTAINER_ORACLE_ISOLATION_ENTRYPOINT,
    ContainerWorkspacePlan,
)
from evaluation.task.release import ArchiveLimits, prepare_release, publish_release

pytestmark = pytest.mark.integration


def _context(tmp_path: Path) -> AgentSandboxContext:
    workspace = tmp_path / "workspace"
    workspace.mkdir()
    return AgentSandboxContext(
        docker_available=False,
        workspace_dir=workspace,
        task_dir=tmp_path / "task",
        run_dir=tmp_path / "run",
        artifact_directory=tmp_path / "artifacts",
        compose_files=(),
        compose_project_name="controlled",
        mount_manifest_path=tmp_path / "mounts.json",
        agent_container_name="controlled-agent",
        container_cleanup_label="controlled",
        command="true",
        env={},
        notes=(),
    )


# Cold preparation reserves protected metadata before the adapter sees read-only mounts.
@pytest.mark.parametrize("controller_identity", tuple(HarnessExecutionIdentity))
@pytest.mark.parametrize("sandbox_profile", tuple(SandboxProfile))
def test_preparation_declares_protected_runtime_capabilities(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    controller_identity: HarnessExecutionIdentity,
    sandbox_profile: SandboxProfile,
) -> None:
    release_directory = tmp_path / "release"
    publish_release(("true",), release_directory)
    release = prepare_release(release_directory, tmp_path / "workspace")
    assert not (release.tasks["true"].workspace / ".codex").exists()
    run_directory = tmp_path / "case"
    run_directory.mkdir()
    preparations: list[AgentPreparationContext] = []

    def prepare_agent(context: AgentPreparationContext) -> AgentLaunchSpec:
        for name in (".agents", ".git", ".codex"):
            assert (context.workspace_directory / name).is_dir()
        preparations.append(context)
        launcher = context.staging_directory / "agent"
        launcher.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
        launcher.chmod(0o755)
        return AgentLaunchSpec(
            image="agent:test",
            sandbox_profile=sandbox_profile,
            controller_identity=controller_identity,
        )

    monkeypatch.setattr(runtime, "docker_runtime_available", lambda: True)
    context = prepare_agent_sandbox_context(
        prepare_agent=prepare_agent,
        record_launch=lambda command, prompt: None,
        compose_file=tmp_path / "base-compose.yml",
        env={"PATH": os.environ["PATH"]},
        run_context=CandidateRunContext(
            run_directory, "true", "direct", run_directory / "artifacts"
        ),
        prepared_candidate=release.tasks["true"],
        release=release,
    )
    (preparation,) = preparations
    compose = yaml.safe_load(context.compose_files[1].read_text(encoding="utf-8"))
    agent = compose["services"]["agent-workflow"]
    assert compose["services"]["task-staging"]["image"] == (
        agent["image"]
        if controller_identity is HarnessExecutionIdentity.TRUSTED_ROOT
        else "dafnyutils-task:latest"
    )
    expected_services = {"agent-workflow", "task-staging"}
    if controller_identity is HarnessExecutionIdentity.TRUSTED_ROOT:
        expected_services.add("ownership-handoff")
        helper = compose["services"]["ownership-handoff"]
        assert helper["image"] == agent["image"]
        assert helper["network_mode"] == "none"
        assert helper["read_only"]
        assert helper.get("environment", {}) == {}
        assert helper["cap_drop"] == ["ALL"]
        allowed = {
            mount["source"]
            for mount in agent["volumes"]
            if not mount["read_only"] and mount["target"] != "/run/agent_home"
        }
        assert {mount["source"] for mount in helper["volumes"]} <= allowed
        assert context.ownership_handoff_command[-1] == "ownership-handoff"
        assert context.ownership_handoff_validation_command
        readonly = {mount["source"] for mount in agent["volumes"] if mount["read_only"]}
        assert not readonly.intersection(mount["source"] for mount in helper["volumes"])
    assert set(compose["services"]) == expected_services
    assert agent["user"] == controller_identity.value
    assert agent["build"]["args"] == {
        "AGENT_UID": str(os.getuid()),
        "AGENT_GID": str(os.getgid()),
    }
    assert agent["command"][0] == CONTAINER_ORACLE_ISOLATION_ENTRYPOINT
    assert agent["environment"]["EVAL_BLOCKED_COREUTIL"] == "true"
    assert ("security_opt" in agent) is (sandbox_profile is SandboxProfile.NESTED_USER_NAMESPACE)
    task_spec = release.tasks["true"].workspace_spec
    assert preparation.read_only_workspace_paths == (
        *task_spec.read_only_paths,
        Path("task"),
        Path("agent"),
        Path(".git"),
        Path(".agents"),
        Path(".codex"),
    )
    assert not set(task_spec.editable_paths).intersection(preparation.read_only_workspace_paths)
    volumes = {mount["target"]: mount for mount in agent["volumes"]}
    for relative in task_spec.read_only_paths:
        assert volumes[f"/workspace/{relative}"]["read_only"]
    for relative in task_spec.editable_paths:
        assert not volumes[f"/workspace/{relative}"]["read_only"]
    for target in ("/workspace", "/workspace/task", "/workspace/agent", "/run/repo_agent"):
        assert volumes[target]["read_only"]
    assert volumes["/usr/bin/true"]["read_only"]
    assert all(not target.startswith(("/repo", "/target")) for target in volumes)
    for target in (
        "/workspace/.agent",
        "/workspace/_build",
        "/run",
        "/run/agent_artifacts",
        "/run/agent_home",
        "/tmp",
    ):
        assert not volumes[target]["read_only"]
    assert preparation.readable_tool_paths == (Path("/opt/dafnyutils-dafny"),)


def _execution(
    *,
    exit_code: int | None = 0,
    timed_out: bool = False,
    protocol_error: str | None = None,
    execution_present: bool = True,
) -> CandidateExecution[str]:
    return CandidateExecution("observed", execution_present, exit_code, timed_out, protocol_error)


def _controlled_boundaries(monkeypatch: pytest.MonkeyPatch, events: list[str]) -> None:
    monkeypatch.setattr(
        runtime, "stop_agent_sandbox_containers", lambda label, env: events.append("stop")
    )
    monkeypatch.setattr(
        runtime, "cleanup_agent_sandbox_context", lambda context: events.append("remove")
    )
    monkeypatch.setattr(
        runtime, "cleanup_sandbox_control_files", lambda context: events.append("control")
    )
    monkeypatch.setattr(
        runtime, "package_workspace", lambda workspace, manifest, archive: events.append("archive")
    )


# A normal candidate is archived only after confirmed shutdown and cleanup.
def test_normal_run_orders_archive_after_shutdown(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    events: list[str] = []
    _controlled_boundaries(monkeypatch, events)
    context = _context(tmp_path)
    outcome = run_candidate_lifecycle(
        prepare=lambda: events.append("prepare") or context,
        execute=lambda prepared: events.append("execute") or _execution(),
        manifest=object(),
        archive_path=tmp_path / "result.tar.gz",
    )
    assert events == ["prepare", "execute", "stop", "remove", "control", "archive"]
    assert outcome.failure_reason is None
    assert not outcome.agent_failed


# Readable public files remain collectable after the usual shutdown barrier.
def test_readable_public_workspace_collects_after_shutdown(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    events: list[str] = []
    context = _context(tmp_path)
    public = context.workspace_dir / "bench/public"
    public.mkdir(parents=True)
    candidate = public / "Core.dfy"
    candidate.write_text("module Candidate {}\n", encoding="utf-8")
    candidate.chmod(0o644)
    public.chmod(0o755)
    manifest = SimpleNamespace(
        task_roots=("bench/public",),
        excluded_names=(),
        excluded_paths=(),
        limits=ArchiveLimits(),
    )
    monkeypatch.setattr(
        runtime, "stop_agent_sandbox_containers", lambda label, env: events.append("stop")
    )
    monkeypatch.setattr(
        runtime, "cleanup_agent_sandbox_context", lambda prepared: events.append("remove")
    )
    monkeypatch.setattr(
        runtime, "cleanup_sandbox_control_files", lambda prepared: events.append("control")
    )
    actual_package = runtime.package_workspace

    def collect(workspace, declared_manifest, archive):
        events.append("archive")
        return actual_package(workspace, declared_manifest, archive)

    monkeypatch.setattr(runtime, "package_workspace", collect)
    archive_path = tmp_path / "result.tar.gz"
    outcome = run_candidate_lifecycle(
        prepare=lambda: context,
        execute=lambda prepared: events.append("execute") or _execution(),
        manifest=manifest,
        archive_path=archive_path,
    )

    assert outcome.failure_reason is None
    assert events == ["execute", "stop", "remove", "control", "archive"]
    with tarfile.open(archive_path, "r:gz") as archive:
        source = archive.extractfile("bench/public/Core.dfy")
        assert source is not None
        assert source.read() == b"module Candidate {}\n"


# A preparation failure does not execute or package a candidate.
def test_preparation_failure_preserves_reason(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    events: list[str] = []
    _controlled_boundaries(monkeypatch, events)

    def fail_prepare() -> AgentSandboxContext:
        raise RuntimeError("controlled setup failure")

    outcome = run_candidate_lifecycle(
        prepare=fail_prepare,
        execute=lambda context: events.append("execute") or _execution(),
        manifest=object(),
        archive_path=tmp_path / "result.tar.gz",
    )
    assert outcome.failure_reason == "controlled setup failure"
    assert outcome.agent_failed
    assert events == []


# A nonzero candidate exit blocks collection while still closing its environment.
def test_nonzero_exit_blocks_archive(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    events: list[str] = []
    _controlled_boundaries(monkeypatch, events)
    outcome = run_candidate_lifecycle(
        prepare=lambda: _context(tmp_path),
        execute=lambda context: _execution(exit_code=7),
        manifest=object(),
        archive_path=tmp_path / "result.tar.gz",
    )
    assert outcome.failure_reason == "agent did not terminate normally: exit code 7"
    assert outcome.agent_failed
    assert events == ["stop", "remove", "control"]


# A timed-out candidate blocks collection even if the command reports a zero exit.
def test_timeout_blocks_archive(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    events: list[str] = []
    _controlled_boundaries(monkeypatch, events)
    outcome = run_candidate_lifecycle(
        prepare=lambda: _context(tmp_path),
        execute=lambda context: _execution(timed_out=True),
        manifest=object(),
        archive_path=tmp_path / "result.tar.gz",
    )
    assert outcome.failure_reason is not None and "timed out" in outcome.failure_reason
    assert events == ["stop", "remove", "control"]


# An invalid candidate report blocks collection after a successful process exit.
def test_protocol_error_blocks_archive(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    events: list[str] = []
    _controlled_boundaries(monkeypatch, events)
    outcome = run_candidate_lifecycle(
        prepare=lambda: _context(tmp_path),
        execute=lambda context: _execution(protocol_error="agent protocol error: bad report"),
        manifest=object(),
        archive_path=tmp_path / "result.tar.gz",
    )
    assert outcome.failure_reason == (
        "agent did not terminate normally: agent protocol error: bad report"
    )
    assert events == ["stop", "remove", "control"]


# An absent command retains the established missing-command failure detail.
def test_missing_execution_blocks_archive(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    events: list[str] = []
    _controlled_boundaries(monkeypatch, events)
    outcome = run_candidate_lifecycle(
        prepare=lambda: _context(tmp_path),
        execute=lambda context: _execution(exit_code=None, execution_present=False),
        manifest=object(),
        archive_path=tmp_path / "result.tar.gz",
    )
    assert outcome.failure_reason == "agent did not terminate normally: agent command was not run"
    assert events == ["stop", "remove", "control"]


# An unconfirmed shutdown blocks archive collection and retains private control files.
def test_unconfirmed_shutdown_blocks_archive(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    events: list[str] = []
    _controlled_boundaries(monkeypatch, events)

    def fail_stop(label: str, env: dict[str, str]) -> None:
        events.append("stop")
        raise CandidateTerminationError("cannot confirm candidate environment termination")

    monkeypatch.setattr(runtime, "stop_agent_sandbox_containers", fail_stop)
    outcome = run_candidate_lifecycle(
        prepare=lambda: _context(tmp_path),
        execute=lambda context: _execution(),
        manifest=object(),
        archive_path=tmp_path / "result.tar.gz",
    )
    assert outcome.failure_reason == "cannot confirm candidate environment termination"
    assert outcome.agent_failed
    assert events == ["stop", "remove"]


# A host packaging failure blocks evaluation without reclassifying the agent run.
def test_packaging_failure_is_separate_from_agent_failure(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    events: list[str] = []
    _controlled_boundaries(monkeypatch, events)

    def fail_package(workspace: Path, manifest: object, archive: Path) -> None:
        events.append("archive")
        raise ValueError("invalid candidate path")

    monkeypatch.setattr(runtime, "package_workspace", fail_package)
    outcome = run_candidate_lifecycle(
        prepare=lambda: _context(tmp_path),
        execute=lambda context: _execution(),
        manifest=object(),
        archive_path=tmp_path / "result.tar.gz",
    )
    assert outcome.failure_reason == "host submission packaging failed: invalid candidate path"
    assert not outcome.agent_failed
    assert events == ["stop", "remove", "control", "archive"]


# An execution exception still closes the candidate before propagating the bug.
def test_execution_exception_cleans_up(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    events: list[str] = []
    _controlled_boundaries(monkeypatch, events)

    def fail_execute(context: AgentSandboxContext) -> CandidateExecution[str]:
        raise AssertionError("observer failed")

    with pytest.raises(AssertionError, match="observer failed"):
        run_candidate_lifecycle(
            prepare=lambda: _context(tmp_path),
            execute=fail_execute,
            manifest=object(),
            archive_path=tmp_path / "result.tar.gz",
        )
    assert events == ["stop", "remove", "control"]


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


def _fake_docker_command(
    tmp_path: Path,
    *,
    fail_copy: bool,
    agent_exit_code: int = 7,
    failing_exit_hook: bool = False,
    trusted_controller: bool = False,
    active_container: bool = False,
    fail_handoff: bool = False,
) -> subprocess.CompletedProcess[str]:
    fake_bin = tmp_path / "bin"
    fake_bin.mkdir()
    docker = fake_bin / "docker"
    docker.write_text(
        """#!/usr/bin/env bash
printf '%s\\n' "$*" >> "$DOCKER_CALLS"
if [ "$1" = cp ] && [ "$FAIL_COPY" = 1 ]; then exit 17; fi
if [ "$1" = logs ]; then printf 'agent output\\n'; fi
if [ "$1" = wait ]; then printf '%s\\n' "$AGENT_EXIT_CODE"; fi
if [ "$1" = ps ] && [ "$ACTIVE_CONTAINER" = 1 ]; then printf 'still-active\\n'; fi
if [ "$2" = run ] && [ "$FAIL_HANDOFF" = 1 ]; then exit 19; fi
""",
        encoding="utf-8",
    )
    docker.chmod(0o755)
    command = build_docker_compose_agent_command(
        compose_files=(tmp_path / "compose.yaml",),
        service="agent-workflow",
        project_name="run-123",
        container_name="run-123-agent",
        staging_container_name="run-123-staging",
        workspace_dir=tmp_path / "workspace",
        ownership_handoff_command=("docker", "compose", "run", "ownership-handoff")
        if trusted_controller
        else (),
        ownership_handoff_validation_command=("true",) if trusted_controller else (),
        ownership_handoff_complete_path=tmp_path / "handoff-complete"
        if trusted_controller
        else None,
        container_cleanup_label="run-123" if trusted_controller else None,
    )
    if failing_exit_hook:
        command = "trap 'false' EXIT; " + command
    return subprocess.run(
        ["bash", "-c", command],
        cwd=tmp_path,
        env={
            **os.environ,
            "PATH": f"{fake_bin}:{os.environ['PATH']}",
            "DOCKER_CALLS": str(tmp_path / "docker-calls"),
            "FAIL_COPY": "1" if fail_copy else "0",
            "AGENT_EXIT_CODE": str(agent_exit_code),
            "ACTIVE_CONTAINER": "1" if active_container else "0",
            "FAIL_HANDOFF": "1" if fail_handoff else "0",
        },
        capture_output=True,
        text=True,
        check=False,
    )


# A generic launch spec renders its command, mounts, user, and permitted environment.
def test_launch_spec_renders_agent_service(tmp_path: Path) -> None:
    agent_plan = ContainerWorkspacePlan(
        service="agent-workflow",
        mounts=(),
        working_dir="/workspace",
        environment={},
    )
    output = tmp_path / "compose.yaml"
    write_compose_override(
        path=output,
        agent_plan=agent_plan,
        agent_environment={},
        agent_container_name="agent-test",
        staging_container_name="agent-test-staging",
        staged_workspace_dir=tmp_path / "public_workspace",
        agent_launch=AgentLaunchSpec(
            image="cosyn-evaluation:test",
            forwarded_secret_environment=("CODEX_API_KEY",),
            sandbox_profile=SandboxProfile.NESTED_USER_NAMESPACE,
        ),
        launch_command=(
            "./agent",
            "exec",
            "--prompt=Implement the task. Preserve 'quotes', $variables and\nnewlines.",
        ),
    )

    payload = yaml.safe_load(output.read_text(encoding="utf-8"))
    agent = payload["services"]["agent-workflow"]
    staging = payload["services"]["task-staging"]
    assert staging["image"] == "dafnyutils-task:latest"
    assert staging["volumes"][0]["read_only"] is False
    assert agent["image"] == "cosyn-evaluation:test"
    assert agent["user"] == "agent"
    assert agent["build"]["args"] == {
        "AGENT_UID": str(os.getuid()),
        "AGENT_GID": str(os.getgid()),
    }
    assert agent["working_dir"] == "/workspace"
    assert agent["command"][-3:] == [
        "./agent",
        "exec",
        "--prompt=Implement the task. Preserve 'quotes', $$variables and\nnewlines.",
    ]
    assert agent["security_opt"] == [
        "seccomp=unconfined",
        "apparmor=unconfined",
        "systempaths=unconfined",
    ]
    assert agent["environment"]["CODEX_API_KEY"] is None


# Typed controller identities reject ad hoc users instead of altering container authority.
def test_launch_spec_rejects_untyped_controller_identity() -> None:
    with pytest.raises(TypeError, match="controller_identity must be"):
        AgentLaunchSpec(image="agent:test", controller_identity="0:0")


# A copied public workspace reaches the agent only after create and preserves its exit code.
def test_agent_container_starts_after_copy_and_reports_exit_code(tmp_path: Path) -> None:
    result = _fake_docker_command(tmp_path, fail_copy=False)

    assert result.returncode == 7
    assert "agent output" in result.stdout
    calls = (tmp_path / "docker-calls").read_text(encoding="utf-8").splitlines()
    assert " create --no-build task-staging" in calls[0]
    assert "/workspace/. run-123-staging:/workspace/" in calls[1]
    assert calls[2] == "rm run-123-staging"
    assert " create --no-build agent-workflow" in calls[3]
    assert calls[4:] == [
        "start run-123-agent",
        "logs --follow run-123-agent",
        "wait run-123-agent",
    ]


# Normal trusted-controller return hands metadata back only after Docker confirms no actors.
def test_normal_trusted_handoff_precedes_host_return(tmp_path: Path) -> None:
    result = _fake_docker_command(
        tmp_path, fail_copy=False, agent_exit_code=0, trusted_controller=True
    )
    assert result.returncode == 0
    calls = (tmp_path / "docker-calls").read_text().splitlines()
    assert calls[-3:] == [
        "wait run-123-agent",
        "ps -q --filter label=dafnyutils.eval.run=run-123",
        "compose run ownership-handoff",
    ]
    assert (tmp_path / "handoff-complete").is_file()


# A live run-labeled actor prevents metadata handoff and host-side collection admission.
def test_normal_handoff_refuses_active_container(tmp_path: Path) -> None:
    result = _fake_docker_command(
        tmp_path, fail_copy=False, trusted_controller=True, active_container=True
    )
    assert result.returncode == 125
    assert "containers remain active" in result.stderr
    assert not (tmp_path / "handoff-complete").exists()
    assert (tmp_path / "docker-calls").read_text().splitlines()[-1].startswith("ps ")


# A failed normal handoff reports an infrastructure error instead of returning success.
def test_normal_handoff_failure_blocks_return(tmp_path: Path) -> None:
    result = _fake_docker_command(
        tmp_path, fail_copy=False, agent_exit_code=0, trusted_controller=True, fail_handoff=True
    )
    assert result.returncode == 125
    assert "ownership handoff failed" in result.stderr
    assert not (tmp_path / "handoff-complete").exists()


# Successful metadata handoff preserves the original candidate failure exit code.
def test_trusted_handoff_preserves_candidate_exit_code(tmp_path: Path) -> None:
    result = _fake_docker_command(tmp_path, fail_copy=False, trusted_controller=True)
    assert result.returncode == 7
    assert (tmp_path / "handoff-complete").is_file()


# A failing caller-shell cleanup cannot turn normal candidate completion into failure.
def test_normal_agent_exit_survives_failing_shell_exit_hook(tmp_path: Path) -> None:
    result = _fake_docker_command(
        tmp_path, fail_copy=False, agent_exit_code=0, failing_exit_hook=True
    )

    assert result.returncode == 0
    assert "agent output" in result.stdout


# A failing caller-shell cleanup cannot replace the candidate's nonzero exit code.
def test_failed_agent_exit_survives_failing_shell_exit_hook(tmp_path: Path) -> None:
    result = _fake_docker_command(
        tmp_path, fail_copy=False, agent_exit_code=7, failing_exit_hook=True
    )

    assert result.returncode == 7
    assert "agent output" in result.stdout


# A failed public file copy stops before the candidate process starts.
def test_agent_container_never_starts_after_failed_copy(tmp_path: Path) -> None:
    result = _fake_docker_command(tmp_path, fail_copy=True)

    assert result.returncode == 17
    calls = (tmp_path / "docker-calls").read_text(encoding="utf-8").splitlines()
    assert len(calls) == 2
    assert calls[1].startswith("cp ")


def _trusted_context(tmp_path: Path) -> AgentSandboxContext:
    return replace(
        _context(tmp_path),
        env={"PATH": os.environ["PATH"], "CODEX_API_KEY": "public-test-sentinel"},
        ownership_handoff_command=("docker", "compose", "run", "ownership-handoff"),
        ownership_handoff_validation_command=("validate-sources",),
        ownership_handoff_complete_path=tmp_path / "handoff-complete",
    )


# Forced-stop collection transfers metadata only after stop and before any control cleanup.
def test_forced_stop_handoff_orders_metadata_before_cleanup(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    events: list[str] = []
    _controlled_boundaries(monkeypatch, events)
    context = _trusted_context(tmp_path)

    def fake_run(command, **kwargs):
        if command[0] == "validate-sources":
            events.append("validate")
        else:
            events.append("handoff")
            assert "CODEX_API_KEY" not in kwargs["env"]
        return subprocess.CompletedProcess(command, 0)

    monkeypatch.setattr(runtime.subprocess, "run", fake_run)
    outcome = run_candidate_lifecycle(
        prepare=lambda: context,
        execute=lambda prepared: _execution(timed_out=True),
        manifest=object(),
        archive_path=tmp_path / "result.tar.gz",
    )
    assert events == ["stop", "validate", "handoff", "remove", "control"]
    assert outcome.failure_reason is not None and "timed out" in outcome.failure_reason
    assert context.ownership_handoff_complete_path.is_file()


# Metadata handoff failure remains an infrastructure failure and prevents archive creation.
def test_failed_handoff_blocks_archive_without_blaming_candidate(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    events: list[str] = []
    _controlled_boundaries(monkeypatch, events)
    context = _trusted_context(tmp_path)

    def fail_handoff(command, **kwargs):
        if command[0] == "validate-sources":
            return subprocess.CompletedProcess(command, 0)
        events.append("handoff")
        raise subprocess.CalledProcessError(19, command)

    monkeypatch.setattr(runtime.subprocess, "run", fail_handoff)
    outcome = run_candidate_lifecycle(
        prepare=lambda: context,
        execute=lambda prepared: _execution(),
        manifest=object(),
        archive_path=tmp_path / "result.tar.gz",
    )
    assert outcome.failure_reason == "candidate output ownership handoff failed"
    assert not outcome.agent_failed
    assert events == ["stop", "handoff", "remove"]
    assert not context.ownership_handoff_complete_path.exists()


# Failed termination cannot transfer ownership while an untrusted actor may still run.
def test_unconfirmed_stop_blocks_trusted_handoff(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    events: list[str] = []
    _controlled_boundaries(monkeypatch, events)
    context = _trusted_context(tmp_path)

    def fail_stop(label, env):
        events.append("stop")
        raise CandidateTerminationError("candidate still active")

    monkeypatch.setattr(runtime, "stop_agent_sandbox_containers", fail_stop)
    monkeypatch.setattr(
        runtime, "handoff_agent_sandbox_ownership", lambda prepared: events.append("handoff")
    )
    outcome = run_candidate_lifecycle(
        prepare=lambda: context,
        execute=lambda prepared: _execution(),
        manifest=object(),
        archive_path=tmp_path / "result.tar.gz",
    )
    assert outcome.failure_reason == "candidate still active"
    assert events == ["stop", "remove"]


# A host-only normal completion marker avoids repeating the successful metadata helper.
def test_completed_normal_handoff_is_not_repeated(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    events: list[str] = []
    _controlled_boundaries(monkeypatch, events)
    context = _trusted_context(tmp_path)
    context.ownership_handoff_complete_path.touch()
    outcome = run_candidate_lifecycle(
        prepare=lambda: context,
        execute=lambda prepared: _execution(),
        manifest=object(),
        archive_path=tmp_path / "result.tar.gz",
    )
    assert outcome.failure_reason is None
    assert events == ["stop", "remove", "control", "archive"]


def _readonly_control_context(context: AgentSandboxContext) -> AgentSandboxContext:
    root = context.workspace_dir.parent
    control = root / "control"
    projection = control / "model_workspace/public-inputs/task/bench/public"
    projection.mkdir(parents=True)
    public_input = projection / "Spec.dfy"
    public_input.write_bytes(b"public readonly projection\n")
    public_input.chmod(0o444)
    outside = root / "outside-input"
    outside.mkdir()
    sentinel = outside / "sentinel"
    sentinel.write_bytes(b"external readonly sentinel\n")
    sentinel.chmod(0o444)
    (projection / "hardlink").hardlink_to(sentinel)
    (projection / "symlink").symlink_to(sentinel)
    (projection / "directory-link").symlink_to(outside, target_is_directory=True)
    outside.chmod(0o555)
    for directory, _, _ in os.walk(control):
        Path(directory).chmod(0o555)
    return replace(context, control_dir=control)


def _control_modes(context: AgentSandboxContext) -> dict[Path, int]:
    assert context.control_dir is not None
    return {
        path: path.lstat().st_mode & 0o7777
        for path in (context.control_dir, *context.control_dir.rglob("*"))
    }


# Confirmed shutdown and handoff remove real readonly projections without chmod of linked inputs.
def test_confirmed_cleanup_removes_readonly_projection_and_preserves_links(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    context = _readonly_control_context(_trusted_context(tmp_path))
    modes = _control_modes(context)
    events: list[str] = []
    actual_cleanup = runtime.cleanup_sandbox_control_files
    _controlled_boundaries(monkeypatch, events)

    def barrier(event: str) -> None:
        assert _control_modes(context) == modes
        events.append(event)

    monkeypatch.setattr(runtime, "stop_agent_sandbox_containers", lambda *args: barrier("stop"))
    monkeypatch.setattr(
        runtime, "handoff_agent_sandbox_ownership", lambda prepared: barrier("handoff")
    )

    def cleanup(prepared: AgentSandboxContext) -> None:
        events.append("control")
        actual_cleanup(prepared)

    def archive(*args: object) -> None:
        assert not context.control_dir.exists()
        events.append("archive")

    monkeypatch.setattr(runtime, "cleanup_sandbox_control_files", cleanup)
    monkeypatch.setattr(runtime, "package_workspace", archive)
    sentinel = tmp_path / "outside-input/sentinel"
    before = sentinel.stat()
    outcome = run_candidate_lifecycle(
        prepare=lambda: context,
        execute=lambda prepared: _execution(),
        manifest=object(),
        archive_path=tmp_path / "result.tar.gz",
    )
    assert outcome.failure_reason is None
    assert events == ["stop", "handoff", "remove", "control", "archive"]
    assert not context.control_dir.exists()
    assert sentinel.read_bytes() == b"external readonly sentinel\n"
    after = sentinel.stat()
    assert (after.st_mode, after.st_uid, after.st_gid) == (
        before.st_mode,
        before.st_uid,
        before.st_gid,
    )
    assert sentinel.parent.stat().st_mode & 0o7777 == 0o555


# A stopped timed-out candidate still releases readonly control projections without archiving.
def test_timeout_removes_readonly_control_after_handoff(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    context = _readonly_control_context(_trusted_context(tmp_path))
    events: list[str] = []
    actual_cleanup = runtime.cleanup_sandbox_control_files
    _controlled_boundaries(monkeypatch, events)
    monkeypatch.setattr(runtime, "cleanup_sandbox_control_files", actual_cleanup)
    monkeypatch.setattr(
        runtime, "handoff_agent_sandbox_ownership", lambda prepared: events.append("handoff")
    )
    outcome = run_candidate_lifecycle(
        prepare=lambda: context,
        execute=lambda prepared: _execution(timed_out=True),
        manifest=object(),
        archive_path=tmp_path / "result.tar.gz",
    )
    assert outcome.failure_reason is not None and "timed out" in outcome.failure_reason
    assert not context.control_dir.exists()
    assert events == ["stop", "handoff", "remove"]


# Failed termination leaves real readonly directory and file permissions untouched.
def test_unconfirmed_stop_retains_readonly_control_permissions(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    context = _readonly_control_context(_trusted_context(tmp_path))
    modes = _control_modes(context)
    events: list[str] = []
    actual_cleanup = runtime.cleanup_sandbox_control_files
    _controlled_boundaries(monkeypatch, events)
    monkeypatch.setattr(runtime, "cleanup_sandbox_control_files", actual_cleanup)

    def fail_stop(*args: object) -> None:
        events.append("stop")
        raise CandidateTerminationError("candidate still active")

    monkeypatch.setattr(runtime, "stop_agent_sandbox_containers", fail_stop)
    monkeypatch.setattr(
        runtime, "handoff_agent_sandbox_ownership", lambda prepared: events.append("handoff")
    )
    outcome = run_candidate_lifecycle(
        prepare=lambda: context,
        execute=lambda prepared: _execution(),
        manifest=object(),
        archive_path=tmp_path / "result.tar.gz",
    )
    assert outcome.failure_reason == "candidate still active"
    assert _control_modes(context) == modes
    assert events == ["stop", "remove"]


# Failed ownership handoff leaves real readonly directory and file permissions untouched.
def test_failed_handoff_retains_readonly_control_permissions(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    context = _readonly_control_context(_trusted_context(tmp_path))
    modes = _control_modes(context)
    events: list[str] = []
    actual_cleanup = runtime.cleanup_sandbox_control_files
    _controlled_boundaries(monkeypatch, events)
    monkeypatch.setattr(runtime, "cleanup_sandbox_control_files", actual_cleanup)

    def fail_handoff(prepared: AgentSandboxContext) -> None:
        events.append("handoff")
        raise runtime.CandidateOwnershipError("candidate output ownership handoff failed")

    monkeypatch.setattr(runtime, "handoff_agent_sandbox_ownership", fail_handoff)
    outcome = run_candidate_lifecycle(
        prepare=lambda: context,
        execute=lambda prepared: _execution(),
        manifest=object(),
        archive_path=tmp_path / "result.tar.gz",
    )
    assert outcome.failure_reason == "candidate output ownership handoff failed"
    assert not outcome.agent_failed
    assert _control_modes(context) == modes
    assert events == ["stop", "handoff", "remove"]


# A real control removal error blocks archiving and reports a host infrastructure failure.
def test_control_removal_error_blocks_archive(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    context = replace(_context(tmp_path), control_dir=tmp_path / "control")
    context.control_dir.mkdir()
    events: list[str] = []
    actual_cleanup = runtime.cleanup_sandbox_control_files
    _controlled_boundaries(monkeypatch, events)
    monkeypatch.setattr(runtime, "cleanup_sandbox_control_files", actual_cleanup)

    def fail_remove(*args: object, **kwargs: object) -> None:
        raise PermissionError("control removal denied")

    monkeypatch.setattr(runtime.shutil, "rmtree", fail_remove)
    outcome = run_candidate_lifecycle(
        prepare=lambda: context,
        execute=lambda prepared: _execution(),
        manifest=object(),
        archive_path=tmp_path / "result.tar.gz",
    )
    assert outcome.failure_reason == "host sandbox control cleanup failed: control removal denied"
    assert not outcome.agent_failed
    assert context.control_dir.exists()
    assert events == ["stop", "remove"]


# A cleanup I/O failure cannot replace the execution exception that caused finalization.
def test_control_removal_error_preserves_execution_bug(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    events: list[str] = []
    _controlled_boundaries(monkeypatch, events)

    def fail_execute(prepared: AgentSandboxContext) -> CandidateExecution[str]:
        raise AssertionError("observer failed")

    def fail_cleanup(prepared: AgentSandboxContext) -> None:
        raise PermissionError("control removal denied")

    monkeypatch.setattr(runtime, "cleanup_sandbox_control_files", fail_cleanup)
    with pytest.raises(AssertionError, match="observer failed"):
        run_candidate_lifecycle(
            prepare=lambda: _context(tmp_path),
            execute=fail_execute,
            manifest=object(),
            archive_path=tmp_path / "result.tar.gz",
        )
    assert events == ["stop", "remove"]


# Metadata transfer keeps private result bytes and permission modes intact.
def test_handoff_preserves_private_modes_and_bytes(tmp_path: Path) -> None:
    root = tmp_path / "outputs"
    root.mkdir(mode=0o755)
    result = root / "agent-result.json"
    result.write_bytes(b'{"public": "fake-result"}\n')
    result.chmod(0o600)
    ownership.handoff_ownership((root,), exclusions=(), uid=os.getuid(), gid=os.getgid())
    assert result.read_bytes() == b'{"public": "fake-result"}\n'
    assert result.stat().st_mode & 0o7777 == 0o600
    assert root.stat().st_mode & 0o7777 == 0o755
    assert (result.stat().st_uid, result.stat().st_gid) == (os.getuid(), os.getgid())


# Symlinks and declared readonly children never receive ownership metadata changes.
def test_handoff_preserves_external_link_and_readonly_sentinels(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    root = tmp_path / "outputs"
    root.mkdir()
    outside = tmp_path / "readonly-external"
    outside.write_bytes(b"external sentinel")
    outside.chmod(0o444)
    protected = root / "Spec.dfy"
    protected.write_bytes(b"protected sentinel")
    protected.chmod(0o444)
    (root / "link").symlink_to(outside)
    changed: set[int] = set()
    actual_chown = os.fchown

    def observe_chown(descriptor, uid, gid):
        changed.add(os.fstat(descriptor).st_ino)
        actual_chown(descriptor, uid, gid)

    monkeypatch.setattr(ownership.os, "fchown", observe_chown)
    ownership.handoff_ownership((root,), exclusions=(protected,), uid=os.getuid(), gid=os.getgid())
    assert outside.stat().st_ino not in changed
    assert protected.stat().st_ino not in changed
    assert outside.read_bytes() == b"external sentinel"
    assert protected.read_bytes() == b"protected sentinel"
    assert outside.stat().st_mode & 0o7777 == protected.stat().st_mode & 0o7777 == 0o444


# Hardlinked files cannot make metadata transfer affect an external inode.
def test_handoff_refuses_hardlinked_file(tmp_path: Path) -> None:
    root = tmp_path / "outputs"
    root.mkdir()
    outside = tmp_path / "external"
    outside.write_bytes(b"external sentinel")
    (root / "alias").hardlink_to(outside)
    with pytest.raises(ValueError, match="hardlinked"):
        ownership.handoff_ownership((root,), exclusions=(), uid=os.getuid(), gid=os.getgid())
    assert outside.read_bytes() == b"external sentinel"


# Fresh validation rejects a writable ancestor substituted after initial staging checks.
def test_post_stop_validation_refuses_replaced_source_ancestor(tmp_path: Path) -> None:
    writable = tmp_path / "writable"
    source = writable / "output"
    source.mkdir(parents=True)
    readonly = tmp_path / "readonly"
    (readonly / "output").mkdir(parents=True)
    sentinel = readonly / "output/sentinel"
    sentinel.write_bytes(b"readonly sentinel")
    sentinel.chmod(0o444)
    ownership.validate_handoff_sources((source,), protected=(readonly,))
    writable.rename(tmp_path / "original-writable")
    writable.symlink_to(readonly, target_is_directory=True)
    with pytest.raises(OSError):
        ownership.validate_handoff_sources((source,), protected=(readonly,))
    assert sentinel.read_bytes() == b"readonly sentinel"
    assert sentinel.stat().st_mode & 0o7777 == 0o444


# Explicit protected inode aliases are rejected before a privileged helper can mount them.
def test_post_stop_validation_refuses_protected_source_alias(tmp_path: Path) -> None:
    sentinel = tmp_path / "protected"
    sentinel.write_bytes(b"readonly sentinel")
    sentinel.chmod(0o444)
    with pytest.raises(ValueError, match="aliases a protected input"):
        ownership.validate_handoff_sources((sentinel,), protected=(sentinel,))
    assert sentinel.stat().st_mode & 0o7777 == 0o444


# A large hostile link set consumes the same bounded traversal budget as ordinary entries.
def test_handoff_bounds_skipped_links(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    root = tmp_path / "outputs"
    root.mkdir()
    (root / "first").symlink_to(tmp_path / "outside")
    (root / "second").symlink_to(tmp_path / "outside")
    monkeypatch.setattr(ownership, "_MAX_ENTRIES", 1)
    with pytest.raises(TimeoutError, match="exceeded its bounds"):
        ownership.handoff_ownership((root,), exclusions=(), uid=os.getuid(), gid=os.getgid())


# Transient runtime IPC keeps its metadata while the ordinary result completes handoff.
@pytest.mark.parametrize("ipc_kind", ("fifo", "socket"))
def test_handoff_skips_ipc(tmp_path: Path, monkeypatch: pytest.MonkeyPatch, ipc_kind: str) -> None:
    root = tmp_path / "outputs"
    root.mkdir()
    ipc = root / "ipc"
    endpoint = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM) if ipc_kind == "socket" else None
    if endpoint is None:
        os.mkfifo(ipc, 0o700)
    else:
        endpoint.bind(str(ipc))
        ipc.chmod(0o700)
    result = root / "agent-result.json"
    result.write_bytes(b'{"ok": false}\n')
    result.chmod(0o600)
    before = ipc.lstat()
    opened: list[str] = []
    changed: set[tuple[int, int]] = set()
    actual_open = os.open
    actual_chown = os.fchown

    def observe_open(path, flags, *args, **kwargs):
        opened.append(str(path))
        return actual_open(path, flags, *args, **kwargs)

    def observe_chown(descriptor, uid, gid):
        metadata = os.fstat(descriptor)
        changed.add((metadata.st_dev, metadata.st_ino))
        actual_chown(descriptor, uid, gid)

    monkeypatch.setattr(ownership.os, "open", observe_open)
    monkeypatch.setattr(ownership.os, "fchown", observe_chown)
    try:
        ownership.handoff_ownership((root,), exclusions=(), uid=os.getuid(), gid=os.getgid())
    finally:
        if endpoint is not None:
            endpoint.close()
    after = ipc.lstat()
    assert (after.st_dev, after.st_ino, after.st_mode, after.st_uid, after.st_gid) == (
        before.st_dev,
        before.st_ino,
        before.st_mode,
        before.st_uid,
        before.st_gid,
    )
    assert "ipc" not in opened
    assert (after.st_dev, after.st_ino) not in changed
    assert (result.stat().st_dev, result.stat().st_ino) in changed
    assert result.read_bytes() == b'{"ok": false}\n'
    assert result.stat().st_mode & 0o7777 == 0o600
    assert (result.stat().st_uid, result.stat().st_gid) == (os.getuid(), os.getgid())


# A special root is refused rather than admitted by the child-only IPC exception.
def test_handoff_refuses_fifo_root(tmp_path: Path) -> None:
    pipe = tmp_path / "pipe"
    os.mkfifo(pipe, 0o700)
    before = pipe.lstat()
    with pytest.raises(ValueError, match="root must be a regular file or directory"):
        ownership.handoff_ownership((pipe,), exclusions=(), uid=os.getuid(), gid=os.getgid())
    assert pipe.lstat() == before
    with pytest.raises(ValueError, match="source must be a real file or directory"):
        ownership.validate_handoff_sources((pipe,), protected=())


# Device metadata is rejected before opening even when an ordinary entry changes type.
def test_handoff_rejects_device_child_before_open(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    root = tmp_path / "outputs"
    root.mkdir()
    device = root / "device"
    device.write_bytes(b"device sentinel")
    before = device.stat()
    opened: list[str] = []
    actual_open = os.open
    actual_stat = os.stat

    def device_metadata(path, *args, **kwargs):
        metadata = actual_stat(path, *args, **kwargs)
        if path == "device":
            return os.stat_result((stat.S_IFCHR | 0o600, *metadata[1:]))
        return metadata

    def observe_open(path, flags, *args, **kwargs):
        opened.append(str(path))
        return actual_open(path, flags, *args, **kwargs)

    monkeypatch.setattr(ownership.os, "stat", device_metadata)
    monkeypatch.setattr(ownership.os, "open", observe_open)
    with pytest.raises(ValueError, match="unsupported filesystem entry"):
        ownership.handoff_ownership((root,), exclusions=(), uid=os.getuid(), gid=os.getgid())
    assert "device" not in opened
    assert device.stat() == before
    assert device.read_bytes() == b"device sentinel"


# Skipped FIFO endpoints still consume the bounded traversal budget.
def test_handoff_bounds_skipped_fifos(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    root = tmp_path / "outputs"
    root.mkdir()
    os.mkfifo(root / "pipe", 0o600)
    monkeypatch.setattr(ownership, "_MAX_ENTRIES", 1)
    with pytest.raises(TimeoutError, match="exceeded its bounds"):
        ownership.handoff_ownership((root,), exclusions=(), uid=os.getuid(), gid=os.getgid())


# An expired handoff deadline still prevents traversal of a directory containing IPC.
def test_handoff_bounds_expired_ipc(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    root = tmp_path / "outputs"
    root.mkdir()
    os.mkfifo(root / "pipe", 0o600)
    monkeypatch.setattr(ownership, "_TIMEOUT_SECONDS", 0)
    with pytest.raises(TimeoutError, match="exceeded its bounds"):
        ownership.handoff_ownership((root,), exclusions=(), uid=os.getuid(), gid=os.getgid())
