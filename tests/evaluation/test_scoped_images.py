"""Check image transport using in-memory preparation and Compose boundaries."""

from __future__ import annotations

import os
import shlex
import shutil
import subprocess
import tempfile
from pathlib import Path
from types import SimpleNamespace
from typing import Any
from unittest.mock import Mock

import pytest
import yaml

from benchmarks.checks import OracleExecutionLocation
from benchmarks.definition import BenchmarkEvaluation, OutputContract
from benchmarks.profiles import ResolvedBenchmark, RuntimeExternExecution
from evaluation.agent import runtime
from evaluation.enums import MountMode
from evaluation.submission.container_mounts import ContainerMount, ContainerWorkspacePlan
from evaluation.submission.oracles import build_evaluations, derived_oracle_commands


def _forbidden(*args: Any, **kwargs: Any) -> Any:
    raise AssertionError("an operational I/O boundary must be faked")


@pytest.fixture(autouse=True)
def _guard_io(monkeypatch: pytest.MonkeyPatch) -> None:
    # Collection imports definitions only; execution never stages or cleans files.
    for name in ("mkdir", "write_text", "write_bytes", "read_text", "read_bytes", "touch"):
        monkeypatch.setattr(Path, name, _forbidden)
    monkeypatch.setattr(Path, "resolve", lambda path, *args, **kwargs: path)
    for module, names in (
        (tempfile, ("mkdtemp", "TemporaryDirectory")),
        (shutil, ("rmtree", "copytree", "copy2")),
        (subprocess, ("run", "Popen")),
        (os, ("fsync", "fdatasync", "sync", "walk")),
        (
            runtime,
            (
                "docker_runtime_available",
                "seed_workspace_isolation_tools",
                "prepare_oracle_executable_block",
                "write_agent_task",
                "candidate_container_plan",
                "write_mount_manifest",
                "prepare_agent_mount_permissions",
            ),
        ),
    ):
        for name in names:
            monkeypatch.setattr(module, name, _forbidden)
    monkeypatch.setattr(ContainerMount, "as_compose_volume", _forbidden)


def _plan() -> ContainerWorkspacePlan:
    return ContainerWorkspacePlan(
        service="agent-workflow",
        mounts=(
            ContainerMount(Path("/virtual/public"), "/workspace", MountMode.READ_ONLY),
            ContainerMount(Path("/virtual/output"), "/workspace/output", MountMode.READ_WRITE),
            ContainerMount(Path("/virtual/task"), "/workspace/task", MountMode.READ_ONLY),
            ContainerMount(Path("/virtual/home"), "/run/agent_home", MountMode.READ_WRITE),
        ),
        working_dir="/workspace",
        environment={"HOME": "/run/agent_home"},
    )


def _compose_inputs(**overrides: Any) -> dict[str, Any]:
    return {
        "path": Path("/virtual/compose.yml"),
        "agent_plan": _plan(),
        "agent_environment": {"NUGET_PACKAGES": "/cache/nuget"},
        "agent_container_name": "run-agent",
        "staging_container_name": "run-staging",
        "staged_workspace_dir": Path("/virtual/staged"),
        "agent_launch": runtime.AgentLaunchSpec(
            image="harness:run",
            environment={"MODE": "test"},
            forwarded_secret_environment=("AUTH",),
            sandbox_profile=runtime.SandboxProfile.NESTED_USER_NAMESPACE,
        ),
        "launch_command": ("./agent", "exec", "--prompt=public $input"),
        "container_labels": {"dafnyutils.eval.run": "run"},
        **overrides,
    }


def _render(monkeypatch: pytest.MonkeyPatch, **overrides: Any) -> dict[str, Any]:
    written: list[str] = []
    monkeypatch.setattr(Path, "mkdir", Mock())
    monkeypatch.setattr(Path, "read_text", lambda *args, **kwargs: "ownership-script")
    monkeypatch.setattr(Path, "write_text", lambda path, text, **kwargs: written.append(text))
    monkeypatch.setattr(
        ContainerMount,
        "as_compose_volume",
        lambda mount: {
            "type": "bind",
            "source": str(mount.source),
            "target": mount.target,
            "read_only": mount.mode is MountMode.READ_ONLY,
        },
    )
    runtime.write_compose_override(**_compose_inputs(**overrides))
    assert len(written) == 1
    return yaml.safe_load(written[0])["services"]


def _prepare_inputs() -> dict[str, Any]:
    return {
        "prepare_agent": Mock(return_value=runtime.AgentLaunchSpec("harness:run")),
        "record_launch": Mock(),
        "compose_file": Path("/virtual/base-compose.yml"),
        "env": {"PATH": "/bin", "UNRELATED": "excluded"},
        "run_context": runtime.CandidateRunContext(
            run_dir=Path("/virtual/run"),
            utility_name="demo",
            comparison_id="comparison",
            agent_artifact_dir=Path("/virtual/artifacts"),
        ),
        "prepared_candidate": SimpleNamespace(
            workspace=Path("/virtual/public"),
            workspace_spec=SimpleNamespace(
                read_only_paths=(Path("public.dfy"), Path("bench/core/IOExtern.cs"))
            ),
            configuration=SimpleNamespace(
                evaluation=SimpleNamespace(reference_executable=None),
                task_profile=SimpleNamespace(
                    compiler_dependency_paths=("bench/core/IOExtern.cs",),
                    runtime_extern_execution=RuntimeExternExecution.NATIVE,
                ),
            ),
        ),
        "release": SimpleNamespace(
            manifest=SimpleNamespace(
                files={"bench/core/IOExtern.cs": "a" * 64},
                fixed_files={"bench/core/IOExtern.cs": "a" * 64},
            )
        ),
    }


def _benchmark() -> ResolvedBenchmark:
    return ResolvedBenchmark(
        name="demo",
        class_name="Demo",
        official_doc_node=None,
        task_label=None,
        item_directory="bench/utils/demo",
        evaluation=BenchmarkEvaluation(
            test_path="tests/demo.py",
            cases_path=None,
            fuzzer_target="demo",
            reference_executable="demo",
            output_contract=OutputContract.TOKENS,
        ),
    )


# Callers omitting image selection retain the previous staging image.
def test_default_staging_image(monkeypatch: pytest.MonkeyPatch) -> None:
    services = _render(monkeypatch)

    assert services["task-staging"]["image"] == "dafnyutils-task:latest"
    assert services["agent-workflow"]["image"] == "harness:run"


# A selected staging image leaves the candidate's isolation and launch contract intact.
def test_custom_staging_image_preserves_isolation(monkeypatch: pytest.MonkeyPatch) -> None:
    services = _render(monkeypatch, staging_image="task:unique-run")

    assert set(services) == {"agent-workflow", "task-staging"}
    assert services["task-staging"] == {
        "container_name": "run-staging",
        "image": "task:unique-run",
        "command": ["sleep", "infinity"],
        "network_mode": "none",
        "labels": {"dafnyutils.eval.run": "run"},
        "volumes": [
            {
                "type": "bind",
                "source": "/virtual/staged",
                "target": "/workspace",
                "read_only": False,
            }
        ],
    }
    agent = services["agent-workflow"]
    assert agent["image"] == "harness:run"
    assert agent["user"] == "agent"
    assert agent["working_dir"] == "/workspace"
    assert agent["command"] == [
        "/run/tools/oracle-isolation-entrypoint",
        "./agent",
        "exec",
        "--prompt=public $$input",
    ]
    assert agent["environment"] == {
        "NUGET_PACKAGES": "/cache/nuget",
        "HOME": "/run/agent_home",
        "MODE": "test",
        "AUTH": None,
    }
    assert agent["volumes"] == [mount.as_compose_volume() for mount in _plan().mounts]
    assert agent["security_opt"] == [
        "seccomp=unconfined",
        "apparmor=unconfined",
        "systempaths=unconfined",
    ]


# Trusted-root staging and ownership handoff continue to use the harness image.
def test_trusted_root_uses_harness_image(monkeypatch: pytest.MonkeyPatch) -> None:
    services = _render(
        monkeypatch,
        staging_image="task:unique-run",
        agent_launch=runtime.AgentLaunchSpec(
            image="trusted-harness:run",
            controller_identity=runtime.HarnessExecutionIdentity.TRUSTED_ROOT,
        ),
    )

    assert services["agent-workflow"]["user"] == "0:0"
    assert services["task-staging"]["image"] == "trusted-harness:run"
    assert services["task-staging"]["network_mode"] == "none"
    handoff = services["ownership-handoff"]
    assert handoff["image"] == "trusted-harness:run"
    assert handoff["user"] == "0:0"
    assert handoff["network_mode"] == "none"
    assert handoff["read_only"] is True
    assert handoff["security_opt"] == ["no-new-privileges:true"]
    assert handoff["command"] == [
        "python3",
        "-I",
        "-c",
        "ownership-script",
        str(os.getuid()),
        str(os.getgid()),
        "--root",
        "/handoff/0",
        "--root",
        "/handoff/1",
    ]
    assert handoff["volumes"] == [
        {"type": "bind", "source": "/virtual/output", "target": "/handoff/0", "read_only": False},
        {"type": "bind", "source": "/virtual/home", "target": "/handoff/1", "read_only": False},
    ]
    assert "environment" not in handoff
    assert handoff["cap_drop"] == ["ALL"]
    assert handoff["cap_add"] == ["CHOWN", "FOWNER", "DAC_OVERRIDE"]
    assert handoff["entrypoint"] == []
    assert handoff["working_dir"] == "/"
    assert services["agent-workflow"]["volumes"] == [
        mount.as_compose_volume() for mount in _plan().mounts
    ]
    assert services["agent-workflow"]["environment"]["HOME"] == "/run/agent_home"


# Blank explicit selections fail before Compose serialization can touch a filesystem boundary.
@pytest.mark.parametrize("image", ("", " ", "\t\n"))
@pytest.mark.parametrize("identity", tuple(runtime.HarnessExecutionIdentity))
def test_compose_rejects_blank_image(
    image: str, identity: runtime.HarnessExecutionIdentity
) -> None:
    with pytest.raises(ValueError, match="staging image must not be empty"):
        runtime.write_compose_override(
            **_compose_inputs(
                staging_image=image,
                agent_launch=runtime.AgentLaunchSpec("harness:run", controller_identity=identity),
            )
        )


# Public preparation rejects blank selections before checking Docker or allocating control paths.
@pytest.mark.parametrize("image", ("", " ", "\t\n"))
def test_public_prepare_rejects_blank_image(image: str) -> None:
    with pytest.raises(ValueError, match="staging image must not be empty"):
        runtime.prepare_agent_sandbox_context(**_prepare_inputs(), staging_image=image)


# Direct private preparation also rejects blank selections before staging begins.
@pytest.mark.parametrize("image", ("", " ", "\t\n"))
def test_private_prepare_rejects_blank_image(image: str) -> None:
    with pytest.raises(ValueError, match="staging image must not be empty"):
        runtime._prepare_agent_sandbox_context(
            **_prepare_inputs(), control_dir=Path("/virtual/control"), staging_image=image
        )


# The public owner API forwards its default or selected image without altering the result.
@pytest.mark.parametrize("image", (None, "task:unique-run"))
def test_public_prepare_forwards_image(monkeypatch: pytest.MonkeyPatch, image: str | None) -> None:
    expected = object()
    prepare = Mock(return_value=expected)
    allocate = Mock(return_value="/virtual/control")
    monkeypatch.setattr(runtime, "docker_runtime_available", lambda: True)
    monkeypatch.setattr(runtime, "_prepare_agent_sandbox_context", prepare)
    monkeypatch.setattr(tempfile, "mkdtemp", allocate)
    inputs = _prepare_inputs()
    selected = {} if image is None else {"staging_image": image}

    result = runtime.prepare_agent_sandbox_context(**inputs, **selected)

    assert result is expected
    prepare.assert_called_once_with(
        **inputs, control_dir=Path("/virtual/control"), staging_image=image
    )
    allocate.assert_called_once_with(prefix=".run-control-", dir=Path("/virtual"))


# Private preparation delivers the selected image to the Compose writer across fake staging seams.
@pytest.mark.parametrize("image", (None, "task:unique-run"))
def test_private_prepare_forwards_image(monkeypatch: pytest.MonkeyPatch, image: str | None) -> None:
    for name in (
        "seed_workspace_isolation_tools",
        "write_mount_manifest",
        "prepare_agent_mount_permissions",
    ):
        monkeypatch.setattr(runtime, name, Mock())
    monkeypatch.setattr(Path, "mkdir", Mock())
    monkeypatch.setattr(Path, "is_file", lambda path: True)
    monkeypatch.setattr(Path, "is_symlink", lambda path: False)
    monkeypatch.setattr(os, "access", lambda *args: True)
    monkeypatch.setattr(runtime, "prepare_oracle_executable_block", Mock(return_value=None))
    monkeypatch.setattr(runtime, "write_agent_task", Mock(return_value=object()))
    monkeypatch.setattr(runtime, "agent_prompt", Mock(return_value="public task"))
    monkeypatch.setattr(runtime, "candidate_container_plan", Mock(return_value=_plan()))
    writer = Mock()
    monkeypatch.setattr(runtime, "write_compose_override", writer)
    inputs = _prepare_inputs()
    selected = {} if image is None else {"staging_image": image}

    context = runtime._prepare_agent_sandbox_context(
        **inputs, control_dir=Path("/virtual/control"), **selected
    )

    assert writer.call_count == 1
    assert writer.call_args.kwargs["staging_image"] == image
    assert writer.call_args.kwargs["agent_launch"].image == "harness:run"
    assert context.workspace_dir == Path("/virtual/public")
    assert context.env == {"PATH": "/bin"}
    preparation = inputs["prepare_agent"].call_args.args[0]
    assert preparation.runtime_dependencies == (
        runtime.RuntimeDependency(Path("bench/core/IOExtern.cs"), "a" * 64),
    )
    assert preparation.runtime_extern_execution is RuntimeExternExecution.NATIVE
    inputs["record_launch"].assert_called_once_with(
        ("./agent", "exec", "--prompt=public task"), "public task"
    )


# A declared companion must exist in the verified public release inventory.
def test_runtime_dependency_must_be_public() -> None:
    manifest = SimpleNamespace(files={}, fixed_files={})

    with pytest.raises(ValueError, match="not a public release file"):
        runtime._runtime_dependencies(
            ("bench/core/IOExtern.cs",),
            manifest=manifest,
            read_only_paths=(Path("bench/core/IOExtern.cs"),),
        )


# A public companion without an owner-fixed digest cannot become executable runtime input.
def test_runtime_dependency_must_be_fixed() -> None:
    manifest = SimpleNamespace(files={"bench/core/IOExtern.cs": "a" * 64}, fixed_files={})

    with pytest.raises(ValueError, match="not fixed by the release"):
        runtime._runtime_dependencies(
            ("bench/core/IOExtern.cs",),
            manifest=manifest,
            read_only_paths=(Path("bench/core/IOExtern.cs"),),
        )


# A public fixed companion outside the task's read-only boundary is rejected.
def test_runtime_dependency_must_be_read_only() -> None:
    manifest = SimpleNamespace(
        files={"bench/core/IOExtern.cs": "a" * 64},
        fixed_files={"bench/core/IOExtern.cs": "a" * 64},
    )

    with pytest.raises(ValueError, match="not read-only for the task"):
        runtime._runtime_dependencies(
            ("bench/core/IOExtern.cs",),
            manifest=manifest,
            read_only_paths=(Path("bench/utils/demo"),),
        )


# The official fuzzer receives one quoted image parameter with the historical default.
def test_fuzzer_image_command_contract() -> None:
    command = derived_oracle_commands(_benchmark())["fuzzer"]

    assert shlex.split(command) == [
        "python3",
        "${EVAL_REPO_ROOT:-.}/tools/coreutils_fuzzer/run.py",
        "fuzz",
        "demo",
        "--container-image",
        "${COREUTILS_FUZZER_IMAGE:-dafnyutils-coreutils-fuzzer:latest}",
    ]
    lexer = shlex.shlex(command, posix=False)
    lexer.whitespace_split = True
    assert list(lexer)[-1] == '"${COREUTILS_FUZZER_IMAGE:-dafnyutils-coreutils-fuzzer:latest}"'


# Image transport preserves required evaluation selection and the fuzzer's trusted-host location.
def test_fuzzer_image_preserves_evaluation_contract() -> None:
    plans = build_evaluations(utility_cfg=_benchmark(), checkout_root=Path("/virtual/repo"))

    assert tuple(plan.required_checks for plan in plans) == (
        ("impl_layout", "proof_layout"),
        ("implementation_tests",),
        ("fuzzer",),
        ("dafny_verify",),
    )
    assert plans[2].commands[0].location is OracleExecutionLocation.TRUSTED_HOST
    assert plans[2].commands[0].cwd == Path("/virtual/repo")
