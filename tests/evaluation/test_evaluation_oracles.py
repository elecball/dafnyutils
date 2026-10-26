"""Check evaluation stage planning derives oracle commands from utility profiles."""

from __future__ import annotations

import shlex
from pathlib import Path
from types import SimpleNamespace

import pytest

from benchmarks import make_tasks
from benchmarks.checks import (
    EvaluationName,
    OracleExecutionLocation,
    required_checks_for_evaluation,
)
from benchmarks.profiles import (
    IMPLEMENTATION_COMPILER_DEPENDENCY_PATHS,
    IMPLEMENTATION_SUPPORT_FILES,
    ResolvedBenchmark,
    ResolvedDafnyEntry,
    ResolvedTaskProfile,
    RuntimeExternExecution,
    dafny_analysis_support_files,
    required_checks_for_task,
)
from evaluation.submission.oracle_environment import (
    containerized_evaluation,
)
from evaluation.submission.oracles import (
    build_evaluations,
    configured_oracle_commands,
    derived_oracle_commands,
)
from evaluation.submission.sandbox import SandboxContext
from evaluation.task import workspace as task_workspace
from tests.evaluation.evaluation_test_support import (
    benchmark_utility_configs,
    utility_config,
)


# Every command-line task uses the same explicit Dafny support source boundary.
def test_analysis_support_selects_only_dafny_sources() -> None:
    selected = dafny_analysis_support_files()

    assert selected == tuple(path for path in IMPLEMENTATION_SUPPORT_FILES if path.endswith(".dfy"))


# The implementation profile declares its companion and native extern policy independently.
def test_implementation_profile_declares_runtime_companion() -> None:
    profile = _utility_cfg("cat").task_profile

    assert profile.compiler_dependency_paths == IMPLEMENTATION_COMPILER_DEPENDENCY_PATHS
    assert profile.runtime_extern_execution is RuntimeExternExecution.NATIVE
    assert IMPLEMENTATION_COMPILER_DEPENDENCY_PATHS == ("bench/core/IOExtern.cs",)


# Profiles without an explicit compiler companion retain the safe draft defaults.
def test_profile_runtime_defaults_are_empty_and_draft() -> None:
    profile = ResolvedTaskProfile(
        support_files=(),
        editable_outputs=(),
        placeholder_outputs=(),
        required_checks=(),
        required_outputs=(),
        execution_entry=ResolvedDafnyEntry("Demo.dfy", "Demo.Run"),
    )

    assert profile.compiler_dependency_paths == ()
    assert profile.runtime_extern_execution is RuntimeExternExecution.DRAFT


# Generated ordinary build arguments reuse the implementation profile's exact companion tuple.
def test_generated_build_args_use_profile_companions(monkeypatch: pytest.MonkeyPatch) -> None:
    profile = _utility_cfg("cat")
    monkeypatch.setattr(
        task_workspace,
        "_shell_template",
        lambda name, values: values.get("RUNTIME_BUILD_ARGS", name),
    )
    monkeypatch.setattr(task_workspace, "_run_core_scaffold", lambda *_args: "scaffold")
    monkeypatch.setattr(Path, "read_text", lambda *_args, **_kwargs: "config")
    analysis = SimpleNamespace(
        manifest=SimpleNamespace(
            execution_entry=SimpleNamespace(source_path="bench/utils/cat/Cat.dfy"),
            spec_definitions=(),
            support_source_sha256={},
            model_dump_json=lambda **_kwargs: "{}",
        ),
        source_document=object(),
        utility_sources=(),
        execution_source=Path("/virtual/Cat.dfy"),
        execution=object(),
    )

    generated = task_workspace._generated_files(profile, "cat", analysis)

    build_script = dict(generated)[Path("eval_support/build.sh")]
    assert shlex.split(build_script)[-1:] == list(IMPLEMENTATION_COMPILER_DEPENDENCY_PATHS)


# The local ordinary build invokes the same profile-declared companion through a fake process seam.
def test_local_build_uses_profile_companions(monkeypatch: pytest.MonkeyPatch) -> None:
    profile = _utility_cfg("cat")
    definition = SimpleNamespace(
        task_id="cat", project_config_path="bench/utils/cat/dfyconfig.toml"
    )
    commands: list[list[str]] = []
    monkeypatch.setattr(
        make_tasks.ResolvedBenchmark, "from_definition", lambda _definition: profile
    )
    monkeypatch.setattr(Path, "mkdir", lambda *_args, **_kwargs: None)
    monkeypatch.setattr(Path, "resolve", lambda path: path)
    monkeypatch.setattr(
        make_tasks,
        "_run",
        lambda command, **_kwargs: commands.append(command) or 0,
    )

    assert make_tasks._build(Path("/virtual/repo"), definition) == 0
    assert commands[0][-len(IMPLEMENTATION_COMPILER_DEPENDENCY_PATHS) :] == list(
        IMPLEMENTATION_COMPILER_DEPENDENCY_PATHS
    )


def _utility_cfg(utility_name: str) -> ResolvedBenchmark:
    return utility_config(utility_name)


# Coreutils evaluator stages must run the entry-driven generated gates on the candidate target.
def test_coreutils_oracles_use_generated_entry_gates() -> None:
    commands = derived_oracle_commands(_utility_cfg("cat"))

    assert commands["impl_layout"] == "./eval_support/build.sh"
    assert commands["proof_layout"] == "./eval_support/check_proof_layout.sh"
    assert commands["dafny_verify"] == "./eval_support/verify.sh"
    assert "bench/utils/cat" in commands["implementation_tests"]
    assert "make" in commands["implementation_tests"]
    assert "EVAL_BENCH_DLL=_build/bench/cat_bench.dll" in commands["implementation_tests"]
    assert commands["spec_consistency"].startswith("pytest -q -n0 ")
    for command_name in ("spec_shape", "spec_consistency"):
        assert "--allow-axioms" not in commands[command_name]
        assert "--allow-warnings" not in commands[command_name]
    assert "--allow-external-contracts" in commands["spec_shape"]
    assert "--dont-verify-dependencies" in commands["spec_shape"]


# Coreutils evaluation fuzzing compares stderr unless a caller explicitly opts out.
def test_coreutils_fuzzer_command_checks_stderr() -> None:
    command = derived_oracle_commands(_utility_cfg("cat"))["fuzzer"]

    assert shlex.split(command) == [
        "python3",
        "${EVAL_REPO_ROOT:-.}/tools/coreutils_fuzzer/run.py",
        "fuzz",
        "cat",
        "--container-image",
        "${COREUTILS_FUZZER_IMAGE:-dafnyutils-coreutils-fuzzer:latest}",
    ]


# Coreutils evaluation assigns all five mandatory commands to the four evaluation types.
def test_coreutils_evaluations_select_all_required_checks() -> None:
    utility_cfg = _utility_cfg("cat")
    commands = derived_oracle_commands(utility_cfg)
    layout, testcase, fuzzing, verification = build_evaluations(
        utility_cfg=utility_cfg,
        checkout_root=Path("/tmp/evaluator_checkout"),
    )
    assert layout.required_checks == ("impl_layout", "proof_layout")
    assert testcase.required_checks == ("implementation_tests",)
    assert fuzzing.required_checks == ("fuzzer",)
    assert verification.required_checks == ("dafny_verify",)
    for plan in (layout, testcase, fuzzing, verification):
        assert [command.command for command in plan.commands] == [
            commands[name] for name in plan.required_checks
        ]


# A coreutils archive runs only its container-managing fuzzer on the trusted host.
def test_coreutils_fuzzer_stays_on_host_when_evaluator_checks_are_wrapped() -> None:
    layout, _, fuzzing, _ = build_evaluations(
        utility_cfg=_utility_cfg("cat"),
        checkout_root=Path("/trusted/repository"),
    )
    context = SandboxContext((Path("/trusted/compose.yml"),), "evaluation", "evaluator")

    mapped_layout = containerized_evaluation(layout, context)
    mapped_fuzzing = containerized_evaluation(fuzzing, context)

    assert all(
        command.location is OracleExecutionLocation.EVALUATOR_CONTAINER
        for command in mapped_layout.commands
    )
    assert all(
        mapped.command != original.command
        for mapped, original in zip(mapped_layout.commands, layout.commands, strict=True)
    )
    assert mapped_fuzzing.commands[0].location is OracleExecutionLocation.TRUSTED_HOST
    assert mapped_fuzzing.commands[0].command == fuzzing.commands[0].command
    assert mapped_fuzzing.commands[0].cwd == fuzzing.commands[0].cwd


# Algorithm evaluations schedule the same mandatory CLI runtime and proof gates.
def test_algorithm_oracles_use_container_visible_repo_and_workspace_paths() -> None:
    utility_cfg = _utility_cfg("algorithm-63")
    commands = derived_oracle_commands(utility_cfg)
    layout, testcase, fuzzing, verification = build_evaluations(
        utility_cfg=utility_cfg,
        checkout_root=Path("/tmp/evaluator_checkout"),
    )

    assert commands["impl_layout"] == "./eval_support/build.sh"
    assert commands["proof_layout"] == "./eval_support/check_proof_layout.sh"
    assert commands["dafny_verify"] == "./eval_support/verify.sh"
    assert testcase.required_checks == ("implementation_tests",)
    assert "bench/algorithm/63" in testcase.commands[0].command
    assert [command.name for command in layout.commands] == ["impl_layout", "proof_layout"]
    assert verification.commands[0].name == "dafny_verify"
    assert fuzzing.required_checks == ()
    assert fuzzing.commands == ()
    for command_name in ("spec_shape", "spec_consistency"):
        assert "--allow-axioms" not in commands[command_name]
        assert "--allow-warnings" not in commands[command_name]


# Empty oracle commands are invalid configuration data.
def test_configured_oracle_commands_rejects_empty_command() -> None:
    with pytest.raises(ValueError, match="oracle commands must not be empty: dafny_verify"):
        configured_oracle_commands({"dafny_verify": ""})


# Missing required oracle commands block their evaluation without shrinking required checks.
def test_missing_required_oracle_command_blocks_evaluation() -> None:
    utility_cfg = _utility_cfg("cat")
    commands = derived_oracle_commands(utility_cfg)
    del commands["fuzzer"]

    fuzzing = build_evaluations(
        utility_cfg=utility_cfg,
        checkout_root=Path("/tmp/evaluator_checkout"),
        oracle_commands=commands,
    )[2]

    assert fuzzing.required_checks == ("fuzzer",)
    assert fuzzing.commands == ()
    assert fuzzing.blocked_reason == "missing oracle commands for required checks: fuzzer"


# An unrecognized public check cannot be silently dropped from evaluations.
def test_unknown_required_check_rejects_evaluation_selection() -> None:
    with pytest.raises(ValueError, match="unknown required benchmark checks: security_scan"):
        required_checks_for_evaluation(("impl_layout", "security_scan"), EvaluationName.LAYOUT)


# Every benchmark task keeps each required command in exactly one evaluation.
def test_benchmark_tasks_declare_all_required_oracle_checks() -> None:
    for utility_cfg in benchmark_utility_configs():
        commands = derived_oracle_commands(utility_cfg)
        required = required_checks_for_task(utility_cfg)
        missing = [check for check in required if not str(commands.get(check, "")).strip()]
        assert missing == [], utility_cfg.name
        assigned = tuple(
            check
            for evaluation in EvaluationName
            for check in required_checks_for_evaluation(required, evaluation)
        )
        assert sorted(assigned) == sorted(required), utility_cfg.name
