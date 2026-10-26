"""Derive authored benchmark paths, outputs, support files, and required check metadata."""

from __future__ import annotations

import re
from dataclasses import dataclass, field
from enum import StrEnum
from pathlib import Path

from benchmarks.paths import REPO_ROOT

from .checks import required_checks_for_evaluation_capabilities
from .definition import (
    BenchmarkDefinition,
    BenchmarkEvaluation,
    BenchmarkKind,
    class_name_for_task_id,
)
from .repository import BenchmarkRepository

IMPLEMENTATION_COMPILER_DEPENDENCY_PATHS = ("bench/core/IOExtern.cs",)
IMPLEMENTATION_SUPPORT_FILES = (
    "bench/core/Result.dfy",
    "bench/core/Errno.dfy",
    "bench/core/World.dfy",
    "bench/core/Utf8.dfy",
    "bench/core/StringEscaping.dfy",
    "bench/core/IO.dfy",
    "bench/core/IOContract.dfy",
    "bench/core/SecurityModel.dfy",
    "bench/core/CliTypes.dfy",
    *IMPLEMENTATION_COMPILER_DEPENDENCY_PATHS,
)
DAFNY_ANALYSIS_SUPPORT_FILES = tuple(
    path for path in IMPLEMENTATION_SUPPORT_FILES if path.endswith(".dfy")
)


class RuntimeExternExecution(StrEnum):
    """Select how an agent runtime executes declared extern callables."""

    DRAFT = "draft"
    NATIVE = "native"


@dataclass(frozen=True)
class ResolvedDafnyEntry:
    source_path: str
    symbol: str


@dataclass(frozen=True)
class ResolvedOutput:
    kind: str
    path: str
    role: str


@dataclass(frozen=True)
class ResolvedTaskProfile:
    support_files: tuple[str, ...]
    editable_outputs: tuple[str, ...]
    placeholder_outputs: tuple[str, ...]
    required_checks: tuple[str, ...]
    required_outputs: tuple[ResolvedOutput, ...]
    execution_entry: ResolvedDafnyEntry
    compiler_dependency_paths: tuple[str, ...] = ()
    runtime_extern_execution: RuntimeExternExecution = RuntimeExternExecution.DRAFT


@dataclass(frozen=True)
class ResolvedBenchmark:
    """Internal values derived from a validated benchmark task identifier."""

    name: str
    class_name: str
    official_doc_node: str | None
    task_label: str | None
    item_directory: str
    evaluation: BenchmarkEvaluation
    task_profile: ResolvedTaskProfile = field(init=False)

    @classmethod
    def for_task(cls, task_id: str) -> ResolvedBenchmark:
        definition = BenchmarkRepository.open(REPO_ROOT).load_definition(task_id)
        return cls.from_definition(definition)

    @classmethod
    def from_definition(cls, definition: BenchmarkDefinition) -> ResolvedBenchmark:
        task_id = definition.task_id
        class_name = derived_utility_class_name(task_id)
        algorithm = definition.kind is BenchmarkKind.ALGORITHM
        return cls(
            name=task_id,
            class_name=class_name,
            official_doc_node=None if algorithm else f"{task_id} invocation",
            task_label=f"problem {_algorithm_id(task_id)}" if algorithm else None,
            item_directory=definition.item_directory,
            evaluation=definition.evaluation,
        )

    def __post_init__(self) -> None:
        value = self.name
        if re.fullmatch(r"[a-z0-9][a-z0-9-]*", value) is None:
            raise ValueError("benchmark name must be safe for Make targets and path derivation")
        object.__setattr__(self, "task_profile", derived_task_profile(self, self.name))

    @property
    def utility_dir(self) -> str:
        return utility_paths(self, self.name)["utility_dir"]

    @property
    def disabled_checks(self) -> dict[str, str]:
        return {}


@dataclass(frozen=True)
class BenchmarkProject:
    name: str
    project_config: str


def benchmark_projects(root: Path = REPO_ROOT) -> tuple[BenchmarkProject, ...]:
    repository = BenchmarkRepository.open(root)
    return tuple(
        BenchmarkProject(
            name=definition.task_id,
            project_config=definition.project_config_path,
        )
        for definition in repository.definitions()
    )


def required_checks_for_task(
    utility_cfg: ResolvedBenchmark,
) -> tuple[str, ...]:
    return utility_cfg.task_profile.required_checks


def utility_class_name(utility_cfg: ResolvedBenchmark) -> str:
    return utility_cfg.class_name


def dafny_analysis_support_files() -> tuple[str, ...]:
    return DAFNY_ANALYSIS_SUPPORT_FILES


def benchmark_dafny_analysis_support_paths(
    root: Path = REPO_ROOT,
) -> tuple[Path, ...]:
    """Resolve the extra Dafny sources an entry-contract analysis must read for a task."""

    return tuple(root / path for path in dafny_analysis_support_files())


def _algorithm_id(utility_name: str) -> str:
    return utility_name.removeprefix("algorithm-")


def derived_utility_class_name(utility_name: str) -> str:
    return class_name_for_task_id(utility_name)


def derived_dafny_entries(
    utility_cfg: ResolvedBenchmark,
    utility_name: str,
) -> ResolvedDafnyEntry:
    class_name = utility_class_name(utility_cfg)
    return ResolvedDafnyEntry(
        f"{class_name}.dfy", f"{class_name}.{class_name}BenchmarkItem.RunCore"
    )


def utility_paths(utility_cfg: ResolvedBenchmark, utility_name: str) -> dict[str, str]:
    class_name = utility_class_name(utility_cfg)
    if utility_name != utility_cfg.name:
        raise ValueError("benchmark name does not match the resolved configuration")
    utility_dir = utility_cfg.item_directory
    base = f"{utility_dir}/{class_name}"
    return {
        "utility_dir": utility_dir,
        "project_config": f"{utility_dir}/dfyconfig.toml",
        "schema": f"{base}Schema.dfy",
        "nl_spec": f"{utility_dir}/{utility_name}.md",
        "spec": f"{base}Spec.dfy",
        "core": f"{base}Core.dfy",
        "proof": f"{base}Proof.dfy",
        "wrapper": f"{base}.dfy",
        "cli": f"{base}Cli.dfy",
        "cli_support": f"{utility_dir}/CliSupport.dfy",
    }


def derived_task_profile(
    utility_cfg: ResolvedBenchmark,
    utility_name: str,
) -> ResolvedTaskProfile:
    paths = utility_paths(utility_cfg, utility_name)
    execution_entry = derived_dafny_entries(utility_cfg, utility_name)
    return _task_profile(
        support_files=(*IMPLEMENTATION_SUPPORT_FILES, paths["cli_support"]),
        required_checks=required_checks_for_evaluation_capabilities(utility_cfg.evaluation),
        required_outputs=_cli_required_outputs(
            paths,
            execution_entry=execution_entry,
            class_name=utility_class_name(utility_cfg),
        ),
        placeholder_outputs=(),
        execution_entry=execution_entry,
        editable_outputs=(paths["utility_dir"],),
        compiler_dependency_paths=IMPLEMENTATION_COMPILER_DEPENDENCY_PATHS,
        runtime_extern_execution=RuntimeExternExecution.NATIVE,
    )


def _task_profile(
    *,
    support_files: tuple[str, ...],
    required_checks: tuple[str, ...],
    required_outputs: tuple[ResolvedOutput, ...],
    placeholder_outputs: tuple[str, ...],
    execution_entry: ResolvedDafnyEntry,
    editable_outputs: tuple[str, ...],
    compiler_dependency_paths: tuple[str, ...] = (),
    runtime_extern_execution: RuntimeExternExecution = RuntimeExternExecution.DRAFT,
) -> ResolvedTaskProfile:
    return ResolvedTaskProfile(
        support_files=support_files,
        editable_outputs=editable_outputs,
        placeholder_outputs=placeholder_outputs,
        required_checks=required_checks,
        required_outputs=required_outputs,
        execution_entry=execution_entry,
        compiler_dependency_paths=compiler_dependency_paths,
        runtime_extern_execution=runtime_extern_execution,
    )


def _cli_required_outputs(
    paths: dict[str, str],
    *,
    execution_entry: ResolvedDafnyEntry,
    class_name: str,
) -> tuple[ResolvedOutput, ...]:
    return (
        ResolvedOutput("build_entry", paths["cli"], f"{class_name}Cli.Main"),
        ResolvedOutput(
            "execution_entry",
            f"{paths['utility_dir']}/{execution_entry.source_path}",
            execution_entry.symbol,
        ),
    )
