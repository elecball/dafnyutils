from __future__ import annotations

from pathlib import Path
from types import SimpleNamespace

import pytest

from benchmarks import checks as benchmark_checks
from benchmarks.checks import EvaluationName
from benchmarks.contribution import (
    check_commands,
    run_benchmark_checks,
)
from benchmarks.definition import BenchmarkDefinition, BenchmarkKind, BenchmarkSource
from benchmarks.repository import BenchmarkRepository
from benchmarks.selection import affected_task_ids
from benchmarks.validation import load_validated_benchmark
from benchmarks.verify import local_verification_contract

ROOT = Path(__file__).resolve().parents[2]


# Registered definitions preserve canonical IDs across utility and algorithm directory layouts.
@pytest.mark.integration
def test_repository_round_trips_every_registered_task() -> None:
    repository = BenchmarkRepository.open(ROOT)

    for task_id in repository.task_ids():
        definition = repository.load_definition(task_id)
        assert definition.task_id == task_id
        assert repository.definition_path(task_id) == (
            ROOT / definition.item_directory / "benchmark.yaml"
        )

    assert "cat" in repository.task_ids(BenchmarkKind.COREUTILS)
    assert "algorithm-1" in repository.task_ids(BenchmarkKind.ALGORITHM)
    assert "1" not in repository.task_ids()


# Only the fixed migration baseline can use unknown legacy provenance.
def test_new_definition_cannot_claim_legacy_provenance() -> None:
    payload = {
        "schema_version": "benchmark.definition.v2",
        "task_id": "new-task",
        "kind": "coreutils",
        "capabilities": {"gnu_reference": True, "fuzzer": True},
        "source": {
            "status": "legacy-unverified",
            "name": "Unknown",
        },
    }

    with pytest.raises(ValueError, match="migration baseline"):
        BenchmarkDefinition.model_validate(payload)


# Unsupported contributor schema versions require an explicit migration.
@pytest.mark.parametrize("schema_version", ("benchmark.definition.v1", "benchmark.definition.v3"))
def test_definition_rejects_unsupported_schema_version(schema_version: str) -> None:
    payload = {
        "schema_version": schema_version,
        "task_id": "sample",
        "kind": "coreutils",
        "capabilities": {"gnu_reference": True, "fuzzer": True},
        "source": {
            "status": "verified",
            "name": "Sample source",
            "url": "https://example.com/sample",
            "license": "MIT",
        },
    }

    with pytest.raises(ValueError, match="benchmark.definition.v2"):
        BenchmarkDefinition.model_validate(payload)


# A copied v1 path cannot override the evaluator path derived from the v2 task ID.
def test_definition_rejects_legacy_path_override() -> None:
    payload = {
        "schema_version": "benchmark.definition.v2",
        "task_id": "sample",
        "kind": "coreutils",
        "capabilities": {"gnu_reference": True, "fuzzer": True},
        "source": {
            "status": "verified",
            "name": "Sample source",
            "url": "https://example.com/sample",
            "license": "MIT",
        },
        "evaluation": {"test_path": "tools/bench/other.py"},
    }

    with pytest.raises(ValueError, match="evaluation"):
        BenchmarkDefinition.model_validate(payload)


# Verified provenance requires normalized human-readable fields and an HTTP(S) URL.
@pytest.mark.parametrize(
    "source",
    (
        {"status": "verified", "name": " Source", "url": "https://example.com", "license": "MIT"},
        {"status": "verified", "name": "Source", "url": "file:///tmp/source", "license": "MIT"},
        {"status": "verified", "name": "Source", "url": "https://example.com", "license": " TODO "},
    ),
)
def test_verified_provenance_rejects_placeholder_or_malformed_fields(
    source: dict[str, object],
) -> None:
    with pytest.raises(ValueError):
        BenchmarkSource.model_validate(source)


# Shared changes expand selection; item changes stay focused and algorithms use canonical IDs.
def test_affected_task_selection_uses_manifest_families() -> None:
    repository = BenchmarkRepository.open(ROOT)

    assert affected_task_ids(repository, ("bench/utils/cat/CatSpec.dfy",)) == ("cat",)
    assert affected_task_ids(repository, ("bench/algorithm/1/Algorithm1Spec.dfy",)) == (
        "algorithm-1",
    )
    assert set(affected_task_ids(repository, ("tools/coreutils_fuzzer/src/lib.rs",))) == set(
        repository.task_ids(BenchmarkKind.COREUTILS)
    )


# Shared benchmark helpers affect every item rather than naming a nonexistent task.
def test_affected_selection_includes_all_tasks_for_shared_benchmark_helpers() -> None:
    repository = BenchmarkRepository.open(ROOT)

    assert affected_task_ids(repository, ("tools/bench_test_support.py",)) == repository.task_ids()


# Changes to shared analysis, verifier, and candidate execution select every item.
@pytest.mark.parametrize(
    "path",
    (
        "src/analysis/client.py",
        "src/dafny_cli.py",
        "dafny",
        "dafny/Source/DafnyCore/AST/Expressions/Expression.cs",
    ),
)
def test_affected_selection_includes_all_tasks_for_shared_execution(path: str) -> None:
    repository = BenchmarkRepository.open(ROOT)

    assert affected_task_ids(repository, (path,)) == repository.task_ids()


# Deleted and renamed item paths remain selected so CI fails closed on missing definitions.
def test_affected_selection_retains_missing_deleted_or_renamed_ids() -> None:
    repository = BenchmarkRepository.open(ROOT)

    assert affected_task_ids(
        repository,
        (
            "bench/utils/deleted/benchmark.yaml",
            "bench/utils/replacement/benchmark.yaml",
            "bench/algorithm/999/benchmark.yaml",
        ),
    ) == ("algorithm-999", "deleted", "replacement")


# Every CLI task runs runtime and proof checks with its optional oracle capabilities.
@pytest.mark.parametrize("task_id", ("cat", "algorithm-1"))
def test_check_plan_keeps_required_capability_checks(task_id: str) -> None:
    repository = BenchmarkRepository.open(ROOT)
    commands = check_commands(ROOT, repository.load_definition(task_id))

    expected = (
        (
            "build",
            "coreutils-reference",
            "implementation-tests",
            "fuzzer",
            "dafny-verify",
            "benchmark-proof-tests",
        )
        if task_id == "cat"
        else ("build", "implementation-tests", "dafny-verify", "benchmark-proof-tests")
    )
    assert tuple(command.name for command in commands) == expected
    proof = next(command for command in commands if command.name == "dafny-verify")
    assert proof.argv == (
        "make",
        "-C",
        repository.load_definition(task_id).item_directory,
        "verify",
    )
    if task_id == "cat":
        assert commands[-1].argv[1:] == (
            "-m",
            "pytest",
            "-q",
            "-n0",
            "--import-mode=importlib",
            "-m",
            "dafny_verify",
            "bench/utils/cat/Tests.py",
        )


# A newly required check cannot silently disappear from contributor validation.
def test_check_plan_rejects_unimplemented_required_check(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    repository = BenchmarkRepository.open(ROOT)
    monkeypatch.setattr(
        benchmark_checks,
        "MANDATORY_CHECKS",
        (
            *benchmark_checks.MANDATORY_CHECKS,
            benchmark_checks.MandatoryCheck("security_scan", EvaluationName.VERIFICATION),
        ),
    )

    with pytest.raises(ValueError, match="missing contributor commands.*security_scan"):
        check_commands(ROOT, repository.load_definition("cat"))


# The verification gate enumerates included Core and Proof files, not only the wrapper entry.
@pytest.mark.integration
def test_verification_session_includes_algorithm_core_and_proof() -> None:
    contract = local_verification_contract(ROOT / "bench/algorithm/1")

    sources = {path.name for path in contract.verification_sources}

    assert {"Algorithm1.dfy", "Algorithm1Core.dfy", "Algorithm1Proof.dfy"} <= sources


# A failed mandatory command stops the check and is never reported as success.
@pytest.mark.integration
def test_check_fails_on_first_failed_mandatory_command(monkeypatch: pytest.MonkeyPatch) -> None:
    repository = BenchmarkRepository.open(ROOT)
    validated = load_validated_benchmark(repository, "cat")
    monkeypatch.setattr(
        "benchmarks.contribution.load_validated_benchmark",
        lambda _repository, _task_id: validated,
    )
    calls: list[tuple[str, ...]] = []

    def failed_run(argv: tuple[str, ...], **_kwargs: object) -> SimpleNamespace:
        calls.append(argv)
        return SimpleNamespace(returncode=7)

    monkeypatch.setattr("benchmarks.contribution.subprocess.run", failed_run)

    with pytest.raises(RuntimeError, match="build.*exit code 7"):
        run_benchmark_checks(repository, "cat")
    assert len(calls) == 1
