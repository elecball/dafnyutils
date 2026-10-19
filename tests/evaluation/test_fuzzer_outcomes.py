"""Typed outcomes from standalone fuzzer evidence."""

from evaluation.models import FuzzerOutcome
from evaluation.submission.output_adapters import parse_fuzzer_outcome


# Missing time observations remain incomplete coverage in the typed command report.
def test_incomplete_time_coverage_marker_is_preserved() -> None:
    evidence = parse_fuzzer_outcome(
        name="fuzzer",
        stdout_bytes=b"",
        stderr_bytes=b"FUZZER_OUTCOME=incomplete_coverage\ntime evidence is incomplete\n",
        timed_out=False,
        exit_code=2,
    )

    assert evidence.outcome == FuzzerOutcome.INCOMPLETE_COVERAGE
    assert evidence.model_fields()["fuzzer_outcome"] == FuzzerOutcome.INCOMPLETE_COVERAGE


# Namespace setup evidence stays typed infrastructure rather than an inferred build failure.
def test_namespace_failure_marker_is_preserved() -> None:
    evidence = parse_fuzzer_outcome(
        name="fuzzer",
        stdout_bytes=b"",
        stderr_bytes=(
            b"FUZZER_OUTCOME=fuzzer_infrastructure_failure\n"
            b"Docker container startup failed: permission denied\n"
        ),
        timed_out=False,
        exit_code=2,
    )
    assert evidence.outcome == FuzzerOutcome.INFRASTRUCTURE_FAILURE
    assert evidence.model_fields()["fuzzer_outcome"] == FuzzerOutcome.INFRASTRUCTURE_FAILURE


# Ordinary marked build errors continue to classify as failures rather than infrastructure blockers.
def test_build_failure_marker_remains_build_failure() -> None:
    evidence = parse_fuzzer_outcome(
        name="fuzzer",
        stdout_bytes=b"",
        stderr_bytes=b"FUZZER_OUTCOME=fuzzer_build_failure\nCargo build failed\n",
        timed_out=False,
        exit_code=2,
    )
    assert evidence.outcome == FuzzerOutcome.BUILD_FAILURE


# An unmarked nonzero fuzzer invocation retains the existing conservative build-error fallback.
def test_unmarked_fuzzer_failure_keeps_existing_fallback() -> None:
    evidence = parse_fuzzer_outcome(
        name="fuzzer",
        stdout_bytes=b"",
        stderr_bytes=b"Cargo invocation failed\n",
        timed_out=False,
        exit_code=2,
    )
    assert evidence.outcome == FuzzerOutcome.BUILD_FAILURE
