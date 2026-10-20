"""Required benchmark checks shared by public profiles and evaluation."""

from __future__ import annotations

from dataclasses import dataclass
from enum import StrEnum

from .definition import BenchmarkEvaluation


class EvaluationName(StrEnum):
    LAYOUT = "layout"
    TESTCASE = "testcase"
    FUZZING = "fuzzing"
    VERIFICATION = "verification"


class OracleExecutionLocation(StrEnum):
    EVALUATOR_CONTAINER = "evaluator_container"
    TRUSTED_HOST = "trusted_host"


@dataclass(frozen=True)
class MandatoryCheck:
    name: str
    evaluation: EvaluationName
    requires_fuzzer: bool = False
    location: OracleExecutionLocation = OracleExecutionLocation.EVALUATOR_CONTAINER


MANDATORY_CHECKS = (
    MandatoryCheck("impl_layout", EvaluationName.LAYOUT),
    MandatoryCheck("implementation_tests", EvaluationName.TESTCASE),
    MandatoryCheck(
        "fuzzer",
        EvaluationName.FUZZING,
        requires_fuzzer=True,
        location=OracleExecutionLocation.TRUSTED_HOST,
    ),
    MandatoryCheck("proof_layout", EvaluationName.LAYOUT),
    MandatoryCheck("dafny_verify", EvaluationName.VERIFICATION),
)


def required_checks_for_evaluation_capabilities(
    evaluation: BenchmarkEvaluation,
) -> tuple[str, ...]:
    return tuple(
        check.name
        for check in MANDATORY_CHECKS
        if not check.requires_fuzzer or evaluation.fuzzer_target is not None
    )


def location_for_check(name: str) -> OracleExecutionLocation:
    for check in MANDATORY_CHECKS:
        if check.name == name:
            return check.location
    raise ValueError(f"unknown required benchmark check: {name}")


def required_checks_for_evaluation(
    names: tuple[str, ...], evaluation: EvaluationName
) -> tuple[str, ...]:
    by_name = {check.name: check for check in MANDATORY_CHECKS}
    unknown = sorted(set(names) - by_name.keys())
    if unknown:
        raise ValueError("unknown required benchmark checks: " + ", ".join(unknown))
    return tuple(name for name in names if by_name[name].evaluation is evaluation)
