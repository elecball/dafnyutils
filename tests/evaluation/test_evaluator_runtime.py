"""Exercise trusted runtime deployment without native execution or filesystem writes."""

from __future__ import annotations

import os
import shutil
import stat
import subprocess
from pathlib import Path
from types import SimpleNamespace
from typing import Any, cast

import pytest

from evaluation.enums import CheckStatus
from evaluation.models import (
    CandidateOutputCaptureResultModel,
    CheckReportModel,
    EvaluationResultsModel,
)
from evaluation.submission import api, workspace
from evaluation.submission.runner import EvaluationRun
from evaluation.submission.sandbox import SandboxContext
from evaluation.task.api import PreparedCandidateTask


def _unexpected(*args: Any, **kwargs: Any) -> Any:
    raise AssertionError("unexpected external boundary")


@pytest.fixture(autouse=True)
def _deny_external_effects(monkeypatch: pytest.MonkeyPatch) -> None:
    for name in ("run", "Popen"):
        monkeypatch.setattr(subprocess, name, _unexpected)
    for name in ("mkdir", "chmod", "write_text", "write_bytes", "open"):
        monkeypatch.setattr(Path, name, _unexpected)
    monkeypatch.setattr(Path, "lstat", _unexpected)
    monkeypatch.setattr(os, "access", _unexpected)
    for name in ("copy2", "copyfile", "copytree", "copymode", "copystat"):
        monkeypatch.setattr(shutil, name, _unexpected)
    monkeypatch.setattr(api, "run_evaluations", _unexpected)
    monkeypatch.setattr(api, "write_json", _unexpected)
    monkeypatch.setattr(workspace, "append_jsonl", _unexpected)


def _captured_evaluation(
    monkeypatch: pytest.MonkeyPatch,
    events: list[object],
    *,
    options: api.CandidateEvaluationOptions | None = None,
    capture_error: str | None = None,
    evaluator: SandboxContext | None = None,
) -> api.CandidateEvaluationResult:
    task = cast(
        PreparedCandidateTask,
        SimpleNamespace(
            task_id="public-touch-alias",
            configuration=SimpleNamespace(name="touch"),
            run_directory=Path("/evaluation/run"),
        ),
    )

    def run(**kwargs: Any) -> EvaluationRun:
        events.append(("checks", kwargs["blocked_reason"], kwargs["evaluator"]))
        report = CheckReportModel(
            applicable=True,
            status=CheckStatus.BLOCKED,
            required_checks=["required-check"],
            passed_checks=[],
            failed_checks=[],
            blocked_reason=kwargs["blocked_reason"],
        )
        return EvaluationRun(
            [],
            EvaluationResultsModel(
                layout=report, testcase=report, fuzzing=report, verification=report
            ),
            [],
        )

    monkeypatch.setattr(api, "_evaluation_plans", lambda *args: ())
    monkeypatch.setattr(api, "candidate_check_plan", lambda task: [])
    monkeypatch.setattr(api, "run_evaluations", run)
    monkeypatch.setattr(api, "write_json", lambda *args: events.append("persist"))
    return api._evaluate_captured(
        task,
        options or api.CandidateEvaluationOptions(),
        CandidateOutputCaptureResultModel(attempted=True, copied=True, error=capture_error),
        [],
        evaluator,
    )


# Every shared evaluation route deploys the canonical utility runtime before checks.
@pytest.mark.parametrize("evaluator", [None, SandboxContext((), "test", "evaluator")])
def test_evaluation_prepares_canonical_runtime_before_checks(
    monkeypatch: pytest.MonkeyPatch, evaluator: SandboxContext | None
) -> None:
    events: list[object] = []
    monkeypatch.setattr(
        api,
        "prepare_evaluator_runtime",
        lambda **kwargs: events.append(("prepare", kwargs)),
        raising=False,
    )

    _captured_evaluation(monkeypatch, events, evaluator=evaluator)

    assert events == [
        (
            "prepare",
            {
                "utility_name": "touch",
                "target_root": Path("/evaluation/run/sandbox/evaluator_target"),
            },
        ),
        ("checks", None, evaluator),
        "persist",
    ]


# A pre-existing operator block prevents runtime preparation and keeps its reason.
def test_operator_block_skips_runtime_preparation(monkeypatch: pytest.MonkeyPatch) -> None:
    events: list[object] = []
    monkeypatch.setattr(api, "prepare_evaluator_runtime", _unexpected, raising=False)

    result = _captured_evaluation(
        monkeypatch,
        events,
        options=api.CandidateEvaluationOptions(blocked_reason="operator block"),
        capture_error="capture error",
    )

    assert events == [("checks", "operator block", None), "persist"]
    assert result.notes == ["operator block", "capture error"]


# An unsuccessful capture skips runtime preparation without changing candidate metadata.
def test_capture_error_skips_runtime_preparation(monkeypatch: pytest.MonkeyPatch) -> None:
    events: list[object] = []
    monkeypatch.setattr(api, "prepare_evaluator_runtime", _unexpected, raising=False)

    result = _captured_evaluation(monkeypatch, events, capture_error="capture error")

    assert events == [("checks", "capture error", None), "persist"]
    assert result.candidate_capture.error == "capture error"


def _runtime_boundaries(
    monkeypatch: pytest.MonkeyPatch,
    events: list[object],
    *,
    mode: int = stat.S_IFREG | 0o755,
    executable: bool = True,
) -> None:
    monkeypatch.setattr(workspace, "REPO_ROOT", Path("/trusted/benchmark"))
    monkeypatch.setattr(
        subprocess, "run", lambda command, **kwargs: events.append(("build", command, kwargs))
    )

    def metadata(path: Path) -> SimpleNamespace:
        events.append(("validate", path))
        return SimpleNamespace(st_mode=mode)

    monkeypatch.setattr(Path, "lstat", metadata)
    monkeypatch.setattr(os, "access", lambda path, mode: executable)


# The parser is built from trusted inputs at the exact isolated DLL sibling.
def test_touch_runtime_uses_trusted_make_and_exact_isolated_output(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    events: list[object] = []
    _runtime_boundaries(monkeypatch, events)

    workspace.prepare_evaluator_runtime(
        utility_name="touch", target_root=Path("/evaluation/target")
    )

    assert events == [
        (
            "build",
            [
                "make",
                "-C",
                "/trusted/benchmark/bench/utils/touch",
                "build-time-parser",
                "BUILD_DIR=/trusted/benchmark/_build",
                "TOUCH_TIME_PARSER=/evaluation/target/_build/bench/touch_time_parser",
            ],
            {"cwd": Path("/trusted/benchmark"), "check": True},
        ),
        ("validate", Path("/evaluation/target/_build/bench/touch_time_parser")),
    ]


# A previously built parser still goes through Make's dependency freshness check.
def test_touch_runtime_rechecks_make_freshness(monkeypatch: pytest.MonkeyPatch) -> None:
    events: list[object] = []
    _runtime_boundaries(monkeypatch, events)

    for _ in range(2):
        workspace.prepare_evaluator_runtime(
            utility_name="touch", target_root=Path("/evaluation/one")
        )

    assert len([event for event in events if cast(tuple, event)[0] == "build"]) == 2


# Separate evaluations never send their linkers to the same helper output.
def test_distinct_evaluations_use_distinct_helper_outputs(monkeypatch: pytest.MonkeyPatch) -> None:
    events: list[object] = []
    _runtime_boundaries(monkeypatch, events)

    for root in (Path("/evaluation/one"), Path("/evaluation/two")):
        workspace.prepare_evaluator_runtime(utility_name="touch", target_root=root)

    outputs = [cast(tuple, event)[1][-1] for event in events if cast(tuple, event)[0] == "build"]
    assert outputs == [
        "TOUCH_TIME_PARSER=/evaluation/one/_build/bench/touch_time_parser",
        "TOUCH_TIME_PARSER=/evaluation/two/_build/bench/touch_time_parser",
    ]


# Relative standalone evaluation paths remain anchored to the operator's working directory.
def test_relative_target_is_anchored_before_make_changes_directory(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    events: list[object] = []
    _runtime_boundaries(monkeypatch, events)
    monkeypatch.setattr(os, "getcwd", lambda: "/operator")

    workspace.prepare_evaluator_runtime(utility_name="touch", target_root=Path("relative-run"))

    assert events[-1] == (
        "validate",
        Path("/operator/relative-run/_build/bench/touch_time_parser"),
    )


# Utilities without native parser dependencies never invoke a build or filesystem boundary.
def test_other_utility_needs_no_runtime_preparation() -> None:
    workspace.prepare_evaluator_runtime(utility_name="cat", target_root=Path("/evaluation/target"))


# A failing trusted Make command stops before inspecting any output.
def test_helper_build_failure_stops_validation(monkeypatch: pytest.MonkeyPatch) -> None:
    def fail(*args: Any, **kwargs: Any) -> None:
        raise subprocess.CalledProcessError(2, "make")

    monkeypatch.setattr(subprocess, "run", fail)

    with pytest.raises(workspace.EvaluatorRuntimeError, match="unable to build trusted"):
        workspace.prepare_evaluator_runtime(
            utility_name="touch", target_root=Path("/evaluation/one")
        )


# An unavailable Make executable is an infrastructure error before output validation.
def test_missing_make_is_runtime_failure(monkeypatch: pytest.MonkeyPatch) -> None:
    def fail(*args: Any, **kwargs: Any) -> None:
        raise FileNotFoundError("make is unavailable")

    monkeypatch.setattr(subprocess, "run", fail)

    with pytest.raises(workspace.EvaluatorRuntimeError, match="unable to build trusted"):
        workspace.prepare_evaluator_runtime(
            utility_name="touch", target_root=Path("/evaluation/one")
        )


# A successful Make process without its promised helper cannot proceed to checks.
def test_missing_helper_is_runtime_failure(monkeypatch: pytest.MonkeyPatch) -> None:
    events: list[object] = []
    _runtime_boundaries(monkeypatch, events)

    def missing(path: Path) -> None:
        raise FileNotFoundError(str(path))

    monkeypatch.setattr(Path, "lstat", missing)

    with pytest.raises(workspace.EvaluatorRuntimeError, match="is unavailable"):
        workspace.prepare_evaluator_runtime(
            utility_name="touch", target_root=Path("/evaluation/one")
        )


# A failed write at the trusted Make boundary blocks evaluation as infrastructure.
def test_make_output_permission_failure_is_runtime_failure(monkeypatch: pytest.MonkeyPatch) -> None:
    def fail(*args: Any, **kwargs: Any) -> None:
        raise PermissionError("cannot prepare output")

    monkeypatch.setattr(subprocess, "run", fail)

    with pytest.raises(workspace.EvaluatorRuntimeError, match="unable to build trusted"):
        workspace.prepare_evaluator_runtime(
            utility_name="touch", target_root=Path("/evaluation/one")
        )


# Link outputs must be regular files rather than symlinks or directories.
@pytest.mark.parametrize("mode", [stat.S_IFLNK | 0o777, stat.S_IFDIR | 0o755])
def test_nonregular_helper_is_runtime_failure(monkeypatch: pytest.MonkeyPatch, mode: int) -> None:
    events: list[object] = []
    _runtime_boundaries(monkeypatch, events, mode=mode)

    with pytest.raises(workspace.EvaluatorRuntimeError, match="not a regular executable"):
        workspace.prepare_evaluator_runtime(
            utility_name="touch", target_root=Path("/evaluation/one")
        )


# The operating system must permit executing the produced regular helper.
def test_nonexecutable_helper_is_runtime_failure(monkeypatch: pytest.MonkeyPatch) -> None:
    events: list[object] = []
    _runtime_boundaries(monkeypatch, events, executable=False)

    with pytest.raises(workspace.EvaluatorRuntimeError, match="not a regular executable"):
        workspace.prepare_evaluator_runtime(
            utility_name="touch", target_root=Path("/evaluation/one")
        )


# Runtime failure uses the existing runner block without rejecting the candidate submission.
def test_runtime_failure_blocks_checks_and_records_infrastructure_note(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    events: list[object] = []

    def fail(**kwargs: Any) -> None:
        raise workspace.EvaluatorRuntimeError("helper build failed")

    monkeypatch.setattr(api, "prepare_evaluator_runtime", fail)

    result = _captured_evaluation(monkeypatch, events)

    reason = "evaluator runtime infrastructure failure: helper build failed"
    assert events == [("checks", reason, None), "persist"]
    assert result.notes == [reason]
    assert result.executions == []
    assert result.candidate_capture.error is None
    assert result.evaluations.layout.status is CheckStatus.BLOCKED
    assert not result.scores.overall_passed
