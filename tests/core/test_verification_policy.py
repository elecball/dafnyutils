from __future__ import annotations

import xml.etree.ElementTree as ElementTree
from contextlib import nullcontext
from pathlib import Path

import pytest

import verification
from analysis.kinds import DefinitionKind
from analysis.models import DefinitionInfo, DefinitionVerificationTarget
from entry_contract import EntryValidationFailure, ValidatedEntryContract
from runtime.process import CapturedProcess


def _definition(
    symbol: str,
    kind: DefinitionKind = DefinitionKind.METHOD,
    *,
    body_start: int | None = 10,
) -> DefinitionInfo:
    return DefinitionInfo(
        name=symbol.rsplit(".", 1)[-1],
        full_name=symbol,
        kind=kind,
        enclosing_name="Runner",
        line=1,
        column=1,
        start=0,
        body_start=body_start,
        end=20,
        source_path="/workspace/toy/Implementation.dfy",
        ghost=False,
        has_by_method=False,
        has_loop=False,
        world_related=False,
        returns=(),
        return_names=(),
        requires=(),
        ensures=(),
        modifies=(),
        recursive=False,
        recursive_group=(),
        callees=(),
        references=(),
    )


def _contract(
    *definitions: DefinitionInfo,
    targets: tuple[DefinitionVerificationTarget, ...] | None = None,
) -> ValidatedEntryContract:
    source = Path("/workspace/toy/Implementation.dfy")
    if targets is None:
        targets = tuple(
            DefinitionVerificationTarget(
                full_name=definition.full_name, source_path=definition.source_path, attributes=()
            )
            for definition in definitions
            if definition.kind is not DefinitionKind.FUNCTION_BY_METHOD
        )
    return ValidatedEntryContract(source, (source,), (source,), definitions, targets)


def _fake_boundaries(
    monkeypatch: pytest.MonkeyPatch,
    reports: tuple[tuple[str, ...], ...] = (("Passed",),),
) -> list[tuple[list[str], dict[str, object]]]:
    calls: list[tuple[list[str], dict[str, object]]] = []
    pending = iter(reports)

    def run(command: list[str], **kwargs: object) -> CapturedProcess:
        calls.append((command, kwargs))
        return CapturedProcess(0, b"", b"", False, 123, 123)

    def parse(path: Path) -> ElementTree.ElementTree:
        outcomes = next(pending)
        root = ElementTree.Element("TestRun")
        for outcome in outcomes:
            ElementTree.SubElement(root, "UnitTestResult", outcome=outcome)
        return ElementTree.ElementTree(root)

    monkeypatch.setattr(verification, "run_process_capture_bytes", run)
    monkeypatch.setattr(verification.ElementTree, "parse", parse)
    monkeypatch.setattr(
        verification.tempfile, "TemporaryDirectory", lambda: nullcontext("/memory/reports")
    )
    return calls


def _verify(contract: ValidatedEntryContract, *, validate=lambda: None) -> int:
    return verification.verify_contract(
        contract,
        Path("/workspace"),
        "dafny-benchmark",
        verification.verification_options(),
        validate=validate,
    )


# Multiple targets in the same file each receive the complete mutation and process budget.
def test_each_target_gets_topdown_policy(monkeypatch: pytest.MonkeyPatch) -> None:
    calls = _fake_boundaries(monkeypatch, (("Passed",) * 3, ("Passed",) * 3))
    contract = _contract(_definition("Runner.RunCore"), _definition("Runner.Helper"))

    assert _verify(contract) == 0
    assert len(calls) == 2
    assert {call[0][call[0].index("--mutations") + 1] for call in calls} == {"3"}
    assert {call[0][call[0].index("--random-seed") + 1] for call in calls} == {"0"}
    for command, kwargs in calls:
        assert command[1] == "measure-complexity"
        assert "--verification-time-limit:30" in command
        assert "--isolate-assertions" in command
        assert "--verify-included-files" in command
        assert "--filter-position=toy/Implementation.dfy" in command
        assert kwargs["timeout_sec"] == 100
        assert kwargs["start_new_session"] is True
    assert {
        arg for command, _ in calls for arg in command if arg.startswith("--filter-symbol=")
    } == {
        "--filter-symbol=Runner.RunCore.",
        "--filter-symbol=Runner.Helper.",
    }


# A failed mutation receipt rejects the candidate even if the native process exits successfully.
def test_failed_mutation_receipt_rejects(monkeypatch: pytest.MonkeyPatch) -> None:
    _fake_boundaries(monkeypatch, (("Passed", "Failed", "Passed"),))

    assert _verify(_contract(_definition("Runner.RunCore"))) == 1


# A target reaching the outer cap fails without treating partial proof output as a pass.
def test_outer_timeout_rejects(monkeypatch: pytest.MonkeyPatch, capsys) -> None:
    _fake_boundaries(monkeypatch)

    def timeout(command, **kwargs):
        return CapturedProcess(-9, b"partial proof\n", b"", True, 123, 123)

    monkeypatch.setattr(verification, "run_process_capture_bytes", timeout)

    assert _verify(_contract(_definition("Runner.RunCore"))) == 1
    assert "DAFNY_VERIFICATION_OUTCOME=verification_failure phase=verify" in capsys.readouterr().out


# A zero-obligation helper does not invalidate successful evidence for the complete surface.
def test_empty_target_receipt_is_allowed(monkeypatch: pytest.MonkeyPatch) -> None:
    _fake_boundaries(monkeypatch, ((), ("Passed",) * 3))

    assert _verify(_contract(_definition("Runner.Helper"), _definition("Runner.RunCore"))) == 0


# Missing native evidence remains an infrastructure failure even after a successful exit.
def test_missing_report_rejects(monkeypatch: pytest.MonkeyPatch, capsys) -> None:
    _fake_boundaries(monkeypatch)

    def missing(path):
        raise FileNotFoundError(path)

    monkeypatch.setattr(verification.ElementTree, "parse", missing)

    assert _verify(_contract(_definition("Runner.RunCore"))) == 1
    assert (
        "DAFNY_VERIFICATION_OUTCOME=infrastructure_failure phase=evidence"
        in capsys.readouterr().out
    )


# Non-callable witness obligations retain their own native target and can fail verification.
def test_constrained_type_obligations_are_checked(monkeypatch: pytest.MonkeyPatch) -> None:
    calls = _fake_boundaries(monkeypatch, (("Failed",), ("Passed",)))

    assert (
        _verify(
            _contract(
                _definition("Runner.BadWitness", DefinitionKind.SUBSET_TYPE, body_start=None),
                _definition("Runner.RunCore"),
            )
        )
        == 1
    )
    assert "--filter-symbol=Runner.BadWitness." in calls[0][0]


# A function-by-method analysis entry reuses its native owner instead of losing method obligations.
def test_function_by_method_uses_owner(monkeypatch: pytest.MonkeyPatch) -> None:
    calls = _fake_boundaries(monkeypatch)

    assert (
        _verify(
            _contract(
                _definition("Runner.Compute", DefinitionKind.FUNCTION),
                _definition("Runner.Compute#by-method", DefinitionKind.FUNCTION_BY_METHOD),
            )
        )
        == 0
    )
    assert len(calls) == 1
    assert "--filter-symbol=Runner.Compute." in calls[0][0]


# A bodyless candidate callable remains invalid before native execution.
def test_bodyless_callable_rejects(monkeypatch: pytest.MonkeyPatch) -> None:
    calls = _fake_boundaries(monkeypatch)

    assert _verify(_contract(_definition("Runner.RunCore", body_start=None))) == 1
    assert calls == []


# A native warning cannot be hidden by a passing mutation report.
def test_warning_rejects(monkeypatch: pytest.MonkeyPatch) -> None:
    _fake_boundaries(monkeypatch)
    monkeypatch.setattr(
        verification,
        "run_process_capture_bytes",
        lambda command, **kwargs: CapturedProcess(
            0, b"Implementation.dfy(1,1): Warning: suspicious proof\n", b"", False, 123, 123
        ),
    )

    assert _verify(_contract(_definition("Runner.RunCore"))) == 1


# Source identity is checked after every successful proof receipt before accepting the candidate.
def test_changed_source_identity_rejects(monkeypatch: pytest.MonkeyPatch) -> None:
    _fake_boundaries(monkeypatch)

    def changed():
        raise EntryValidationFailure("source snapshot changed")

    assert _verify(_contract(_definition("Runner.RunCore")), validate=changed) == 1


# Datatype constructor defaults use the exact native target rather than an ambiguous type prefix.
def test_datatype_constructor_target_is_checked(monkeypatch: pytest.MonkeyPatch) -> None:
    calls = _fake_boundaries(monkeypatch, (("Failed",),))
    constructor = DefinitionVerificationTarget(
        full_name="#Runner.Choice.Some",
        source_path="/workspace/toy/Implementation.dfy",
        attributes=(),
    )

    assert (
        _verify(
            _contract(
                _definition("Runner.Choice", DefinitionKind.DATATYPE, body_start=None),
                targets=(constructor,),
            )
        )
        == 1
    )
    assert "--filter-symbol=#Runner.Choice.Some." in calls[0][0]


# A missing native target surface cannot masquerade as zero-obligation success.
def test_missing_targets_rejects(monkeypatch: pytest.MonkeyPatch) -> None:
    calls = _fake_boundaries(monkeypatch)

    assert _verify(_contract(_definition("Runner.RunCore"), targets=())) == 1
    assert calls == []


# The final evidence wire still requires at least one proof receipt across the full surface.
def test_empty_aggregate_receipt_rejects(monkeypatch: pytest.MonkeyPatch) -> None:
    _fake_boundaries(monkeypatch, ((),))

    assert _verify(_contract(_definition("Runner.RunCore"))) == 1
