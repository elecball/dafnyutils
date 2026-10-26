"""Individual feedback uses fake storage, native processes and validated contracts."""

from __future__ import annotations

import os
import xml.etree.ElementTree as ElementTree
from contextlib import nullcontext
from dataclasses import replace
from pathlib import Path
from types import SimpleNamespace

import pytest

import verification
from analysis.models import DefinitionVerificationTarget
from benchmarks import generated_profile
from benchmarks.task import PublicCheck, PublicRule, TaskProfile
from entry_contract import EntryContractCheckSession, EntryValidationFailure, ValidatedEntryContract
from evaluation.task import release, workspace
from runtime.process import CapturedProcess


def _target(symbol: str = "Proof.Check", source: str = "toy/Proof.dfy"):
    return DefinitionVerificationTarget(
        full_name=symbol, source_path=f"/workspace/{source}", attributes=()
    )


def _contract(*targets: DefinitionVerificationTarget):
    source = Path("/workspace/toy/Proof.dfy")
    return ValidatedEntryContract(source, (source,), (source,), (), tuple(targets))


def _boundaries(monkeypatch, contract=None, *, outcomes=("Passed",)):
    contract = contract if contract is not None else _contract(_target())
    calls = []
    validations = []

    def validate(self):
        validations.append(self)
        return contract

    def run(command, **kwargs):
        calls.append((command, kwargs))
        return CapturedProcess(0, b"", b"", False, 123, 123)

    def parse(path):
        root = ElementTree.Element("TestRun")
        for outcome in outcomes:
            ElementTree.SubElement(root, "UnitTestResult", outcome=outcome)
        return ElementTree.ElementTree(root)

    # No helper creates storage, examines tool trees, launches a process or reads a TRX file.
    monkeypatch.setattr(Path, "resolve", lambda path: Path(os.path.abspath(path)))
    monkeypatch.setattr(verification, "dafny_bench_core_library_options", lambda root: ())
    monkeypatch.setattr(verification.tempfile, "TemporaryDirectory", lambda: nullcontext("/memory"))
    monkeypatch.setattr(verification, "run_process_capture_bytes", run)
    monkeypatch.setattr(verification.ElementTree, "parse", parse)
    monkeypatch.setattr(EntryContractCheckSession, "validate", validate)
    session = EntryContractCheckSession(
        Path("/workspace"), Path("toy"), SimpleNamespace(), tool_identity="dafny-benchmark"
    )
    return session, calls, validations


def _check(session, source="toy/Proof.dfy", symbol="Proof.Check"):
    return verification.verify_individual_session(
        session, "dafny-benchmark", source=Path(source), symbol=symbol
    )


# Listing retains native constructor names and does not invoke a proof process.
def test_list_native_targets(monkeypatch, capsys):
    session, calls, _ = _boundaries(
        monkeypatch, _contract(_target("#Proof.Choice.Some"), _target())
    )

    assert verification.verify_individual_session(session, "dafny-benchmark") == 0
    assert capsys.readouterr().out.splitlines() == [
        "toy/Proof.dfy::#Proof.Choice.Some",
        "toy/Proof.dfy::Proof.Check",
    ]
    assert calls == []


# Exact native selection uses the global fixed seed and emits only scoped success.
def test_individual_policy_and_scoped_receipt(monkeypatch, capsys):
    session, calls, validations = _boundaries(
        monkeypatch, _contract(_target(), _target("Proof.Other"))
    )

    assert _check(session) == 0
    assert len(calls) == 1
    command, kwargs = calls[0]
    assert command[1] == "verify"
    assert "--filter-position=/workspace/toy/Proof.dfy" in command
    assert "--filter-symbol=Proof.Check." in command
    assert "--boogie=/randomSeed:42" in command
    assert "--verification-time-limit:30" in command
    assert "--isolate-assertions" in command
    assert kwargs["timeout_sec"] == 100
    assert kwargs["start_new_session"] is True
    assert len(validations) == 2
    output = capsys.readouterr().out.splitlines()
    assert "DAFNY_TARGET_VERIFICATION_OUTCOME=verified phase=verify" in output
    assert not any(line.startswith("DAFNY_VERIFICATION_OUTCOME=") for line in output)


# A prefix, unknown symbol, protected source or escaping path cannot select a target.
@pytest.mark.parametrize(
    ("source", "symbol"),
    [
        ("toy/Proof.dfy", "Proof"),
        ("toy/Proof.dfy", "Missing"),
        ("toy/Spec.dfy", "Proof.Check"),
        ("../private/Proof.dfy", "Proof.Check"),
    ],
)
def test_invalid_selector_rejects(monkeypatch, source, symbol):
    session, calls, _ = _boundaries(monkeypatch)

    assert _check(session, source, symbol) == 1
    assert calls == []


# Duplicate native identities fail closed before selection or execution.
def test_ambiguous_target_rejects(monkeypatch):
    session, calls, _ = _boundaries(monkeypatch, _contract(_target(), _target()))

    assert _check(session) == 1
    assert calls == []


# Native suffix matching cannot silently include a nested module's declaration.
def test_native_symbol_suffix_collision_rejects(monkeypatch, capsys):
    session, calls, _ = _boundaries(
        monkeypatch, _contract(_target("A.Check"), _target("Other.A.Check"))
    )

    assert _check(session, symbol="A.Check") == 1
    assert calls == []
    assert "native symbol suffix filter is ambiguous" in capsys.readouterr().err


# The longer native identity remains independently selectable when its suffix is unique.
def test_unique_nested_native_symbol_remains_selectable(monkeypatch):
    session, calls, _ = _boundaries(
        monkeypatch, _contract(_target("A.Check"), _target("Other.A.Check"))
    )

    assert _check(session, symbol="Other.A.Check") == 0
    assert "--filter-symbol=Other.A.Check." in calls[0][0]


# Absolute source filtering separates identical symbols in nested relative-suffix paths.
def test_relative_source_suffix_collision_uses_absolute_filter(monkeypatch):
    targets = (_target(), _target(source="nested/toy/Proof.dfy"))
    sources = tuple(Path(target.source_path) for target in targets)
    contract = replace(_contract(*targets), verification_sources=sources, utility_sources=sources)
    session, calls, _ = _boundaries(monkeypatch, contract)

    assert _check(session) == 0
    assert len(calls) == 1
    assert "--filter-position=/workspace/toy/Proof.dfy" in calls[0][0]


# Even an absolute source suffix collision with a protected analysis input fails closed.
def test_absolute_source_suffix_collision_rejects(monkeypatch, capsys):
    contract = replace(
        _contract(_target()),
        analysis_sources=(Path("/workspace/nested/workspace/toy/Proof.dfy"),),
    )
    session, calls, _ = _boundaries(monkeypatch, contract)

    assert _check(session) == 1
    assert calls == []
    assert "native source suffix filter is ambiguous" in capsys.readouterr().err


# Even malformed validated data cannot introduce a protected or outside native target.
@pytest.mark.parametrize("source", ["toy/Spec.dfy", "../private/Proof.dfy"])
def test_noneditable_native_target_rejects(monkeypatch, source):
    session, calls, _ = _boundaries(monkeypatch, _contract(_target(source=source)))

    assert _check(session, source) == 1
    assert calls == []


# Constructor targets keep their exact native selector including its leading hash.
def test_constructor_target_selector(monkeypatch):
    session, calls, _ = _boundaries(monkeypatch, _contract(_target("#Proof.Choice.Some")))

    assert _check(session, symbol="#Proof.Choice.Some") == 0
    assert "--filter-symbol=#Proof.Choice.Some." in calls[0][0]


# A failed obligation fails the target despite successful process exit.
def test_failed_obligation_rejects(monkeypatch):
    session, _, _ = _boundaries(monkeypatch, outcomes=("Passed", "Failed", "Passed"))

    assert _check(session) == 1


# A successful zero-obligation command is explicitly non-verified feedback.
def test_zero_obligations_are_explicit(monkeypatch, capsys):
    session, _, _ = _boundaries(monkeypatch, outcomes=())

    assert _check(session) == 1
    captured = capsys.readouterr()
    assert "DAFNY_TARGET_VERIFICATION_OUTCOME=no_obligations phase=verify" in captured.out
    assert "no verification obligations" in captured.err


# Native timeout, failure exit and warnings cannot be hidden by passing receipts.
@pytest.mark.parametrize(
    "result",
    [
        CapturedProcess(-9, b"", b"", True, 123, 123),
        CapturedProcess(1, b"", b"", False, 123, 123),
        CapturedProcess(0, b"Proof.dfy(1,1): Warning: bad proof\n", b"", False, 123, 123),
    ],
)
def test_native_failure_rejects(monkeypatch, result):
    session, _, _ = _boundaries(monkeypatch)
    monkeypatch.setattr(verification, "run_process_capture_bytes", lambda *args, **kwargs: result)

    assert _check(session) == 1


# Missing or malformed native reports fail evidence validation.
@pytest.mark.parametrize("error", [FileNotFoundError("missing"), ElementTree.ParseError("bad")])
def test_invalid_evidence_rejects(monkeypatch, error):
    session, _, _ = _boundaries(monkeypatch)

    def parse(path):
        raise error

    monkeypatch.setattr(verification.ElementTree, "parse", parse)

    assert _check(session) == 1


# Candidate integrity failure prevents listing and target execution alike.
def test_contract_integrity_failure_rejects(monkeypatch):
    session, calls, _ = _boundaries(monkeypatch)

    def invalid(self):
        raise EntryValidationFailure("candidate verification time limit override")

    monkeypatch.setattr(EntryContractCheckSession, "validate", invalid)

    assert _check(session) == 1
    assert calls == []


# A source changed during proof execution cannot receive a scoped success receipt.
def test_changed_source_rejects(monkeypatch):
    session, _, _ = _boundaries(monkeypatch)
    validations = iter([_contract(_target()), EntryValidationFailure("source changed")])

    def validate(self):
        value = next(validations)
        if isinstance(value, Exception):
            raise value
        return value

    monkeypatch.setattr(EntryContractCheckSession, "validate", validate)

    assert _check(session) == 1


# Scoped selectors cannot change the full verifier or be combined with a build.
@pytest.mark.parametrize(
    "flags",
    [
        ["--full", "--list"],
        ["--full", "--individual", "--list"],
        ["--individual", "--list", "--build-arg=dafny"],
        ["--individual", "--list", "--source=toy/Proof.dfy", "--symbol=Proof.Check"],
        ["--individual", "--source=toy/Proof.dfy"],
    ],
)
def test_cli_rejects_scope_confusion(flags):
    with pytest.raises(SystemExit) as result:
        verification.main(["--utility-root=toy", "--manifest=manifest.json", *flags])

    assert result.value.code == 2


# The original full CLI still invokes its complete build and proof path.
def test_full_cli_keeps_complete_gate(monkeypatch):
    calls = []
    monkeypatch.setattr(verification, "run_full", lambda *args: calls.append(args) or 7)

    assert (
        verification.main(
            ["--utility-root=toy", "--manifest=manifest.json", "--full", "--build-arg=dafny"]
        )
        == 7
    )
    assert calls[0][-1] == ["dafny"]


def _generated_workspace(monkeypatch, public_task_id):
    manifest = SimpleNamespace(
        execution_entry=SimpleNamespace(source_path="toy/Runner.dfy"),
        spec_definitions=(),
        support_source_sha256={},
        model_dump_json=lambda **kwargs: "{}",
    )
    analysis = SimpleNamespace(
        manifest=manifest,
        utility_sources=(),
        execution_source=Path("/workspace/toy/Runner.dfy"),
        execution=None,
    )
    config = SimpleNamespace(
        task_profile=SimpleNamespace(
            support_files=(),
            editable_outputs=("toy/Runner.dfy",),
            placeholder_outputs=(),
            compiler_dependency_paths=(),
        )
    )
    paths = {"utility_dir": "toy", "project_config": "toy/dfyconfig.toml"}
    monkeypatch.setattr(workspace, "utility_paths", lambda *args: paths)
    monkeypatch.setattr(workspace, "analyze_task_entry_contract", lambda *args: analysis)
    monkeypatch.setattr(workspace, "_run_core_scaffold", lambda *args: "scaffold")
    original_read = Path.read_text
    monkeypatch.setattr(
        Path,
        "read_text",
        lambda path, **kwargs: (
            "config" if path.suffix == ".toml" else original_read(path, **kwargs)
        ),
    )

    return workspace.task_workspace_spec(
        utility_cfg=config, utility_name="algorithm-1", public_task_id=public_task_id
    )


# The public helper is generated and protected in both supported support layouts.
@pytest.mark.parametrize("public_task_id", [None, "task-1"])
def test_helper_generation_and_protection(monkeypatch, public_task_id):
    spec = _generated_workspace(monkeypatch, public_task_id)
    support = Path("eval_support") / public_task_id if public_task_id else Path("eval_support")
    helper = support / "verify-target.sh"
    assert helper in dict(spec.generated_files)
    assert helper in spec.read_only_paths
    assert helper not in spec.editable_paths
    assert "@{SCRIPT_PARENT}" not in dict(spec.generated_files)[helper]


# Released guidance receives the same namespaced directory as the generated protected helper.
def test_release_guidance_matches_delivered_directory(monkeypatch):
    spec = _generated_workspace(monkeypatch, "algorithm-1")
    directories = []
    rule = PublicRule(
        rule_id="individual-verification", title="Optional feedback", description="Use"
    )
    other_rule = PublicRule(rule_id="other", title="Other", description="Preserve")
    profile = TaskProfile.model_construct(
        public_rules=(rule, other_rule),
        public_checks=(
            PublicCheck(check_id="verify", title="Complete", argv=("./eval_support/verify.sh",)),
        ),
    )

    def guidance(support_directory):
        directories.append(support_directory)
        return rule.model_copy(update={"description": support_directory.as_posix()})

    monkeypatch.setattr(release, "individual_verification_rule", guidance)

    public = release._public_profile(profile, "algorithm-1")

    delivered_directory = Path("eval_support/algorithm-1")
    assert directories == [delivered_directory]
    helper = directories[0] / "verify-target.sh"
    assert helper in dict(spec.generated_files)
    assert helper in spec.read_only_paths
    assert public.public_rules[0] == rule.model_copy(
        update={"description": delivered_directory.as_posix()}
    )
    assert public.public_rules[1] == other_rule
    assert public.public_checks[0].argv == ("./eval_support/algorithm-1/verify.sh",)


# Optional feedback guidance adds no mandatory check and keeps the existing full command.
def test_public_check_contract_unchanged(monkeypatch):
    paths = {
        "core": "toy/Core.dfy",
        "proof": "toy/Proof.dfy",
        "nl_spec": "toy/README.md",
        "utility_dir": "toy",
    }
    contract = {
        "spec_definitions": [{"source_path": "toy/Spec.dfy"}],
        "execution_entry": {"source_path": "toy/Runner.dfy"},
        "utility_dir": "toy",
        "spec_entries": [],
    }
    monkeypatch.setattr(generated_profile, "utility_paths", lambda *args: paths)
    monkeypatch.setattr(generated_profile, "dafny_entry_contract", lambda *args, **kwargs: contract)

    payload = generated_profile._profile_payload(
        SimpleNamespace(),
        SimpleNamespace(
            task_id="algorithm-1",
            title="Toy",
            evaluation=SimpleNamespace(reference_executable=None),
        ),
        analysis=None,
    )

    assert payload["public_checks"] == [
        {
            "check_id": "verify",
            "title": "Build, boundary, and Dafny verification gate",
            "argv": ["./eval_support/verify.sh"],
            "working_directory": None,
        }
    ]
    assert "individual-verification" in {rule["rule_id"] for rule in payload["public_rules"]}
