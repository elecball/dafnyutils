"""Proof reuse exposes strict wire data and fake-boundary finalization behavior."""

from __future__ import annotations

import json
from pathlib import Path
from types import SimpleNamespace

import pytest
from pydantic import ValidationError

import verification
from analysis.kinds import DefinitionKind
from analysis.models import DefinitionVerificationTarget
from benchmarks.task import ProofReuseCapability, PublicCheck
from entry_contract import EntryContractSourceSnapshot, EntryValidationFailure

_OPTIONS = (
    "--standard-libraries:false",
    "--library:bench/core",
    "--allow-warnings",
    "--boogie=/randomSeed:42",
    "--verify-included-files",
    "--isolate-assertions",
    "--verification-time-limit:30",
    "--allow-external-contracts",
)


def _target(symbol: str = "Proof.Check") -> DefinitionVerificationTarget:
    return DefinitionVerificationTarget(
        full_name=symbol,
        source_path="/workspace/toy/Proof.dfy",
        attributes=(),
    )


def _contract(*targets: DefinitionVerificationTarget, definitions=()):
    source = Path("/workspace/toy/Proof.dfy")
    return SimpleNamespace(
        execution_source=Path("/workspace/toy/Runner.dfy"),
        utility_sources=(source, Path("/workspace/toy/Runner.dfy")),
        verification_sources=(source,),
        verification_targets=targets,
        verification_definitions=definitions,
        analysis_sources=(Path("/workspace/bench/core/IO.dfy"),),
    )


def _session(contract, *, validate=None):
    validate = validate or (lambda: contract)
    return SimpleNamespace(
        workspace_root=Path("/workspace"),
        utility_root=Path("/workspace/toy"),
        manifest=SimpleNamespace(),
        tool_identity="dafny-benchmark",
        verification_options=_OPTIONS,
        validate=validate,
    )


def _snapshot(digest: str = "1" * 64) -> EntryContractSourceSnapshot:
    return EntryContractSourceSnapshot(
        files=(("toy/Runner.dfy", "toy/Runner.dfy", digest),),
        manifest_sha256="2" * 64,
        utility_sources=(("toy/Runner.dfy", "toy/Runner.dfy"),),
    )


def _compile_command(*extra: str) -> tuple[str, ...]:
    return (
        "dafny-benchmark",
        "build",
        "--no-verify",
        "--output",
        "_build/bench/toy.dll",
        "toy/dfyconfig.toml",
        *extra,
    )


def _scope_boundaries(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(verification, "_verification_options", lambda _root: _OPTIONS)
    monkeypatch.setattr(
        verification,
        "entry_contract_source_snapshot",
        lambda *_args, **_kwargs: _snapshot(),
    )


# A legacy public check omits the absent optional capability from JSON exactly.
def test_legacy_public_check_serialization_is_unchanged() -> None:
    check = PublicCheck(
        check_id="verify",
        title="Complete verification",
        argv=("./eval_support/verify.sh",),
    )

    assert check.model_dump(mode="json") == {
        "check_id": "verify",
        "title": "Complete verification",
        "argv": ["./eval_support/verify.sh"],
        "working_directory": None,
    }


# Unknown protocols and malformed command vectors fail strict public validation.
@pytest.mark.parametrize(
    ("field", "value"),
    [
        ("protocol", "benchmark.dafny-proof-reuse.v2"),
        ("proof_roots", []),
        ("proof_roots", ["../escape.dfy"]),
        ("verification_options", []),
        ("describe_argv", []),
        ("compile_argv", [""]),
    ],
)
def test_capability_rejects_malformed_values(field: str, value: object) -> None:
    payload = {
        "protocol": "benchmark.dafny-proof-reuse.v1",
        "proof_roots": ["toy/Runner.dfy"],
        "verification_options": list(_OPTIONS),
        "describe_argv": ["./eval_support/verify.sh", "--describe-proof-scope"],
        "compile_argv": ["./eval_support/verify.sh", "--compile-only"],
    }
    payload[field] = value

    with pytest.raises(ValidationError):
        ProofReuseCapability.model_validate_json(json.dumps(payload))


# The descriptor contains the exact sorted targets, canonical policy and one snapshot identity.
def test_scope_descriptor_is_exact_json(monkeypatch: pytest.MonkeyPatch, capsys) -> None:
    _scope_boundaries(monkeypatch)
    session = _session(_contract(_target("Proof.Other"), _target()))

    assert verification.describe_proof_scope_session(session, "dafny-benchmark") == 0

    captured = capsys.readouterr()
    assert captured.err == ""
    payload = json.loads(captured.out)
    assert payload["protocol"] == "benchmark.dafny-proof-reuse.v1"
    assert payload["proof_roots"] == ["toy/Runner.dfy"]
    assert payload["verification_options"] == list(_OPTIONS)
    assert payload["targets"] == [
        {"source_path": "toy/Proof.dfy", "symbol": "Proof.Check"},
        {"source_path": "toy/Proof.dfy", "symbol": "Proof.Other"},
    ]
    assert len(payload["source_identity"]) == 64
    assert captured.out.count("\n") == 1


# Empty, ambiguous and forbidden-body scopes fail without emitting partial JSON.
@pytest.mark.parametrize(
    "contract",
    [
        _contract(),
        _contract(_target(), _target()),
        _contract(_target("A.Check"), _target("Other.A.Check")),
        _contract(
            _target(),
            definitions=(SimpleNamespace(body_start=None, kind=DefinitionKind.METHOD),),
        ),
    ],
)
def test_scope_descriptor_rejects_invalid_scope(
    monkeypatch: pytest.MonkeyPatch, capsys, contract
) -> None:
    _scope_boundaries(monkeypatch)

    assert verification.describe_proof_scope_session(_session(contract), "dafny-benchmark") == 1
    assert capsys.readouterr().out == ""


# A source mutation detected while the descriptor is formed cannot receive an identity.
def test_scope_descriptor_rejects_source_mutation(monkeypatch: pytest.MonkeyPatch, capsys) -> None:
    _scope_boundaries(monkeypatch)
    contract = _contract(_target())
    validations = iter((contract, EntryValidationFailure("source changed")))

    def validate():
        value = next(validations)
        if isinstance(value, Exception):
            raise value
        return value

    assert (
        verification.describe_proof_scope_session(
            _session(contract, validate=validate), "dafny-benchmark"
        )
        == 1
    )
    assert capsys.readouterr().out == ""


# Compile-only validates both sides, invokes one build and never enters proof verification.
def test_compile_only_builds_once_without_verification(
    monkeypatch: pytest.MonkeyPatch, capsys
) -> None:
    _scope_boundaries(monkeypatch)
    contract = _contract(_target())
    validations = []
    commands = []

    def validate():
        validations.append(True)
        return contract

    def build(command, *, cwd):
        commands.append((command, cwd))
        return SimpleNamespace(returncode=0)

    monkeypatch.setattr(verification, "_run_build_command", build)
    monkeypatch.setattr(
        verification,
        "_verify_sources",
        lambda *_args, **_kwargs: pytest.fail("compile-only called proof verification"),
    )
    command = _compile_command()

    assert (
        verification.compile_only_session(
            _session(contract, validate=validate), "dafny-benchmark", command
        )
        == 0
    )
    assert commands == [(command, Path("/workspace"))]
    assert len(validations) == 4
    assert capsys.readouterr().out == "DAFNY_COMPILE_OUTCOME=compiled phase=build\n"


# A failed compiler process is a compile failure and cannot be reported as proof success.
def test_compile_only_rejects_build_failure(monkeypatch: pytest.MonkeyPatch, capsys) -> None:
    _scope_boundaries(monkeypatch)
    contract = _contract(_target())
    monkeypatch.setattr(
        verification,
        "_run_build_command",
        lambda *_args, **_kwargs: SimpleNamespace(returncode=1),
    )

    assert (
        verification.compile_only_session(_session(contract), "dafny-benchmark", _compile_command())
        == 1
    )
    assert capsys.readouterr().out == "DAFNY_COMPILE_OUTCOME=compile_failure phase=build\n"


# Compile-only rejects non-build or proof-enabled argv before reaching the process boundary.
@pytest.mark.parametrize(
    "command",
    [
        (
            "dafny-benchmark",
            "verify",
            "--no-verify",
            "--output",
            "_build/bench/toy.dll",
            "toy/Runner.dfy",
        ),
        ("dafny-benchmark", "build", "toy/dfyconfig.toml"),
        (
            "dafny-benchmark",
            "build",
            "--no-verify:false",
            "--output",
            "_build/bench/toy.dll",
            "toy/dfyconfig.toml",
        ),
        _compile_command("--no-verify=false"),
        _compile_command("/noVerify:false"),
        _compile_command("@options.rsp"),
        (
            "dafny-benchmark",
            "build",
            "--no-verify --no-verify:false",
            "--output",
            "_build/bench/toy.dll",
            "toy/dfyconfig.toml",
        ),
        _compile_command("--no-verify"),
        (
            "other-dafny",
            "build",
            "--no-verify",
            "--output",
            "_build/bench/toy.dll",
            "toy/dfyconfig.toml",
        ),
    ],
)
def test_compile_only_rejects_non_compile_command(
    monkeypatch: pytest.MonkeyPatch, capsys, command: tuple[str, ...]
) -> None:
    _scope_boundaries(monkeypatch)
    calls = []
    monkeypatch.setattr(
        verification,
        "_run_build_command",
        lambda *_args, **_kwargs: calls.append(True) or SimpleNamespace(returncode=0),
    )

    assert (
        verification.compile_only_session(
            _session(_contract(_target())), "dafny-benchmark", command
        )
        == 1
    )
    assert calls == []
    assert capsys.readouterr().out == (
        "DAFNY_COMPILE_OUTCOME=infrastructure_failure phase=evidence\n"
    )


# A changed post-build identity rejects finalization after an otherwise successful build.
def test_compile_only_rejects_post_build_identity_change(
    monkeypatch: pytest.MonkeyPatch, capsys
) -> None:
    monkeypatch.setattr(verification, "_verification_options", lambda _root: _OPTIONS)
    identities = iter(("1" * 64, "2" * 64))
    monkeypatch.setattr(verification, "_validated_source_identity", lambda *_args: next(identities))
    monkeypatch.setattr(
        verification,
        "_run_build_command",
        lambda *_args, **_kwargs: SimpleNamespace(returncode=0),
    )
    contract = _contract(_target())

    assert (
        verification.compile_only_session(_session(contract), "dafny-benchmark", _compile_command())
        == 1
    )
    assert capsys.readouterr().out == (
        "DAFNY_COMPILE_OUTCOME=infrastructure_failure phase=evidence\n"
    )


# The two new CLI modes dispatch only to their explicitly selected owner functions.
@pytest.mark.parametrize(
    ("flag", "function_name"),
    [
        ("--describe-proof-scope", "describe_proof_scope"),
        ("--compile-only", "run_compile_only"),
    ],
)
def test_cli_dispatches_explicit_finalization_modes(
    monkeypatch: pytest.MonkeyPatch, flag: str, function_name: str
) -> None:
    calls = []
    monkeypatch.setattr(verification, function_name, lambda *args: calls.append(args) or 7)
    args = ["--utility-root=toy", "--manifest=manifest.json", flag]
    if flag == "--compile-only":
        args.append("--build-arg=dafny-benchmark")

    assert verification.main(args) == 7
    assert len(calls) == 1
