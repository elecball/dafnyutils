from __future__ import annotations

import json
import subprocess
from pathlib import Path

import pytest
from pydantic import ValidationError

import entry_contract
from analysis import client
from analysis.kinds import DefinitionKind
from analysis.models import (
    DefinitionAnalysisDocument,
    DefinitionAttribute,
    DefinitionInfo,
    DefinitionSourceFacts,
    DefinitionVerificationTarget,
)
from entry_contract import EntryValidationFailure, _reject_candidate_verification_limits


def _definition(attribute: str, *, source: str = "/workspace/toy/Proof.dfy") -> DefinitionInfo:
    return DefinitionInfo(
        name="Helper",
        full_name="Proof.Helper",
        kind=DefinitionKind.METHOD,
        enclosing_name="Proof",
        line=1,
        column=1,
        start=0,
        body_start=20,
        end=50,
        source_path=source,
        ghost=True,
        has_by_method=False,
        has_loop=False,
        world_related=False,
        attributes=(DefinitionAttribute(name=attribute, arguments=("90",), start=7, end=19),),
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


# Native body visibility parses with its camel-case wire names and round-trips unchanged.
def test_definition_info_parses_native_body_visibility() -> None:
    payload = _definition("helper").model_dump(mode="json", by_alias=True, exclude_none=True)
    payload["bodyVisibility"] = {
        "referencedDeclarations": ["Proof.Helper", "Proof.Secret"],
        "isOpaque": True,
        "revealedFunctions": ["Proof.Public"],
        "revealsAllFunctions": False,
    }

    definition = DefinitionInfo.model_validate_json(json.dumps(payload))

    assert definition.body_visibility is not None
    assert definition.body_visibility.referenced_declarations == ("Proof.Helper", "Proof.Secret")
    assert definition.body_visibility.is_opaque is True
    assert definition.body_visibility.revealed_functions == ("Proof.Public",)
    assert definition.body_visibility.reveals_all_functions is False
    assert (
        definition.model_dump(mode="json", by_alias=True)["bodyVisibility"]
        == payload["bodyVisibility"]
    )


# Existing native results that omit optional body visibility retain the None default.
def test_definition_info_accepts_missing_body_visibility() -> None:
    payload = _definition("helper").model_dump(mode="json", by_alias=True, exclude_none=True)

    definition = DefinitionInfo.model_validate_json(json.dumps(payload))

    assert definition.body_visibility is None


# Body visibility booleans reject string coercion at the JSON boundary.
def test_definition_info_rejects_coerced_body_visibility_boolean() -> None:
    payload = _definition("helper").model_dump(mode="json", by_alias=True, exclude_none=True)
    payload["bodyVisibility"] = {
        "referencedDeclarations": [],
        "isOpaque": "true",
        "revealedFunctions": [],
        "revealsAllFunctions": False,
    }

    with pytest.raises(ValidationError):
        DefinitionInfo.model_validate_json(json.dumps(payload))


# Body visibility declaration names reject non-string JSON values.
def test_definition_info_rejects_non_string_body_visibility_declaration() -> None:
    payload = _definition("helper").model_dump(mode="json", by_alias=True, exclude_none=True)
    payload["bodyVisibility"] = {
        "referencedDeclarations": [7],
        "isOpaque": False,
        "revealedFunctions": [],
        "revealsAllFunctions": False,
    }

    with pytest.raises(ValidationError):
        DefinitionInfo.model_validate_json(json.dumps(payload))


# The nested body visibility object remains closed to unknown wire fields.
def test_definition_info_rejects_extra_body_visibility_field() -> None:
    payload = _definition("helper").model_dump(mode="json", by_alias=True, exclude_none=True)
    payload["bodyVisibility"] = {
        "referencedDeclarations": [],
        "isOpaque": False,
        "revealedFunctions": [],
        "revealsAllFunctions": False,
        "unexpected": True,
    }

    with pytest.raises(ValidationError):
        DefinitionInfo.model_validate_json(json.dumps(payload))


# An editable proof cannot override either the base time budget or an equivalent multiplier.
@pytest.mark.parametrize(
    "attribute",
    ["timeLimit", "timeLimitMultiplier", "_timeLimit", "TimeLimit", "TimeLimitMultiplier"],
)
def test_candidate_limit_override_rejects(attribute: str) -> None:
    definition = _definition(attribute)

    with pytest.raises(EntryValidationFailure, match="overrides the verification time limit"):
        _reject_candidate_verification_limits((Path(definition.source_path),), (definition,), set())


# Authored limits in unchanged protected support do not invalidate an unrelated candidate.
def test_protected_support_limit_is_preserved() -> None:
    definition = _definition("timeLimit")
    source = Path(definition.source_path)

    _reject_candidate_verification_limits((source,), (definition,), {source})


# Ordinary declaration attributes retain their existing proof behavior.
def test_other_candidate_attribute_is_allowed() -> None:
    definition = _definition("isolate_assertions")

    _reject_candidate_verification_limits((Path(definition.source_path),), (definition,), set())


def _fake_analysis(monkeypatch: pytest.MonkeyPatch):
    workspace = Path("/workspace")
    utility = workspace / "toy"
    source = utility / "Implementation.dfy"
    spec_source = utility / "Spec.dfy"
    helper = _definition("timeLimit")
    execution = helper.model_copy(
        update={
            "name": "RunCore",
            "full_name": "Runner.RunCore",
            "source_path": str(source),
            "attributes": (),
        }
    )
    spec = helper.model_copy(
        update={
            "name": "Allowed",
            "full_name": "Spec.Allowed",
            "source_path": str(spec_source),
            "attributes": (),
        }
    )
    definitions = (execution, helper, spec)
    document = DefinitionAnalysisDocument(
        definitions=(),
        source_facts=DefinitionSourceFacts(
            modules=(),
            imports=(),
            includes=(),
            verification_targets=tuple(
                DefinitionVerificationTarget(
                    full_name=definition.full_name,
                    source_path=definition.source_path,
                    attributes=definition.attributes,
                )
                for definition in definitions
            ),
        ),
    )
    resolved = entry_contract._ResolvedContract(
        sources=(source, Path(helper.source_path), spec_source),
        analysis_sources=(source, Path(helper.source_path), spec_source),
        document=document,
        infos=definitions,
        execution_source=source,
        execution=execution,
        spec_entries=(spec,),
        spec_closure=(spec,),
    )
    digest = "a" * 64
    monkeypatch.setattr(entry_contract, "_resolved_contract", lambda *args: resolved)
    monkeypatch.setattr(entry_contract, "_project_config", lambda root: root / "dfyconfig.toml")
    monkeypatch.setattr(entry_contract, "_sha256", lambda path: digest)
    monkeypatch.setattr(entry_contract, "_run_core_header_sha256", lambda *args: digest)
    monkeypatch.setattr(entry_contract, "_masked_sha256", lambda *args: digest)
    monkeypatch.setattr(entry_contract, "_definition_sha256", lambda *args: digest)
    monkeypatch.setattr(entry_contract, "_safe_workspace_path", lambda root, path: root / path)
    return workspace, utility, entry_contract.DafnyEntry("toy/Implementation.dfy", "Runner.RunCore")


# Baseline manifest generation can analyze authored limits before candidate policy enforcement.
def test_baseline_manifest_allows_authored_limits(monkeypatch: pytest.MonkeyPatch) -> None:
    manifest = entry_contract.analyze_entry_contract(*_fake_analysis(monkeypatch)).manifest

    assert manifest.execution_entry.symbol == "Runner.RunCore"


# Candidate validation rejects editable limits after baseline construction accepted them.
def test_validated_candidate_rejects_authored_limits(monkeypatch: pytest.MonkeyPatch) -> None:
    workspace, utility, entry = _fake_analysis(monkeypatch)
    manifest = entry_contract.analyze_entry_contract(workspace, utility, entry).manifest

    with pytest.raises(EntryValidationFailure, match="overrides the verification time limit"):
        entry_contract.validated_entry_contract(workspace, utility, manifest)


# Constructor attributes are enforced even without a corresponding authored definition entry.
def test_native_constructor_limit_rejects() -> None:
    target = DefinitionVerificationTarget(
        full_name="#Proof.Choice.Some",
        source_path="/workspace/toy/Proof.dfy",
        attributes=(DefinitionAttribute(name="timeLimit", arguments=("90",), start=7, end=19),),
    )

    with pytest.raises(EntryValidationFailure, match="overrides the verification time limit"):
        _reject_candidate_verification_limits((Path(target.source_path),), (target,), set())


# Missing opt-in target facts fail closed rather than silently falling back to guessed symbols.
def test_analysis_requires_requested_native_facts(monkeypatch: pytest.MonkeyPatch) -> None:
    payload = {"definitions": [], "sourceFacts": {"modules": [], "imports": [], "includes": []}}
    monkeypatch.setattr(Path, "read_text", lambda *args, **kwargs: "")
    monkeypatch.setattr(
        client,
        "_run_definition_analysis",
        lambda command, **kwargs: subprocess.CompletedProcess(command, 0, json.dumps(payload), ""),
    )

    with pytest.raises(RuntimeError, match="omitted requested verification facts"):
        client.definition_analysis_document_from_paths(
            (Path("/workspace/toy/Proof.dfy"),),
            include_semantic_facts=False,
            include_verification_facts=True,
        )


# Native target identity survives analysis unchanged, including compiler constructor names.
def test_analysis_preserves_native_target_identity(monkeypatch: pytest.MonkeyPatch) -> None:
    payload = {
        "definitions": [],
        "sourceFacts": {
            "modules": [],
            "imports": [],
            "includes": [],
            "verificationTargets": [
                {
                    "fullName": "#Proof.Choice.Some",
                    "sourcePath": "/workspace/toy/Proof.dfy",
                    "attributes": [],
                }
            ],
        },
    }
    commands = []

    def analyze(command, **kwargs):
        commands.append(command)
        return subprocess.CompletedProcess(command, 0, json.dumps(payload), "")

    monkeypatch.setattr(Path, "read_text", lambda *args, **kwargs: "")
    monkeypatch.setattr(client, "_run_definition_analysis", analyze)

    document = client.definition_analysis_document_from_paths(
        (Path("/workspace/toy/Proof.dfy"),),
        include_semantic_facts=False,
        include_verification_facts=True,
    )

    assert "--include-verification-facts" in commands[0]
    assert document.source_facts.verification_targets is not None
    assert document.source_facts.verification_targets[0].full_name == "#Proof.Choice.Some"
