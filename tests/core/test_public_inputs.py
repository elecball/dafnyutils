"""Check release boundaries using small native facts and byte strings in memory."""

from dataclasses import dataclass
from pathlib import Path

import pytest
from dafny_analysis.kinds import DefinitionKind
from dafny_analysis.models import DefinitionInfo
from yaml.constructor import ConstructorError

from benchmarks.profiles import IMPLEMENTATION_SUPPORT_FILES
from tools.public_inputs.cli import _interface_error, _store_or_compare
from tools.public_inputs.models import (
    ExceptionEntry,
    Lock,
    Manifest,
    Obligation,
    Permission,
    Role,
    manifest_from_yaml,
    manifest_to_yaml,
)
from tools.public_inputs.policy import (
    PolicyError,
    declaration_errors,
    make_lock,
    project_dependencies,
    public_closure,
    role,
    specification_inputs,
)

ROOT = Path("/workspace/public-input-tests")
SPEC = "bench/utils/demo/Spec/DemoSpec.dfy"
ENTRY = "bench/utils/demo/Impl/Demo.dfy"
SUPPORT = "bench/core/Model.dfy"
CORE = "bench/utils/demo/Impl/DemoCore.dfy"
PAYLOAD = b"method RunCore() {solution} trailing"


def info(path: str, symbol: str, **updates: object) -> DefinitionInfo:
    """Provide only the native facts needed by a scenario."""
    values = dict(
        name=symbol.split(".")[-1],
        full_name=symbol,
        kind=DefinitionKind.FUNCTION,
        enclosing_name="DemoSpec",
        line=1,
        column=1,
        start=0,
        body_start=17,
        end=27,
        source_path=ROOT / path,
        ghost=True,
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
    values.update(updates)
    return DefinitionInfo.model_validate(values)


def manifest(**updates: object) -> Manifest:
    """Declare one public root and an exact existing method header."""
    values = dict(
        task_id="demo",
        public_roots=(SPEC,),
        obligation=Obligation(
            path=ENTRY,
            symbol="Demo.RunCore",
            signature="method RunCore()",
            candidate_outputs=(CORE,),
        ),
    )
    values.update(updates)
    return Manifest.model_validate(values)


def include(target: str) -> dict[str, object]:
    """Return one native include edge from the fixed entry scaffold."""
    return dict(source_path=ROOT / ENTRY, target_path=ROOT / target, start=0, end=1)


# A fixed scaffold cannot import CLI support through a candidate path.
def test_hole_support_under_candidate_path_blocks_lock() -> None:
    entry = info(
        ENTRY,
        "Demo.RunCore",
        kind=DefinitionKind.METHOD,
        local_includes=(include("bench/utils/demo/Impl/CliSupport.dfy"),),
    )
    with pytest.raises(PolicyError, match="forbidden role candidate-output"):
        public_closure(manifest(), (info(SPEC, "DemoSpec.Spec"), entry), ROOT)


# Explicit candidate modules do not enter the public include closure.
def test_candidate_module_include_is_excluded() -> None:
    entry = info(ENTRY, "Demo.RunCore", kind=DefinitionKind.METHOD, local_includes=(include(CORE),))
    assert public_closure(manifest(), (info(SPEC, "DemoSpec.Spec"), entry), ROOT) == (
        ENTRY,
        SPEC,
    )


# Public support that the fixed hole scaffold imports is locked transitively.
def test_fixed_hole_support_is_included() -> None:
    entry = info(
        ENTRY, "Demo.RunCore", kind=DefinitionKind.METHOD, local_includes=(include(SUPPORT),)
    )
    actual = public_closure(
        manifest(),
        (info(SPEC, "DemoSpec.Spec"), entry, info(SUPPORT, "Model.T")),
        ROOT,
    )
    assert SUPPORT in actual


# Changing only a candidate's method body preserves the immutable digest.
def test_lock_excludes_only_native_body() -> None:
    entry = info(ENTRY, "Demo.RunCore", kind=DefinitionKind.METHOD, body_start=17, end=27)
    sources = {SPEC: b"public spec", ENTRY: PAYLOAD}
    first = make_lock(
        manifest(),
        b"manifest",
        (info(SPEC, "DemoSpec.Spec"), entry),
        ROOT,
        sources.__getitem__,
        ("native-v1", "client-v1"),
    )
    sources[ENTRY] = PAYLOAD[:17] + b"different-body" + PAYLOAD[27:]
    changed = entry.model_copy(update={"end": 17 + len(b"different-body")})
    second = make_lock(
        manifest(),
        b"manifest",
        (info(SPEC, "DemoSpec.Spec"), changed),
        ROOT,
        sources.__getitem__,
        ("native-v1", "client-v1"),
    )
    assert first == second


# A changed formal contract invalidates the owner-authored signature.
def test_signature_change_rejects_lock() -> None:
    entry = info(ENTRY, "Demo.RunCore", kind=DefinitionKind.METHOD, body_start=17, end=27)
    sources = {SPEC: b"public spec", ENTRY: b"method Different {solution} trailing"}
    with pytest.raises(PolicyError, match="signature differs"):
        make_lock(
            manifest(),
            b"manifest",
            (info(SPEC, "DemoSpec.Spec"), entry),
            ROOT,
            sources.__getitem__,
            ("native-v1", "client-v1"),
        )


# A native executable declaration requires a reasoned, specific exception.
def test_executable_declaration_requires_exception() -> None:
    declaration = info(SPEC, "DemoSpec.Text", ghost=False)
    assert any(
        "missing executable exception" in error
        for error in declaration_errors(
            manifest(),
            (declaration,),
            ROOT,
            reachable=False,
        )
    )


# Trust flags cannot receive implicit permission from an executable exception.
def test_trust_requires_separate_permission() -> None:
    declaration = info(SPEC, "DemoSpec.Text", ghost=False, has_assume_statement=True)
    approved = manifest(
        specification_exceptions=(
            ExceptionEntry(
                path=SPEC,
                symbol="DemoSpec.Text",
                permits=(Permission.EXECUTABLE,),
                reason="Fixed public diagnostic text.",
            ),
        )
    )
    assert declaration_errors(approved, (declaration,), ROOT, reachable=False) == (
        f"{SPEC}:DemoSpec.Text: missing trust exception",
    )


# Owner exceptions must still name existing public declarations.
def test_removed_declaration_leaves_stale_exception() -> None:
    approved = manifest(
        specification_exceptions=(
            ExceptionEntry(
                path=SPEC,
                symbol="DemoSpec.Removed",
                permits=(Permission.EXECUTABLE,),
                reason="Fixed public diagnostic text.",
            ),
        )
    )
    assert "does not name" in declaration_errors(approved, (), ROOT)[0]


# Native header dependencies reach declarations without exposing the solution body.
def test_reachability_starts_at_fixed_obligation_header() -> None:
    entry = info(
        ENTRY, "Demo.RunCore", kind=DefinitionKind.METHOD, header_dependencies=("DemoSpec.Spec",)
    )
    assert declaration_errors(manifest(), (entry, info(SPEC, "DemoSpec.Spec")), ROOT) == ()


# Unreachable declarations need explicit owner permission even if they are ghost.
def test_unreachable_declaration_requires_exception() -> None:
    assert declaration_errors(manifest(), (info(SPEC, "DemoSpec.Unused"),), ROOT) == (
        f"{SPEC}:DemoSpec.Unused: missing unreachable exception",
    )


# Only the declared hole may override an implementation file's role.
def test_hole_role_exception_is_exact() -> None:
    assert role(ENTRY) is Role.CANDIDATE
    assert role(ENTRY, ENTRY) is Role.SUPPORT
    assert role(CORE, ENTRY) is Role.CANDIDATE


# A private directory called Spec cannot redefine the owner's path convention.
def test_unowned_spec_directory_stays_private() -> None:
    assert role("private/Spec/Secret.dfy") is Role.PRIVATE


# Changing fixed scaffold bytes invalidates its digest even after the method body.
def test_lock_binds_fixed_scaffold_suffix() -> None:
    entry = info(ENTRY, "Demo.RunCore", kind=DefinitionKind.METHOD, body_start=17, end=27)
    sources = {SPEC: b"public spec", ENTRY: PAYLOAD}
    first = make_lock(
        manifest(),
        b"manifest",
        (info(SPEC, "DemoSpec.Spec"), entry),
        ROOT,
        sources.__getitem__,
        ("native-v1", "client-v1"),
    )
    sources[ENTRY] += b" changed fixed code"
    second = make_lock(
        manifest(),
        b"manifest",
        (info(SPEC, "DemoSpec.Spec"), entry),
        ROOT,
        sources.__getitem__,
        ("native-v1", "client-v1"),
    )
    assert first != second


# New public bytes require a regenerated committed lock.
def test_lock_changes_with_public_specification_bytes() -> None:
    entry = info(ENTRY, "Demo.RunCore", kind=DefinitionKind.METHOD, body_start=17, end=27)
    sources = {SPEC: b"public spec", ENTRY: PAYLOAD}
    first = make_lock(
        manifest(),
        b"manifest",
        (info(SPEC, "DemoSpec.Spec"), entry),
        ROOT,
        sources.__getitem__,
        ("native-v1", "client-v1"),
    )
    sources[SPEC] = b"changed public spec"
    second = make_lock(
        manifest(),
        b"manifest",
        (info(SPEC, "DemoSpec.Spec"), entry),
        ROOT,
        sources.__getitem__,
        ("native-v1", "client-v1"),
    )
    assert first != second


# Unknown versions fail before the tool treats an artifact as a current manifest.
def test_unknown_manifest_schema_is_rejected() -> None:
    with pytest.raises(ValueError, match="unsupported manifest schema"):
        manifest(schema_version="unrecognized.v999")


# An owner artifact cannot replace RunCore with a different method as the task obligation.
def test_manifest_cannot_select_another_entry_method() -> None:
    changed = manifest(
        obligation=Obligation(
            path=ENTRY,
            symbol="Demo.DemoBenchmarkItem.Name",
            signature="method Name()",
            candidate_outputs=(
                CORE,
                "bench/utils/demo/Proof/DemoProof.dfy",
                "bench/utils/demo/Impl/DemoCli.dfy",
            ),
        )
    )
    paths = {
        "wrapper": ENTRY,
        "core": CORE,
        "proof": "bench/utils/demo/Proof/DemoProof.dfy",
        "cli": "bench/utils/demo/Impl/DemoCli.dfy",
    }
    assert _interface_error("demo", changed, paths) is not None


def project_text(includes: str) -> bytes:
    """Provide a tiny in-memory native project configuration."""
    return f"""includes = [{includes}]
[options]
target = "cs"
no-verify = true
standard-libraries = false
""".encode()


# Fixed project configuration may name only an explicitly declared candidate entry.
def test_project_excludes_designated_candidate_cli() -> None:
    path = "bench/utils/demo/dfyconfig.toml"
    sources = {path: project_text('"Impl/DemoCli.dfy"')}
    assert (
        project_dependencies(path, sources.__getitem__, ("bench/utils/demo/Impl/DemoCli.dfy",))
        == ()
    )


# A project cannot expose an undeclared implementation file through a configuration root.
def test_project_rejects_undeclared_candidate_include() -> None:
    path = "bench/utils/demo/dfyconfig.toml"
    sources = {path: project_text('"Impl/Unexpected.dfy"')}
    with pytest.raises(PolicyError, match="undeclared candidate/private"):
        project_dependencies(path, sources.__getitem__, ())


# Every literal specification dependency from a project joins the public closure.
def test_project_follows_public_specification_include() -> None:
    path = "bench/utils/demo/dfyconfig.toml"
    sources = {path: project_text('"Spec/DemoSpec.dfy"')}
    assert project_dependencies(path, sources.__getitem__, ()) == (SPEC,)


# Unsupported globs fail rather than silently omitting build inputs.
def test_project_rejects_unimplemented_include_patterns() -> None:
    path = "bench/utils/demo/dfyconfig.toml"
    sources = {path: project_text('"Spec/*.dfy"')}
    with pytest.raises(PolicyError, match="unsupported project include"):
        project_dependencies(path, sources.__getitem__, ())


@dataclass
class MemoryLock:
    """Keep the lock file boundary entirely in memory."""

    payload: bytes
    writes: int = 0

    def is_file(self) -> bool:
        return True

    def read_bytes(self) -> bytes:
        return self.payload

    def write_text(self, text: str, encoding: str) -> int:
        self.payload = text.encode(encoding)
        self.writes += 1
        return len(text)


def lock_document() -> Lock:
    """Create a small valid lock without filesystem operations."""
    entry = info(ENTRY, "Demo.RunCore", kind=DefinitionKind.METHOD, body_start=17, end=27)
    sources = {SPEC: b"public spec", ENTRY: PAYLOAD}
    return make_lock(
        manifest(),
        b"manifest",
        (info(SPEC, "DemoSpec.Spec"), entry),
        ROOT,
        sources.__getitem__,
        ("native-v1", "client-v1"),
    )


# A changed manifest or exception list needs a new release before lock regeneration.
def test_lock_rejects_changed_manifest_under_same_release() -> None:
    existing = lock_document()
    memory = MemoryLock(existing.model_dump_json().encode())
    changed = existing.model_copy(update={"manifest_sha256": "f" * 64})
    assert _store_or_compare("lock", memory, changed)
    assert memory.writes == 0


# Changed public source bytes cannot silently replace a lock for the same release.
def test_lock_rejects_changed_public_bytes_under_same_release() -> None:
    existing = lock_document()
    memory = MemoryLock(existing.model_dump_json().encode())
    files = tuple(item.model_copy(update={"sha256": "f" * 64}) for item in existing.files)
    changed = existing.model_copy(update={"files": files})
    assert _store_or_compare("lock", memory, changed)
    assert memory.writes == 0


# Malformed old locks need explicit repair rather than implicit regeneration.
def test_lock_refuses_to_overwrite_malformed_existing_artifact() -> None:
    memory = MemoryLock(b"not JSON")
    assert _store_or_compare("lock", memory, lock_document())
    assert memory.writes == 0


# A role-invalid old lock cannot become fresh through silent replacement.
def test_lock_refuses_to_overwrite_existing_private_role() -> None:
    existing = lock_document()
    invalid = existing.model_copy(
        update={
            "files": (
                existing.files[0].model_copy(update={"role": Role.PRIVATE}),
                *existing.files[1:],
            )
        }
    )
    memory = MemoryLock(invalid.model_dump_json().encode())
    assert _store_or_compare("lock", memory, existing)
    assert memory.writes == 0


# An explicit new release permits the owner to regenerate a changed public contract.
def test_lock_accepts_explicit_new_release_identity() -> None:
    existing = lock_document()
    memory = MemoryLock(existing.model_dump_json().encode())
    changed = existing.model_copy(update={"release": "new-release", "manifest_sha256": "f" * 64})
    assert _store_or_compare("lock", memory, changed) == ()
    assert Lock.model_validate_json(memory.payload) == changed


def fixed_interface() -> tuple[Manifest, dict[str, str]]:
    """Provide the existing owner interface with every mandatory public root."""
    paths = {
        "wrapper": ENTRY,
        "spec": SPEC,
        "project_config": "bench/utils/demo/dfyconfig.toml",
        "core": CORE,
        "proof": "bench/utils/demo/Proof/DemoProof.dfy",
        "cli": "bench/utils/demo/Impl/DemoCli.dfy",
    }
    authored = manifest(
        public_roots=(SPEC, paths["project_config"], *IMPLEMENTATION_SUPPORT_FILES),
        obligation=Obligation(
            path=ENTRY,
            symbol="Demo.DemoBenchmarkItem.RunCore",
            signature="method RunCore()",
            candidate_outputs=(paths["core"], paths["proof"], paths["cli"]),
        ),
    )
    return authored, paths


# A task manifest cannot omit the fixed configuration that defines its native build.
def test_manifest_requires_fixed_project_root() -> None:
    authored, paths = fixed_interface()
    omitted = authored.model_copy(
        update={
            "public_roots": tuple(
                path for path in authored.public_roots if path != paths["project_config"]
            )
        }
    )
    assert _interface_error("demo", omitted, paths) is not None


# A task manifest cannot omit support that the published task interface delivers.
def test_manifest_requires_fixed_shared_support_roots() -> None:
    authored, paths = fixed_interface()
    omitted = authored.model_copy(
        update={
            "public_roots": tuple(
                path for path in authored.public_roots if path != "bench/core/IOExtern.cs"
            )
        }
    )
    assert _interface_error("demo", omitted, paths) is not None


# A changed trusted native producer also requires an explicit release transition.
def test_lock_rejects_checker_change_under_same_release() -> None:
    existing = lock_document()
    memory = MemoryLock(existing.model_dump_json().encode())
    changed = existing.model_copy(update={"checker": "native-v2"})
    assert _store_or_compare("lock", memory, changed)
    assert memory.writes == 0


# The complete existing task interface satisfies the mandatory-root contract.
def test_manifest_accepts_existing_complete_interface() -> None:
    authored, paths = fixed_interface()
    assert _interface_error("demo", authored, paths) is None


# Bodyless twostate callables require trust permission even without an axiom attribute.
@pytest.mark.parametrize(
    "kind", (DefinitionKind.TWOSTATE_FUNCTION, DefinitionKind.TWOSTATE_PREDICATE)
)
def test_bodyless_twostate_contract_requires_trust_exception(kind: DefinitionKind) -> None:
    declaration = info(
        SPEC,
        "DemoSpec.F",
        kind=kind,
        ghost=True,
        body_start=None,
        has_axiom_attribute=False,
        ensures=("false",),
    )
    assert declaration_errors(manifest(), (declaration,), ROOT, reachable=False) == (
        f"{SPEC}:DemoSpec.F: missing trust exception",
    )


# A specification that only the fixed hole imports must receive native declaration lint.
def test_native_inputs_cover_specification_reached_only_by_hole() -> None:
    helper = "bench/utils/demo/Spec/HoleOnly.dfy"
    entry = info(
        ENTRY,
        "Demo.RunCore",
        kind=DefinitionKind.METHOD,
        local_includes=(include(helper), include(CORE)),
    )
    facts = (info(SPEC, "DemoSpec.Spec"), info(helper, "HoleOnly.Helper"), entry)
    selected = set(specification_inputs(manifest(), facts, ROOT))
    expected = {ROOT / path for path in public_closure(manifest(), facts, ROOT)} - {ROOT / ENTRY}
    assert selected == expected
    assert ROOT / helper in selected


# A forbidden sibling dependency cannot hide another specification from native lint.
def test_native_inputs_keep_hole_specification_when_other_role_is_blocked() -> None:
    helper = "bench/utils/demo/Spec/HoleOnly.dfy"
    entry = info(
        ENTRY,
        "Demo.RunCore",
        kind=DefinitionKind.METHOD,
        local_includes=(include(helper), include("bench/utils/demo/Impl/CliSupport.dfy")),
    )
    facts = (info(SPEC, "DemoSpec.Spec"), info(helper, "HoleOnly.Helper"), entry)
    with pytest.raises(PolicyError, match="forbidden role"):
        public_closure(manifest(), facts, ROOT)
    assert ROOT / helper in specification_inputs(manifest(), facts, ROOT)


# Safe YAML roundtrips preserve signature indentation, trailing spaces and final newlines.
def test_manifest_yaml_preserves_multiline_signature_whitespace() -> None:
    signature = "method RunCore()\n      ensures true  \n\n"
    authored = manifest(
        obligation=Obligation(path=ENTRY, symbol="Demo.RunCore", signature=signature)
    )
    restored = manifest_from_yaml(manifest_to_yaml(authored))
    assert restored == authored
    assert restored.obligation.signature == signature


# Duplicate top-level fields cannot silently replace an authored contract.
def test_manifest_yaml_rejects_duplicate_top_level_key() -> None:
    payload = manifest_to_yaml(manifest()) + "task_id: another\n"
    with pytest.raises(ConstructorError, match="duplicate mapping key"):
        manifest_from_yaml(payload)


# Duplicate nested fields cannot silently replace the fixed obligation.
def test_manifest_yaml_rejects_duplicate_obligation_key() -> None:
    payload = """task_id: demo
public_roots: [bench/utils/demo/Spec/DemoSpec.dfy]
obligation:
  path: bench/utils/demo/Impl/Demo.dfy
  symbol: Demo.RunCore
  signature: method RunCore()
  hole: method-body
  hole: method-body
"""
    with pytest.raises(ConstructorError, match="duplicate mapping key"):
        manifest_from_yaml(payload)
