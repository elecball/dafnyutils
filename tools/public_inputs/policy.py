"""Pure release checks that consume native facts and owner-authored declarations."""

import hashlib
import tomllib
from collections.abc import Callable, Sequence
from functools import lru_cache
from pathlib import Path, PurePosixPath

from dafny_analysis.kinds import DefinitionKind
from dafny_analysis.models import DefinitionInfo
from pydantic import ValidationError

from tools.public_inputs.models import Lock, LockedFile, Manifest, Permission, Project, Role


class PolicyError(ValueError):
    """Reject a public-input boundary or an inconsistent owner artifact."""


@lru_cache(maxsize=8192)
def role(path: str, hole_path: str | None = None) -> Role:
    """Apply the documented owner path convention, with only the declared hole exception."""
    name = PurePosixPath(path)
    if path == hole_path:
        return Role.SUPPORT
    if name.parts[:2] == ("bench", "core"):
        return Role.SUPPORT
    if (
        len(name.parts) == 4
        and name.parts[:2]
        in {
            ("bench", "utils"),
            ("bench", "algorithm"),
        }
        and name.name == "dfyconfig.toml"
    ):
        return Role.SUPPORT
    if name.suffix == ".dfy" and (
        (len(name.parts) == 5 and name.parts[:2] == ("bench", "utils") and name.parts[3] == "Spec")
        or (
            len(name.parts) == 4
            and name.parts[:2] == ("bench", "algorithm")
            and name.stem.endswith(("Spec", "Schema"))
        )
    ):
        return Role.SPECIFICATION
    if name.suffix == ".dfy" and name.parts[:2] in {
        ("bench", "utils"),
        ("bench", "algorithm"),
    }:
        return Role.CANDIDATE
    return Role.PRIVATE


@lru_cache(maxsize=8192)
def relative(path: Path, root: Path) -> str:
    """Reject native source facts that leave the owner repository."""
    resolved = path.resolve()
    if not resolved.is_relative_to(root.resolve()):
        raise PolicyError(f"native source escapes repository: {path}")
    return resolved.relative_to(root.resolve()).as_posix()


def entry_info(manifest: Manifest, infos: Sequence[DefinitionInfo], root: Path) -> DefinitionInfo:
    """Require exactly one native method body at the declared obligation."""
    found = [
        info
        for info in infos
        if relative(info.source_path, root) == manifest.obligation.path
        and info.full_name == manifest.obligation.symbol
    ]
    if len(found) != 1 or found[0].kind is not DefinitionKind.METHOD:
        raise PolicyError("obligation must identify exactly one native method")
    if found[0].body_start is None:
        raise PolicyError("obligation method has no body hole")
    return found[0]


def public_closure(
    manifest: Manifest,
    infos: Sequence[DefinitionInfo],
    root: Path,
    *,
    read: Callable[[str], bytes] | None = None,
) -> tuple[str, ...]:
    """Follow native include edges and reject candidate or private dependencies."""
    edges: dict[str, set[str]] = {}
    for info in infos:
        for include in info.local_includes:
            source = relative(include.source_path, root)
            edges.setdefault(source, set()).add(relative(include.target_path, root))
    known_sources = {relative(info.source_path, root) for info in infos}
    reached: set[str] = set()
    pending = list(manifest.public_roots) + _hole_dependencies(manifest, edges)
    while pending:
        path = pending.pop()
        if path in reached:
            continue
        if role(path) not in {Role.SPECIFICATION, Role.SUPPORT}:
            raise PolicyError(f"public dependency has forbidden role {role(path)}: {path}")
        if path.endswith(".dfy") and path not in known_sources:
            raise PolicyError(f"native include facts unavailable for public source: {path}")
        reached.add(path)
        pending.extend(edges.get(path, ()))
        if path.endswith(".toml"):
            pending.extend(project_dependencies(path, read, manifest.obligation.candidate_outputs))
    reached.add(manifest.obligation.path)
    return tuple(sorted(reached))


def _hole_dependencies(manifest: Manifest, edges: dict[str, set[str]]) -> list[str]:
    pending = []
    for path in edges.get(manifest.obligation.path, ()):
        if path in manifest.obligation.candidate_outputs:
            if role(path) is not Role.CANDIDATE or PurePosixPath(path).name == "CliSupport.dfy":
                raise PolicyError(f"designated candidate output is not an allowed output: {path}")
        else:
            pending.append(path)
    return pending


def make_lock(
    manifest: Manifest,
    manifest_bytes: bytes,
    infos: Sequence[DefinitionInfo],
    root: Path,
    read: Callable[[str], bytes],
    identity: tuple[str, str],
) -> Lock:
    """Hash immutable raw bytes while excluding only the native obligation body."""
    entry = entry_info(manifest, infos, root)
    files = []
    for path in public_closure(manifest, infos, root, read=read):
        payload = read(path)
        hole = path == manifest.obligation.path
        if hole:
            assert entry.body_start is not None
            signature = payload[entry.start : entry.body_start].decode().strip()
            if signature != manifest.obligation.signature:
                raise PolicyError("native obligation signature differs from the manifest")
            payload = payload[: entry.body_start] + payload[entry.end :]
        files.append(
            LockedFile(
                path=path,
                role=role(path, manifest.obligation.path),
                sha256=hashlib.sha256(payload).hexdigest(),
                excludes_obligation_body=hole,
            )
        )
    return Lock(
        manifest_sha256=hashlib.sha256(manifest_bytes).hexdigest(),
        release=manifest.release,
        checker=identity[0],
        analysis_client=identity[1],
        files=tuple(files),
    )


def _permissions(info: DefinitionInfo, reached: set[str]) -> set[Permission]:
    needed = set()
    if info.full_name not in reached:
        needed.add(Permission.UNREACHABLE)
    callable_kinds = {
        DefinitionKind.FUNCTION,
        DefinitionKind.FUNCTION_BY_METHOD,
        DefinitionKind.PREDICATE,
        DefinitionKind.TWOSTATE_FUNCTION,
        DefinitionKind.TWOSTATE_PREDICATE,
        DefinitionKind.LEAST_PREDICATE,
        DefinitionKind.GREATEST_PREDICATE,
        DefinitionKind.METHOD,
        DefinitionKind.CONSTRUCTOR,
        DefinitionKind.ITERATOR,
    }
    if info.has_by_method:
        needed.add(Permission.PROOF)
    if info.kind in callable_kinds and info.body_start is not None:
        if not info.ghost:
            needed.add(Permission.EXECUTABLE)
        elif info.kind in {DefinitionKind.METHOD, DefinitionKind.CONSTRUCTOR}:
            needed.add(Permission.PROOF)
    if (
        info.has_axiom_attribute
        or info.has_assume_statement
        or info.has_verify_false_attribute
        or info.has_extern_attribute
        or (info.kind in callable_kinds and info.body_start is None)
    ):
        needed.add(Permission.TRUST)
    return needed


def declaration_errors(
    manifest: Manifest, infos: Sequence[DefinitionInfo], root: Path, *, reachable: bool = True
) -> tuple[str, ...]:
    """Check native declaration reachability, executable/proof roles and trust exceptions."""
    by_name = {info.full_name: info for info in infos}
    reached = set()
    pending = [manifest.obligation.symbol]
    while pending:
        symbol = pending.pop()
        if symbol in reached:
            continue
        reached.add(symbol)
        info = by_name.get(symbol)
        if info is not None:
            # Header references preserve the fixed obligation without following its solution.
            dependencies = (
                info.header_dependencies
                if symbol == manifest.obligation.symbol
                else (
                    *info.dependencies,
                    *(reference.target_full_name for reference in info.references),
                )
            )
            pending.extend(dependencies)
    exceptions = {(item.path, item.symbol): item for item in manifest.specification_exceptions}
    seen = set()
    errors = []
    for info in infos:
        path = relative(info.source_path, root)
        if role(path) is not Role.SPECIFICATION:
            continue
        key = (path, info.full_name)
        seen.add(key)
        needed = _permissions(info, reached)
        exception = exceptions.get(key)
        permitted = set(exception.permits) if exception else set()
        if not reachable:
            needed.discard(Permission.UNREACHABLE)
            permitted.discard(Permission.UNREACHABLE)
        for missing in sorted(needed - permitted):
            errors.append(f"{path}:{info.full_name}: missing {missing} exception")
        for redundant in sorted(permitted - needed):
            errors.append(f"{path}:{info.full_name}: stale {redundant} exception")
    for path, symbol in sorted(exceptions.keys() - seen):
        errors.append(
            f"{path}:{symbol}: exception does not name a public specification declaration"
        )
    return tuple(errors)


def hole_source(
    manifest: Manifest, infos: Sequence[DefinitionInfo], root: Path, payload: bytes
) -> str:
    """Replace only native body/include spans and provide empty candidate modules."""
    entry = entry_info(manifest, infos, root)
    assert entry.body_start is not None
    edits = {(entry.body_start, entry.end): b"{ assert false; }"}
    for info in infos:
        if relative(info.source_path, root) != manifest.obligation.path:
            continue
        for include in info.local_includes:
            path = relative(include.target_path, root)
            replacement = b""
            if path not in manifest.obligation.candidate_outputs:
                replacement = f'include "{root / path}"'.encode()
            edits[(include.start, include.end)] = replacement
    for (start, end), replacement in sorted(edits.items(), reverse=True):
        payload = payload[:start] + replacement + payload[end:]
    shells = "\n".join(
        f"module {PurePosixPath(path).stem} {{}}" for path in manifest.obligation.candidate_outputs
    )
    return payload.decode() + "\n" + shells + "\n"


def specification_inputs(
    manifest: Manifest,
    infos: Sequence[DefinitionInfo],
    root: Path,
    *,
    read: Callable[[str], bytes] | None = None,
) -> tuple[Path, ...]:
    """Select public declarations reached from roots and fixed hole dependencies."""
    edges: dict[str, set[str]] = {}
    for info in infos:
        for include in info.local_includes:
            edges.setdefault(relative(include.source_path, root), set()).add(
                relative(include.target_path, root)
            )
    reached = set()
    pending = list(manifest.public_roots) + _hole_dependencies(manifest, edges)
    while pending:
        path = pending.pop()
        if path in reached or role(path) not in {Role.SPECIFICATION, Role.SUPPORT}:
            continue
        reached.add(path)
        pending.extend(edges.get(path, ()))
        if path.endswith(".toml"):
            pending.extend(project_dependencies(path, read, manifest.obligation.candidate_outputs))
    return tuple(root / path for path in sorted(reached) if path.endswith(".dfy"))


def project_dependencies(
    path: str,
    read: Callable[[str], bytes] | None,
    candidate_outputs: tuple[str, ...],
) -> tuple[str, ...]:
    """Follow literal native project includes and reject undeclared candidate inputs."""
    if read is None:
        raise PolicyError(f"project dependency reader unavailable: {path}")
    try:
        project = Project.model_validate(tomllib.loads(read(path).decode("utf-8")))
    except (UnicodeDecodeError, tomllib.TOMLDecodeError, ValidationError) as exc:
        raise PolicyError(f"invalid or unsupported native project {path}: {exc}") from exc
    dependencies = []
    for included in project.includes:
        name = PurePosixPath(included)
        if (
            name.is_absolute()
            or ".." in name.parts
            or any(char in included for char in "*?[]{}")
            or name.suffix != ".dfy"
        ):
            raise PolicyError(f"unsupported project include in {path}: {included}")
        target = (PurePosixPath(path).parent / name).as_posix()
        if target in candidate_outputs:
            continue
        if role(target) not in {Role.SPECIFICATION, Role.SUPPORT}:
            raise PolicyError(f"project includes an undeclared candidate/private input: {target}")
        dependencies.append(target)
    return tuple(sorted(set(dependencies)))
