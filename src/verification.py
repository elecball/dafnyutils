"""Verify candidate-editable Dafny sources and validate their TRX results."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import subprocess
import sys
import tempfile
import xml.etree.ElementTree as ElementTree
from collections.abc import Callable, Sequence
from pathlib import Path

from analysis.kinds import DefinitionKind
from analysis.models import DefinitionVerificationTarget
from benchmarks.task import (
    ProofReuseProtocolVersion,
    ProofReuseScope,
    ProofReuseTarget,
)
from dafny_cli import dafny_command
from entry_contract import (
    EntryContractCheckSession,
    EntryContractManifest,
    EntryContractSourceSnapshot,
    EntryValidationFailure,
    ValidatedEntryContract,
    entry_contract_source_snapshot,
)
from runtime.process import CapturedProcess, run_process_capture_bytes
from standard_library import (
    DAFNY_BENCH_CORE_LIBRARY_OPTION,
    DAFNY_STANDARD_LIBRARY_OPTION,
    dafny_bench_core_library_options,
    has_dafny_warning,
    without_expected_dafny_library_warnings,
    without_expected_library_warnings,
)

DAFNY_VERIFICATION_TIME_LIMIT_SEC = 30
DAFNY_VERIFICATION_TARGET_TIMEOUT_SEC = 100
DAFNY_VERIFICATION_RANDOM_SEED = 42

_FORBIDDEN_BODYLESS_KINDS = frozenset(
    {
        DefinitionKind.METHOD,
        DefinitionKind.CONSTRUCTOR,
        DefinitionKind.CONSTANT,
        DefinitionKind.FUNCTION,
        DefinitionKind.PREDICATE,
        DefinitionKind.TWOSTATE_FUNCTION,
        DefinitionKind.TWOSTATE_PREDICATE,
        DefinitionKind.ITERATOR,
        DefinitionKind.FUNCTION_BY_METHOD,
        DefinitionKind.LEAST_PREDICATE,
        DefinitionKind.GREATEST_PREDICATE,
    }
)


class _BodylessProofDeclaration(EntryValidationFailure):
    pass


class _EmptyProofScope(EntryValidationFailure):
    pass


def _verification_options(workspace_root: Path) -> tuple[str, ...]:
    return verification_options(dafny_bench_core_library_options(workspace_root))


def verification_options(library_options: Sequence[str] = ()) -> tuple[str, ...]:
    """Keep proof batching and limits consistent for local and evaluator verification."""
    return (
        DAFNY_STANDARD_LIBRARY_OPTION,
        *library_options,
        f"--boogie=/randomSeed:{DAFNY_VERIFICATION_RANDOM_SEED}",
        "--verify-included-files",
        "--isolate-assertions",
        f"--verification-time-limit:{DAFNY_VERIFICATION_TIME_LIMIT_SEC}",
        "--allow-external-contracts",
    )


def _trx_counts(report_path: Path) -> tuple[int, int]:
    results = ElementTree.parse(report_path).getroot().findall(".//{*}UnitTestResult")
    return len(results), sum(item.get("outcome") != "Passed" for item in results)


def _emit_outcome(outcome: str, phase: str) -> None:
    print(f"DAFNY_VERIFICATION_OUTCOME={outcome} phase={phase}")


def _emit_target_outcome(outcome: str, phase: str) -> None:
    print(f"DAFNY_TARGET_VERIFICATION_OUTCOME={outcome} phase={phase}")


def _emit_compile_outcome(outcome: str, phase: str) -> None:
    print(f"DAFNY_COMPILE_OUTCOME={outcome} phase={phase}")


def _run_verification_command(
    command: list[str],
    *,
    cwd: Path,
) -> CapturedProcess:
    return run_process_capture_bytes(
        command,
        cwd=cwd,
        env={**os.environ, "TMPDIR": "/tmp"},
        timeout_sec=DAFNY_VERIFICATION_TARGET_TIMEOUT_SEC,
        start_new_session=True,
    )


def _stream_text(stream: str | bytes | None) -> str:
    if isinstance(stream, bytes):
        return stream.decode(errors="replace")
    return stream or ""


def _emit_process_output(stdout: str, stderr: str) -> None:
    if stdout:
        print(stdout, end="", file=sys.stdout)
    if stderr:
        print(stderr, end="", file=sys.stderr)


def _run_build_command(
    command: Sequence[str],
    *,
    cwd: Path,
) -> subprocess.CompletedProcess[bytes]:
    return subprocess.run(command, cwd=cwd, env={**os.environ, "TMPDIR": "/tmp"}, check=False)


def _verify_target(
    target: DefinitionVerificationTarget,
    contract: ValidatedEntryContract,
    workspace_root: Path,
    dafny: str,
    report_path: Path,
    options: tuple[str, ...],
    libraries: tuple[Path, ...],
    *,
    emit_outcome: Callable[[str, str], None] = _emit_outcome,
    source_filter: str | None = None,
) -> tuple[int, int] | None:
    source_path = (
        source_filter
        if source_filter is not None
        else Path(target.source_path).relative_to(workspace_root).as_posix()
    )
    try:
        result = _run_verification_command(
            [
                dafny,
                "verify",
                options[0],
                str(contract.execution_source),
                *options[1:],
                f"--filter-position={source_path}",
                f"--filter-symbol={target.full_name}.",
                "--log-format",
                f"trx;LogFileName={report_path}",
            ],
            cwd=workspace_root,
        )
    except OSError:
        emit_outcome("infrastructure_failure", "build")
        return None
    stdout = _stream_text(result.stdout)
    stderr = _stream_text(result.stderr)
    if DAFNY_BENCH_CORE_LIBRARY_OPTION in options:
        stdout = without_expected_dafny_library_warnings(stdout, workspace_root)
        stderr = without_expected_dafny_library_warnings(stderr, workspace_root)
    if libraries:
        stdout = without_expected_library_warnings(stdout, libraries)
        stderr = without_expected_library_warnings(stderr, libraries)
    _emit_process_output(stdout, stderr)
    if (
        result.timed_out
        or has_dafny_warning(stdout)
        or has_dafny_warning(stderr)
        or result.returncode != 0
    ):
        emit_outcome("verification_failure", "verify")
        return None
    try:
        return _trx_counts(report_path)
    except (OSError, ElementTree.ParseError):
        emit_outcome("infrastructure_failure", "evidence")
        return None


def _verify_sources(
    contract: ValidatedEntryContract,
    workspace_root: Path,
    dafny: str,
    report_dir: Path,
    verification_options: tuple[str, ...],
    libraries: tuple[Path, ...] = (),
) -> tuple[int, int] | None:
    try:
        targets = _verification_targets(contract)
    except _BodylessProofDeclaration:
        _emit_outcome("verification_failure", "verify")
        return None
    except EntryValidationFailure:
        _emit_outcome("infrastructure_failure", "evidence")
        return None
    total = 0
    failed = 0
    print(f"Verification targets ({len(targets)} declarations):", flush=True)
    for index, target in enumerate(targets):
        progress = f"[{index + 1}/{len(targets)}]"
        source_path = Path(target.source_path).relative_to(workspace_root).as_posix()
        print(f"{progress} Verifying {source_path}::{target.full_name}", flush=True)
        counts = _verify_target(
            target,
            contract,
            workspace_root,
            dafny,
            report_dir / f"{index}.trx",
            verification_options,
            libraries,
        )
        if counts is None:
            return None
        report_total, report_failed = counts
        total += report_total
        failed += report_failed
        print(
            f"{progress} Completed {source_path}: total={report_total} failed={report_failed}",
            flush=True,
        )
    return total, failed


def _verification_targets(
    contract: ValidatedEntryContract,
) -> tuple[DefinitionVerificationTarget, ...]:
    if any(
        definition.body_start is None and definition.kind in _FORBIDDEN_BODYLESS_KINDS
        for definition in contract.verification_definitions
    ):
        raise _BodylessProofDeclaration(
            "verification scope contains a forbidden bodyless declaration"
        )
    targets = contract.verification_targets
    if not targets:
        raise _EmptyProofScope("verification scope has no native targets")
    return targets


def _validated_proof_targets(
    contract: ValidatedEntryContract, workspace_root: Path
) -> tuple[DefinitionVerificationTarget, ...]:
    _verification_targets(contract)
    targets = individual_targets(contract, workspace_root)
    for target in targets:
        _select_individual_target(
            contract,
            targets,
            Path(target.source_path).resolve(),
            target.full_name,
        )
    return targets


def _source_identity(snapshot: EntryContractSourceSnapshot) -> str:
    payload = {
        "files": snapshot.files,
        "manifest_sha256": snapshot.manifest_sha256,
        "utility_sources": snapshot.utility_sources,
    }
    encoded = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def _validated_source_identity(
    session: EntryContractCheckSession,
    contract: ValidatedEntryContract,
) -> str:
    snapshot = entry_contract_source_snapshot(
        session.workspace_root,
        session.utility_root,
        session.manifest,
        additional_sources=contract.analysis_sources,
    )
    session.validate()
    return _source_identity(snapshot)


def _validated_session_contract(
    session: EntryContractCheckSession,
    dafny: str,
) -> tuple[ValidatedEntryContract, tuple[str, ...]]:
    options = _verification_options(session.workspace_root)
    if session.tool_identity is not None and session.tool_identity != dafny:
        raise EntryValidationFailure("contract session Dafny tool does not match verifier tool")
    if session.verification_options and session.verification_options != options:
        raise EntryValidationFailure("contract session verifier options do not match")
    return session.validate(), options


def verify_session(session: EntryContractCheckSession, dafny: str) -> int:
    """Verify one already-bound contract session using one explicit Dafny tool."""
    try:
        contract, options = _validated_session_contract(session, dafny)
    except (EntryValidationFailure, OSError, ValueError):
        _emit_outcome("infrastructure_failure", "evidence")
        return 1

    return verify_contract(
        contract, session.workspace_root, dafny, options, validate=session.validate
    )


def proof_reuse_scope(
    session: EntryContractCheckSession,
    dafny: str,
) -> ProofReuseScope:
    """Return the exact validated native proof scope for trusted-host reuse."""
    contract, options = _validated_session_contract(session, dafny)
    targets = _validated_proof_targets(contract, session.workspace_root)
    identity = _validated_source_identity(session, contract)
    return ProofReuseScope(
        protocol=ProofReuseProtocolVersion.V1,
        source_identity=identity,
        targets=tuple(
            ProofReuseTarget(
                source_path=Path(target.source_path).relative_to(session.workspace_root).as_posix(),
                symbol=target.full_name,
            )
            for target in targets
        ),
        proof_roots=(contract.execution_source.relative_to(session.workspace_root).as_posix(),),
        verification_options=options,
    )


def describe_proof_scope_session(session: EntryContractCheckSession, dafny: str) -> int:
    """Write one JSON proof-scope descriptor and no other standard output."""
    try:
        scope = proof_reuse_scope(session, dafny)
    except (EntryValidationFailure, OSError, ValueError) as error:
        print(str(error), file=sys.stderr)
        return 1
    print(scope.model_dump_json())
    return 0


def compile_only_session(
    session: EntryContractCheckSession,
    dafny: str,
    build_command: Sequence[str],
) -> int:
    """Compile once between matching validated source identities without proving."""
    try:
        if (
            len(build_command) < 6
            or build_command[0] != dafny
            or tuple(build_command[1:4]) != ("build", "--no-verify", "--output")
            or any(
                not argument or argument.startswith(("-", "/", "@"))
                for argument in build_command[4:]
            )
        ):
            raise EntryValidationFailure("compile command must match the fixed no-verify shape")
        contract, _ = _validated_session_contract(session, dafny)
        before = _validated_source_identity(session, contract)
    except (EntryValidationFailure, OSError, ValueError):
        _emit_compile_outcome("infrastructure_failure", "evidence")
        return 1
    try:
        build_result = _run_build_command(build_command, cwd=session.workspace_root)
    except OSError:
        _emit_compile_outcome("infrastructure_failure", "build")
        return 1
    if build_result.returncode != 0:
        _emit_compile_outcome("compile_failure", "build")
        return 1
    try:
        contract = session.validate()
        after = _validated_source_identity(session, contract)
        if before != after:
            raise EntryValidationFailure("workspace source identity changed during compilation")
    except (EntryValidationFailure, OSError, ValueError):
        _emit_compile_outcome("infrastructure_failure", "evidence")
        return 1
    _emit_compile_outcome("compiled", "build")
    return 0


def verify_contract(
    contract: ValidatedEntryContract,
    working_directory: Path,
    dafny: str,
    options: tuple[str, ...],
    *,
    validate: Callable[[], object],
    libraries: tuple[Path, ...] = (),
) -> int:
    """Verify a resolved proof surface and recheck its source identity before success."""
    try:
        reports = tempfile.TemporaryDirectory()
    except OSError:
        _emit_outcome("infrastructure_failure", "evidence")
        return 1
    with reports as report_dir:
        counts = _verify_sources(
            contract,
            working_directory,
            dafny,
            Path(report_dir),
            options,
            libraries,
        )
    if counts is None:
        return 1
    try:
        validate()
    except (EntryValidationFailure, OSError, ValueError):
        _emit_outcome("infrastructure_failure", "evidence")
        return 1
    total, failed = counts

    if total == 0:
        _emit_outcome("infrastructure_failure", "evidence")
        return 1
    if failed:
        _emit_outcome("verification_failure", "verify")
        return 1
    _emit_outcome("verified", "verify")
    print(f"DAFNY_VERIFICATION_RESULT total={total} failed=0")
    return 0


def run_full_session(
    session: EntryContractCheckSession,
    dafny: str,
    build_command: Sequence[str],
) -> int:
    """Run build, proof-layout, and verification phases through one session."""
    try:
        session.validate()
    except (EntryValidationFailure, OSError, ValueError):
        _emit_outcome("infrastructure_failure", "build")
        return 1

    try:
        build_result = _run_build_command(build_command, cwd=session.workspace_root)
    except OSError:
        _emit_outcome("infrastructure_failure", "build")
        return 1
    if build_result.returncode != 0:
        _emit_outcome("infrastructure_failure", "build")
        return 1

    try:
        session.validate()
    except (EntryValidationFailure, OSError, ValueError):
        _emit_outcome("infrastructure_failure", "proof_layout")
        return 1
    return verify_session(session, dafny)


def _load_session(
    workspace_root: Path,
    utility_root: Path,
    manifest_path: Path,
    dafny: str,
) -> EntryContractCheckSession:
    workspace_root = workspace_root.resolve()
    utility_root = (workspace_root / utility_root).resolve()
    manifest = EntryContractManifest.model_validate_json(manifest_path.read_text(encoding="utf-8"))
    return EntryContractCheckSession(
        workspace_root,
        utility_root,
        manifest,
        tool_identity=dafny,
        verification_options=_verification_options(workspace_root),
    )


def run(
    workspace_root: Path,
    utility_root: Path,
    manifest_path: Path,
    dafny: str,
) -> int:
    """Verify every entry-reachable candidate source from one execution root."""
    try:
        session = _load_session(workspace_root, utility_root, manifest_path, dafny)
    except (OSError, ValueError):
        _emit_outcome("infrastructure_failure", "evidence")
        return 1
    return verify_session(session, dafny)


def run_full(
    workspace_root: Path,
    utility_root: Path,
    manifest_path: Path,
    dafny: str,
    build_command: Sequence[str],
) -> int:
    """Load one manifest and run every public verification phase in one process."""
    try:
        session = _load_session(workspace_root, utility_root, manifest_path, dafny)
    except (OSError, ValueError):
        _emit_outcome("infrastructure_failure", "build")
        return 1
    return run_full_session(session, dafny, build_command)


def describe_proof_scope(
    workspace_root: Path,
    utility_root: Path,
    manifest_path: Path,
    dafny: str,
) -> int:
    """Load a public contract and print its validated proof-reuse scope."""
    try:
        session = _load_session(workspace_root, utility_root, manifest_path, dafny)
    except (OSError, ValueError) as error:
        print(str(error), file=sys.stderr)
        return 1
    return describe_proof_scope_session(session, dafny)


def run_compile_only(
    workspace_root: Path,
    utility_root: Path,
    manifest_path: Path,
    dafny: str,
    build_command: Sequence[str],
) -> int:
    """Load a public contract and run its declared compile-only command."""
    try:
        session = _load_session(workspace_root, utility_root, manifest_path, dafny)
    except (OSError, ValueError):
        _emit_compile_outcome("infrastructure_failure", "evidence")
        return 1
    return compile_only_session(session, dafny, build_command)


def individual_targets(
    contract: ValidatedEntryContract, workspace_root: Path
) -> tuple[DefinitionVerificationTarget, ...]:
    """Return unique native targets confined to validated editable sources."""
    targets = sorted(
        contract.verification_targets, key=lambda target: (target.source_path, target.full_name)
    )
    identities: set[tuple[Path, str]] = set()
    for target in targets:
        source = Path(target.source_path).resolve()
        identity = (source, target.full_name)
        if (
            not source.is_relative_to(workspace_root)
            or source not in contract.verification_sources
            or identity in identities
        ):
            raise EntryValidationFailure("invalid or ambiguous native verification target")
        identities.add(identity)
    return tuple(targets)


def _select_individual_target(
    contract: ValidatedEntryContract,
    targets: tuple[DefinitionVerificationTarget, ...],
    selected_source: Path,
    symbol: str,
) -> DefinitionVerificationTarget:
    matches = tuple(
        target
        for target in targets
        if Path(target.source_path).resolve() == selected_source and target.full_name == symbol
    )
    if len(matches) != 1:
        raise EntryValidationFailure("target must identify one listed editable native declaration")
    # Native filters are suffix matches, so exact Python selection alone is insufficient.
    matching_symbols = tuple(
        target
        for target in targets
        if Path(target.source_path).resolve() == selected_source
        and target.full_name.endswith(symbol)
    )
    if matching_symbols != matches:
        raise EntryValidationFailure("native symbol suffix filter is ambiguous for this source")
    sources = {path.resolve() for path in (*contract.analysis_sources, *contract.utility_sources)}
    sources.update(Path(target.source_path).resolve() for target in targets)
    if any(
        source != selected_source and source.as_posix().endswith(selected_source.as_posix())
        for source in sources
    ):
        raise EntryValidationFailure("native source suffix filter is ambiguous")
    return matches[0]


def verify_individual_session(
    session: EntryContractCheckSession,
    dafny: str,
    *,
    source: Path | None = None,
    symbol: str | None = None,
) -> int:
    """List native targets or verify one exact target without running the full gate."""
    options = _verification_options(session.workspace_root)
    try:
        if session.tool_identity is not None and session.tool_identity != dafny:
            raise EntryValidationFailure("contract session Dafny tool does not match verifier tool")
        if session.verification_options and session.verification_options != options:
            raise EntryValidationFailure("contract session verifier options do not match")
        contract = session.validate()
        targets = individual_targets(contract, session.workspace_root)
        if source is None and symbol is None:
            for target in targets:
                relative = Path(target.source_path).relative_to(session.workspace_root)
                print(f"{relative.as_posix()}::{target.full_name}")
            return 0
        if source is None or not symbol:
            raise EntryValidationFailure("both --source and --symbol are required")
        selected_source = (session.workspace_root / source).resolve()
        if not selected_source.is_relative_to(session.workspace_root):
            raise EntryValidationFailure("target source is outside the workspace")
        target = _select_individual_target(contract, targets, selected_source, symbol)
    except (EntryValidationFailure, OSError, ValueError) as error:
        print(str(error), file=sys.stderr)
        _emit_target_outcome("infrastructure_failure", "selection")
        return 1
    return _verify_individual_target(session, contract, target, dafny, options)


def _verify_individual_target(
    session: EntryContractCheckSession,
    contract: ValidatedEntryContract,
    target: DefinitionVerificationTarget,
    dafny: str,
    options: tuple[str, ...],
) -> int:
    try:
        reports = tempfile.TemporaryDirectory()
    except OSError:
        _emit_target_outcome("infrastructure_failure", "evidence")
        return 1
    with reports as report_dir:
        counts = _verify_target(
            target,
            contract,
            session.workspace_root,
            dafny,
            Path(report_dir) / "target.trx",
            options,
            (),
            emit_outcome=_emit_target_outcome,
            source_filter=Path(target.source_path).resolve().as_posix(),
        )
    if counts is None:
        return 1
    try:
        session.validate()
    except (EntryValidationFailure, OSError, ValueError):
        _emit_target_outcome("infrastructure_failure", "evidence")
        return 1
    total, failed = counts
    if failed:
        _emit_target_outcome("verification_failure", "verify")
        return 1
    if total == 0:
        print("Selected target has no verification obligations.", file=sys.stderr)
        _emit_target_outcome("no_obligations", "verify")
        return 1
    _emit_target_outcome("verified", "verify")
    source = Path(target.source_path).relative_to(session.workspace_root).as_posix()
    print(
        f"DAFNY_TARGET_VERIFICATION_RESULT source={source} symbol={target.full_name} total={total}"
    )
    return 0


def _dispatch_explicit_mode(
    parser: argparse.ArgumentParser,
    arguments: argparse.Namespace,
) -> int | None:
    if arguments.individual:
        if arguments.full or arguments.build_arg:
            parser.error(
                "--individual cannot be combined with full verification or build arguments"
            )
        if arguments.list:
            if arguments.source is not None or arguments.symbol is not None:
                parser.error("--list cannot be combined with target selectors")
        elif arguments.source is None or not arguments.symbol:
            parser.error("--individual requires --list or both --source and --symbol")
        return run_individual(
            arguments.workspace_root,
            arguments.utility_root,
            arguments.manifest,
            arguments.dafny,
            source=arguments.source,
            symbol=arguments.symbol,
        )
    if arguments.describe_proof_scope:
        if arguments.build_arg:
            parser.error("--describe-proof-scope cannot be combined with build arguments")
        return describe_proof_scope(
            arguments.workspace_root,
            arguments.utility_root,
            arguments.manifest,
            arguments.dafny,
        )
    if arguments.compile_only:
        if not arguments.build_arg:
            parser.error("--compile-only requires at least one --build-arg")
        return run_compile_only(
            arguments.workspace_root,
            arguments.utility_root,
            arguments.manifest,
            arguments.dafny,
            arguments.build_arg,
        )
    return None


def main(argv: Sequence[str] | None = None) -> int:
    """Dispatch full verification or separately scoped candidate feedback."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--workspace-root", default=".", type=Path)
    parser.add_argument("--utility-root", required=True, type=Path)
    parser.add_argument("--manifest", required=True, type=Path)
    parser.add_argument("--dafny", default=dafny_command())
    parser.add_argument("--full", action="store_true")
    parser.add_argument("--build-arg", action="append", default=[])
    parser.add_argument("--individual", action="store_true")
    parser.add_argument("--describe-proof-scope", action="store_true")
    parser.add_argument("--compile-only", action="store_true")
    parser.add_argument("--list", action="store_true")
    parser.add_argument("--source", type=Path)
    parser.add_argument("--symbol")
    arguments = parser.parse_args(argv)
    scoped = arguments.list or arguments.source is not None or arguments.symbol is not None
    modes = sum(
        (
            arguments.full,
            arguments.individual,
            arguments.describe_proof_scope,
            arguments.compile_only,
        )
    )
    if modes > 1:
        parser.error("verification modes cannot be combined")
    if scoped and not arguments.individual:
        parser.error("target selectors require --individual and cannot scope the full gate")
    selected = _dispatch_explicit_mode(parser, arguments)
    if selected is not None:
        return selected
    if arguments.full:
        if not arguments.build_arg:
            parser.error("--full requires at least one --build-arg")
        return run_full(
            arguments.workspace_root,
            arguments.utility_root,
            arguments.manifest,
            arguments.dafny,
            arguments.build_arg,
        )
    return run(
        arguments.workspace_root,
        arguments.utility_root,
        arguments.manifest,
        arguments.dafny,
    )


def run_individual(
    workspace_root: Path,
    utility_root: Path,
    manifest_path: Path,
    dafny: str,
    *,
    source: Path | None = None,
    symbol: str | None = None,
) -> int:
    """Bind individual feedback to the same immutable manifest as full verification."""
    try:
        session = _load_session(workspace_root, utility_root, manifest_path, dafny)
    except (OSError, ValueError):
        _emit_target_outcome("infrastructure_failure", "evidence")
        return 1
    return verify_individual_session(session, dafny, source=source, symbol=symbol)


if __name__ == "__main__":
    raise SystemExit(main())
