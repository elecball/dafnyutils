"""Maintain the complete owner catalog without altering candidate delivery."""

import argparse
import subprocess
from pathlib import Path

from dafny_analysis.client import DefinitionAnalysisError
from dafny_analysis.models import DefinitionInfo
from pydantic import ValidationError
from yaml import YAMLError

from benchmarks.definition import class_name_for_task_id
from benchmarks.profiles import IMPLEMENTATION_SUPPORT_FILES, ResolvedBenchmark, utility_paths
from benchmarks.repository import BenchmarkRepository
from tools.public_inputs.models import (
    InitializationResult,
    Lock,
    Manifest,
    Obligation,
    Report,
    TaskResult,
    manifest_from_yaml,
    manifest_to_yaml,
)
from tools.public_inputs.native import Native
from tools.public_inputs.policy import (
    PolicyError,
    declaration_errors,
    hole_source,
    make_lock,
    public_closure,
    relative,
    specification_inputs,
)


def catalog(root: Path) -> dict[str, dict[str, str]]:
    """Derive task identities and source locations from the existing data contract."""
    return {
        definition.task_id: utility_paths(
            ResolvedBenchmark.from_definition(definition), definition.task_id
        )
        for definition in BenchmarkRepository.open(root).definitions()
    }


def inventory(root: Path, tasks: dict[str, dict[str, str]]) -> tuple[Path, ...]:
    """Parse only public specifications, shared support and fixed entry scaffolds."""
    sources = set((root / "bench/core").glob("*.dfy"))
    sources.update((root / "bench/utils").glob("*/Spec/*.dfy"))
    sources.update((root / "bench/algorithm").glob("*/*Spec.dfy"))
    sources.update((root / "bench/algorithm").glob("*/*Schema.dfy"))
    for paths in tasks.values():
        directory = root / paths["utility_dir"]
        if (directory / "Spec").is_dir():
            sources.update((directory / "Spec").glob("*.dfy"))
        else:
            sources.update(directory.glob("*Spec.dfy"))
            sources.update(directory.glob("*Schema.dfy"))
        sources.add(root / paths["wrapper"])
    return tuple(sorted(sources))


def bootstrap(
    task_id: str, paths: dict[str, str], infos: tuple[DefinitionInfo, ...], root: Path
) -> Manifest:
    """Capture an existing entry header without copying its implementation body."""
    class_name = class_name_for_task_id(task_id)
    symbol = f"{class_name}.{class_name}BenchmarkItem.RunCore"
    found = [
        info
        for info in infos
        if info.full_name == symbol and relative(info.source_path, root) == paths["wrapper"]
    ]
    if len(found) != 1 or found[0].body_start is None:
        raise PolicyError(f"{task_id}: native RunCore method body is missing or ambiguous")
    entry = found[0]
    payload = (root / paths["wrapper"]).read_bytes()
    return Manifest(
        task_id=task_id,
        public_roots=(paths["spec"], paths["project_config"], *IMPLEMENTATION_SUPPORT_FILES),
        obligation=Obligation(
            path=paths["wrapper"],
            symbol=symbol,
            signature=payload[entry.start : entry.body_start].decode().strip(),
            candidate_outputs=(paths["core"], paths["proof"], paths["cli"]),
        ),
    )


def _read_public(root: Path, path: str) -> bytes:
    target = root / path
    if relative(target, root) != path:
        raise PolicyError(f"public file must retain its canonical repository identity: {path}")
    return target.read_bytes()


def _save(path: Path, document: Manifest | Lock) -> None:
    text = (
        manifest_to_yaml(document)
        if isinstance(document, Manifest)
        else document.model_dump_json(indent=2) + "\n"
    )
    path.write_text(text, encoding="utf-8")


def _lint_native(
    manifest: Manifest, paths: dict[str, str], parsed: tuple[DefinitionInfo, ...], native: Native
) -> tuple[str, ...]:
    try:
        sources = specification_inputs(
            manifest, parsed, native.root, read=lambda path: _read_public(native.root, path)
        )
    except (OSError, PolicyError) as exc:
        return (str(exc), "native resolution blocked by project dependencies")
    try:
        resolved = native.resolve(sources)
    except DefinitionAnalysisError as exc:
        return (str(exc), "declaration/trust/reachability checks blocked by public resolution")
    errors = []
    try:
        public_closure(
            manifest, parsed, native.root, read=lambda path: _read_public(native.root, path)
        )
    except PolicyError as exc:
        errors.extend((str(exc), "obligation elaboration/reachability blocked by public roles"))
        errors.extend(
            declaration_errors(manifest, resolved.definitions, native.root, reachable=False)
        )
        return tuple(errors)
    scaffold = hole_source(
        manifest,
        parsed,
        native.root,
        (native.root / manifest.obligation.path).read_bytes(),
    )
    try:
        hole_infos = native.resolve_hole(scaffold, native.root)
    except DefinitionAnalysisError as exc:
        return (str(exc), "obligation elaboration/reachability blocked by native resolution")
    hole_infos = tuple(
        info.model_copy(
            update={
                "source_path": native.root / manifest.obligation.path,
            }
        )
        for info in hole_infos
    )
    errors.extend(
        declaration_errors(
            manifest,
            (*resolved.definitions, *hole_infos),
            native.root,
        )
    )
    return tuple(errors)


def _check_task(
    task: str,
    command: str,
    paths: dict[str, str],
    directory: Path,
    parsed: tuple[DefinitionInfo, ...],
    native: Native,
    identity: tuple[str, str],
) -> TaskResult:
    """Record task-local defects without hiding errors in other catalog entries."""
    root = native.root
    errors = []
    manifest_path = directory / f"{task}.manifest.yaml"
    lock_path = directory / f"{task}.lock.json"
    try:
        manifest_bytes = manifest_path.read_bytes()
    except OSError as exc:
        return TaskResult(task=task, errors=(str(exc),))
    try:
        manifest = manifest_from_yaml(manifest_bytes)
    except (ValidationError, YAMLError) as exc:
        return TaskResult(task=task, errors=(str(exc),))
    if manifest.task_id != task:
        return TaskResult(task=task, errors=("manifest task ID differs from catalog identity",))
    if mismatch := _interface_error(task, manifest, paths):
        return TaskResult(task=task, errors=(mismatch,))
    if command == "lint":
        errors.extend(_lint_native(manifest, paths, parsed, native))
        errors.extend(_check_lock_file(lock_path))
    try:
        expected = make_lock(
            manifest,
            manifest_bytes,
            parsed,
            root,
            lambda path: _read_public(root, path),
            identity,
        )
    except (OSError, PolicyError) as exc:
        errors.append(str(exc))
        return TaskResult(task=task, errors=tuple(dict.fromkeys(errors)))
    errors.extend(_store_or_compare(command, lock_path, expected))
    return TaskResult(task=task, errors=tuple(dict.fromkeys(errors)))


def _interface_error(task: str, manifest: Manifest, paths: dict[str, str]) -> str | None:
    class_name = class_name_for_task_id(task)
    expected_symbol = f"{class_name}.{class_name}BenchmarkItem.RunCore"
    if (manifest.obligation.path, manifest.obligation.symbol) != (
        paths["wrapper"],
        expected_symbol,
    ):
        return "obligation differs from the fixed task entry"
    if manifest.obligation.candidate_outputs != (paths["core"], paths["proof"], paths["cli"]):
        return "candidate outputs differ from fixed task interface"
    required_roots = {paths["spec"], paths["project_config"], *IMPLEMENTATION_SUPPORT_FILES}
    if missing := sorted(required_roots - set(manifest.public_roots)):
        return f"manifest omits mandatory fixed public roots: {missing}"
    return None


def _check_lock_file(path: Path) -> tuple[str, ...]:
    if not path.is_file():
        return ("committed lock is missing",)
    return ()


def _store_or_compare(command: str, path: Path, expected: Lock) -> tuple[str, ...]:
    try:
        existing = Lock.model_validate_json(path.read_bytes()) if path.is_file() else None
    except (OSError, ValidationError) as exc:
        return (f"existing lock is invalid; refusing replacement: {exc}",)
    if command != "lock":
        return ("committed lock is stale",) if existing is not None and existing != expected else ()
    if existing is not None and existing != expected and existing.release == expected.release:
        return ("public inputs changed under the same release identity; declare a new release",)
    try:
        _save(path, expected)
    except OSError as exc:
        return (str(exc),)
    return ()


def execute(args: argparse.Namespace) -> int:
    """Generate strict locks or report every catalog release defect."""
    root = args.root.resolve()
    tasks = catalog(root)
    selected = args.task or list(tasks)
    if unknown := sorted(set(selected) - tasks.keys()):
        raise PolicyError(f"unknown task IDs: {unknown}")
    native = Native(root, args.dafny)
    parsed = native.parse(inventory(root, {task: tasks[task] for task in selected}))
    identity = native.identity()
    directory = root / "public-inputs"
    if args.command == "init":
        directory.mkdir(exist_ok=True)
        for task in selected:
            path = directory / f"{task}.manifest.yaml"
            if path.exists():
                raise PolicyError(f"refusing to overwrite owner-authored manifest: {path}")
            _save(path, bootstrap(task, tasks[task], parsed, root))
        print(InitializationResult(manifests_created=len(selected)).model_dump_json())
        return 0
    results = [
        _check_task(task, args.command, tasks[task], directory, parsed, native, identity)
        for task in selected
    ]
    print(Report(command=args.command, results=tuple(results)).model_dump_json(indent=2))
    return int(any(item.errors for item in results))


def main() -> int:
    """Run the owner maintenance command with an explicit repository boundary."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=("init", "lock", "lint"))
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[2])
    parser.add_argument("--dafny")
    parser.add_argument("--task", action="append")
    args = parser.parse_args()
    try:
        return execute(args)
    except (
        OSError,
        PolicyError,
        ValidationError,
        DefinitionAnalysisError,
        subprocess.SubprocessError,
    ) as exc:
        parser.exit(2, f"public-input tooling unavailable: {exc}\n")


if __name__ == "__main__":
    raise SystemExit(main())
