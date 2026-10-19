from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path

from analysis.models import DefinitionAnalysisImport
from standard_library import (
    dafny_standard_library_import_errors,
)


def _import(
    target: str,
    *,
    has_alias: bool = True,
    opened: bool = False,
) -> DefinitionAnalysisImport:
    return DefinitionAnalysisImport(
        moduleName="Runner",
        alias="Library",
        hasAlias=has_alias,
        resolvedTarget=target,
        resolvedTargetSourcePath="/dafny/Source/DafnyStandardLibraries/src/Std/Module.dfy",
        opened=opened,
        sourcePath="/workspace/Runner.dfy",
        start=10,
        end=40,
    )


# Packaged standard-library modules remain unavailable even through a closed alias.
def test_standard_library_policy_rejects_previously_selected_module() -> None:
    assert dafny_standard_library_import_errors((_import("Std.Collections.Seq"),)) == (
        "Dafny standard-library import is not allowed: Std.Collections.Seq",
    )


# An axiom-dependent module must remain unavailable even through a safe import shape.
def test_standard_library_policy_rejects_frames_module() -> None:
    errors = dafny_standard_library_import_errors((_import("Std.Frames"),))

    assert errors == ("Dafny standard-library import is not allowed: Std.Frames",)


# Import shape cannot re-enable a disabled packaged standard-library module.
def test_standard_library_policy_rejects_implicit_alias() -> None:
    errors = dafny_standard_library_import_errors(
        (_import("Std.Collections.Seq", has_alias=False),)
    )

    assert errors == ("Dafny standard-library import is not allowed: Std.Collections.Seq",)


# Opened imports are covered by the same total packaged-library rejection.
def test_standard_library_policy_rejects_opened_import() -> None:
    errors = dafny_standard_library_import_errors((_import("Std.Collections.Seq", opened=True),))

    assert errors == ("Dafny standard-library import is not allowed: Std.Collections.Seq",)


# Internal top-down facts use Path sources and must still reject the import.
def test_standard_library_policy_formats_path_source() -> None:
    @dataclass(frozen=True)
    class InternalImport:
        resolved_target: str
        has_alias: bool
        opened: bool
        source_path: Path

    errors = dafny_standard_library_import_errors(
        (
            InternalImport(
                resolved_target="Std.Collections.Seq",
                has_alias=False,
                opened=False,
                source_path=Path("bench/utils/toy/ToyCore.dfy"),
            ),
        )
    )

    assert errors == ("Dafny standard-library import is not allowed: Std.Collections.Seq",)


# A selected string path must match an internal Path source before policy validation.
def test_standard_library_policy_filters_path_source_by_selected_string() -> None:
    @dataclass(frozen=True)
    class InternalImport:
        resolved_target: str
        has_alias: bool
        opened: bool
        source_path: Path

    errors = dafny_standard_library_import_errors(
        (
            InternalImport(
                resolved_target="Std.Frames",
                has_alias=True,
                opened=False,
                source_path=Path("bench/utils/toy/ToyCore.dfy"),
            ),
        ),
        selected_source_paths=("bench/utils/toy/ToyCore.dfy",),
    )

    assert errors == ("Dafny standard-library import is not allowed: Std.Frames",)
