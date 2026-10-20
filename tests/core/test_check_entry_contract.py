from __future__ import annotations

from pathlib import Path

import pytest

from benchmarks.generated_profile import generate_task_profile
from benchmarks.profiles import coreutils_dafny_analysis_support_files
from benchmarks.repository import BenchmarkRepository
from entry_contract import (
    DafnyEntry,
    create_manifest,
)


# The generated chmod contract spans every source containing its reachable definitions.
@pytest.mark.integration
def test_chmod_entry_contract_records_split_specification_sources() -> None:
    root = Path(__file__).parents[2]
    manifest = create_manifest(
        root,
        root / "bench" / "utils" / "chmod",
        DafnyEntry(
            "bench/utils/chmod/Chmod.dfy",
            "Chmod.ChmodBenchmarkItem.RunCore",
        ),
        (
            root / "bench/utils/chmod/ChmodCli.dfy",
            *(root / path for path in coreutils_dafny_analysis_support_files("chmod")),
        ),
    )

    assert tuple(entry.symbol for entry in manifest.spec_entries) == (
        "ChmodDescriptorPrincipalSpec.Spec",
    )
    definition = BenchmarkRepository.open(root).load_definition("chmod")
    generated = generate_task_profile(definition, repository_root=root).profile
    assert tuple(
        (definition.source_path, definition.symbol, definition.kind)
        for definition in manifest.spec_definitions
    ) == tuple(
        (definition.source_path, definition.symbol, definition.kind)
        for definition in generated.dafny.spec_definitions
    )
    assert {key.split("::", 1)[0] for key in manifest.spec_definition_sha256} == {
        "bench/core/BenchmarkItem.dfy",
        "bench/core/CliExtern.dfy",
        "bench/core/CliModel.dfy",
        "bench/core/CliTypes.dfy",
        "bench/core/Errno.dfy",
        "bench/core/IO.dfy",
        "bench/core/IOContract.dfy",
        "bench/core/Result.dfy",
        "bench/core/SecurityModel.dfy",
        "bench/core/Utf8.dfy",
        "bench/core/World.dfy",
        "bench/core/WorldLookupProof.dfy",
        "bench/utils/chmod/ChmodDescriptorPrincipalSpec.dfy",
        "bench/utils/chmod/ChmodDescriptorSpec.dfy",
        "bench/utils/chmod/ChmodOperandSpec.dfy",
        "bench/utils/chmod/ChmodQuoteSpec.dfy",
        "bench/utils/chmod/ChmodRecursiveSpec.dfy",
        "bench/utils/chmod/ChmodSchema.dfy",
        "bench/utils/chmod/ChmodSpec.dfy",
    }
