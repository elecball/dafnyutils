"""Use the pinned native parser and resolver without importing evaluator code."""

import os
import subprocess
import sys
from collections.abc import Sequence
from pathlib import Path

from dafny_analysis.client import (
    DefinitionAnalysisError,
    definition_analysis_document_from_paths,
    definition_analysis_infos_from_paths,
    definition_analysis_infos_from_stdin,
)
from dafny_analysis.models import DafnyAnalysisResult, DefinitionInfo
from dafny_analysis.runner import DafnyInvocation


class Native:
    """Run native declaration tools at the release boundary."""

    def __init__(self, root: Path, executable: str | None = None) -> None:
        self.root = root
        self.executable = executable or os.environ.get("DAFNY_BENCHMARK", "dafny-benchmark")

    def run(self, invocation: DafnyInvocation) -> subprocess.CompletedProcess[str]:
        """Honor the native client's timeout and source transport."""
        try:
            return subprocess.run(
                [self.executable, *invocation.arguments],
                cwd=invocation.cwd,
                input=invocation.source_text,
                capture_output=True,
                text=True,
                timeout=invocation.timeout_seconds,
                check=False,
            )
        except subprocess.TimeoutExpired as exc:
            raise RuntimeError(
                f"native analysis timed out after {invocation.timeout_seconds} seconds"
            ) from exc

    def identity(self) -> tuple[str, str]:
        """Record version identities without reading installed toolchain trees."""
        result = subprocess.run(
            [self.executable, "--version"],
            cwd=self.root,
            capture_output=True,
            text=True,
            timeout=30,
            check=True,
        )
        package = subprocess.run(
            [sys.executable, "-m", "pip", "show", "dafny-analysis"],
            cwd=self.root,
            capture_output=True,
            text=True,
            timeout=30,
            check=True,
        )
        versions = [line for line in package.stdout.splitlines() if line.startswith("Version: ")]
        if len(versions) != 1:
            raise DefinitionAnalysisError(
                "cannot identify the installed dafny-analysis distribution"
            )
        return result.stdout.strip(), "dafny-analysis " + versions[0].removeprefix("Version: ")

    def parse(self, sources: Sequence[Path]) -> tuple[DefinitionInfo, ...]:
        """Obtain native include edges and exact source ranges without candidate resolution."""
        return tuple(
            definition_analysis_infos_from_paths(sources, runner=self.run, spans_only=True)
        )

    def resolve(self, sources: Sequence[Path]) -> DafnyAnalysisResult:
        """Resolve public declarations without any task implementation or proof input."""
        return definition_analysis_document_from_paths(
            sources,
            runner=self.run,
            include_semantic_facts=False,
            include_verification_facts=True,
        )

    def resolve_hole(self, text: str, source_dir: Path) -> tuple[DefinitionInfo, ...]:
        """Resolve a fixed scaffold with empty modules instead of candidate outputs."""
        return tuple(
            definition_analysis_infos_from_stdin(text, source_dir=source_dir, runner=self.run)
        )
