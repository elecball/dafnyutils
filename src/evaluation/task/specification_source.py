"""Extract public specification declarations while preserving their source structure."""

from __future__ import annotations

from pathlib import Path

from analysis.kinds import DefinitionKind
from analysis.models import DefinitionAnalysisDocument

PLACEHOLDER_FILE_CONTENT = "// Agent-editable scaffold populated inside the sandbox workspace.\n"


def _module_spans(source: Path, analysis: DefinitionAnalysisDocument) -> list[tuple[int, int]]:
    resolved = source.resolve()
    return [
        span
        for module in analysis.source_facts.modules
        if Path(module.source_path).resolve() == resolved
        for span in ((module.start, module.body_start + 1), (module.body_end, module.end))
    ]


def _source_slices(source: Path, spans: list[tuple[int, int]]) -> str:
    payload = source.read_bytes()
    merged: list[tuple[int, int]] = []
    for start, end in sorted(spans):
        if not 0 <= start <= end <= len(payload):
            raise ValueError(f"invalid declaration source span in {source}: {start}:{end}")
        if start == end:
            continue
        if merged and start <= merged[-1][1]:
            merged[-1] = (merged[-1][0], max(merged[-1][1], end))
        else:
            merged.append((start, end))
    return "\n".join(payload[start:end].decode("utf-8") for start, end in merged) + "\n"


def module_placeholder(source: Path, analysis: DefinitionAnalysisDocument) -> str:
    spans = _module_spans(source, analysis)
    return _source_slices(source, spans) if spans else PLACEHOLDER_FILE_CONTENT


def filtered_specification_source(
    source: Path,
    analysis: DefinitionAnalysisDocument,
    retained_symbols: set[str],
) -> str:
    resolved = source.resolve()
    spans = _module_spans(source, analysis)
    spans.extend(
        (item.start, item.end)
        for item in (*analysis.source_facts.includes, *analysis.source_facts.imports)
        if Path(item.source_path).resolve() == resolved
    )
    for info in analysis.definitions:
        if (
            Path(info.source_path).resolve() != resolved
            or info.full_name not in retained_symbols
            or info.kind is DefinitionKind.FUNCTION_BY_METHOD
        ):
            continue
        start = info.source_group.start if info.source_group else info.start
        end = info.source_group.end if info.source_group else info.end
        cursor = start
        for child in sorted(info.children, key=lambda span: (span.start, span.end)):
            if not start <= child.start <= child.end <= end:
                raise ValueError(f"invalid member source span in {info.full_name}")
            if cursor < child.start:
                spans.append((cursor, child.start))
            cursor = max(cursor, child.end)
        if cursor < end:
            spans.append((cursor, end))
    return _source_slices(source, spans) if spans else module_placeholder(source, analysis)
