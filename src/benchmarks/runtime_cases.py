"""Evaluate fixed raw stdin cases through the benchmark executable interface."""

from __future__ import annotations

import re
from pathlib import Path

from pydantic import BaseModel, ConfigDict, StrictInt, StrictStr

from benchmarks.definition import OutputContract


class RuntimeCase(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    input: StrictStr
    output: StrictStr


class CaseParameter(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    name: StrictStr
    python_type: StrictStr


class RuntimeCases(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    problem_id: StrictStr
    parser: StrictStr
    input_count: StrictInt
    parameters: tuple[CaseParameter, ...]
    positive: tuple[RuntimeCase, ...]


def load_runtime_cases(path: Path) -> tuple[RuntimeCase, ...]:
    """Keep legacy parser metadata inert; candidate code receives raw stdin only."""
    cases = RuntimeCases.model_validate_json(path.read_text(encoding="utf-8")).positive
    if not cases:
        raise ValueError("mandatory runtime case set must not be empty")
    return cases


def assert_runtime_observation(
    case: RuntimeCase,
    actual: tuple[bytes, bytes, int],
    contract: OutputContract = OutputContract.TOKENS,
) -> None:
    stdout, stderr, exit_code = actual
    assert exit_code == 0, f"candidate exited {exit_code}"
    assert stderr == b"", "candidate wrote an unexpected diagnostic"
    output = stdout.decode("utf-8")
    if contract is OutputContract.INTEGER:
        actual_tokens = output.split()
        assert len(actual_tokens) == 1, "expected one integer"
        assert _decimal_integer(actual_tokens[0]) == _decimal_integer(case.output.strip()), (
            "incorrect integer result"
        )
    elif contract is OutputContract.COVERING_CELL:
        _assert_covering_cell(case, output)
    elif contract is OutputContract.MINIMAL_FRAME:
        _assert_minimal_frame(case, output)
    else:
        assert output.split() == case.output.split(), "candidate output differs from the case"


def _decimal_integer(token: str) -> int:
    assert re.fullmatch(r"[+-]?[0-9]+", token), "expected a decimal integer"
    return int(token)


def _assert_covering_cell(case: RuntimeCase, output: str) -> None:
    expected = case.output.split()
    actual = output.split()
    assert actual and expected and actual[0] == expected[0], "incorrect feasibility result"
    if actual[0] == "NO":
        assert len(actual) == 1, "negative result must contain only NO"
        return
    assert actual[0] == "YES" and len(actual) == 3, "expected YES and two coordinates"
    row, column = (_decimal_integer(value) for value in actual[1:])
    source = case.input.split()
    height, width = (int(value) for value in source[:2])
    grid = source[2:]
    assert 1 <= row <= height and 1 <= column <= width, "cell is outside the grid"
    assert all(
        grid[r][c] != "*" or r + 1 == row or c + 1 == column
        for r in range(height)
        for c in range(width)
    ), "cell leaves an uncovered wall"


def _frame_extent(lines: list[str]) -> tuple[int, int, int]:
    marked = [(r, c) for r, line in enumerate(lines) for c, ch in enumerate(line) if ch != "."]
    assert marked, "frame must contain the original white pixel"
    top = min(r for r, _ in marked)
    bottom = max(r for r, _ in marked)
    left = min(c for _, c in marked)
    right = max(c for _, c in marked)
    assert bottom - top == right - left, "frame is not square"
    return top, left, bottom - top + 1


def _assert_minimal_frame(case: RuntimeCase, output: str) -> None:
    expected = case.output.split()
    actual = output.split()
    if expected == ["-1"]:
        assert actual == expected, "expected an impossible frame"
        return
    source = case.input.split()
    height, width = (int(value) for value in source[:2])
    screen = source[2:]
    assert len(actual) == height and all(len(row) == width for row in actual), "wrong grid shape"
    top, left, side = _frame_extent(actual)
    assert side == _frame_extent(expected)[2], "frame is not minimal"
    for r in range(height):
        for c in range(width):
            on_frame = (
                top <= r < top + side
                and left <= c < left + side
                and (r in (top, top + side - 1) or c in (left, left + side - 1))
            )
            assert screen[r][c] != "w" or on_frame, "white pixel is outside the frame"
            wanted = "w" if screen[r][c] == "w" else "+" if on_frame else screen[r][c]
            assert actual[r][c] == wanted, "frame changes the wrong pixel"
