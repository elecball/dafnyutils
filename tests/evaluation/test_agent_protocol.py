"""Benchmark agent wire, delivery, report, and candidate isolation contracts."""

from __future__ import annotations

import pytest

from evaluation.agent.protocol import (
    agent_command,
)
from evaluation.agent.report import normal_termination_detail


# A blank launcher prompt cannot form a valid agent command.
def test_agent_command_rejects_blank_prompt() -> None:
    with pytest.raises(ValueError, match="nonempty"):
        agent_command("   ")


# Normal termination errors preserve the run report's established messages.
def test_normal_termination_detail() -> None:
    assert (
        normal_termination_detail(
            execution_present=False, exit_code=None, timed_out=False, protocol_error=None
        )
        == "agent command was not run"
    )
