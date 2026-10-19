"""Run-local task input materialization tests."""

from __future__ import annotations

import json
from pathlib import Path

import pytest

from benchmarks.generated_profile import generate_task_profile
from benchmarks.paths import REPO_ROOT
from benchmarks.profiles import ResolvedBenchmark
from benchmarks.repository import BenchmarkRepository
from benchmarks.task import TaskProfile
from tests.evaluation.evaluation_test_support import utility_config

pytestmark = pytest.mark.integration


def _utility_cfg(utility_name: str) -> ResolvedBenchmark:
    return utility_config(utility_name)


def _generated_profile(utility_name: str, repository_root: Path = REPO_ROOT):
    repository = BenchmarkRepository.open(repository_root)
    return generate_task_profile(
        repository.load_definition(utility_name),
        repository_root=repository_root,
        configuration=_utility_cfg(utility_name),
    )


# An external task JSON cannot omit a source required by its formal specification closure.
def test_task_profile_rejects_missing_formal_resource() -> None:
    profile = _generated_profile("algorithm-1").profile
    payload = profile.model_dump(mode="json")
    required_path = profile.dafny.spec_definitions[0].source_path
    payload["resources"] = [
        resource for resource in payload["resources"] if resource["path"] != required_path
    ]

    with pytest.raises(ValueError, match="every specification definition source"):
        TaskProfile.model_validate_json(json.dumps(payload))
