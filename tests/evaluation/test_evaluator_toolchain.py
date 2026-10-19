from __future__ import annotations

import inspect

from evaluation.submission.container_mounts import (
    DEFAULT_EVALUATOR_IMAGE,
    write_evaluator_compose_override,
)


# Generic evaluator callers retain the documented mutable default until they pass an image.
def test_evaluator_override_retains_default_evaluator_image() -> None:
    parameter = inspect.signature(write_evaluator_compose_override).parameters["evaluator_image"]
    assert parameter.default == DEFAULT_EVALUATOR_IMAGE
