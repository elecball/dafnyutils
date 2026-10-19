from __future__ import annotations

import pytest

import dafny_cli as dafny_cli
from analysis.kinds import DefinitionKind
from analysis.models import (
    DEFINITION_INFO_LIST,
)

pytestmark = pytest.mark.integration


# Dafny reports twostate predicates as their own definition kind in JSON output.
def test_definition_info_accepts_twostate_predicate_kind() -> None:
    definitions = DEFINITION_INFO_LIST.validate_python(
        [
            {
                "name": "Stable",
                "fullName": "ToySpec.Stable",
                "kind": "twostate predicate",
                "enclosingName": "ToySpec",
                "line": 3,
                "column": 3,
                "start": 10,
                "bodyStart": 42,
                "end": 50,
                "ghost": True,
                "hasByMethod": False,
                "hasLoop": False,
                "worldRelated": False,
                "declarationKind": "twostate predicate",
                "recursive": False,
                "recursiveGroup": [],
                "callees": [],
                "references": [],
                "returns": [],
                "returnNames": [],
                "requires": [],
                "ensures": [],
                "modifies": [],
            }
        ]
    )

    assert definitions[0].kind == DefinitionKind.TWOSTATE_PREDICATE
