"""Native declaration coverage and public-source dependency preservation."""

from pathlib import Path

import pytest

from analysis.client import definition_analysis_document_from_paths
from analysis.kinds import DefinitionKind
from analysis.queries import definition_semantic_fingerprint, spec_dependency_closure
from evaluation.task.specification_source import filtered_specification_source

pytestmark = pytest.mark.integration


# Every parser-authored type and member family is visible through the native analysis contract.
@pytest.mark.parametrize(
    ("declaration", "symbol", "kind"),
    (
        ("type Item<T> = seq<T>", "Item", DefinitionKind.TYPE_SYNONYM),
        ("type Item = x: int | x >= 0 witness 0", "Item", DefinitionKind.SUBSET_TYPE),
        ("newtype Item = x: int | x >= 0 witness 0", "Item", DefinitionKind.NEWTYPE),
        ("type Item", "Item", DefinitionKind.ABSTRACT_TYPE),
        ("datatype Item = Empty | Full(value: int)", "Item", DefinitionKind.DATATYPE),
        ("codatatype Item = More(value: int, rest: Item)", "Item", DefinitionKind.DATATYPE),
        ("class Item {}", "Item", DefinitionKind.CLASS),
        ("trait Item {}", "Item", DefinitionKind.TRAIT),
        ("iterator Item() yields (x: int) { x := 0; yield; }", "Item", DefinitionKind.ITERATOR),
        ("class Item { var value: int }", "Item.value", DefinitionKind.FIELD),
        ("class Item { const value: int := 2 }", "Item.value", DefinitionKind.CONSTANT),
        ("class Item { constructor() {} }", "Item._ctor", DefinitionKind.CONSTRUCTOR),
        ("const Item: int := 2", "Item", DefinitionKind.CONSTANT),
        ("function Item(): int { 0 }", "Item", DefinitionKind.FUNCTION),
        ("ghost function Item(): int { 0 }", "Item", DefinitionKind.FUNCTION),
        (
            "function Item(): int { 0 } by method { return 0; }",
            "Item#by-method",
            DefinitionKind.FUNCTION_BY_METHOD,
        ),
        ("predicate Item() { true }", "Item", DefinitionKind.PREDICATE),
        ("twostate function Item(): int { 0 }", "Item", DefinitionKind.TWOSTATE_FUNCTION),
        ("twostate predicate Item() { true }", "Item", DefinitionKind.TWOSTATE_PREDICATE),
        ("least predicate Item(n: nat) { n == 0 }", "Item", DefinitionKind.LEAST_PREDICATE),
        ("greatest predicate Item(n: nat) { n == 0 }", "Item", DefinitionKind.GREATEST_PREDICATE),
        ("method Item() {}", "Item", DefinitionKind.METHOD),
        ("ghost method Item() {}", "Item", DefinitionKind.METHOD),
        ("lemma Item() {}", "Item", DefinitionKind.METHOD),
        ("twostate lemma Item() {}", "Item", DefinitionKind.METHOD),
        ("least lemma Item() {}", "Item", DefinitionKind.METHOD),
        ("greatest lemma Item() {}", "Item", DefinitionKind.METHOD),
        ("export Public reveals Item\ntype Item = int", "Public", DefinitionKind.EXPORT),
    ),
)
def test_authored_declaration_is_reported(
    tmp_path: Path, declaration: str, symbol: str, kind: DefinitionKind
) -> None:
    source = tmp_path / "Declarations.dfy"
    source.write_text(f"module Coverage {{\n{declaration}\n}}\n", encoding="utf-8")
    document = definition_analysis_document_from_paths((source,))
    matches = [info for info in document.definitions if info.full_name == f"Coverage.{symbol}"]
    assert len(matches) == 1
    info = matches[0]
    assert info.kind is kind
    assert 0 <= info.start < info.end <= len(source.read_bytes())
    assert info.source_path == str(source)
    assert definition_semantic_fingerprint(document.source_facts, info).declaration_sha256


def _round_trip(source: Path, symbol: str):
    document = definition_analysis_document_from_paths((source,))
    closure = spec_dependency_closure(
        document.definitions, source_paths=(source,), spec_entries=((source, symbol),)
    )
    retained = {info.full_name for info in closure}
    filtered = source.with_name("Filtered.dfy")
    filtered.write_text(filtered_specification_source(source, document, retained), encoding="utf-8")
    restored = definition_analysis_document_from_paths((filtered,))
    restored_closure = spec_dependency_closure(
        restored.definitions, source_paths=(filtered,), spec_entries=((filtered, symbol),)
    )
    assert {(info.full_name, info.kind) for info in restored_closure} == {
        (info.full_name, info.kind) for info in closure
    }
    original_hashes = {
        info.full_name: definition_semantic_fingerprint(
            document.source_facts, info
        ).declaration_sha256
        for info in closure
    }
    restored_hashes = {
        info.full_name: definition_semantic_fingerprint(
            restored.source_facts, info
        ).declaration_sha256
        for info in restored_closure
    }
    assert original_hashes == restored_hashes
    return retained, {info.full_name for info in restored.definitions}


# Alias chains retain generic arguments and constraints plus witness dependencies after extraction.
def test_alias_constraint_witness_dependency_round_trip(tmp_path: Path) -> None:
    source = tmp_path / "Types.dfy"
    source.write_text(
        """module Types {
  function Floor(): int { 0 }
  type Scalar = int
  type Positive = x: Scalar | x >= Floor() witness Floor()
  type Items<T> = seq<T>
  type Accepted = Items<Positive>
  predicate Spec(values: Accepted) { |values| >= 0 }
  function Unused(): int { 91 }
}
""",
        encoding="utf-8",
    )
    retained, published = _round_trip(source, "Types.Spec")
    assert retained == {
        "Types.Spec",
        "Types.Accepted",
        "Types.Items",
        "Types.Positive",
        "Types.Scalar",
        "Types.Floor",
    }
    assert published == retained


# Class methods keep their receiver container and fields without publishing unrelated methods.
def test_class_member_dependency_round_trip(tmp_path: Path) -> None:
    source = tmp_path / "Classes.dfy"
    source.write_text(
        """module Classes {
  class Box {
    var value: int
    const Limit: int := 10
    predicate Valid() reads this { value <= Limit }
    method Unused() modifies this { value := 91; }
  }
  predicate Spec(box: Box) reads box { box.Valid() }
}
""",
        encoding="utf-8",
    )
    retained, published = _round_trip(source, "Classes.Spec")
    assert retained == {
        "Classes.Box",
        "Classes.Box.value",
        "Classes.Box.Limit",
        "Classes.Box.Valid",
        "Classes.Spec",
    }
    assert "Classes.Box.Unused" not in published


# A field declared after a comma retains its entire authored declaration group.
def test_grouped_field_dependency_round_trip(tmp_path: Path) -> None:
    source = tmp_path / "Fields.dfy"
    source.write_text(
        """module Fields {
  class Box {
    ghost var first: int, second: int
  }
  ghost predicate Spec(box: Box) reads box { box.second == 0 }
}
""",
        encoding="utf-8",
    )
    retained, published = _round_trip(source, "Fields.Spec")
    assert retained == {"Fields.Box", "Fields.Box.first", "Fields.Box.second", "Fields.Spec"}
    assert published == retained


# Explicit export-set imports retain their API declaration and referenced exported symbols.
def test_export_set_dependency_round_trip(tmp_path: Path) -> None:
    source = tmp_path / "Exports.dfy"
    source.write_text(
        """module Library {
  export Public reveals Item
  type Item = int
  function Unused(): int { 91 }
}
module Client {
  import L = Library`Public
  predicate Spec(item: L.Item) { item >= 0 }
}
""",
        encoding="utf-8",
    )
    retained, published = _round_trip(source, "Client.Spec")
    assert retained == {"Client.Spec", "Library.Public", "Library.Item"}
    assert published == retained


# Nested abstract module headers and default-module declarations survive source extraction.
def test_nested_module_dependency_round_trip(tmp_path: Path) -> None:
    source = tmp_path / "Nested.dfy"
    source.write_text(
        """module RootTypes { type Root = int }
abstract module Outer {
  module Inner {
    import R = RootTypes
    type Value = R.Root
    predicate Spec(value: Value) { value >= 0 }
  }
}
""",
        encoding="utf-8",
    )
    retained, published = _round_trip(source, "Outer.Inner.Spec")
    assert retained == {"RootTypes.Root", "Outer.Inner.Value", "Outer.Inner.Spec"}
    assert published == retained


# Prefix-named modules retain their original headers and qualified declaration names.
def test_prefix_module_dependency_round_trip(tmp_path: Path) -> None:
    source = tmp_path / "Prefix.dfy"
    source.write_text(
        """module Outer.Inner {
  type Value = int
  ghost predicate Spec(value: Value) { value >= 0 }
}
""",
        encoding="utf-8",
    )
    retained, published = _round_trip(source, "Outer.Inner.Spec")
    assert retained == {"Outer.Inner.Value", "Outer.Inner.Spec"}
    assert published == retained


# Type names appearing only in a quantified body are still specification dependencies.
def test_body_type_dependency_round_trip(tmp_path: Path) -> None:
    source = tmp_path / "Quantified.dfy"
    source.write_text(
        """module Quantified {
  type Value = int
  ghost predicate Spec() { forall value: Value :: value == value }
}
""",
        encoding="utf-8",
    )
    retained, published = _round_trip(source, "Quantified.Spec")
    assert retained == {"Quantified.Spec", "Quantified.Value"}
    assert published == retained


# Default-module imports and declarations stay at file scope after extraction.
def test_default_module_dependency_round_trip(tmp_path: Path) -> None:
    source = tmp_path / "Default.dfy"
    source.write_text(
        """module Library { type Value = int }
import L = Library
type Item = L.Value
ghost predicate Spec() { forall value: Item :: value == value }
""",
        encoding="utf-8",
    )
    retained, published = _round_trip(source, "Spec")
    assert retained == {"Library.Value", "Item", "Spec"}
    assert published == retained


# UTF-8 string constants at declaration boundaries keep their full tokens after extraction.
def test_unicode_declaration_dependency_round_trip(tmp_path: Path) -> None:
    source = tmp_path / "Unicode.dfy"
    source.write_text(
        """module Unicode {
  const Message: string := "café"
  ghost predicate Spec() { Message == "café" }
}
""",
        encoding="utf-8",
    )
    retained, published = _round_trip(source, "Unicode.Spec")
    assert retained == {
        "Unicode.Message",
        "Unicode.Spec",
    }
    assert published == retained


# A receiver's inherited field keeps its defining trait and the class's extends clause.
def test_inherited_member_dependency_round_trip(tmp_path: Path) -> None:
    source = tmp_path / "Inheritance.dfy"
    source.write_text(
        """module Inheritance {
  trait Basis extends object { var value: int }
  class Box extends Basis {}
  ghost predicate Spec(box: Box) reads box { box.value >= 0 }
}
""",
        encoding="utf-8",
    )
    retained, published = _round_trip(source, "Inheritance.Spec")
    assert retained == {
        "Inheritance.Basis",
        "Inheritance.Basis.value",
        "Inheritance.Box",
        "Inheritance.Spec",
    }
    assert published == retained


# Datatype extension methods keep constructor syntax but exclude unused implementation members.
def test_datatype_member_dependency_round_trip(tmp_path: Path) -> None:
    source = tmp_path / "Records.dfy"
    source.write_text(
        """module Records {
  datatype Item = Item(value: int) {
    function Read(): int { value }
    method Unused() {}
  }
  ghost predicate Spec(item: Item) { item.Read() >= 0 }
}
""",
        encoding="utf-8",
    )
    retained, published = _round_trip(source, "Records.Spec")
    assert retained == {"Records.Item", "Records.Item.Read", "Records.Spec"}
    assert published == retained


# A nullary constructor used only in the body retains the owning datatype declaration.
def test_constructor_body_dependency_round_trip(tmp_path: Path) -> None:
    source = tmp_path / "Constructors.dfy"
    source.write_text(
        """module Constructors {
  datatype Value = Empty | Full(value: int)
  ghost predicate Spec() { Empty != Full(0) }
}
""",
        encoding="utf-8",
    )
    retained, published = _round_trip(source, "Constructors.Spec")
    assert retained == {"Constructors.Value", "Constructors.Spec"}
    assert published == retained


# Newtype base aliases and predicate constraints survive member-aware source extraction.
def test_newtype_dependency_round_trip(tmp_path: Path) -> None:
    source = tmp_path / "Newtypes.dfy"
    source.write_text(
        """module Newtypes {
  type Scalar = int
  function Floor(): Scalar { 0 }
  newtype Value = x: Scalar | x >= Floor() witness Floor()
  ghost predicate Spec(value: Value) { value >= 0 }
}
""",
        encoding="utf-8",
    )
    retained, published = _round_trip(source, "Newtypes.Spec")
    assert retained == {"Newtypes.Scalar", "Newtypes.Floor", "Newtypes.Value", "Newtypes.Spec"}
    assert published == retained


# An abstract import preserves its facade syntax and the selected export-set dependency.
def test_abstract_import_dependency_round_trip(tmp_path: Path) -> None:
    source = tmp_path / "Facades.dfy"
    source.write_text(
        """module Library {
  export Public reveals Value
  type Value = int
}
abstract module Client {
  import L : Library`Public
  ghost predicate Spec(value: L.Value) { value >= 0 }
}
""",
        encoding="utf-8",
    )
    retained, published = _round_trip(source, "Client.Spec")
    assert retained == {"Client.Spec", "Library.Public", "Library.Value"}
    assert published == retained


# Two abstract facade imports share one authored callable and preserve its resolved call identity.
def test_facade_callable_source_identity(tmp_path: Path) -> None:
    source = tmp_path / "CallableFacades.dfy"
    source.write_text(
        """module Library {
  export Public reveals Accepted
  ghost predicate Accepted(value: int) { value >= 0 }
}
abstract module Client {
  import First : Library`Public
  import Second : Library`Public
  ghost predicate Spec(value: int) { First.Accepted(value) && Second.Accepted(value) }
}
""",
        encoding="utf-8",
    )
    retained, published = _round_trip(source, "Client.Spec")
    assert retained == {"Client.Spec", "Library.Public", "Library.Accepted"}
    assert published == retained


# Refinement-inherited types and calls resolve to one authored base declaration.
def test_refinement_dependency_round_trip(tmp_path: Path) -> None:
    source = tmp_path / "Refinement.dfy"
    source.write_text(
        """abstract module Library {
  type Item = int
  ghost predicate Accepted(value: Item) { value >= 0 }
}
module Refined refines Library {
  ghost predicate Spec(value: Item) { Accepted(value) }
}
""",
        encoding="utf-8",
    )
    retained, published = _round_trip(source, "Refined.Spec")
    assert retained == {"Library.Item", "Library.Accepted", "Refined.Spec"}
    assert published == retained


# Static class constants retain their enclosing class without publishing unused constants.
def test_static_class_constant_dependency_round_trip(tmp_path: Path) -> None:
    source = tmp_path / "Constants.dfy"
    source.write_text(
        """module Constants {
  class Holder {
    static const First: int := 1
    static const Second: int := 2
  }
  ghost predicate Spec() { Holder.Second > 0 }
}
""",
        encoding="utf-8",
    )
    retained, published = _round_trip(source, "Constants.Spec")
    assert retained == {"Constants.Holder", "Constants.Holder.Second", "Constants.Spec"}
    assert published == retained


# Iterator formals and yield contracts are reported separately from ordinary contracts.
def test_iterator_contract_details(tmp_path: Path) -> None:
    source = tmp_path / "Iterator.dfy"
    source.write_text(
        """module Iterators {
  iterator Values(start: int) yields (value: int)
    requires start >= 0
    yield ensures value >= start
    decreases 1
  { value := start; yield; }
}
""",
        encoding="utf-8",
    )
    document = definition_analysis_document_from_paths((source,))
    assert len(document.definitions) == 1
    iterator = document.definitions[0]
    assert iterator.kind is DefinitionKind.ITERATOR
    assert iterator.parameter_names == ("start",)
    assert iterator.return_names == ("value",)
    assert iterator.requires == ("start >= 0",)
    assert iterator.yield_ensures == ("value >= start",)
    assert iterator.decreases == ("1",)
    assert iterator.body_start is not None
