include "DateSpec.dfy"
include "DateCalendar.dfy"

module DateFormat {
  import S = DateSpec
  import M = DateModel
  import Calendar = DateCalendar

  lemma AppendAtom(atoms: seq<S.Atom>, text: string, cuts: seq<nat>, atom: S.Atom, piece: string)
    requires S.AtomPartition(atoms, text, cuts)
    requires S.AtomText(atom, piece)
    ensures S.AtomPartition(atoms + [atom], text + piece, cuts + [|text| + |piece|])
  {
    var next := cuts + [|text| + |piece|];
    forall i: int | 0 <= i < |atoms| + 1
      ensures next[i] <= next[i + 1] &&
              S.AtomText((atoms + [atom])[i], (text + piece)[next[i]..next[i + 1]])
    {
      if i < |atoms| {
        assert (text + piece)[next[i]..next[i + 1]] == text[cuts[i]..cuts[i + 1]];
      } else {
        assert i == |atoms|;
        assert (text + piece)[next[i]..next[i + 1]] == piece;
      }
    }
  }

  method Atoms(atoms: seq<S.Atom>) returns (text: string, ghost cuts: seq<nat>)
    ensures S.AtomPartition(atoms, text, cuts)
  {
    text := "";
    cuts := [0];
    var i := 0;
    while i < |atoms|
      invariant 0 <= i <= |atoms|
      invariant S.AtomPartition(atoms[..i], text, cuts)
      decreases |atoms| - i
    {
      var piece: string;
      match atoms[i] {
        case Numeric(value, width, pad) => piece := Calendar.Number(value, width, pad);
        case Text(value) => piece := value;
      }
      AppendAtom(atoms[..i], text, cuts, atoms[i], piece);
      assert atoms[..i] + [atoms[i]] == atoms[..i + 1];
      text := text + piece;
      cuts := cuts + [|text|];
      i := i + 1;
    }
  }

  ghost predicate Prefix(format: string, end: nat, seconds: int, nanos: int,
                         civil: M.Civil, iso: M.Civil, text: string, inputCuts: seq<nat>, outputCuts: seq<nat>)
  {
    end <= |format| && |inputCuts| == |outputCuts| && |inputCuts| > 0 &&
    inputCuts[0] == 0 && outputCuts[0] == 0 && inputCuts[|inputCuts| - 1] == end &&
    outputCuts[|outputCuts| - 1] == |text| &&
    (forall i: int | 0 <= i < |inputCuts| :: inputCuts[i] <= end && outputCuts[i] <= |text|) &&
    (forall i: int | 0 <= i < |inputCuts| - 1 ::
       inputCuts[i] < inputCuts[i + 1] && outputCuts[i] <= outputCuts[i + 1] &&
       S.Token(format, inputCuts[i], inputCuts[i + 1], seconds, nanos, civil, iso,
               text[outputCuts[i]..outputCuts[i + 1]]))
  }

  lemma AppendToken(format: string, end: nat, next: nat, seconds: int, nanos: int,
                    civil: M.Civil, iso: M.Civil, text: string, piece: string,
                    inputCuts: seq<nat>, outputCuts: seq<nat>)
    requires Prefix(format, end, seconds, nanos, civil, iso, text, inputCuts, outputCuts)
    requires S.Token(format, end, next, seconds, nanos, civil, iso, piece)
    ensures Prefix(format, next, seconds, nanos, civil, iso, text + piece,
                   inputCuts + [next], outputCuts + [|text| + |piece|])
  {
    var ins := inputCuts + [next];
    var outs := outputCuts + [|text| + |piece|];
    forall i: int | 0 <= i < |ins| - 1
      ensures ins[i] < ins[i + 1] && outs[i] <= outs[i + 1] &&
              S.Token(format, ins[i], ins[i + 1], seconds, nanos, civil, iso,
                      (text + piece)[outs[i]..outs[i + 1]])
    {
      if i < |inputCuts| - 1 {
        assert (text + piece)[outs[i]..outs[i + 1]] == text[outputCuts[i]..outputCuts[i + 1]];
      } else {
        assert i == |inputCuts| - 1;
        assert (text + piece)[outs[i]..outs[i + 1]] == piece;
      }
    }
  }

  method Render(format: string, seconds: int, nanos: int, civil: M.Civil, iso: M.Civil)
    returns (text: string)
    ensures S.Formatted(format, seconds, nanos, civil, iso, text)
  {
    text := "";
    var index: nat := 0;
    ghost var inputCuts: seq<nat> := [0];
    ghost var outputCuts: seq<nat> := [0];
    while index < |format|
      invariant Prefix(format, index, seconds, nanos, civil, iso, text, inputCuts, outputCuts)
      decreases |format| - index
    {
      var next: nat;
      var piece: string;
      if format[index] != '%' {
        next := index + 1;
        piece := [format[index]];
      } else if index + 1 == |format| {
        next := index + 1;
        piece := "%";
      } else if index + 2 < |format| && format[index + 1] == ':' && format[index + 2] == 'z' {
        next := index + 3;
        piece := "+00:00";
      } else if index + 3 < |format| && format[index + 1..index + 3] == "::" && format[index + 3] == 'z' {
        next := index + 4;
        piece := "+00:00:00";
      } else if index + 4 < |format| && format[index + 1..index + 4] == ":::" && format[index + 4] == 'z' {
        next := index + 5;
        piece := "+00";
      } else {
        next := index + 2;
        ghost var cuts: seq<nat>;
        piece, cuts := Atoms(S.Meaning(format[index + 1], seconds, nanos, civil, iso));
      }
      AppendToken(format, index, next, seconds, nanos, civil, iso, text, piece, inputCuts, outputCuts);
      text := text + piece;
      inputCuts := inputCuts + [next];
      outputCuts := outputCuts + [|text|];
      index := next;
    }
    assert S.FormatPartition(format, seconds, nanos, civil, iso, text, inputCuts, outputCuts);
  }
}
