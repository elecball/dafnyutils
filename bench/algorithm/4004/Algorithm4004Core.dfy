include "Algorithm4004TextCore.dfy"
include "Algorithm4004Spec.dfy"
include "Algorithm4004Schema.dfy"
include "../../core/IO.dfy"
module Algorithm4004Core {
  import BenchIO
  import BenchWorld
  import Schema = Algorithm4004Schema
  import CliSpec = Algorithm4004Spec
  import Text = Algorithm4004TextCore

  twostate predicate CoreSummary(raw: Schema.Algorithm4004CmdRaw, io: BenchIO.IO, exit: int)
    reads io.stdoutRegion, io.stderrRegion, io.trustedStreamsRegion
  {
    if CliSpec.Valid(raw) then
      io.stderr() == old(io.stderr()) &&
      exists out: int ::
        AnswerSummary(raw.n, raw.a, out) && CliSpec.Output(io, CliSpec.OutputText(out), exit)
    else
      io.stdout() == old(io.stdout()) && CliSpec.InvalidInput(io, exit)
  }

  method RunCore(raw: Schema.Algorithm4004CmdRaw, io: BenchIO.IO) returns (exit: int)
    modifies io.stdoutRegion, io.stderrRegion
    ensures CoreSummary(raw, io, exit)
    decreases *
  {
    if !CliSpec.Valid(raw) {
      var written := io.WriteStderr(CliSpec.InvalidInputText());
      exit := if written.Err? then 1 else 2;
      return;
    }
    var out := Solve(raw.n, raw.a);
    var text := Text.OutputText(out);
    var written := io.WriteStdout(text);
    exit := if written.Err? then 1 else 0;
  }

  ghost predicate IsMin(a: seq<int>, lo: int)
  {
    |a| > 0 &&
    (exists i :: 0 <= i < |a| && a[i] == lo) &&
    forall i :: 0 <= i < |a| ==> lo <= a[i]
  }

  ghost predicate IsMax(a: seq<int>, hi: int)
  {
    |a| > 0 &&
    (exists i :: 0 <= i < |a| && a[i] == hi) &&
    forall i :: 0 <= i < |a| ==> a[i] <= hi
  }

  ghost predicate AllInTwo(a: seq<int>, lo: int, hi: int)
  {
    forall i :: 0 <= i < |a| ==> a[i] == lo || a[i] == hi
  }

  ghost predicate AllInThree(a: seq<int>, lo: int, mid: int, hi: int)
  {
    forall i :: 0 <= i < |a| ==> a[i] == lo || a[i] == mid || a[i] == hi
  }

  method Solve(n: int, a: seq<int>) returns (out: int)
    ensures AnswerSummary(n, a, out)
  {
    if |a| <= 1 {
      out := 0;
      return;
    }

    var lo := a[0];
    var hi := a[0];
    var i := 1;
    while i < |a|
      invariant 1 <= i <= |a|
      invariant exists j :: 0 <= j < i && a[j] == lo
      invariant exists j :: 0 <= j < i && a[j] == hi
      invariant forall j :: 0 <= j < i ==> lo <= a[j]
      invariant forall j :: 0 <= j < i ==> a[j] <= hi
    {
      if a[i] < lo {
        lo := a[i];
      }
      if a[i] > hi {
        hi := a[i];
      }
      i := i + 1;
    }
    assert IsMin(a, lo);
    assert IsMax(a, hi);
    assert lo <= hi;

    var diff := hi - lo;
    var mid := lo + diff / 2;
    var allTwo := true;
    var allThree := diff % 2 == 0;

    i := 0;
    while i < |a|
      invariant 0 <= i <= |a|
      invariant allTwo ==> forall j :: 0 <= j < i ==> a[j] == lo || a[j] == hi
      invariant !allTwo ==> exists j :: 0 <= j < i && a[j] != lo && a[j] != hi
      invariant allThree ==> diff % 2 == 0 && forall j :: 0 <= j < i ==> a[j] == lo || a[j] == mid || a[j] == hi
      invariant !allThree ==> diff % 2 != 0 || exists j :: 0 <= j < i && a[j] != lo && a[j] != mid && a[j] != hi
    {
      if a[i] != lo && a[i] != hi {
        allTwo := false;
      }
      if a[i] != lo && a[i] != mid && a[i] != hi {
        allThree := false;
      }
      i := i + 1;
    }

    if allTwo {
      if diff % 2 == 0 {
        out := diff / 2;
      } else {
        out := diff;
      }
      assert AllInTwo(a, lo, hi);
    } else if allThree {
      out := diff / 2;
      assert diff % 2 == 0;
      assert AllInThree(a, lo, mid, hi);
    } else {
      out := -1;
      assert !AllInTwo(a, lo, hi);
      assert !(diff % 2 == 0 && AllInThree(a, lo, mid, hi));
    }
  }

  ghost predicate AnswerSummary(n: int, a: seq<int>, out: int)
  {
    if |a| <= 1 then
      out == 0
    else
      exists lo, hi ::
        IsMin(a, lo) &&
        IsMax(a, hi) &&
        lo <= hi &&
        var diff := hi - lo;
        var mid := lo + diff / 2;
        (
          (AllInTwo(a, lo, hi) &&
           ((diff % 2 == 0 && out == diff / 2) ||
            (diff % 2 != 0 && out == diff))) ||
          (!AllInTwo(a, lo, hi) &&
           diff % 2 == 0 &&
           AllInThree(a, lo, mid, hi) &&
           out == diff / 2) ||
          (!AllInTwo(a, lo, hi) &&
           !(diff % 2 == 0 && AllInThree(a, lo, mid, hi)) &&
           out == -1)
        )
  }
}
