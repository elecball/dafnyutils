include "Algorithm38TextCore.dfy"
include "Algorithm38Schema.dfy"
include "../../core/IO.dfy"
include "Algorithm38Spec.dfy"

module Algorithm38Core {
  import BenchIO
  import BenchWorld
  import Schema = Algorithm38Schema
  import CliSpec = Algorithm38Spec
  import Text = Algorithm38TextCore

  twostate predicate CoreSummary(raw: Schema.Algorithm38CmdRaw, io: BenchIO.IO, exit: int)
    reads io.stdoutRegion, io.stderrRegion, io.trustedStreamsRegion
  {
    if CliSpec.Valid(raw) then
      io.stderr() == old(io.stderr()) &&
      exists result: string ::
        AnswerSummary(raw.n, raw.L, raw.kefa, raw.sasha, result) && CliSpec.Output(io, CliSpec.OutputText(result), exit)
    else
      io.stdout() == old(io.stdout()) && CliSpec.InvalidInput(io, exit)
  }

  method RunCore(raw: Schema.Algorithm38CmdRaw, io: BenchIO.IO) returns (exit: int)
    requires CliSpec.Valid(raw) ==> ValidInput(raw.n, raw.L, raw.kefa, raw.sasha)
    modifies io.stdoutRegion, io.stderrRegion
    ensures CoreSummary(raw, io, exit)
    decreases *
  {
    if !CliSpec.Valid(raw) {
      var written := io.WriteStderr(CliSpec.InvalidInputText());
      exit := if written.Err? then 1 else 2;
      return;
    }
    var result := Solve(raw.n, raw.L, raw.kefa, raw.sasha);
    var text := Text.OutputText(result);
    var written := io.WriteStdout(text);
    exit := if written.Err? then 1 else 0;
  }

  import Spec = Algorithm38Spec

  predicate IsSorted(s: seq<int>)
  {
    forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
  }

  predicate ValidInput(n: int, L: int, kefa: seq<int>, sasha: seq<int>)
  {
    n >= 1 && n <= 50 &&
    L >= n && L <= 100 &&
    |kefa| == n && |sasha| == n &&
    IsSorted(kefa) && IsSorted(sasha) &&
    (forall x :: x in kefa ==> 0 <= x < L) &&
    (forall x :: x in sasha ==> 0 <= x < L)
  }

  function DistSeq(p: seq<int>, L: int): seq<int>
  {
    if |p| == 0 then
      []
    else
      seq(|p|, i =>
        if 0 <= i && i + 1 < |p| then
          p[i + 1] - p[i]
        else
          L - p[|p| - 1] + p[0]
          )
  }

  predicate IsRotation(s1: seq<int>, s2: seq<int>, offset: int)
  {
    |s1| == |s2| &&
    0 <= offset < |s1| &&
    forall i :: 0 <= i < |s1| ==> s2[i] == s1[(i + offset) % |s1|]
  }

  predicate HasRotation(n: int, L: int, kefa: seq<int>, sasha: seq<int>)
  {
    exists offset ::
      0 <= offset < n &&
      IsRotation(DistSeq(kefa, L), DistSeq(sasha, L), offset)
  }

  predicate AnswerSummary(n: int, L: int, kefa: seq<int>, sasha: seq<int>, result: string)
  {
    ValidInput(n, L, kefa, sasha) &&
    (
      (HasRotation(n, L, kefa, sasha) && result == Spec.PositiveResult()) ||
      (!HasRotation(n, L, kefa, sasha) && result == Spec.NegativeResult())
    )
  }

  method Solve(n: int, L: int, kefa: seq<int>, sasha: seq<int>) returns (result: string)
    requires ValidInput(n, L, kefa, sasha)
    ensures AnswerSummary(n, L, kefa, sasha, result)
  {
    if HasRotation(n, L, kefa, sasha) {
      result := Spec.PositiveResult();
    } else {
      result := Spec.NegativeResult();
    }
  }
}
