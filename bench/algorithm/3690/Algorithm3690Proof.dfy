include "Algorithm3690Spec.dfy"
include "Algorithm3690Core.dfy"

module Algorithm3690Proof {
  import BenchIO
  import Schema = Algorithm3690Schema
  import CliSpec = Algorithm3690Spec
  import CliCore = Algorithm3690Core

  twostate lemma CoreSummaryImpliesSpec(raw: Schema.Algorithm3690CmdRaw, io: BenchIO.IO, exit: int)
    requires CliCore.CoreSummary(raw, io, exit)
    ensures CliSpec.Spec(raw, io, exit)
  {
    if CliSpec.Valid(raw) {
      var result :| CliCore.AnswerSummary(raw.h, raw.m, raw.s, raw.t1, raw.t2, result) &&
                    CliSpec.Output(io, CliSpec.OutputText(result), exit);
      AnswerSummaryImpliesAnswer(raw.h, raw.m, raw.s, raw.t1, raw.t2, result);
    }
  }

  import SpecMod = Algorithm3690Spec
  import Core = Algorithm3690Core

  lemma ValidInputSpecToCore(h: int, m: int, s: int, t1: int, t2: int)
    requires SpecMod.ValidInput(h, m, s, t1, t2)
    ensures Core.ValidInput(h, m, s, t1, t2)
  {
  }

  lemma IsStrictlyBetweenCoreToSpec(p: real, start: real, end: real)
    ensures Core.IsStrictlyBetweenOnCircle(p, start, end) == SpecMod.IsStrictlyBetweenOnCircle(p, start, end)
  {
  }

  lemma ArcIsClearCoreToSpec(start: real, end: real, blockedPositions: set<real>)
    ensures Core.ArcIsClear(start, end, blockedPositions) == SpecMod.ArcIsClear(start, end, blockedPositions)
  {
    if start != end {
      forall p | p in blockedPositions
        ensures !Core.IsStrictlyBetweenOnCircle(p, start, end) ==>
                  !SpecMod.IsStrictlyBetweenOnCircle(p, start, end)
      {
        IsStrictlyBetweenCoreToSpec(p, start, end);
      }
      forall p | p in blockedPositions
        ensures !SpecMod.IsStrictlyBetweenOnCircle(p, start, end) ==>
                  !Core.IsStrictlyBetweenOnCircle(p, start, end)
      {
        IsStrictlyBetweenCoreToSpec(p, start, end);
      }
    }
  }

  lemma AnswerSummaryImpliesAnswer(h: int, m: int, s: int, t1: int, t2: int, result: string)
    ensures Core.AnswerSummary(h, m, s, t1, t2, result) ==>
              SpecMod.Answer(h, m, s, t1, t2, result)
  {
    if Core.AnswerSummary(h, m, s, t1, t2, result) {
      var hp := if h == 12 then 0.0 else h as real;
      var hourPos := hp + (m as real) / 60.0 + (s as real) / 3600.0;
      var mp := (m as real) / 5.0 + (s as real) / (5.0 * 60.0);
      var sp := (s as real) / 5.0;
      var t1p := if t1 == 12 then 0.0 else t1 as real;
      var t2p := if t2 == 12 then 0.0 else t2 as real;
      var handPositions := {hourPos, mp, sp};
      ArcIsClearCoreToSpec(t1p, t2p, handPositions);
      ArcIsClearCoreToSpec(t2p, t1p, handPositions);
      assert SpecMod.Answer(h, m, s, t1, t2, result);
    }
  }
}
