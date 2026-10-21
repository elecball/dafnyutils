include "Algorithm4Spec.dfy"
include "Algorithm4Core.dfy"

module Algorithm4Proof {
  import BenchIO
  import Schema = Algorithm4Schema
  import CliSpec = Algorithm4Spec
  import CliCore = Algorithm4Core

  twostate lemma CoreSummaryImpliesSpec(raw: Schema.Algorithm4CmdRaw, io: BenchIO.IO, exit: int)
    requires CliCore.CoreSummary(raw, io, exit)
    ensures CliSpec.Spec(raw, io, exit)
  {
    if CliSpec.Valid(raw) {
      var y :| CliCore.AnswerSummary(raw.x, raw.hh, raw.mm, y) &&
               CliSpec.Output(io, CliSpec.OutputText(y), exit);
      AnswerSummaryImpliesAnswer(raw.x, raw.hh, raw.mm, y);
    }
  }

  import SpecMod = Algorithm4Spec
  import Core = Algorithm4Core

  lemma ContainsDigit7Equivalent(v: int)
    ensures Core.ContainsDigit7(v) == SpecMod.ContainsDigit7(v)
    decreases if v < 10 then 0 else v
  {
    if v >= 10 {
      ContainsDigit7Equivalent(v / 10);
    }
  }

  lemma LuckyAtEquivalent(x: int, hh: int, mm: int, y: int)
    ensures Core.LuckyAt(x, hh, mm, y) ==
            SpecMod.IsLuckyTime(((hh * 60 + mm - x * y) % 1440 + 1440) % 1440 / 60,
                                ((hh * 60 + mm - x * y) % 1440 + 1440) % 1440 % 60)
  {
    var t := Core.TimeAt(x, hh, mm, y);
    assert t == ((hh * 60 + mm - x * y) % 1440 + 1440) % 1440;
    ContainsDigit7Equivalent(t / 60);
    ContainsDigit7Equivalent(t % 60);
    assert Core.IsLuckyTime(t / 60, t % 60) ==
           SpecMod.IsLuckyTime(t / 60, t % 60);
  }

  lemma AnswerSummaryImpliesAnswer(x: int, hh: int, mm: int, y: int)
    ensures Core.AnswerSummary(x, hh, mm, y) ==> SpecMod.Answer(x, hh, mm, y)
  {
    if Core.AnswerSummary(x, hh, mm, y) {
      LuckyAtEquivalent(x, hh, mm, y);
      assert SpecMod.IsLuckyTime(((hh * 60 + mm - x * y) % 1440 + 1440) % 1440 / 60,
                                 ((hh * 60 + mm - x * y) % 1440 + 1440) % 1440 % 60);

      forall z | 0 <= z < y
        ensures !SpecMod.IsLuckyTime(((hh * 60 + mm - x * z) % 1440 + 1440) % 1440 / 60,
                                     ((hh * 60 + mm - x * z) % 1440 + 1440) % 1440 % 60)
      {
        LuckyAtEquivalent(x, hh, mm, z);
        assert !Core.LuckyAt(x, hh, mm, z);
      }

      assert SpecMod.Answer(x, hh, mm, y);
    }
  }
}
