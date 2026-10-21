include "Algorithm1Spec.dfy"
include "Algorithm1Core.dfy"

module Algorithm1Proof {
  import BenchIO
  import Schema = Algorithm1Schema
  import CliSpec = Algorithm1Spec
  import CliCore = Algorithm1Core

  twostate lemma CoreSummaryImpliesSpec(raw: Schema.Algorithm1CmdRaw, io: BenchIO.IO, exit: int)
    requires CliCore.CoreSummary(raw, io, exit)
    ensures CliSpec.Spec(raw, io, exit)
  {
    if CliSpec.Valid(raw) {
      var result :| CliCore.AnswerSummary(raw.x, result) &&
                    CliSpec.Output(io, CliSpec.OutputText(result), exit);
      AnswerSummaryImpliesAnswer(raw.x, result);
    }
  }

  import SpecMod = Algorithm1Spec
  import Core = Algorithm1Core

  lemma SumOfDigitsEquivalent(n: int)
    ensures Core.SumOfDigits(n) == SpecMod.SumOfDigits(n)
    decreases if n <= 0 then 0 else n
  {
    if n > 0 {
      SumOfDigitsEquivalent(n / 10);
    }
  }

  lemma AnswerSummaryImpliesAnswer(x: int, result: int)
    ensures Core.AnswerSummary(x, result) ==> SpecMod.Answer(x, result)
  {
    if Core.AnswerSummary(x, result) {
      assert x >= 1;
      assert result == Core.Best(x);
      Core.BestIsOptimal(x);
      SumOfDigitsEquivalent(result);

      forall t | 1 <= t <= x
        ensures SpecMod.SumOfDigits(result) >= SpecMod.SumOfDigits(t)
      {
        SumOfDigitsEquivalent(t);
        assert Core.SumOfDigits(result) >= Core.SumOfDigits(t);
      }

      forall t | 1 <= t <= x && SpecMod.SumOfDigits(t) == SpecMod.SumOfDigits(result)
        ensures t <= result
      {
        SumOfDigitsEquivalent(t);
        assert Core.SumOfDigits(t) == Core.SumOfDigits(result);
        assert t <= result;
      }

      assert SpecMod.Answer(x, result);
    }
  }
}
