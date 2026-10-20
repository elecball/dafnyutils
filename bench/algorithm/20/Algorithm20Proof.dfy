include "Algorithm20Spec.dfy"
include "Algorithm20Core.dfy"

module Algorithm20Proof {
  import BenchIO
  import Schema = Algorithm20Schema
  import CliSpec = Algorithm20Spec
  import CliCore = Algorithm20Core

  twostate lemma CoreSummaryImpliesSpec(raw: Schema.Algorithm20CmdRaw, io: BenchIO.IO, exit: int)
    requires CliCore.CoreSummary(raw, io, exit)
    ensures CliSpec.Spec(raw, io, exit)
  {
    if CliSpec.Valid(raw) {
      var result :| CliCore.AnswerSummary(raw.time, result) &&
        CliSpec.Output(io, CliSpec.OutputText(result), exit);
      AnswerSummaryImpliesAnswer(raw.time, result);
    }
  }

  import SpecMod = Algorithm20Spec
  import Core = Algorithm20Core

  lemma CharToNatEquivalent(c: char)
    ensures Core.CharToNat(c) == SpecMod.CharToNat(c)
  {
  }

  lemma NatToCharEquivalent(n: int)
    ensures Core.NatToChar(n) == SpecMod.NatToChar(n)
  {
  }

  lemma TimeToMinutesEquivalent(time: string)
    requires |time| == 5
    ensures Core.TimeToMinutes(time) == SpecMod.TimeToMinutes(time)
  {
    CharToNatEquivalent(time[0]);
    CharToNatEquivalent(time[1]);
    CharToNatEquivalent(time[3]);
    CharToNatEquivalent(time[4]);
  }

  lemma TwoDigitStrEquivalent(n: int)
    ensures Core.TwoDigitStr(n) == SpecMod.TwoDigitStr(n)
  {
    NatToCharEquivalent(n / 10);
    NatToCharEquivalent(n % 10);
  }

  lemma MinutesToTimeEquivalent(m: int)
    ensures Core.MinutesToTime(m) == SpecMod.MinutesToTime(m)
  {
    TwoDigitStrEquivalent(m / 60);
    TwoDigitStrEquivalent(m % 60);
  }

  lemma IsPalindromeTimeEquivalent(t: string)
    ensures Core.IsPalindromeTime(t) == SpecMod.IsPalindromeTime(t)
  {
  }

  lemma PalindromeAfterEquivalent(time: string, result: int)
    requires |time| == 5
    ensures Core.PalindromeAfter(time, result) ==
            SpecMod.PalindromeAfter(time, result)
  {
    TimeToMinutesEquivalent(time);
    MinutesToTimeEquivalent((Core.TimeToMinutes(time) + result) % 1440);
    IsPalindromeTimeEquivalent(Core.MinutesToTime((Core.TimeToMinutes(time) + result) % 1440));
  }

  lemma MinimalityAt(time: string, result: int, k: int)
    requires Core.AnswerSummary(time, result)
    requires 0 <= k < result
    ensures !SpecMod.PalindromeAfter(time, k)
  {
    assert |time| == 5;
    PalindromeAfterEquivalent(time, k);
    assert !Core.PalindromeAfter(time, k);
    assert !SpecMod.PalindromeAfter(time, k);
  }

  lemma AnswerSummaryImpliesAnswer(time: string, result: int)
    ensures Core.AnswerSummary(time, result) ==> SpecMod.Answer(time, result)
  {
    if Core.AnswerSummary(time, result) {
      PalindromeAfterEquivalent(time, result);
      assert SpecMod.PalindromeAfter(time, result);

      forall k | 0 <= k < result
        ensures !SpecMod.PalindromeAfter(time, k)
      {
        MinimalityAt(time, result, k);
      }
      assert |time| == 5;
      assert 0 <= result;
      assert SpecMod.Answer(time, result);
    }
  }
}
