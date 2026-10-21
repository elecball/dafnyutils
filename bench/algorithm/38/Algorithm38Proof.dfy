include "Algorithm38Spec.dfy"
include "Algorithm38Core.dfy"

module Algorithm38Proof {
  import BenchIO
  import Schema = Algorithm38Schema
  import CliSpec = Algorithm38Spec
  import CliCore = Algorithm38Core

  twostate lemma CoreSummaryImpliesSpec(raw: Schema.Algorithm38CmdRaw, io: BenchIO.IO, exit: int)
    requires CliCore.CoreSummary(raw, io, exit)
    ensures CliSpec.Spec(raw, io, exit)
  {
    if CliSpec.Valid(raw) {
      var result :| CliCore.AnswerSummary(raw.n, raw.L, raw.kefa, raw.sasha, result) &&
                    CliSpec.Output(io, CliSpec.OutputText(result), exit);
      AnswerSummaryImpliesAnswer(raw.n, raw.L, raw.kefa, raw.sasha, result);
    }
  }

  import SpecMod = Algorithm38Spec
  import Core = Algorithm38Core

  lemma ValidInputSpecToCore(n: int, L: int, kefa: seq<int>, sasha: seq<int>)
    requires SpecMod.ValidInput(n, L, kefa, sasha)
    ensures Core.ValidInput(n, L, kefa, sasha)
  {
  }

  lemma DistSeqMatches(p: seq<int>, L: int)
    ensures Core.DistSeq(p, L) == SpecMod.DistSeq(p, L)
  {
  }

  lemma RotationMatches(s1: seq<int>, s2: seq<int>, offset: int)
    ensures Core.IsRotation(s1, s2, offset) <==> SpecMod.IsRotation(s1, s2, offset)
  {
  }

  lemma CoreHasRotationImpliesSpecHasRotation(n: int, L: int, kefa: seq<int>, sasha: seq<int>)
    ensures Core.HasRotation(n, L, kefa, sasha) ==>
              (exists offset ::
                 0 <= offset < n &&
                 SpecMod.IsRotation(SpecMod.DistSeq(kefa, L), SpecMod.DistSeq(sasha, L), offset))
  {
    DistSeqMatches(kefa, L);
    DistSeqMatches(sasha, L);
    if Core.HasRotation(n, L, kefa, sasha) {
      var offset :| 0 <= offset < n &&
                    Core.IsRotation(Core.DistSeq(kefa, L), Core.DistSeq(sasha, L), offset);
      RotationMatches(SpecMod.DistSeq(kefa, L), SpecMod.DistSeq(sasha, L), offset);
      assert SpecMod.IsRotation(SpecMod.DistSeq(kefa, L), SpecMod.DistSeq(sasha, L), offset);
    }
  }

  lemma SpecHasRotationImpliesCoreHasRotation(n: int, L: int, kefa: seq<int>, sasha: seq<int>)
    ensures (exists offset ::
               0 <= offset < n &&
               SpecMod.IsRotation(SpecMod.DistSeq(kefa, L), SpecMod.DistSeq(sasha, L), offset)) ==>
              Core.HasRotation(n, L, kefa, sasha)
  {
    DistSeqMatches(kefa, L);
    DistSeqMatches(sasha, L);
    if exists offset ::
        0 <= offset < n &&
        SpecMod.IsRotation(SpecMod.DistSeq(kefa, L), SpecMod.DistSeq(sasha, L), offset) {
      var offset :| 0 <= offset < n &&
                    SpecMod.IsRotation(SpecMod.DistSeq(kefa, L), SpecMod.DistSeq(sasha, L), offset);
      RotationMatches(Core.DistSeq(kefa, L), Core.DistSeq(sasha, L), offset);
      assert Core.IsRotation(Core.DistSeq(kefa, L), Core.DistSeq(sasha, L), offset);
    }
  }

  lemma AnswerSummaryImpliesAnswer(n: int, L: int, kefa: seq<int>, sasha: seq<int>, result: string)
    ensures Core.AnswerSummary(n, L, kefa, sasha, result) ==>
              SpecMod.Answer(n, L, kefa, sasha, result)
  {
    if Core.AnswerSummary(n, L, kefa, sasha, result) {
      assert SpecMod.IsSorted(kefa);
      assert SpecMod.IsSorted(sasha);
      CoreHasRotationImpliesSpecHasRotation(n, L, kefa, sasha);
      SpecHasRotationImpliesCoreHasRotation(n, L, kefa, sasha);
      assert SpecMod.Answer(n, L, kefa, sasha, result);
    }
  }
}
