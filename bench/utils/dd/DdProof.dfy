include "DdCore.dfy"

module DdProof {
  import BenchIO
  import BW = BenchWorld
  import S = DdSchema
  import Core = DdCore
  import Spec = DdSpec
  import C = IOContract

  lemma RenderSatisfiesTransformation(raw: S.DdCmdRaw, data: BW.Bytes)
    ensures Spec.Transformed(raw, data, Core.Render(raw, data))
  {
  }

  twostate lemma CoreSummaryImpliesSpec(raw: S.DdCmdRaw, io: BenchIO.IO, exit: int)
    requires Core.CoreSummary(raw, io, exit)
    ensures Spec.Spec(raw, io, exit)
  {
    if raw.mode == S.Copy && raw.error == S.None {
      var trace: Core.CopyWitness :| Core.WitnessSummary(raw, io, exit, trace);
      reveal Core.WitnessSummary();
      reveal Core.Completed();
      RenderSatisfiesTransformation(raw, trace.data);
    }
  }
}
