include "../Spec/CpSpec.dfy"
include "../Impl/CpCore.dfy"

module CpProof {
  import BenchIO
  import Schema = CpSchema
  import Core = CpCore
  import Spec = CpSpec

  twostate lemma CoreSummaryImpliesSpec(
    raw: Schema.CpCmdRaw, io: BenchIO.IO, exit: int)
    requires Core.CoreSummary(raw, io, exit)
    ensures Spec.Spec(raw, io, exit)
  {
  }
}
