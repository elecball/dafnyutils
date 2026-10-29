include "SumSpec.dfy"
include "SumCore.dfy"

module SumProof {
  import BenchIO
  import Schema = SumSchema
  import Core = SumCore
  import Spec = SumSpec

  twostate lemma CoreSummaryImpliesSpec(
    raw: Schema.SumCmdRaw, io: BenchIO.IO, exit: int)
    requires Core.CoreSummary(raw, io, exit)
    ensures Spec.Spec(raw, io, exit)
  {
    // TODO: prove this connection after replacing the false placeholder relations.
  }
}
