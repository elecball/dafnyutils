include "TsortSpec.dfy"
include "TsortCore.dfy"

module TsortProof {
  import BenchIO
  import Schema = TsortSchema
  import Core = TsortCore
  import Spec = TsortSpec

  twostate lemma CoreSummaryImpliesSpec(
    raw: Schema.TsortCmdRaw, io: BenchIO.IO, exit: int)
    requires Core.CoreSummary(raw, io, exit)
    ensures Spec.Spec(raw, io, exit)
  {
    // TODO: prove this connection after replacing the false placeholder relations.
  }
}
