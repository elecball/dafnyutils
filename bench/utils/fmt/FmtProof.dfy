include "FmtSpec.dfy"
include "FmtCore.dfy"

module FmtProof {
  import BenchIO
  import Schema = FmtSchema
  import Core = FmtCore
  import Spec = FmtSpec

  twostate lemma CoreSummaryImpliesSpec(
    raw: Schema.FmtCmdRaw, io: BenchIO.IO, exit: int)
    requires Core.CoreSummary(raw, io, exit)
    ensures Spec.Spec(raw, io, exit)
  {
    // TODO: prove this connection after replacing the false placeholder relations.
  }
}
