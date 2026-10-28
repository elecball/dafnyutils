include "../Spec/RealpathSpec.dfy"
include "../Impl/RealpathCore.dfy"

module RealpathProof {
  import BenchIO
  import Schema = RealpathSchema
  import Core = RealpathCore
  import Spec = RealpathSpec

  twostate lemma CoreSummaryImpliesSpec(
    raw: Schema.RealpathCmdRaw, io: BenchIO.IO, exit: int)
    requires Core.CoreSummary(raw, io, exit)
    ensures Spec.Spec(raw, io, exit)
  {

  }
}
