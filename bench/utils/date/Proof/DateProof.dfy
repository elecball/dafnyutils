include "../Spec/DateSpec.dfy"
include "../Impl/DateCore.dfy"

module DateProof {
  import BenchIO
  import Schema = DateSchema
  import Core = DateCore
  import Spec = DateSpec

  twostate lemma CoreSummaryImpliesSpec(
    raw: Schema.DateCmdRaw, io: BenchIO.IO, exit: int)
    requires Core.CoreSummary(raw, io, exit)
    ensures Spec.Spec(raw, io, exit)
  {

  }
}
