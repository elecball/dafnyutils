include "../Spec/JoinSpec.dfy"
include "../Impl/JoinCore.dfy"

module JoinProof {
  import BenchIO
  import S = JoinSchema
  import Core = JoinCore
  import Spec = JoinSpec

  twostate lemma CoreSummaryImpliesSpec(raw: S.JoinCmdRaw, io: BenchIO.IO, exit: int)
    requires Core.CoreSummary(raw,io,exit)
    ensures Spec.Spec(raw,io,exit)
  {
  }
}
