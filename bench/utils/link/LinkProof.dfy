include "LinkSpec.dfy"
include "LinkCore.dfy"

module LinkProof {
  import StreamWorld = BenchWorld
  import StreamContract = IOContract

  import BenchIO
  import Schema = LinkSchema
  import Core = LinkCore
  import Spec = LinkSpec

  twostate lemma PreparedSummaryImpliesPreparedSpec(
    raw: Schema.LinkCmdRaw, io: BenchIO.IO, exit: int, plannedStdout: StreamWorld.Bytes, plannedStderr: StreamWorld.Bytes)
    requires Core.PreparedSummary(raw, io, exit, plannedStdout, plannedStderr)
    ensures Spec.PreparedSpec(raw, io, exit, plannedStdout, plannedStderr)
  {

    reveal Core.PreparedSummary();
  }

  twostate lemma CoreSummaryImpliesSpec(raw: Schema.LinkCmdRaw, io: BenchIO.IO, exit: int)
    requires Core.CoreSummary(raw, io, exit)
    ensures Spec.Spec(raw, io, exit)
  {
    var output: StreamWorld.Bytes, diagnostics: StreamWorld.Bytes, normalExit: int :|
      Core.PreparedSummary(raw, io, normalExit, output, diagnostics) &&
      Spec.EmissionFields(old(io.stdout()), old(io.stderr()), io.stdout(), io.stderr(),
                          io.trustedStreams(), output, diagnostics, normalExit, exit);
    PreparedSummaryImpliesPreparedSpec(raw, io, normalExit,
      output, diagnostics);
  }
}
