include "../Spec/FalseSchema.dfy"
include "../Impl/FalseCore.dfy"
include "../Spec/FalseSpec.dfy"

module FalseProof {
  import BenchWorld

  import BenchIO
  import Schema = FalseSchema
  import Core = FalseCore
  import Spec = FalseSpec

  twostate lemma PreparedSummaryImpliesPreparedSpec(raw: Schema.FalseCmdRaw, io: BenchIO.IO, exit: int, new plannedStdout: BenchWorld.Bytes, new plannedStderr: BenchWorld.Bytes)
    requires Core.PreparedSummary(raw, io, exit, plannedStdout, plannedStderr)
    ensures Spec.PreparedSpec(raw, io, exit, plannedStdout, plannedStderr)
  {
    reveal Core.PreparedSummary();
    reveal Spec.PreparedSpec();
    var cmd := Schema.Command(raw);
    if cmd.mode == Schema.ModeHelp {
    } else if cmd.mode == Schema.ModeVersion {
    }
  }

  twostate lemma CoreSummaryImpliesSpec(raw: Schema.FalseCmdRaw, io: BenchIO.IO, exit: int)
    requires Core.CoreSummary(raw, io, exit)
    ensures Spec.Spec(raw, io, exit)
  {
    var out: BenchWorld.Bytes, diagnostics: BenchWorld.Bytes, normalExit: int :|
      Core.PreparedSummary(raw, io, normalExit,
                           old(io.stdout()) + out, old(io.stderr()) + diagnostics) &&
      Spec.Emission(raw, io, out, diagnostics, normalExit, exit);
    PreparedSummaryImpliesPreparedSpec(raw, io, normalExit,
                                       old(io.stdout()) + out, old(io.stderr()) + diagnostics);
  }
}
