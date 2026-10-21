include "TrueSchema.dfy"
include "TrueCore.dfy"
include "TrueSpec.dfy"

module TrueProof {
  import BenchWorld

  import BenchIO
  import Schema = TrueSchema
  import Core = TrueCore
  import Spec = TrueSpec

  twostate lemma PreparedSummaryImpliesPreparedSpec(raw: Schema.TrueCmdRaw, io: BenchIO.IO, exit: int, new plannedStdout: BenchWorld.Bytes, new plannedStderr: BenchWorld.Bytes)
    requires Core.PreparedSummary(raw, io, exit, plannedStdout, plannedStderr)
    ensures Spec.PreparedSpec(raw, io, exit, plannedStdout, plannedStderr)
  {
    var cmd := Schema.Command(raw);
    if cmd.mode == Schema.ModeHelp {
    } else if cmd.mode == Schema.ModeVersion {
    }
  }

  twostate lemma CoreSummaryImpliesSpec(raw: Schema.TrueCmdRaw, io: BenchIO.IO, exit: int)
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
