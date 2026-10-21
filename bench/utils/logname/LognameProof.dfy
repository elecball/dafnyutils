include "../../core/IO.dfy"
include "LognameSchema.dfy"
include "LognameCore.dfy"
include "LognameSpec.dfy"

module LognameProof {
  import Result = Results
  import BenchIO
  import BenchWorld
  import Schema = LognameSchema
  import Core = LognameCore
  import Spec = LognameSpec

  twostate lemma PreparedSummaryImpliesPreparedSpec(raw: Schema.LognameCmdRaw, io: BenchIO.IO, exit: int, new plannedStdout: BenchWorld.Bytes, new plannedStderr: BenchWorld.Bytes)
    requires Core.PreparedSummary(raw, io, exit, plannedStdout, plannedStderr)
    ensures Spec.PreparedSpec(raw, io, exit, plannedStdout, plannedStderr)
  {
    var cmd := Schema.Command(raw);
    if cmd.mode == Schema.ModeHelp {
    } else if cmd.mode == Schema.ModeVersion {
    } else if |cmd.operands| > 0 {
    } else {
      var login: BenchWorld.IOResult<string> :|
        Core.LoginNameResultFields(
          old(io.props()),
          login,
          old(io.stdout()),
          old(io.stderr()),
          plannedStdout,
          plannedStderr,
          exit
        );
      match login
      case Ok(name) =>
        assert Spec.HasLoginNameProps(old(io.props()));
        assert name == old(io.props())["loginName"];
      case Err(_) =>
        assert !Spec.HasLoginNameProps(old(io.props()));
    }
  }

  twostate lemma CoreSummaryImpliesSpec(raw: Schema.LognameCmdRaw, io: BenchIO.IO, exit: int)
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
