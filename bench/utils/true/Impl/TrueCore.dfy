include "../Spec/TrueSpec.dfy"
include "../../../core/IOContract.dfy"
include "../../../core/IO.dfy"
include "../Spec/TrueSchema.dfy"

module TrueCore {
  import StreamContract = IOContract

  import BenchWorld

  import BenchIO
  import Schema = TrueSchema
  import Spec = TrueSpec

  twostate predicate PreparedSummary(raw: Schema.TrueCmdRaw, io: BenchIO.IO, exit: int, plannedStdout: BenchWorld.Bytes, plannedStderr: BenchWorld.Bytes)

  {
    plannedStderr == old(io.stderr()) &&
    (    var cmd := Schema.Command(raw);
         if cmd.mode == Schema.ModeHelp then
           plannedStdout == old(io.stdout()) + Spec.HelpTextSpec() &&
           exit == 0
         else if cmd.mode == Schema.ModeVersion then
           plannedStdout == old(io.stdout()) + Spec.VersionTextSpec() &&
           exit == 0
         else
           plannedStdout == old(io.stdout()) &&
           exit == 0)
  }

  method Prepare(raw: Schema.TrueCmdRaw, io: BenchIO.IO) returns (exit: int, plannedOut: BenchWorld.Bytes, plannedErr: BenchWorld.Bytes)

    ensures PreparedSummary(raw, io, exit, old(io.stdout()) + plannedOut, old(io.stderr()) + plannedErr)
    decreases *
  {
    plannedOut := [];
    plannedErr := [];
    ghost var initialStdout := io.stdout();
    ghost var initialStderr := io.stderr();

    var cmd := Schema.Command(raw);
    if cmd.mode == Schema.ModeHelp {
      var out := Spec.HelpTextSpec();
      plannedOut := plannedOut + out;
      exit := 0;
    } else if cmd.mode == Schema.ModeVersion {
      var out := Spec.VersionTextSpec();
      plannedOut := plannedOut + out;
      exit := 0;
    } else {
      exit := 0;
    }
  }

  twostate predicate CoreSummary(raw: Schema.TrueCmdRaw, io: BenchIO.IO, exit: int)
    reads io.stdoutRegion, io.stderrRegion
  {
    exists out: BenchWorld.Bytes, diagnostics: BenchWorld.Bytes, normalExit: int ::
      PreparedSummary(raw, io, normalExit,
                      old(io.stdout()) + out, old(io.stderr()) + diagnostics) &&
      Spec.Emission(raw, io, out, diagnostics, normalExit, exit)
  }

  method Flush(io: BenchIO.IO, out: BenchWorld.Bytes,
               diagnostics: BenchWorld.Bytes, normalExit: int) returns (exit: int)
    modifies io.stdoutRegion, io.stderrRegion
    ensures Spec.EmitFields(old(io.trustedStreams()), old(io.stdout()), old(io.stderr()),
                            io.stdout(), io.stderr(), out, diagnostics, normalExit, exit)
  {
    var outErr := 0;
    if out != [] {
      var written := io.WriteStdout(out);
      outErr := StreamContract.ResultErrno(written);
    }
    var errors := diagnostics;
    if outErr != 0 {
      var message := io.GetCLocaleErrnoText(outErr);
      errors := errors + Spec.StreamWriteErrorMessage(message);
    }
    assert errors == diagnostics + (if outErr == 0 then [] else
                                    Spec.StreamWriteErrorMessage(StreamContract.CLocaleErrnoTextResult(outErr)));
    var errErr := 0;
    if errors != [] {
      var diagnosed := io.WriteStderr(errors);
      errErr := StreamContract.ResultErrno(diagnosed);
      assert StreamContract.WriteStderrSpec(old(io.stderr()), io.trustedStreams(), io.stderr(),
                                            errors, StreamContract.WriteResultCommitted(diagnosed), errErr);
    }
    exit := if outErr != 0 || errErr != 0 then 1 else normalExit;
  }

  method RunCore(raw: Schema.TrueCmdRaw, io: BenchIO.IO) returns (exit: int)
    modifies io.stdoutRegion, io.stderrRegion
    ensures CoreSummary(raw, io, exit)
    decreases *
  {
    var normalExit, out, diagnostics := Prepare(raw, io);

    assert PreparedSummary(raw, io, normalExit, old(io.stdout()) + out, old(io.stderr()) + diagnostics);
    if Spec.Emits(raw) {
      exit := Flush(io, out, diagnostics, normalExit);
    } else {
      exit := normalExit;
    }
    assert PreparedSummary(raw, io, normalExit, old(io.stdout()) + out, old(io.stderr()) + diagnostics);
    assert Spec.Emission(raw, io, out, diagnostics, normalExit, exit);
  }
}
