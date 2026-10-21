include "../../core/Utf8.dfy"
include "LinkSpec.dfy"
include "../../core/IO.dfy"
include "LinkSchema.dfy"

module LinkCore {
  import Text = LinkSpec
  import StreamWorld = BenchWorld
  import StreamContract = IOContract

  import BenchIO
  import BenchWorld
  import Schema = LinkSchema
  import Spec = LinkSpec
  import C = IOContract
  import Utf8 = Utf8Semantics

  opaque twostate predicate PreparedSummary(raw: Schema.LinkCmdRaw, io: BenchIO.IO, exit: int, plannedStdout: StreamWorld.Bytes, plannedStderr: StreamWorld.Bytes)
    reads io.fsRegion, io.nowRegion, io.trustedFilesystemRegion
  {
    if raw.mode == Schema.ModeHelp then
      io.fs() == old(io.fs()) &&
      plannedStdout == [] + Spec.HelpTextSpec() &&
      plannedStderr == [] &&
      exit == 0
    else if raw.mode == Schema.ModeVersion then
      io.fs() == old(io.fs()) &&
      plannedStdout == [] + Spec.VersionTextSpec() &&
      plannedStderr == [] &&
      exit == 0
    else if raw.mode != Schema.ModeRun then
      match raw.mode
      case ModeExtraOperand(operand) =>
        io.fs() == old(io.fs()) &&
        plannedStdout == [] &&
        plannedStderr == [] +
        Spec.ExtraOperandText(C.QuoteArgumentResult(Utf8.Encode(operand))) &&
        exit == 1
      case _ => false
    else if |raw.operands| == 0 then
      io.fs() == old(io.fs()) &&
      plannedStdout == [] &&
      plannedStderr == [] + Spec.MissingOperandText() &&
      exit == 1
    else if |raw.operands| == 1 then
      io.fs() == old(io.fs()) &&
      plannedStdout == [] &&
      plannedStderr == [] +
      Spec.MissingOperandAfterText(
        C.QuoteArgumentResult(Utf8.Encode(raw.operands[0]))
      ) &&
      exit == 1
    else
      exists ok: bool, err: int ::
        Spec.LinkResult(io, raw.operands[0], raw.operands[1], ok, err) &&
        plannedStdout == [] &&
        (if ok then
           plannedStderr == [] && exit == 0
         else
           plannedStderr == [] +
           Spec.CannotCreateLinkText(
             C.QuoteafPathResult(raw.operands[1]),
             C.QuoteafPathResult(raw.operands[0]),
             C.CLocaleErrnoTextResult(err)
           ) &&
           exit == 1)
  }

  twostate predicate CoreSummary(raw: Schema.LinkCmdRaw, io: BenchIO.IO, exit: int)
    reads io.Footprint()
  {
    exists output: StreamWorld.Bytes, diagnostics: StreamWorld.Bytes, normalExit: int ::
      PreparedSummary(raw, io, normalExit, output, diagnostics) &&
      Spec.EmissionFields(old(io.stdout()), old(io.stderr()), io.stdout(), io.stderr(),
                          io.trustedStreams(), output, diagnostics, normalExit, exit)
  }

  method Prepare(raw: Schema.LinkCmdRaw, io: BenchIO.IO) returns (exit: int, plannedStdout: StreamWorld.Bytes, plannedStderr: StreamWorld.Bytes)
    modifies io.fsRegion
    ensures PreparedSummary(raw, io, exit, plannedStdout, plannedStderr)
  {

    reveal PreparedSummary();    ghost var emissionBeforeOut: StreamWorld.Bytes := [];
    ghost var emissionBeforeErr: StreamWorld.Bytes := [];
    plannedStdout := [];
    plannedStderr := [];
    if raw.mode == Schema.ModeHelp {
      plannedStdout := plannedStdout + (Spec.HelpTextSpec());
      exit := 0;
    } else if raw.mode == Schema.ModeVersion {
      plannedStdout := plannedStdout + (Spec.VersionTextSpec());
      exit := 0;
    } else if raw.mode.ModeExtraOperand? {
      var quotedOperand := io.QuoteArgument(Utf8.Encode(raw.mode.operand));
      plannedStderr := plannedStderr + (Spec.ExtraOperandText(quotedOperand));
      exit := 1;
    } else if |raw.operands| == 0 {
      plannedStderr := plannedStderr + (Spec.MissingOperandText());
      exit := 1;
    } else if |raw.operands| == 1 {
      var quotedSource := io.QuoteArgument(Utf8.Encode(raw.operands[0]));
      plannedStderr := plannedStderr + (
        Spec.MissingOperandAfterText(quotedSource));
      exit := 1;
    } else {
      var source := raw.operands[0];
      var target := raw.operands[1];
      var result := io.CreateHardLink(source, target);
      var ok := result.Ok?;
      var err := C.ResultErrno(result);
      assert Spec.LinkResult(io, source, target, ok, err);

      if ok {
        exit := 0;
      } else {
        var reason := io.GetCLocaleErrnoText(err);
        var quotedTarget := io.QuoteafPath(target);
        var quotedSource := io.QuoteafPath(source);
        plannedStderr := plannedStderr + (
          Text.CannotCreateLinkText(quotedTarget, quotedSource, reason));
        exit := 1;

        assert C.GetCLocaleErrnoTextSpec(err, reason);
        assert Spec.LinkResult(io, source, target, ok, err);
      }
    }
    assert PreparedSummary(raw, io, exit, plannedStdout, plannedStderr) by {
      hide *;
      reveal PreparedSummary();
    }
  }


  method Flush(output: StreamWorld.Bytes, diagnostics: StreamWorld.Bytes,
               normalExit: int, io: BenchIO.IO) returns (exit: int)
    modifies io.stdoutRegion, io.stderrRegion
    ensures Spec.EmissionFields(old(io.stdout()), old(io.stderr()), io.stdout(), io.stderr(),
                                io.trustedStreams(), output, diagnostics, normalExit, exit)
  {
    var committed: nat := 0;
    var outErr := 0;
    if |output| != 0 {
      var result := io.WriteStdout(output);
      committed := StreamContract.WriteResultCommitted(result);
      outErr := StreamContract.ResultErrno(result);
    }
    var finalDiagnostics := diagnostics;
    if outErr != 0 {
      var reason := io.GetCLocaleErrnoText(outErr);
      finalDiagnostics := diagnostics + Text.WriteErrorText(reason);
    }
    assert finalDiagnostics == diagnostics + (if outErr == 0 then []
                                              else Spec.WriteErrorText(StreamContract.CLocaleErrnoTextResult(outErr)));
    var errCommitted: nat := 0;
    var errErr := 0;
    if |finalDiagnostics| != 0 {
      var result := io.WriteStderr(finalDiagnostics);
      errCommitted := StreamContract.WriteResultCommitted(result);
      errErr := StreamContract.ResultErrno(result);
      assert StreamContract.WriteStderrSpec(old(io.stderr()), io.trustedStreams(), io.stderr(),
                                            finalDiagnostics, errCommitted, errErr);
    }
    exit := if outErr != 0 || errErr != 0 then 1 else normalExit;
    assert Spec.EmissionOutcomeFields(old(io.stdout()), old(io.stderr()), io.stdout(), io.stderr(),
                                      io.trustedStreams(), output, diagnostics, normalExit, exit, committed, outErr, errCommitted, errErr);
  }

  method RunCore(raw: Schema.LinkCmdRaw, io: BenchIO.IO) returns (exit: int)
    modifies io.fsRegion, io.stdoutRegion, io.stderrRegion
    ensures CoreSummary(raw, io, exit)
  {
    var normalExit, output, diagnostics := Prepare(raw, io);
    assert PreparedSummary(raw, io, normalExit, output, diagnostics);
    exit := Flush(output, diagnostics, normalExit, io);
    assert PreparedSummary(raw, io, normalExit, output, diagnostics);
    assert Spec.EmissionFields(old(io.stdout()), old(io.stderr()), io.stdout(), io.stderr(),
                               io.trustedStreams(), output, diagnostics, normalExit, exit);
    assert exists emitted: StreamWorld.Bytes, reported: StreamWorld.Bytes, preparedExit: int ::
        PreparedSummary(raw, io, preparedExit, emitted, reported) &&
        Spec.EmissionFields(old(io.stdout()), old(io.stderr()), io.stdout(), io.stderr(),
                            io.trustedStreams(), emitted, reported, preparedExit, exit);
  }
}
