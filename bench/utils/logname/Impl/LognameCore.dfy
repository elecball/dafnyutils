include "../Spec/LognameSpec.dfy"
include "../../../core/IO.dfy"
include "../../../core/IOContract.dfy"
include "../Spec/LognameSchema.dfy"

module LognameCore {
  import StreamContract = IOContract

  import Result = Results
  import BenchIO
  import IOContract
  import Schema = LognameSchema
  import BenchWorld
  import Spec = LognameSpec

  method GetHelpText() returns (out: BenchWorld.Bytes)
    ensures out == Spec.HelpTextSpec()
  {
    out := Spec.HelpTextSpec();
  }

  method GetVersionText() returns (out: BenchWorld.Bytes)
    ensures out == Spec.VersionTextSpec()
  {
    out := Spec.VersionTextSpec();
  }

  method GetExtraOperandMessage(op: string) returns (out: BenchWorld.Bytes)
    ensures out == Spec.ExtraOperandMessageSpec(op)
  {
    out := Spec.ExtraOperandMessageSpec(op);
  }

  method GetNoLoginNameMessage() returns (out: BenchWorld.Bytes)
    ensures out == Spec.NoLoginNameMessageSpec()
  {
    out := Spec.NoLoginNameMessageSpec();
  }

  ghost predicate LoginNameResultFields(
    props: map<string, string>,
    login: BenchWorld.IOResult<string>,
                               preStdout: BenchWorld.Bytes,
                               preStderr: BenchWorld.Bytes,
                               stdout: BenchWorld.Bytes,
                               stderr: BenchWorld.Bytes,
                               exit: int
  )
  {
    IOContract.GetLoginNameContractFields(props, login) &&
    match login
    case Ok(name) =>
      stdout == preStdout + Spec.LoginNameOutput(name) &&
      stderr == preStderr &&
      exit == 0
    case Err(_) =>
      stdout == preStdout &&
      stderr == preStderr + Spec.NoLoginNameMessageSpec() &&
      exit == 1
  }

  twostate predicate PreparedSummary(raw: Schema.LognameCmdRaw, io: BenchIO.IO, exit: int, plannedStdout: BenchWorld.Bytes, plannedStderr: BenchWorld.Bytes)

  {
    var cmd := Schema.Command(raw);
    if cmd.mode == Schema.ModeHelp then
      plannedStdout == old(io.stdout()) + Spec.HelpTextSpec() &&
      plannedStderr == old(io.stderr()) &&
      exit == 0
    else if cmd.mode == Schema.ModeVersion then
      plannedStdout == old(io.stdout()) + Spec.VersionTextSpec() &&
      plannedStderr == old(io.stderr()) &&
      exit == 0
    else if |cmd.operands| > 0 then
      plannedStdout == old(io.stdout()) &&
      plannedStderr == old(io.stderr()) + Spec.ExtraOperandMessageSpec(cmd.operands[0]) &&
      exit == 1
    else
      exists login: BenchWorld.IOResult<string> ::
        LoginNameResultFields(
          old(io.props()),
          login,
          old(io.stdout()),
          old(io.stderr()),
          plannedStdout,
          plannedStderr,
          exit
        )
  }

  method Prepare(raw: Schema.LognameCmdRaw, io: BenchIO.IO) returns (exit: int, plannedOut: BenchWorld.Bytes, plannedErr: BenchWorld.Bytes)


    ensures PreparedSummary(raw, io, exit, old(io.stdout()) + plannedOut, old(io.stderr()) + plannedErr)
    decreases *
  {
    plannedOut := [];
    plannedErr := [];
    ghost var initialStdout := io.stdout();
    ghost var initialStderr := io.stderr();

    ghost var preProps := io.props();
    ghost var preStdout := (initialStdout + plannedOut);
    ghost var preStderr := (initialStderr + plannedErr);
    var cmd := Schema.Command(raw);
    if cmd.mode == Schema.ModeHelp {
      var out := GetHelpText();
      plannedOut := plannedOut + out;
      exit := 0;
      assert PreparedSummary(raw, io, exit, old(io.stdout()) + plannedOut, old(io.stderr()) + plannedErr);
      return;
    }

    if cmd.mode == Schema.ModeVersion {
      var out := GetVersionText();
      plannedOut := plannedOut + out;
      exit := 0;
      assert PreparedSummary(raw, io, exit, old(io.stdout()) + plannedOut, old(io.stderr()) + plannedErr);
      return;
    }

    if |cmd.operands| > 0 {
      var err := GetExtraOperandMessage(cmd.operands[0]);
      plannedErr := plannedErr + err;
      exit := 1;
      assert PreparedSummary(raw, io, exit, old(io.stdout()) + plannedOut, old(io.stderr()) + plannedErr);
      return;
    }

    var login := io.GetLoginName();
    assert IOContract.GetLoginNameContractFields(preProps, login);
    match login
    case Ok(name) =>
      plannedOut := plannedOut + Spec.LoginNameOutput(name);
      exit := 0;
      assert LoginNameResultFields(
          preProps,
          login,
          preStdout,
          preStderr,
          (initialStdout + plannedOut),
          (initialStderr + plannedErr),
          exit
        );
      assert LoginNameResultFields(old(io.props()), login, old(io.stdout()), old(io.stderr()),
                                   old(io.stdout()) + plannedOut, old(io.stderr()) + plannedErr, exit);
      assert exists loginWitness: BenchWorld.IOResult<string> ::
          LoginNameResultFields(old(io.props()), loginWitness, old(io.stdout()), old(io.stderr()),
                                old(io.stdout()) + plannedOut, old(io.stderr()) + plannedErr, exit);
      assert PreparedSummary(raw, io, exit, old(io.stdout()) + plannedOut, old(io.stderr()) + plannedErr);
    case Err(_) =>
      var err := GetNoLoginNameMessage();
      plannedErr := plannedErr + err;
      exit := 1;
      assert LoginNameResultFields(
          preProps,
          login,
          preStdout,
          preStderr,
          (initialStdout + plannedOut),
          (initialStderr + plannedErr),
          exit
        );
      assert LoginNameResultFields(old(io.props()), login, old(io.stdout()), old(io.stderr()),
                                   old(io.stdout()) + plannedOut, old(io.stderr()) + plannedErr, exit);
      assert exists loginWitness: BenchWorld.IOResult<string> ::
          LoginNameResultFields(old(io.props()), loginWitness, old(io.stdout()), old(io.stderr()),
                                old(io.stdout()) + plannedOut, old(io.stderr()) + plannedErr, exit);
      assert PreparedSummary(raw, io, exit, old(io.stdout()) + plannedOut, old(io.stderr()) + plannedErr);
  }

  twostate predicate CoreSummary(raw: Schema.LognameCmdRaw, io: BenchIO.IO, exit: int)
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

  method RunCore(raw: Schema.LognameCmdRaw, io: BenchIO.IO) returns (exit: int)
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
