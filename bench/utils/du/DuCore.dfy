include "../../core/World.dfy"
include "../../core/IO.dfy"
include "../../core/IOContract.dfy"
include "DuSchema.dfy"
include "DuSpec.dfy"

module DuCore {
  import StreamWorld = BenchWorld
  import StreamContract = IOContract

  import Result = Results
  import BenchIO
  import BenchWorld
  import IOContract
  import Schema = DuSchema
  import Spec = DuSpec
  import Utf8 = Utf8Semantics

  function DigitChar(d: nat): char
    requires d < 10
  {
    if d == 0 then '0'
    else if d == 1 then '1'
    else if d == 2 then '2'
    else if d == 3 then '3'
    else if d == 4 then '4'
    else if d == 5 then '5'
    else if d == 6 then '6'
    else if d == 7 then '7'
    else if d == 8 then '8'
    else '9'
  }

  function NatText(n: nat): string
    decreases n
  {
    if n < 10 then
      [DigitChar(n)]
    else
      NatText(n / 10) + [DigitChar(n % 10)]
  }

  function CountLine(size: nat, path: BenchWorld.Path): BenchWorld.Bytes
  {
    NatText(size) + "\t" + Utf8.Encode(path) + "\n"
  }

  function OutputPiece(
    path: BenchWorld.Path,
    result: BenchWorld.IOResult<BenchWorld.Bytes>
  ): BenchWorld.Bytes
  {
    match result
    case Ok(data) => CountLine(|data|, path)
    case Err(_) => []
  }

  function ErrorPiece(
    path: BenchWorld.Path,
    result: BenchWorld.IOResult<BenchWorld.Bytes>
  ): BenchWorld.Bytes
  {
    match result
    case Ok(_) => []
    case Err(err) => Spec.ErrorMessageSpec(path, err)
  }

  ghost function ReadResultCore(
    cmd: Schema.DuCmd,
    preFs: BenchWorld.FileSystem, preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult,
    i: nat
  ): BenchWorld.IOResult<BenchWorld.Bytes>
    requires i < |cmd.operands|
  {
    IOContract.ObservedReadFileResultFields(preFs, preStreams, cmd.operands[i])
  }

  ghost function PrefixOutputCore(
    cmd: Schema.DuCmd,
    preFs: BenchWorld.FileSystem, preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult,
    i: nat
  ): BenchWorld.Bytes
    requires i <= |cmd.operands|
    decreases i
  {
    if i == 0 then
      []
    else
      PrefixOutputCore(cmd, preFs, preStreams, i - 1) +
      OutputPiece(cmd.operands[i - 1], ReadResultCore(cmd, preFs, preStreams, i - 1))
  }

  ghost function PrefixErrorsCore(
    cmd: Schema.DuCmd,
    preFs: BenchWorld.FileSystem, preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult,
    i: nat
  ): BenchWorld.Bytes
    requires i <= |cmd.operands|
    decreases i
  {
    if i == 0 then
      []
    else
      PrefixErrorsCore(cmd, preFs, preStreams, i - 1) +
      ErrorPiece(cmd.operands[i - 1], ReadResultCore(cmd, preFs, preStreams, i - 1))
  }

  ghost predicate PrefixHadErrorCore(
    cmd: Schema.DuCmd,
    preFs: BenchWorld.FileSystem, preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult,
    i: nat
  )
    requires i <= |cmd.operands|
    decreases i
  {
    i > 0 &&
    (PrefixHadErrorCore(cmd, preFs, preStreams, i - 1) ||
     ReadResultCore(cmd, preFs, preStreams, i - 1).Err?)
  }

  opaque twostate predicate PreparedSummary(raw: Schema.DuCmdRaw, io: BenchIO.IO, exit: int, plannedStdout: StreamWorld.Bytes, plannedStderr: StreamWorld.Bytes)
  {
    var cmd := Schema.Command(raw);
    if cmd.mode == Schema.ModeHelp then
      plannedStdout == [] + Spec.HelpTextSpec() &&
      plannedStderr == [] &&
      exit == 0
    else if cmd.mode == Schema.ModeVersion then
      plannedStdout == [] + Spec.VersionTextSpec() &&
      plannedStderr == [] &&
      exit == 0
    else if cmd.mode == Schema.ModeUnsupportedAccounting then
      plannedStdout == [] &&
      plannedStderr == [] + Spec.UnsupportedAccountingMessageSpec() &&
      exit == 1
    else
      plannedStdout == [] + PrefixOutputCore(cmd, old(io.fs()), old(io.trustedStreams()), |cmd.operands|) &&
      plannedStderr == [] + PrefixErrorsCore(cmd, old(io.fs()), old(io.trustedStreams()), |cmd.operands|) &&
      exit == (if PrefixHadErrorCore(cmd, old(io.fs()), old(io.trustedStreams()), |cmd.operands|) then 1 else 0)
  }

  twostate predicate CoreSummary(raw: Schema.DuCmdRaw, io: BenchIO.IO, exit: int)
    reads io.Footprint()
  {
    exists output: StreamWorld.Bytes, diagnostics: StreamWorld.Bytes, normalExit: int ::
      PreparedSummary(raw, io, normalExit, output, diagnostics) &&
      Spec.EmissionFields(old(io.stdout()), old(io.stderr()), io.stdout(), io.stderr(),
                          io.trustedStreams(), output, diagnostics, normalExit, exit)
  }

  method Prepare(raw: Schema.DuCmdRaw, io: BenchIO.IO) returns (exit: int, plannedStdout: StreamWorld.Bytes, plannedStderr: StreamWorld.Bytes)
    ensures PreparedSummary(raw, io, exit, plannedStdout, plannedStderr)
    decreases *
  {

    reveal PreparedSummary();    ghost var emissionBeforeOut: StreamWorld.Bytes := [];
    ghost var emissionBeforeErr: StreamWorld.Bytes := [];
    plannedStdout := [];
    plannedStderr := [];
    ghost var preFs := io.fs();
    ghost var preStreams := io.trustedStreams();
    ghost var preStdout := (emissionBeforeOut + plannedStdout);
    ghost var preStderr := (emissionBeforeErr + plannedStderr);
    var cmd := Schema.Command(raw);

    if cmd.mode == Schema.ModeHelp {
      plannedStdout := plannedStdout + (Spec.HelpTextSpec());
      exit := 0;
      assert PreparedSummary(raw, io, exit, emissionBeforeOut + plannedStdout, emissionBeforeErr + plannedStderr) by {
      hide *;
      reveal PreparedSummary();
    }
      return;
    }

    if cmd.mode == Schema.ModeVersion {
      plannedStdout := plannedStdout + (Spec.VersionTextSpec());
      exit := 0;
      assert PreparedSummary(raw, io, exit, emissionBeforeOut + plannedStdout, emissionBeforeErr + plannedStderr) by {
      hide *;
      reveal PreparedSummary();
    }
      return;
    }

    if cmd.mode == Schema.ModeUnsupportedAccounting {
      plannedStderr := plannedStderr + (Spec.UnsupportedAccountingMessageSpec());
      exit := 1;
      assert PreparedSummary(raw, io, exit, emissionBeforeOut + plannedStdout, emissionBeforeErr + plannedStderr) by {
      hide *;
      reveal PreparedSummary();
    }
      return;
    }

    var output: BenchWorld.Bytes := [];
    var err: BenchWorld.Bytes := [];
    var hadError := false;

    var i := 0;
    while i < |cmd.operands|
      invariant 0 <= i <= |cmd.operands|
      invariant (emissionBeforeOut + plannedStdout) == preStdout
      invariant (emissionBeforeErr + plannedStderr) == preStderr
      invariant output == PrefixOutputCore(cmd, preFs, preStreams, i)
      invariant err == PrefixErrorsCore(cmd, preFs, preStreams, i)
      invariant hadError == PrefixHadErrorCore(cmd, preFs, preStreams, i)
      decreases |cmd.operands| - i
    {
      var path := cmd.operands[i];
      var readResult := io.ReadFile(path);
      assert readResult == ReadResultCore(cmd, preFs, preStreams, i);

      match readResult {
        case Ok(data) =>
          output := output + OutputPiece(path, readResult);
        case Err(e) =>
          err := err + ErrorPiece(path, readResult);
          hadError := true;
      }
      i := i + 1;
      assert hadError == PrefixHadErrorCore(cmd, preFs, preStreams, i) by {
        hide *;
        reveal PrefixHadErrorCore();
      }
    }

    assert (emissionBeforeOut + plannedStdout) == preStdout;
    assert (emissionBeforeErr + plannedStderr) == preStderr;
    plannedStdout := plannedStdout + (output);
    assert (emissionBeforeOut + plannedStdout) == preStdout + output by { hide *; }
    assert (emissionBeforeErr + plannedStderr) == preStderr;
    plannedStderr := plannedStderr + (err);
    assert (emissionBeforeOut + plannedStdout) == preStdout + output by { hide *; }
    assert (emissionBeforeErr + plannedStderr) == preStderr + err by { hide *; }
    exit := if hadError then 1 else 0;
    assert output == PrefixOutputCore(cmd, preFs, preStreams, |cmd.operands|);
    assert err == PrefixErrorsCore(cmd, preFs, preStreams, |cmd.operands|);
    assert hadError == PrefixHadErrorCore(cmd, preFs, preStreams, |cmd.operands|);
    assert PreparedSummary(raw, io, exit, emissionBeforeOut + plannedStdout, emissionBeforeErr + plannedStderr) by {
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
      finalDiagnostics := diagnostics + Spec.WriteErrorText(reason);
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

  method RunCore(raw: Schema.DuCmdRaw, io: BenchIO.IO) returns (exit: int)
    modifies io.stdoutRegion, io.stderrRegion
    ensures CoreSummary(raw, io, exit)
    decreases *
  {
    var normalExit, output, diagnostics := Prepare(raw, io);
    exit := Flush(output, diagnostics, normalExit, io);
  }
}
