include "TeeTextCore.dfy"
include "../../core/World.dfy"
include "../../core/IO.dfy"
include "../../core/IOContract.dfy"
include "TeeSchema.dfy"
include "TeeSpec.dfy"

module TeeCore {
  import Text = TeeTextCore

  import StreamWorld = BenchWorld
  import StreamContract = IOContract

  import Result = Results
  import BenchIO
  import BenchWorld
  import IOContract
  import Schema = TeeSchema
  import Spec = TeeSpec

  ghost predicate WriteOneSummaryFields(
    append: bool,
    path: BenchWorld.Path,
    input: BenchWorld.Bytes,
    preFs: BenchWorld.FileSystem,
    preProps: map<string, string>,
    preNow: int,
    preCredentials: BenchWorld.ProcessCredentials,
    preTrustedFilesystem: (BenchWorld.TrustedFilesystemRequest) -> BenchWorld.TrustedFilesystemResult,
    fs2: BenchWorld.FileSystem,
    stderr: BenchWorld.Bytes,
    exit: int
  )
  {
    if append then
      exists ok: bool, writeErr: int, committed: nat, stage: BenchWorld.FileWriteStage ::
        IOContract.AppendFileSpec(preFs, preProps, preNow, preCredentials, preTrustedFilesystem,
                                  fs2, path, input, ok, writeErr, committed, stage) &&
        stderr == (if ok then [] else Spec.WriteErrorMessageSpec(path, writeErr)) &&
        exit == (if ok then 0 else 1)
    else
      exists ok: bool, writeErr: int, committed: nat, stage: BenchWorld.FileWriteStage ::
        IOContract.WriteFileSpec(preFs, preProps, preNow, preCredentials, preTrustedFilesystem,
                                fs2, path, input, ok, writeErr, committed, stage) &&
        stderr == (if ok then [] else Spec.WriteErrorMessageSpec(path, writeErr)) &&
        exit == (if ok then 0 else 1)
  }

  opaque ghost predicate WriteOutputsSummaryFields(
    append: bool,
    outputs: seq<BenchWorld.Path>,
    input: BenchWorld.Bytes,
    preFs: BenchWorld.FileSystem,
    preProps: map<string, string>,
    preNow: int,
    preCredentials: BenchWorld.ProcessCredentials,
    preTrustedFilesystem: (BenchWorld.TrustedFilesystemRequest) -> BenchWorld.TrustedFilesystemResult,
    fs2: BenchWorld.FileSystem,
    stderr: BenchWorld.Bytes,
    exit: int
  )
    decreases |outputs|
  {
    if |outputs| == 0 then
      fs2 == preFs && stderr == [] && exit == 0
    else
      exists prefixFs: BenchWorld.FileSystem, prefixErr: BenchWorld.Bytes, prefixExit: int,
        stepErr: BenchWorld.Bytes, stepExit: int
        {:trigger WriteOutputsSummaryFields(append, outputs[..|outputs| - 1], input, preFs, preProps,
                                             preNow, preCredentials, preTrustedFilesystem, prefixFs, prefixErr, prefixExit),
        WriteOneSummaryFields(append, outputs[|outputs| - 1], input, prefixFs, preProps,
                              preNow, preCredentials, preTrustedFilesystem, fs2, stepErr, stepExit)} ::
        WriteOutputsSummaryFields(outputs := outputs[..|outputs| - 1], append := append,
                                  input := input, preFs := preFs, preProps := preProps, preNow := preNow,
                                  preCredentials := preCredentials, preTrustedFilesystem := preTrustedFilesystem,
                                  fs2 := prefixFs, stderr := prefixErr, exit := prefixExit) &&
        WriteOneSummaryFields(append, outputs[|outputs| - 1], input, prefixFs, preProps,
                              preNow, preCredentials, preTrustedFilesystem, fs2, stepErr, stepExit) &&
        stderr == prefixErr + stepErr &&
        exit == (if prefixExit == 0 && stepExit == 0 then 0 else 1)
  }

  function Command(raw: Schema.TeeCmdRaw): Schema.TeeCmd
  {
    var mode :=
      if raw.seenHelp && (!raw.seenVersion || raw.helpTokenIndex <= raw.versionTokenIndex) then
        Schema.ModeHelp
      else if raw.seenVersion then
        Schema.ModeVersion
      else
        Schema.ModeRun;
    Schema.TeeCmd(mode, raw.seenAppend, raw.seenIgnoreInterrupts, raw.operands)
  } by method {
    var mode :=
      if raw.seenHelp && (!raw.seenVersion || raw.helpTokenIndex <= raw.versionTokenIndex) then
        Schema.ModeHelp
      else if raw.seenVersion then
        Schema.ModeVersion
      else
        Schema.ModeRun;
    return Schema.TeeCmd(mode, raw.seenAppend, raw.seenIgnoreInterrupts, raw.operands);
  }

  opaque twostate predicate PreparedSummary(raw: Schema.TeeCmdRaw, io: BenchIO.IO, exit: int, plannedStdout: StreamWorld.Bytes, plannedStderr: StreamWorld.Bytes)
    reads io.fsRegion, io.stdinRegion
  {
    var cmd := Command(raw);
    if cmd.mode == Schema.ModeHelp then
      io.fs() == old(io.fs()) &&
      io.stdin() == old(io.stdin()) &&
      plannedStdout == old(io.stdout()) + Spec.HelpTextSpec() &&
      plannedStderr == old(io.stderr()) &&
      exit == 0
    else if cmd.mode == Schema.ModeVersion then
      io.fs() == old(io.fs()) &&
      io.stdin() == old(io.stdin()) &&
      plannedStdout == old(io.stdout()) + Spec.VersionTextSpec() &&
      plannedStderr == old(io.stderr()) &&
      exit == 0
    else
      var read := IOContract.ObservedReadStdinResultFields(old(io.stdin()), old(io.trustedStreams()));
      var input := IOContract.ReadResultData(read);
      exists errOut: BenchWorld.Bytes, writeExit: int ::
        WriteOutputsSummaryFields(cmd.append, cmd.outputs, input, old(io.fs()), old(io.props()),
                                  old(io.now()), old(io.credentials()), old(io.trustedFilesystem()),
                                  io.fs(), errOut, writeExit) &&
        io.stdin() == IOContract.ObservedReadStdinRemainingFields(old(io.stdin()), old(io.trustedStreams())) &&
        plannedStdout == old(io.stdout()) + input &&
        plannedStderr == old(io.stderr()) + errOut +
          (if read.Ok? then [] else Spec.StdinReadError(IOContract.ResultErrno(read))) &&
        exit == (if read.Ok? then writeExit else 1)
  }

  opaque twostate predicate CoreSummary(raw: Schema.TeeCmdRaw, io: BenchIO.IO, exit: int)
    reads io.Footprint()
  {
    exists output: StreamWorld.Bytes, diagnostics: StreamWorld.Bytes, normalExit: int ::
      PreparedSummary(raw, io, normalExit, old(io.stdout()) + output, old(io.stderr()) + diagnostics) &&
      Spec.EmissionFields(raw, old(io.stdout()), old(io.stderr()), io.stdout(), io.stderr(),
                          io.trustedStreams(), output, diagnostics, normalExit, exit)
  }

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

  method GetReadErrnoText(err: BenchWorld.IOError) returns (text: string)
    ensures text == Spec.ReadErrnoTextSpec(err)
  {
    text := Spec.ReadErrnoTextSpec(err);
  }

  method GetWriteErrnoText(err: int, io: BenchIO.IO) returns (text: string)
    ensures text == Spec.WriteErrnoTextSpec(err)
  {
    text := io.GetCLocaleErrnoText(err);
  }

  method GetReadErrorMessage(path: BenchWorld.Path, err: BenchWorld.IOError) returns (msg: BenchWorld.Bytes)
    ensures msg == Text.ReadErrorMessageSpec(path, err)
  {
    msg := Text.ReadErrorMessageSpec(path, err);
  }

  method GetWriteErrorMessage(path: BenchWorld.Path, err: int, io: BenchIO.IO) returns (msg: BenchWorld.Bytes)
    ensures msg == Spec.WriteErrorMessageSpec(path, err)
  {
    var reason := GetWriteErrnoText(err, io);
    msg := Text.WriteErrorMessageText(path, reason);
  }

  method WriteOne(
    append: bool,
    path: BenchWorld.Path,
    input: BenchWorld.Bytes,
    io: BenchIO.IO
  ) returns (stderr: BenchWorld.Bytes, exit: int)
    modifies io.fsRegion
    ensures WriteOneSummaryFields(append, path, input, old(io.fs()), old(io.props()), old(io.now()),
                                  old(io.credentials()), old(io.trustedFilesystem()), io.fs(), stderr, exit)
  {
    hide *;
    reveal WriteOneSummaryFields();
    ghost var beforeFs := io.fs();
    ghost var beforeNow := io.now();
    var result: BenchWorld.IOResult<BenchWorld.WriteReceipt>;
    if append {
      result := io.AppendFile(path, input);
    } else {
      reveal BenchWorld.CREATE_FILE_MODE;
      result := io.WriteFile(path, input);
    }
    if result.Err? {
      stderr := GetWriteErrorMessage(path, IOContract.ResultErrno(result), io);
      exit := 1;
    } else {
      stderr := [];
      exit := 0;
    }
  }

  method WriteOutputs(
    append: bool,
    outputs: seq<BenchWorld.Path>,
    input: BenchWorld.Bytes,
    io: BenchIO.IO
  ) returns (stderr: BenchWorld.Bytes, exit: int)
    modifies io.fsRegion
    ensures WriteOutputsSummaryFields(append, outputs, input, old(io.fs()), old(io.props()), old(io.now()),
                                      old(io.credentials()), old(io.trustedFilesystem()), io.fs(), stderr, exit)
    decreases |outputs|
  {
    hide *;
    reveal WriteOutputsSummaryFields();
    if |outputs| == 0 {
      stderr := [];
      exit := 0;
    } else {
      var prefixErr, prefixExit := WriteOutputs(append, outputs[..|outputs| - 1], input, io);
      var stepErr, stepExit := WriteOne(append, outputs[|outputs| - 1], input, io);
      stderr := prefixErr + stepErr;
      exit := if prefixExit == 0 && stepExit == 0 then 0 else 1;
    }
  }

  method {:isolate_assertions} Prepare(raw: Schema.TeeCmdRaw, io: BenchIO.IO) returns (exit: int, plannedStdout: StreamWorld.Bytes, plannedStderr: StreamWorld.Bytes)
    modifies io.fsRegion, io.stdinRegion
    ensures PreparedSummary(raw, io, exit, old(io.stdout()) + plannedStdout, old(io.stderr()) + plannedStderr)
    decreases *
  {
    hide *;
    reveal PreparedSummary();
    ghost var emissionBeforeOut := io.stdout();
    ghost var emissionBeforeErr := io.stderr();
    plannedStdout := [];
    plannedStderr := [];
    ghost var preFs := io.fs();
    ghost var preStdin := io.stdin();
    ghost var preStdout := (emissionBeforeOut + plannedStdout);
    ghost var preStderr := (emissionBeforeErr + plannedStderr);
    ghost var preNow := io.now();
    ghost var preProps := io.props();
    ghost var preCredentials := io.credentials();
    ghost var preTrustedFilesystem := io.trustedFilesystem();
    var cmd := Command(raw);
    match cmd.mode
    case ModeHelp =>
      var out := GetHelpText();
      plannedStdout := plannedStdout + (out);
      exit := 0;
      assert io.fs() == preFs;
      assert io.stdin() == preStdin;
      assert (emissionBeforeOut + plannedStdout) == preStdout + Spec.HelpTextSpec();
      assert (emissionBeforeErr + plannedStderr) == preStderr;
      return;
    case ModeVersion =>
      var out := GetVersionText();
      plannedStdout := plannedStdout + (out);
      exit := 0;
      assert io.fs() == preFs;
      assert io.stdin() == preStdin;
      assert (emissionBeforeOut + plannedStdout) == preStdout + Spec.VersionTextSpec();
      assert (emissionBeforeErr + plannedStderr) == preStderr;
      return;
    case ModeRun =>
      var read := io.ReadStdin();
      var input := IOContract.ReadResultData(read);
      var errOut, writeExit := WriteOutputs(cmd.append, cmd.outputs, input, io);
      var diagnostics := errOut;
      if read.Err? {
        var reason := io.GetCLocaleErrnoText(IOContract.ResultErrno(read));
        diagnostics := diagnostics + Text.StdinReadErrorText(reason);
      }
      plannedStdout := plannedStdout + (input);
      plannedStderr := plannedStderr + (diagnostics);
      exit := if read.Ok? then writeExit else 1;
      assert WriteOutputsSummaryFields(cmd.append, cmd.outputs, input, preFs, preProps, preNow,
                                       preCredentials, preTrustedFilesystem, io.fs(), errOut, writeExit);
      assert io.stdin() == IOContract.ObservedReadStdinRemainingFields(preStdin, io.trustedStreams());
      assert (emissionBeforeOut + plannedStdout) == preStdout + input;
      assert (emissionBeforeErr + plannedStderr) == preStderr + diagnostics;
      assert diagnostics == errOut + (if read.Ok? then []
        else Spec.StdinReadError(IOContract.ResultErrno(read))) by {
        reveal Spec.StdinReadError();
      }
      assert exists errors: BenchWorld.Bytes, status: int ::
        WriteOutputsSummaryFields(cmd.append, cmd.outputs, input, preFs, preProps,
          preNow, preCredentials, preTrustedFilesystem, io.fs(), errors, status) &&
        plannedStderr == errors + (if read.Ok? then []
          else Spec.StdinReadError(IOContract.ResultErrno(read))) &&
        exit == (if read.Ok? then status else 1) by {
        ghost var errors := errOut;
        ghost var status := writeExit;
      }
  }


  method Flush(raw: Schema.TeeCmdRaw, output: StreamWorld.Bytes, diagnostics: StreamWorld.Bytes,
               normalExit: int, io: BenchIO.IO) returns (exit: int)
    modifies io.stdoutRegion, io.stderrRegion
    ensures Spec.EmissionFields(raw, old(io.stdout()), old(io.stderr()), io.stdout(), io.stderr(),
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
      finalDiagnostics := diagnostics + Text.WriteErrorText(raw, reason);
    }
    assert finalDiagnostics == diagnostics + (if outErr == 0 then []
      else Text.WriteErrorText(raw, StreamContract.CLocaleErrnoTextResult(outErr)));
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
    assert Spec.EmissionOutcomeFields(raw, old(io.stdout()), old(io.stderr()), io.stdout(), io.stderr(),
      io.trustedStreams(), output, diagnostics, normalExit, exit, committed, outErr, errCommitted, errErr);
  }

  method RunCore(raw: Schema.TeeCmdRaw, io: BenchIO.IO) returns (exit: int)
    modifies io.fsRegion, io.stdinRegion, io.stdoutRegion, io.stderrRegion
    ensures CoreSummary(raw, io, exit)
    decreases *
  {
    var normalExit, output, diagnostics := Prepare(raw, io);
    ghost var beforeOut := io.stdout();
    ghost var beforeErr := io.stderr();
    exit := Flush(raw, output, diagnostics, normalExit, io);
    assert exists plannedOut: StreamWorld.Bytes, plannedErr: StreamWorld.Bytes, preparedExit: int ::
      PreparedSummary(raw, io, preparedExit, beforeOut + plannedOut, beforeErr + plannedErr) &&
      Spec.EmissionFields(raw, beforeOut, beforeErr, io.stdout(), io.stderr(),
        io.trustedStreams(), plannedOut, plannedErr, preparedExit, exit) by {
      hide *;
      ghost var plannedOut := output;
      ghost var plannedErr := diagnostics;
      ghost var preparedExit := normalExit;
    }
    assert CoreSummary(raw, io, exit) by {
      hide *;
      reveal CoreSummary();
    }
  }
}
