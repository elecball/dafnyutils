include "../../core/Utf8.dfy"
include "../../core/World.dfy"
include "ReadlinkSpec.dfy"
include "../../core/Errno.dfy"
include "../../core/IO.dfy"
include "ReadlinkSchema.dfy"
include "ReadlinkContextProof.dfy"

module ReadlinkCore {
  import StreamWorld = BenchWorld
  import StreamContract = IOContract

  import Errno = Errnos
  import Result = Results
  import BenchIO
  import Utf8 = Utf8Semantics
  import IOContract
  import BenchWorld
  import Schema = ReadlinkSchema
  import Spec = ReadlinkSpec
  import Context = ReadlinkContextProof

  method ComputeNeedsShellQuote(path: BenchWorld.Path) returns (needs: bool)
    ensures needs == Spec.NeedsShellQuoteSpec(path)
  {
    needs := |path| == 0;
    var i := 0;
    while i < |path|
      invariant 0 <= i <= |path|
      invariant needs ==> |path| == 0 || exists j :: 0 <= j < i && Spec.ShellQuoteTriggerSpec(path[j])
      invariant !needs ==> |path| != 0 && forall j :: 0 <= j < i ==> !Spec.ShellQuoteTriggerSpec(path[j])
      decreases |path| - i
    {
      var trigger := Spec.ShellQuoteTriggerSpec(path[i]);
      if trigger {
        assert Spec.ShellQuoteTriggerSpec(path[i]);
        needs := true;
      }
      i := i + 1;
    }
    assert i == |path|;
  }

  ghost predicate ReadOneSummaryFields(
    cmd: Schema.ReadlinkCmd,
    path: BenchWorld.Path,
    fs: BenchWorld.FileSystem,
    cwd: BenchWorld.Path,
    hadError: bool,
    out: BenchWorld.Bytes,
    errOut: BenchWorld.Bytes
  )
  {
    Spec.ReadObservationRelation(cmd, fs, cwd, path, Spec.ReadlinkResultFieldsSpec(cmd, fs, cwd, path)) &&
    match Spec.ReadlinkResultFieldsSpec(cmd, fs, cwd, path)
    case Ok(target) =>
      !hadError &&
      out == Utf8.Encode(target) + Spec.OutputDelimiterSpec(cmd) &&
      errOut == ""
    case Err(err) =>
      hadError &&
      out == "" &&
      (if cmd.verbose then Spec.ErrorMessageMatchesSpec(path, err, errOut) else errOut == "")
  }

  ghost predicate RunFilesSummaryFields(
    cmd: Schema.ReadlinkCmd,
    files: seq<BenchWorld.Path>,
    fs: BenchWorld.FileSystem,
    cwd: BenchWorld.Path,
    hadError: bool,
    out: BenchWorld.Bytes,
    errOut: BenchWorld.Bytes
  )
    decreases |files|
  {
    if |files| == 0 then
      !hadError && out == "" && errOut == ""
    else
      exists prefixError: bool, prefixOut: BenchWorld.Bytes, prefixErrOut: BenchWorld.Bytes
        {:trigger RunFilesSummaryFields(cmd, files[..|files| - 1], fs, cwd, prefixError, prefixOut, prefixErrOut)} ::
        RunFilesSummaryFields(cmd, files[..|files| - 1], fs, cwd, prefixError, prefixOut, prefixErrOut) &&
        exists stepError: bool, stepOut: BenchWorld.Bytes, stepErrOut: BenchWorld.Bytes
          {:trigger ReadOneSummaryFields(Schema.WithNativeReadOffset(cmd,files[..|files|-1]), files[|files| - 1], fs, cwd, stepError, stepOut, stepErrOut)} ::
          ReadOneSummaryFields(Schema.WithNativeReadOffset(cmd,files[..|files|-1]), files[|files| - 1], fs, cwd, stepError, stepOut, stepErrOut) &&
          hadError == (prefixError || stepError) &&
          out == prefixOut + stepOut &&
          errOut == prefixErrOut + stepErrOut
  }

  lemma RunFilesSummaryAppend(
    cmd: Schema.ReadlinkCmd,
    files: seq<BenchWorld.Path>,
    path: BenchWorld.Path,
    fs: BenchWorld.FileSystem,
    cwd: BenchWorld.Path,
    prefixError: bool,
    prefixOut: BenchWorld.Bytes,
    prefixErrOut: BenchWorld.Bytes,
    stepError: bool,
    stepOut: BenchWorld.Bytes,
    stepErrOut: BenchWorld.Bytes
  )
    requires RunFilesSummaryFields(cmd, files, fs, cwd, prefixError, prefixOut, prefixErrOut)
    requires ReadOneSummaryFields(Schema.WithNativeReadOffset(cmd,files), path, fs, cwd, stepError, stepOut, stepErrOut)
    ensures RunFilesSummaryFields(
              cmd,
              files + [path],
              fs,
              cwd,
              prefixError || stepError,
              prefixOut + stepOut,
              prefixErrOut + stepErrOut
            )
  {
    assert |files + [path]| == |files| + 1;
    assert (files + [path])[..|files + [path]| - 1] == files;
    assert (files + [path])[|files + [path]| - 1] == path;
  }

  opaque twostate predicate PreparedSummary(raw: Schema.ReadlinkCmdRaw, io: BenchIO.IO, exit: int, plannedStdout: StreamWorld.Bytes, plannedStderr: StreamWorld.Bytes)
    reads io.directoryStateRegion,io.fsRegion,io.cwdRegion
  {
    var cmd := Schema.WithNativeFailures(Schema.Command(raw), old(io.trustedNativeFailures()),old(io.cwdContext()));
    io.directoryModel() == old(io.directoryModel()) &&
    io.cwdContext() == Schema.FinalNativeContext(cmd,old(io.cwdContext())) &&
    if cmd.mode == Schema.ModeHelp then
      plannedStdout == [] + Spec.HelpTextSpec() &&
      plannedStderr == [] &&
      exit == 0
    else if cmd.mode == Schema.ModeVersion then
      plannedStdout == [] + Spec.VersionTextSpec() &&
      plannedStderr == [] &&
      exit == 0
    else if |cmd.operands| == 0 then
      plannedStdout == [] &&
      plannedStderr == [] + Spec.MissingOperandMessageSpec() &&
      exit == 1
    else if cmd.mode == Schema.ModeUnsupportedCanonicalize then
      plannedStdout == [] &&
      plannedStderr == [] + Spec.UnsupportedCanonicalizeMessageSpec() &&
      exit == 1
    else
      exists hadError: bool, out: BenchWorld.Bytes, errOut: BenchWorld.Bytes ::
        RunFilesSummaryFields(
          cmd,
          cmd.operands,
          old(io.fs()),
          old(io.cwd()),
          hadError,
          out,
          errOut
        ) &&
        plannedStdout == [] + out &&
        plannedStderr == [] + Spec.InitialWarningSpec(cmd) + errOut &&
        exit == (if hadError then 1 else 0)
  }

  twostate predicate CoreSummary(raw: Schema.ReadlinkCmdRaw, io: BenchIO.IO, exit: int)
    reads io.Footprint()
  {
    exists output: StreamWorld.Bytes, diagnostics: StreamWorld.Bytes, normalExit: int ::
      PreparedSummary(raw, io, normalExit, output, diagnostics) &&
      Spec.EmissionFields(old(io.stdout()), old(io.stderr()), io.stdout(), io.stderr(),
                          io.trustedStreams(), output, diagnostics, normalExit, exit)
  }

  method {:vcs_split_on_every_assert} Prepare(raw: Schema.ReadlinkCmdRaw, io: BenchIO.IO) returns (exit: int, plannedStdout: StreamWorld.Bytes, plannedStderr: StreamWorld.Bytes)
    modifies io.directoryStateRegion
    ensures PreparedSummary(raw, io, exit, plannedStdout, plannedStderr)
    decreases *
  {

    hide *;
    reveal PreparedSummary(),Schema.Command(),Schema.WithNativeFailures(),Schema.WithNativeReadOffset();
    reveal Schema.FinalNativeContext(),Spec.OutputDelimiterSpec();
    ghost var emissionBeforeOut: StreamWorld.Bytes := [];
    ghost var emissionBeforeErr: StreamWorld.Bytes := [];
    plannedStdout := [];
    plannedStderr := [];
    ghost var preFs := io.fs();
    ghost var preCwd := io.cwd();
    ghost var preContext := io.cwdContext();
    ghost var preModel := io.directoryModel();
    ghost var preStdout := (emissionBeforeOut + plannedStdout);
    ghost var preStderr := (emissionBeforeErr + plannedStderr);
    var cmd := Schema.WithNativeFailures(Schema.Command(raw), io.trustedNativeFailures(),preContext);
    assert Schema.NativeReadCount([]) == 0 by { reveal Schema.NativeReadCount(); }
    if cmd.mode == Schema.ModeHelp {
      var out := Spec.HelpTextSpec();
      plannedStdout := plannedStdout + (out);
      exit := 0;
      assert PreparedSummary(raw, io, exit, emissionBeforeOut + plannedStdout, emissionBeforeErr + plannedStderr);
      return;
    }

    if cmd.mode == Schema.ModeVersion {
      var out := Spec.VersionTextSpec();
      plannedStdout := plannedStdout + (out);
      exit := 0;
      assert PreparedSummary(raw, io, exit, emissionBeforeOut + plannedStdout, emissionBeforeErr + plannedStderr);
      return;
    }

    if |cmd.operands| == 0 {
      var err := Spec.MissingOperandMessageSpec();
      plannedStderr := plannedStderr + (err);
      exit := 1;
      assert PreparedSummary(raw, io, exit, emissionBeforeOut + plannedStdout, emissionBeforeErr + plannedStderr);
      return;
    }

    if cmd.mode == Schema.ModeUnsupportedCanonicalize {
      var err := Spec.UnsupportedCanonicalizeMessageSpec();
      plannedStderr := plannedStderr + (err);
      exit := 1;
      assert PreparedSummary(raw, io, exit, emissionBeforeOut + plannedStdout, emissionBeforeErr + plannedStderr);
      return;
    }

    var hadError := false;
    var out: BenchWorld.Bytes := "";
    var errOut: BenchWorld.Bytes := "";
    var i := 0;
    assert RunFilesSummaryFields(cmd, [], preFs, preCwd, false, "", "") by {
      reveal RunFilesSummaryFields();
    }
    while i < |cmd.operands|
      invariant 0 <= i <= |cmd.operands|
      invariant (emissionBeforeOut + plannedStdout) == preStdout
      invariant (emissionBeforeErr + plannedStderr) == preStderr
      invariant RunFilesSummaryFields(cmd, cmd.operands[..i], preFs, preCwd, hadError, out, errOut)
      invariant io.cwdContext() == preContext.(ordinal := preContext.ordinal+Schema.NativeReadCount(cmd.operands[..i]))
      invariant io.directoryModel() == preModel
      decreases *
    {
      var oldI := i;
      assert oldI < |cmd.operands|;
      var path := cmd.operands[i];
      ghost var stepCmd := Schema.WithNativeReadOffset(cmd,cmd.operands[..i]);
      ghost var beforeRead := io.cwdContext();
      assert beforeRead == stepCmd.nativeReads.context;
      var prefixError := hadError;
      var prefixOut := out;
      var prefixErrOut := errOut;
      var stepError := false;
      var stepOut: BenchWorld.Bytes := "";
      var stepErrOut: BenchWorld.Bytes := "";
      var r: BenchWorld.IOResult<BenchWorld.Path>;
      if path == "" {
        r := Result.Err(BenchWorld.NoSuchFile);
      } else {
        r := io.ReadLinkAtCwd(path);
        assert IOContract.ReadLinkAtCwdSpec(preFs, beforeRead, io.trustedNativeFailures(), path, r);
      }
      assert r == Spec.ReadlinkResultFieldsSpec(stepCmd, preFs, preCwd, path) by {
        reveal Spec.ReadlinkResultFieldsSpec(),IOContract.ReadLinkAtCwdSpec();
      }
      assert Spec.ReadObservationRelation(stepCmd, preFs, preCwd, path, r) by {
        reveal Spec.ReadObservationRelation();
      }
      match r {
        case Ok(target) =>
          stepError := false;
          var delimiter := Spec.OutputDelimiterSpec(cmd);
          stepOut := Utf8.Encode(target) + delimiter;
          stepErrOut := "";
        case Err(err) =>
          stepError := true;
          stepOut := "";
          if cmd.verbose {
            stepErrOut := Spec.ErrorMessageSpec(path, err);
          } else {
            stepErrOut := "";
          }
      }
      assert ReadOneSummaryFields(stepCmd, path, preFs, preCwd, stepError, stepOut, stepErrOut) by {
        reveal ReadOneSummaryFields(),Spec.ErrorMessageMatchesSpec();
      }
      hadError := prefixError || stepError;
      out := prefixOut + stepOut;
      errOut := prefixErrOut + stepErrOut;
      RunFilesSummaryAppend(
        cmd,
        cmd.operands[..i],
        path,
        preFs,
        preCwd,
        prefixError,
        prefixOut,
        prefixErrOut,
        stepError,
        stepOut,
        stepErrOut
      );
      i := oldI + 1;
      Context.ReadCountSnoc(cmd.operands[..oldI],path);
      assert cmd.operands[..i] == cmd.operands[..oldI]+[path];
      assert io.cwdContext() == preContext.(ordinal := preContext.ordinal+
                                Schema.NativeReadCount(cmd.operands[..i])) by {
        if path != "" { reveal IOContract.CwdContextReadStepFields(); }
      }
      assert |cmd.operands| - i < |cmd.operands| - oldI;
      assert cmd.operands[..i] == cmd.operands[..i - 1] + [cmd.operands[i - 1]];
      assert RunFilesSummaryFields(cmd, cmd.operands[..i], preFs, preCwd, hadError, out, errOut);
    }
    assert cmd.operands[..i] == cmd.operands;
    plannedStdout := plannedStdout + (out);
    var warning := Spec.InitialWarningSpec(cmd);
    plannedStderr := plannedStderr + (warning + errOut);
    exit := if hadError then 1 else 0;
    assert PreparedSummary(raw, io, exit, emissionBeforeOut + plannedStdout, emissionBeforeErr + plannedStderr) by {
      hide *;
      reveal PreparedSummary(),Schema.FinalNativeContext();
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

  method RunCore(raw: Schema.ReadlinkCmdRaw, io: BenchIO.IO) returns (exit: int)
    modifies io.stdoutRegion, io.stderrRegion,io.directoryStateRegion
    ensures CoreSummary(raw, io, exit)
    decreases *
  {
    var normalExit, output, diagnostics := Prepare(raw, io);
    exit := Flush(output, diagnostics, normalExit, io);
  }
}
