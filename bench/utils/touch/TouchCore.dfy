include "TouchTextCore.dfy"
include "../../core/Errno.dfy"
include "../../core/World.dfy"
include "../../core/IO.dfy"
include "../../core/Utf8.dfy"
include "TouchSchema.dfy"
include "TouchSpec.dfy"

module TouchCore {
  import Text = TouchTextCore
  import StreamWorld = BenchWorld
  import StreamContract = IOContract

  import Errno = Errnos
  import BenchIO
  import IOContract
  import BenchWorld
  import Utf8 = TouchUtf8Core
  import Schema = TouchSchema
  import Spec = TouchSpec


  ghost predicate SetPathTimesSummaryFields(
    observations: (BenchWorld.TrustedFilesystemRequest) -> BenchWorld.TrustedFilesystemResult,
    path: BenchWorld.Path,
    followSymlink: bool,
    selection: Schema.TimeSelection,
    source: Schema.TimeSource,
    preFs: BenchWorld.FileSystem,
    preNow: int,
    fs2: BenchWorld.FileSystem,
    ok: bool,
    err: int
  )
  {
    Spec.SetPathTimesSpecFields(
      observations, path, followSymlink, selection, source,
      preFs, preNow, fs2, ok, err
    )
  }

  ghost predicate SetStdoutTimesSummaryFields(
    nativeFailures: (BenchWorld.NativeFailureRequest) -> int,
    selection: Schema.TimeSelection,
    source: Schema.TimeSource,
    preNow: int,
    beforeTarget: BenchWorld.StdoutTimestampState,
    afterTarget: BenchWorld.StdoutTimestampState,
    ok: bool,
    err: int
  )
  {
    Spec.SetStdoutTimesSpecFields(nativeFailures,
      selection, source, preNow, beforeTarget, afterTarget, ok, err
    )
  }

  opaque ghost predicate RunStepSummaryFields(
    nativeFailures: (BenchWorld.NativeFailureRequest) -> int,
    observations: (BenchWorld.TrustedFilesystemRequest) -> BenchWorld.TrustedFilesystemResult,
    path: BenchWorld.Path,
    noCreate: bool,
    followSymlink: bool,
    selection: Schema.TimeSelection,
    source: Schema.TimeSource,
    preFs: BenchWorld.FileSystem,
    preNow: int,
    preStdout: BenchWorld.Bytes,
    preStdoutTarget: BenchWorld.StdoutTimestampState,
    fs2: BenchWorld.FileSystem,
    stdout2: BenchWorld.Bytes,
    stdoutTarget2: BenchWorld.StdoutTimestampState,
    hadError: bool,
    errOut: BenchWorld.Bytes
  )
  {
    if path == "-" then
      fs2 == preFs &&
      stdout2 == preStdout &&
      exists okStdout: bool, stdoutErr: int ::
        SetStdoutTimesSummaryFields(nativeFailures,
          selection, source, preNow, preStdoutTarget, stdoutTarget2,
          okStdout, stdoutErr
        ) &&
        hadError == !okStdout &&
        errOut == (if okStdout then [] else Spec.StdoutErrorMessageSpec(stdoutErr))
    else
      stdout2 == preStdout &&
      stdoutTarget2 == preStdoutTarget &&
      exists found: bool, existsErr: int ::
        IOContract.TrustedPathExistsContractFields(
          observations, preFs, path, followSymlink, found, existsErr
        ) &&
        if found then
          exists okSet: bool, setErr: int ::
            SetPathTimesSummaryFields(
              observations, path, followSymlink, selection, source,
              preFs, preNow, fs2, okSet, setErr
            ) &&
            hadError == !okSet &&
            errOut == (if okSet then [] else Spec.TouchErrorMessageSpec(path, setErr))
        else if noCreate then
          fs2 == preFs &&
          hadError == (existsErr != Errno.ENOENT) &&
          errOut == (if existsErr == Errno.ENOENT then [] else Spec.TouchErrorMessageSpec(path, existsErr))
        else if !followSymlink then
          fs2 == preFs &&
          hadError == true &&
          errOut == Spec.SetTimesErrorMessageSpec(path, existsErr)
        else
          exists okCreate: bool, createErr: int, createFs: BenchWorld.FileSystem ::
            IOContract.TrustedCreateFileContractFields(
              observations, preFs, preNow, path,
              okCreate, createErr, createFs
            ) &&
            if okCreate then
              if source == Schema.TimeSourceCurrent && selection == Schema.TimeBoth then
                fs2 == createFs &&
                hadError == false &&
                errOut == []
              else
                exists okSet: bool, setErr: int ::
                  SetPathTimesSummaryFields(
                    observations, path, followSymlink, selection, source,
                    createFs, preNow, fs2, okSet, setErr
                  ) &&
                  hadError == !okSet &&
                  errOut == (if okSet then [] else Spec.TouchErrorMessageSpec(path, setErr))
            else
              fs2 == createFs &&
              hadError == true &&
              errOut == Spec.TouchErrorMessageSpec(path, createErr)
  }

  opaque ghost predicate RunFilesSummaryFields(
    nativeFailures: (BenchWorld.NativeFailureRequest) -> int,
    observations: (BenchWorld.TrustedFilesystemRequest) -> BenchWorld.TrustedFilesystemResult,
    files: seq<BenchWorld.Path>,
    noCreate: bool,
    followSymlink: bool,
    selection: Schema.TimeSelection,
    source: Schema.TimeSource,
    preFs: BenchWorld.FileSystem,
    preNow: int,
    preStdout: BenchWorld.Bytes,
    preStdoutTarget: BenchWorld.StdoutTimestampState,
    fs2: BenchWorld.FileSystem,
    stdout2: BenchWorld.Bytes,
    stdoutTarget2: BenchWorld.StdoutTimestampState,
    hadError: bool,
    errOut: BenchWorld.Bytes
  )
    decreases |files|
  {
    if |files| == 0 then
      fs2 == preFs &&
      stdout2 == preStdout &&
      stdoutTarget2 == preStdoutTarget &&
      hadError == false &&
      errOut == []
    else
      exists fs1: BenchWorld.FileSystem, stdout1: BenchWorld.Bytes,
        stdoutTarget1: BenchWorld.StdoutTimestampState,
        prefixError: bool, stepError: bool, prefixOut: BenchWorld.Bytes, stepOut: BenchWorld.Bytes
        {:trigger RunFilesSummaryFields(nativeFailures, observations, files[..|files| - 1], noCreate, followSymlink, selection, source, preFs, preNow, preStdout, preStdoutTarget, fs1, stdout1, stdoutTarget1, prefixError, prefixOut),
        RunStepSummaryFields(nativeFailures, observations, files[|files| - 1], noCreate, followSymlink, selection, source, fs1, preNow, stdout1, stdoutTarget1, fs2, stdout2, stdoutTarget2, stepError, stepOut)} ::
        RunFilesSummaryFields(nativeFailures,
          observations, files[..|files| - 1], noCreate, followSymlink, selection, source,
          preFs, preNow, preStdout, preStdoutTarget,
          fs1, stdout1, stdoutTarget1, prefixError, prefixOut
        ) &&
        RunStepSummaryFields(nativeFailures,
          observations, files[|files| - 1], noCreate, followSymlink, selection, source,
          fs1, preNow, stdout1, stdoutTarget1,
          fs2, stdout2, stdoutTarget2, stepError, stepOut
        ) &&
        hadError == (prefixError || stepError) &&
        errOut == prefixOut + stepOut
  }


  lemma RunFilesSummaryFieldsEmpty(
    nativeFailures: (BenchWorld.NativeFailureRequest) -> int,
    observations: (BenchWorld.TrustedFilesystemRequest) -> BenchWorld.TrustedFilesystemResult,
    noCreate: bool,
    followSymlink: bool,
    selection: Schema.TimeSelection,
    source: Schema.TimeSource,
    preFs: BenchWorld.FileSystem,
    preNow: int,
    preStdout: BenchWorld.Bytes,
    preStdoutTarget: BenchWorld.StdoutTimestampState
  )
    ensures RunFilesSummaryFields(nativeFailures,
              observations, [], noCreate, followSymlink, selection, source,
              preFs, preNow, preStdout, preStdoutTarget,
              preFs, preStdout, preStdoutTarget, false, []
            )
  {
    reveal RunFilesSummaryFields();
  }

  lemma RunFilesSummaryFieldsAppend(
    nativeFailures: (BenchWorld.NativeFailureRequest) -> int,
    observations: (BenchWorld.TrustedFilesystemRequest) -> BenchWorld.TrustedFilesystemResult,
    files: seq<BenchWorld.Path>,
    path: BenchWorld.Path,
    noCreate: bool,
    followSymlink: bool,
    selection: Schema.TimeSelection,
    source: Schema.TimeSource,
    preFs: BenchWorld.FileSystem,
    preNow: int,
    preStdout: BenchWorld.Bytes,
    preStdoutTarget: BenchWorld.StdoutTimestampState,
    fs1: BenchWorld.FileSystem,
    stdout1: BenchWorld.Bytes,
    stdoutTarget1: BenchWorld.StdoutTimestampState,
    fs2: BenchWorld.FileSystem,
    stdout2: BenchWorld.Bytes,
    stdoutTarget2: BenchWorld.StdoutTimestampState,
    prefixError: bool,
    stepError: bool,
    prefixOut: BenchWorld.Bytes,
    stepOut: BenchWorld.Bytes
  )
    requires RunFilesSummaryFields(nativeFailures, observations, files, noCreate, followSymlink, selection, source, preFs, preNow, preStdout, preStdoutTarget, fs1, stdout1, stdoutTarget1, prefixError, prefixOut)
    requires RunStepSummaryFields(nativeFailures, observations, path, noCreate, followSymlink, selection, source, fs1, preNow, stdout1, stdoutTarget1, fs2, stdout2, stdoutTarget2, stepError, stepOut)
    ensures RunFilesSummaryFields(nativeFailures, observations, files + [path], noCreate, followSymlink, selection, source, preFs, preNow, preStdout, preStdoutTarget, fs2, stdout2, stdoutTarget2, prefixError || stepError, prefixOut + stepOut)
  {
    reveal RunFilesSummaryFields();
    assert |files + [path]| > 0;
    assert (files + [path])[..|files + [path]| - 1] == files;
    assert (files + [path])[|files + [path]| - 1] == path;
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

  method GetTouchErrorMessage(path: BenchWorld.Path, err: int, io: BenchIO.IO)
      returns (out: BenchWorld.Bytes)
    ensures out == Spec.TouchErrorMessageSpec(path, err)
  {
    var quoted := io.QuoteafPath(path);
    var errnoText := io.GetCLocaleErrnoText(err);
    out := Utf8.Encode(Spec.TouchErrorMessageSpecPart1()) + quoted
      + Utf8.Encode(Spec.TouchErrorMessageSpecPart2() + errnoText + Spec.TouchErrorMessageSpecPart3());
  }

  method GetReferenceErrorMessage(path: BenchWorld.Path, err: int, io: BenchIO.IO)
      returns (out: BenchWorld.Bytes)
    ensures out == Spec.ReferenceErrorMessageSpec(path, err)
  {
    var quoted := io.QuoteafPath(path);
    var errnoText := io.GetCLocaleErrnoText(err);
    out := Utf8.Encode(Spec.ReferenceErrorMessageSpecPart1()) + quoted
      + Utf8.Encode(Spec.TouchErrorMessageSpecPart2() + errnoText + Spec.TouchErrorMessageSpecPart3());
  }

  method GetSetTimesErrorMessage(path: BenchWorld.Path, err: int, io: BenchIO.IO)
      returns (out: BenchWorld.Bytes)
    ensures out == Spec.SetTimesErrorMessageSpec(path, err)
  {
    var quoted := io.QuoteafPath(path);
    var errnoText := io.GetCLocaleErrnoText(err);
    out := Utf8.Encode(Spec.SetTimesErrorMessageSpecPart1()) + quoted
      + Utf8.Encode(Spec.TouchErrorMessageSpecPart2() + errnoText + Spec.TouchErrorMessageSpecPart3());
  }

  method GetStdoutErrorMessage(err: int, io: BenchIO.IO) returns (out: BenchWorld.Bytes)
    ensures out == Spec.StdoutErrorMessageSpec(err)
  {
    reveal Spec.StdoutErrorMessageSpec();
    var quoted := io.QuoteafPath("-");
    var errnoText := io.GetCLocaleErrnoText(err);
    out := Utf8.Encode(Spec.SetTimesErrorMessageSpecPart1()) + quoted
      + Utf8.Encode(Spec.TouchErrorMessageSpecPart2() + errnoText + Spec.TouchErrorMessageSpecPart3());
  }

  method GetMissingOperandMessage() returns (out: string)
    ensures out == Spec.MissingOperandMessageSpec()
  {
    out := Spec.MissingOperandMessageSpec();
  }

  method GetInvalidTimeMessage(value: string) returns (out: BenchWorld.Bytes)
    ensures out == Spec.InvalidTimeMessageSpec(value)
  {
    out := Text.InvalidTimeMessageSpec(value);
  }

  method GetAmbiguousTimeMessage(value: string) returns (out: BenchWorld.Bytes)
    ensures out == Spec.AmbiguousTimeMessageSpec(value)
  {
    out := Text.AmbiguousTimeMessageSpec(value);
  }

  method GetInvalidDateMessage(value: string) returns (out: BenchWorld.Bytes)
    ensures out == Spec.InvalidDateMessageSpec(value)
  {
    out := Text.InvalidDateMessageSpec(value);
  }

  twostate predicate ResolvedRunSummaryFields(
    cmd: Schema.TouchCmd,
    io: BenchIO.IO,
    exit: int
  , plannedStdout: StreamWorld.Bytes, plannedStderr: StreamWorld.Bytes)
    reads io.fsRegion, io.stdoutTimestampRegion
  {
    exists selection: Schema.TimeSelection, source: Schema.TimeSource ::
      Spec.RequestedSelection(cmd, selection) &&
      Spec.RequestedSourceFields(
        old(io.trustedFilesystem()), cmd, old(io.fs()), old(io.now()),
        old(io.trustedTimeParses()), source
      ) &&
      if |cmd.files| == 0 then
        io.fs() == old(io.fs()) &&
        plannedStdout == old(io.stdout()) &&
        plannedStderr == old(io.stderr()) + Spec.MissingOperandMessageSpec() &&
        exit == 1
      else
        exists hadError: bool, errOut: BenchWorld.Bytes ::
          exit == (if hadError then 1 else 0) &&
          RunFilesSummaryFields(old(io.trustedNativeFailures()),
            old(io.trustedFilesystem()), cmd.files, cmd.noCreate,
            cmd.followSymlink, selection, source,
            old(io.fs()), old(io.now()), old(io.stdout()), old(io.stdoutTimestamp()),
            io.fs(), plannedStdout, io.stdoutTimestamp(), hadError, errOut
          ) &&
          plannedStderr == old(io.stderr()) + errOut
  }

  opaque twostate predicate PreparedSummary(raw: Schema.TouchCmdRaw, io: BenchIO.IO, exit: int, plannedStdout: StreamWorld.Bytes, plannedStderr: StreamWorld.Bytes)
    reads io.fsRegion, io.stdoutTimestampRegion
  {
    var cmd := Schema.Command(raw);
    if cmd.mode == Schema.ModeInvalidTime then
      io.fs() == old(io.fs()) &&
      exit == 1 &&
      plannedStdout == old(io.stdout()) &&
      plannedStderr == old(io.stderr()) + Spec.InvalidTimeMessageSpec(cmd.timeArg)
    else if cmd.mode == Schema.ModeAmbiguousTime then
      io.fs() == old(io.fs()) &&
      exit == 1 &&
      plannedStdout == old(io.stdout()) &&
      plannedStderr == old(io.stderr()) + Spec.AmbiguousTimeMessageSpec(cmd.timeArg)
    else if cmd.mode == Schema.ModeHelp then
      io.fs() == old(io.fs()) &&
      exit == 0 &&
      plannedStdout == old(io.stdout()) + Spec.HelpTextSpec() &&
      plannedStderr == old(io.stderr())
    else if cmd.mode == Schema.ModeVersion then
      io.fs() == old(io.fs()) &&
      exit == 0 &&
      plannedStdout == old(io.stdout()) + Spec.VersionTextSpec() &&
      plannedStderr == old(io.stderr())
    else if cmd.timeArg != "" && Schema.ClassifyTimeWord(cmd.timeArg) == Schema.TimeWordAmbiguous then
      io.fs() == old(io.fs()) &&
      exit == 1 &&
      plannedStdout == old(io.stdout()) &&
      plannedStderr == old(io.stderr()) + Spec.AmbiguousTimeMessageSpec(cmd.timeArg)
    else if cmd.timeArg != "" && Schema.ClassifyTimeWord(cmd.timeArg) == Schema.TimeWordInvalid then
      io.fs() == old(io.fs()) &&
      exit == 1 &&
      plannedStdout == old(io.stdout()) &&
      plannedStderr == old(io.stderr()) + Spec.InvalidTimeMessageSpec(cmd.timeArg)
    else if cmd.hasTimestamp then
      (exists sec: int, nsec: int ::
         IOContract.ParseTimestampContractFields(
           old(io.trustedTimeParses()), cmd.timestampArg, old(io.now()), 0,
           false, sec, nsec
         ) &&
         io.fs() == old(io.fs()) &&
         plannedStdout == old(io.stdout()) &&
         plannedStderr == old(io.stderr()) + Spec.InvalidDateMessageSpec(cmd.timestampArg) &&
         exit == 1) ||
      (Spec.SourceConflict(cmd) &&
       IOContract.TrustedTimeParseResultFields(
         old(io.trustedTimeParses()),
         BenchWorld.TimestampParseRequest(cmd.timestampArg, old(io.now()), 0)).ok &&
       io.fs() == old(io.fs()) &&
       plannedStdout == old(io.stdout()) &&
       plannedStderr == old(io.stderr()) + Spec.SourceConflictMessageSpec() &&
       exit == 1) ||
      ResolvedRunSummaryFields(cmd, io, exit, plannedStdout, plannedStderr)
    else if cmd.hasDate then
      (cmd.hasReference &&
       var observed := old(io.trustedFilesystem())(
         BenchWorld.FilesystemQuery(
           old(io.fs()), cmd.referenceArg, cmd.followSymlink
         )
       );
       observed.postFs == old(io.fs()) && !observed.ok &&
         io.fs() == old(io.fs()) &&
         plannedStdout == old(io.stdout()) &&
         plannedStderr == old(io.stderr()) +
           Spec.ReferenceErrorMessageSpec(cmd.referenceArg, observed.err) &&
         exit == 1) ||
      (Spec.DateParseFailureFields(
         old(io.trustedFilesystem()), cmd, old(io.fs()), old(io.now()),
         old(io.trustedTimeParses())) &&
       io.fs() == old(io.fs()) &&
       plannedStdout == old(io.stdout()) &&
       plannedStderr == old(io.stderr()) + Spec.InvalidDateMessageSpec(cmd.dateArg) &&
       exit == 1) ||
      ResolvedRunSummaryFields(cmd, io, exit, plannedStdout, plannedStderr)
    else if cmd.hasReference then
      (var observed := old(io.trustedFilesystem())(
         BenchWorld.FilesystemQuery(
           old(io.fs()), cmd.referenceArg, cmd.followSymlink
         )
       );
       observed.postFs == old(io.fs()) && !observed.ok &&
         io.fs() == old(io.fs()) &&
         plannedStdout == old(io.stdout()) &&
         plannedStderr == old(io.stderr()) +
           Spec.ReferenceErrorMessageSpec(cmd.referenceArg, observed.err) &&
         exit == 1) ||
      ResolvedRunSummaryFields(cmd, io, exit, plannedStdout, plannedStderr)
    else
      ResolvedRunSummaryFields(cmd, io, exit, plannedStdout, plannedStderr)
  }

  twostate predicate CoreSummary(raw: Schema.TouchCmdRaw, io: BenchIO.IO, exit: int)
    reads io.Footprint()
  {
    exists output: StreamWorld.Bytes, diagnostics: StreamWorld.Bytes, normalExit: int ::
      PreparedSummary(raw, io, normalExit, old(io.stdout()) + output, old(io.stderr()) + diagnostics) &&
      Spec.EmissionFields(old(io.stdout()), old(io.stderr()), io.stdout(), io.stderr(),
                          io.trustedStreams(), output, diagnostics, normalExit, exit)
  }

  method ResolveDateSource(
    cmd: Schema.TouchCmd, selection: Schema.TimeSelection, io: BenchIO.IO
  ) returns (ok: bool, source: Schema.TimeSource, errOut: BenchWorld.Bytes)
    requires cmd.hasDate && !Spec.SourceConflict(cmd)
    requires Spec.RequestedSelection(cmd, selection)
    ensures if ok then
      Spec.RequestedSourceFields(
        io.trustedFilesystem(), cmd, io.fs(), io.now(), io.trustedTimeParses(), source
      ) && errOut == []
    else
      (Spec.DateParseFailureFields(
        io.trustedFilesystem(), cmd, io.fs(), io.now(), io.trustedTimeParses()
      ) && errOut == Spec.InvalidDateMessageSpec(cmd.dateArg)) ||
      (cmd.hasReference &&
       var observed := io.trustedFilesystem()(
         BenchWorld.FilesystemQuery(io.fs(), cmd.referenceArg, cmd.followSymlink));
       observed.postFs == io.fs() && !observed.ok &&
       errOut == Spec.ReferenceErrorMessageSpec(cmd.referenceArg, observed.err))
  {
    ok := false;
    source := Schema.TimeSourceCurrent;
    errOut := [];
    ghost var preFs := io.fs();
    ghost var preNow := io.now();
    ghost var preParses := io.trustedTimeParses();
    ghost var preFilesystemObservations := io.trustedFilesystem();
    var nowSec := io.Now();
    var referenceSec := nowSec;
    var referenceNsec := 0;
    var accessReferenceSec := nowSec;
    var accessReferenceNsec := 0;
    if cmd.hasReference {
      var getFileTimesResult := io.GetFileTimes(cmd.referenceArg, cmd.followSymlink);
      var refOk := getFileTimesResult.Ok?;
      var refAtimeSec := IOContract.ResultValue(getFileTimesResult, BenchWorld.FileTimeStatus(0, 0, 0, 0, false, false, 0, 0, 0)).atimeSec;
      var refAtimeNsec := IOContract.ResultValue(getFileTimesResult, BenchWorld.FileTimeStatus(0, 0, 0, 0, false, false, 0, 0, 0)).atimeNsec;
      var refMtimeSec := IOContract.ResultValue(getFileTimesResult, BenchWorld.FileTimeStatus(0, 0, 0, 0, false, false, 0, 0, 0)).mtimeSec;
      var refMtimeNsec := IOContract.ResultValue(getFileTimesResult, BenchWorld.FileTimeStatus(0, 0, 0, 0, false, false, 0, 0, 0)).mtimeNsec;
      var refIsDir := IOContract.ResultValue(getFileTimesResult, BenchWorld.FileTimeStatus(0, 0, 0, 0, false, false, 0, 0, 0)).isDir;
      var refIsSymlink := IOContract.ResultValue(getFileTimesResult, BenchWorld.FileTimeStatus(0, 0, 0, 0, false, false, 0, 0, 0)).isSymlink;
      var refDevice := IOContract.ResultValue(getFileTimesResult, BenchWorld.FileTimeStatus(0, 0, 0, 0, false, false, 0, 0, 0)).device;
      var refInode := IOContract.ResultValue(getFileTimesResult, BenchWorld.FileTimeStatus(0, 0, 0, 0, false, false, 0, 0, 0)).inode;
      var refLinkCount := IOContract.ResultValue(getFileTimesResult, BenchWorld.FileTimeStatus(0, 0, 0, 0, false, false, 0, 0, 0)).linkCount;
      var refErr := IOContract.ResultErrno(getFileTimesResult);
      if !refOk {
        errOut := GetReferenceErrorMessage(cmd.referenceArg, refErr, io);
        return;
      }
      accessReferenceSec := refAtimeSec;
      accessReferenceNsec := refAtimeNsec;
      referenceSec := refMtimeSec;
      referenceNsec := refMtimeNsec;
    }
    assert Spec.DateReferenceFields(
      preFilesystemObservations, cmd, preFs, preNow,
      referenceSec, referenceNsec
    ) by {
      reveal Spec.DateReferenceFields();
    }
    assert Spec.DateAccessReferenceFields(
      preFilesystemObservations, cmd, preFs, preNow,
      accessReferenceSec, accessReferenceNsec
    );
    var atimeSec := accessReferenceSec;
    var atimeNsec := accessReferenceNsec;
    var mtimeSec := referenceSec;
    var mtimeNsec := referenceNsec;
    if selection != Schema.TimeModify {
      var dateOk;
      var parseDateResult := io.ParseDate(cmd.dateArg, accessReferenceSec, accessReferenceNsec);
      dateOk := parseDateResult.Ok?;
      atimeSec := IOContract.ParsedResultValue(parseDateResult).sec;
      atimeNsec := IOContract.ParsedResultValue(parseDateResult).nsec;
      if !dateOk {
        assert Spec.DateParseFailureFields(
          preFilesystemObservations, cmd, preFs, preNow, preParses
        ) by {
          hide *;
          reveal Spec.DateParseFailureFields(), Spec.RequestedSelection();
          reveal IOContract.ParseDateSpec(), IOContract.ParseDateContractFields();
          var aSec := accessReferenceSec;
          var aNsec := accessReferenceNsec;
          var mSec := referenceSec;
          var mNsec := referenceNsec;
        }
        errOut := Text.InvalidDateMessageSpec(cmd.dateArg);
        return;
      }
    }
    if !cmd.hasReference && selection == Schema.TimeBoth {
      mtimeSec := atimeSec;
      mtimeNsec := atimeNsec;
    } else if selection != Schema.TimeAccess {
      var dateOk;
      var parseDateResult2 := io.ParseDate(cmd.dateArg, referenceSec, referenceNsec);
      dateOk := parseDateResult2.Ok?;
      mtimeSec := IOContract.ParsedResultValue(parseDateResult2).sec;
      mtimeNsec := IOContract.ParsedResultValue(parseDateResult2).nsec;
      if !dateOk {
        assert Spec.DateParseFailureFields(
          preFilesystemObservations, cmd, preFs, preNow, preParses
        ) by {
          hide *;
          reveal Spec.DateParseFailureFields(), Spec.RequestedSelection();
          reveal IOContract.ParseDateSpec(), IOContract.ParseDateContractFields();
          var aSec := accessReferenceSec;
          var aNsec := accessReferenceNsec;
          var mSec := referenceSec;
          var mNsec := referenceNsec;
        }
        errOut := Text.InvalidDateMessageSpec(cmd.dateArg);
        return;
      }
    }
    source := Schema.TimeSourceFixed(atimeSec, atimeNsec, mtimeSec, mtimeNsec);
    assert Spec.RequestedSourceFields(
      preFilesystemObservations, cmd, preFs, preNow, preParses, source
    ) by {
      hide *;
      reveal Spec.RequestedSourceFields(), Spec.RequestedSelection(), Spec.SourceConflict();
      reveal Spec.DateReferenceFields(), Spec.DateAccessReferenceFields();
      reveal IOContract.ParseDateSpec(), IOContract.ParseDateContractFields();
      var aSec := accessReferenceSec;
      var aNsec := accessReferenceNsec;
      var mSec := referenceSec;
      var mNsec := referenceNsec;
    }
    ok := true;
  }

  method Prepare(raw: Schema.TouchCmdRaw, io: BenchIO.IO) returns (exit: int, plannedStdout: StreamWorld.Bytes, plannedStderr: StreamWorld.Bytes)
    modifies io.fsRegion, io.stdoutTimestampRegion
    ensures PreparedSummary(raw, io, exit, old(io.stdout()) + plannedStdout, old(io.stderr()) + plannedStderr)
    decreases *
  {
    ghost var emissionBeforeOut := io.stdout();
    ghost var emissionBeforeErr := io.stderr();
    plannedStdout := [];
    plannedStderr := [];
    ghost var preFs := io.fs();
    ghost var preStdout := (emissionBeforeOut + plannedStdout);
    ghost var preStderr := (emissionBeforeErr + plannedStderr);
    ghost var preNow := io.now();
    ghost var preParses := io.trustedTimeParses();
    ghost var preFilesystemObservations := io.trustedFilesystem();
    var cmd := Schema.Command(raw);
    if cmd.mode == Schema.ModeInvalidTime {
      var err := GetInvalidTimeMessage(cmd.timeArg);
      plannedStderr := plannedStderr + (err);
      exit := 1;
      assert PreparedSummary(raw, io, exit, emissionBeforeOut + plannedStdout, emissionBeforeErr + plannedStderr) by { hide *; reveal PreparedSummary(), Schema.Command(); }
      return;
    }

    if cmd.mode == Schema.ModeAmbiguousTime {
      var err := GetAmbiguousTimeMessage(cmd.timeArg);
      plannedStderr := plannedStderr + (err);
      exit := 1;
      assert PreparedSummary(raw, io, exit, emissionBeforeOut + plannedStdout, emissionBeforeErr + plannedStderr) by { hide *; reveal PreparedSummary(), Schema.Command(); }
      return;
    }

    if cmd.mode == Schema.ModeHelp {
      var out := GetHelpText();
      plannedStdout := plannedStdout + (out);
      exit := 0;
      assert PreparedSummary(raw, io, exit, emissionBeforeOut + plannedStdout, emissionBeforeErr + plannedStderr) by { hide *; reveal PreparedSummary(), Schema.Command(); }
      return;
    }

    if cmd.mode == Schema.ModeVersion {
      var out := GetVersionText();
      plannedStdout := plannedStdout + (out);
      exit := 0;
      assert PreparedSummary(raw, io, exit, emissionBeforeOut + plannedStdout, emissionBeforeErr + plannedStderr) by { hide *; reveal PreparedSummary(), Schema.Command(); }
      return;
    }

    var selection := Spec.RequestedSelectionValue(cmd);
    if cmd.timeArg != "" {
      var timeWord := Schema.ClassifyTimeWord(cmd.timeArg);
      if timeWord == Schema.TimeWordAmbiguous {
        var err := GetAmbiguousTimeMessage(cmd.timeArg);
        plannedStderr := plannedStderr + (err);
        exit := 1;
        assert PreparedSummary(raw, io, exit, emissionBeforeOut + plannedStdout, emissionBeforeErr + plannedStderr) by { hide *; reveal PreparedSummary(), Schema.Command(); }
        return;
      } else if timeWord == Schema.TimeWordInvalid {
        var err := GetInvalidTimeMessage(cmd.timeArg);
        plannedStderr := plannedStderr + (err);
        exit := 1;
        assert PreparedSummary(raw, io, exit, emissionBeforeOut + plannedStdout, emissionBeforeErr + plannedStderr) by { hide *; reveal PreparedSummary(), Schema.Command(); }
        return;
      }
    } else if cmd.touchAtime && !cmd.touchMtime {
      selection := Schema.TimeAccess;
    } else if cmd.touchMtime && !cmd.touchAtime {
      selection := Schema.TimeModify;
    }
    assert Spec.RequestedSelection(cmd, selection);

    var source := Schema.TimeSourceCurrent;
    if cmd.hasTimestamp {
      var nowSec := io.Now();
      var parseTimestampResult := io.ParseTimestamp(cmd.timestampArg, nowSec, 0);
      var timestampOk := parseTimestampResult.Ok?;
      var timestampSec := IOContract.ParsedResultValue(parseTimestampResult).sec;
      var timestampNsec := IOContract.ParsedResultValue(parseTimestampResult).nsec;
      assert IOContract.ParseTimestampContractFields(preParses, cmd.timestampArg, preNow, 0,
        timestampOk, timestampSec, timestampNsec) by {
        hide *; reveal IOContract.ParseTimestampSpec();
      }
      if !timestampOk {
        var err := GetInvalidDateMessage(cmd.timestampArg);
        plannedStderr := plannedStderr + (err);
        exit := 1;
        assert PreparedSummary(raw, io, exit, emissionBeforeOut + plannedStdout, emissionBeforeErr + plannedStderr) by { hide *; reveal PreparedSummary(), Schema.Command(); }
        return;
      }
      if Spec.SourceConflict(cmd) {
        assert IOContract.TrustedTimeParseResultFields(preParses,
          BenchWorld.TimestampParseRequest(cmd.timestampArg, preNow, 0)).ok by {
          hide *; reveal IOContract.ParseTimestampContractFields();
        }
        plannedStderr := plannedStderr + (Spec.SourceConflictMessageSpec());
        exit := 1;
        assert PreparedSummary(raw, io, exit, emissionBeforeOut + plannedStdout, emissionBeforeErr + plannedStderr) by {
          hide *; reveal PreparedSummary(), Schema.Command();
        }
        return;
      }
      source := Schema.TimeSourceFixed(timestampSec, timestampNsec, timestampSec, timestampNsec);
      assert Spec.RequestedSourceFields(
        preFilesystemObservations, cmd, preFs, preNow, preParses, source
      );
    } else if cmd.hasDate {
      var dateOk, dateSource, dateError := ResolveDateSource(cmd, selection, io);
      if !dateOk {
        plannedStderr := plannedStderr + (dateError);
        exit := 1;
        assert PreparedSummary(raw, io, exit, emissionBeforeOut + plannedStdout, emissionBeforeErr + plannedStderr) by {
          hide *; reveal PreparedSummary(), Schema.Command();
        }
        return;
      }
      source := dateSource;
    } else if cmd.hasReference {
      var getFileTimesResult2 := io.GetFileTimes(cmd.referenceArg, cmd.followSymlink);
      var refOk := getFileTimesResult2.Ok?;
      var refAtimeSec := IOContract.ResultValue(getFileTimesResult2, BenchWorld.FileTimeStatus(0, 0, 0, 0, false, false, 0, 0, 0)).atimeSec;
      var refAtimeNsec := IOContract.ResultValue(getFileTimesResult2, BenchWorld.FileTimeStatus(0, 0, 0, 0, false, false, 0, 0, 0)).atimeNsec;
      var refMtimeSec := IOContract.ResultValue(getFileTimesResult2, BenchWorld.FileTimeStatus(0, 0, 0, 0, false, false, 0, 0, 0)).mtimeSec;
      var refMtimeNsec := IOContract.ResultValue(getFileTimesResult2, BenchWorld.FileTimeStatus(0, 0, 0, 0, false, false, 0, 0, 0)).mtimeNsec;
      var refIsDir := IOContract.ResultValue(getFileTimesResult2, BenchWorld.FileTimeStatus(0, 0, 0, 0, false, false, 0, 0, 0)).isDir;
      var refIsSymlink := IOContract.ResultValue(getFileTimesResult2, BenchWorld.FileTimeStatus(0, 0, 0, 0, false, false, 0, 0, 0)).isSymlink;
      var refDevice := IOContract.ResultValue(getFileTimesResult2, BenchWorld.FileTimeStatus(0, 0, 0, 0, false, false, 0, 0, 0)).device;
      var refInode := IOContract.ResultValue(getFileTimesResult2, BenchWorld.FileTimeStatus(0, 0, 0, 0, false, false, 0, 0, 0)).inode;
      var refLinkCount := IOContract.ResultValue(getFileTimesResult2, BenchWorld.FileTimeStatus(0, 0, 0, 0, false, false, 0, 0, 0)).linkCount;
      var refErr := IOContract.ResultErrno(getFileTimesResult2);
      if !refOk {
        var err := GetReferenceErrorMessage(cmd.referenceArg, refErr, io);
        plannedStderr := plannedStderr + (err);
        exit := 1;
        assert IOContract.TrustedFilesystemQueryContractFields(
            preFilesystemObservations, preFs,
            cmd.referenceArg, cmd.followSymlink, false,
            refAtimeSec, refAtimeNsec, refMtimeSec, refMtimeNsec,
            refIsDir, refIsSymlink, refDevice, refInode, refLinkCount, refErr
          );
        assert var observed := preFilesystemObservations(BenchWorld.FilesystemQuery(preFs, cmd.referenceArg, cmd.followSymlink));
          observed.postFs == preFs && !observed.ok && observed.err == refErr by {
          hide *; reveal IOContract.TrustedFilesystemQueryContractFields();
        }
        assert PreparedSummary(raw, io, exit, emissionBeforeOut + plannedStdout, emissionBeforeErr + plannedStderr) by { hide *; reveal PreparedSummary(), Schema.Command(); }
        return;
      }
      assert IOContract.TrustedFilesystemQueryContractFields(
          preFilesystemObservations, preFs,
          cmd.referenceArg, cmd.followSymlink, true,
          refAtimeSec, refAtimeNsec, refMtimeSec, refMtimeNsec,
          refIsDir, refIsSymlink, refDevice, refInode, refLinkCount, refErr
        );
      source := Schema.TimeSourceFixed(refAtimeSec, refAtimeNsec, refMtimeSec, refMtimeNsec);
      assert Spec.SuccessfulReferenceSourceFields(
        preFilesystemObservations, preFs, cmd.referenceArg,
        cmd.followSymlink, source
      ) by {
        reveal Spec.SuccessfulReferenceSourceFields();
      }
      assert Spec.RequestedSourceFields(
        preFilesystemObservations, cmd, preFs, preNow, preParses, source
      );
    }
    assert Spec.RequestedSourceFields(
      preFilesystemObservations, cmd, preFs, preNow, preParses, source
    );

    if |cmd.files| == 0 {
      var err := GetMissingOperandMessage();
      plannedStderr := plannedStderr + (err);
      exit := 1;
      assert ResolvedRunSummaryFields(cmd, io, exit, emissionBeforeOut + plannedStdout, emissionBeforeErr + plannedStderr) by {
        hide *; reveal ResolvedRunSummaryFields();
        assert Spec.RequestedSelection(cmd, selection);
        assert Spec.RequestedSourceFields(
          preFilesystemObservations, cmd, preFs, preNow, preParses, source
        );
      }
      assert PreparedSummary(raw, io, exit, emissionBeforeOut + plannedStdout, emissionBeforeErr + plannedStderr) by { hide *; reveal PreparedSummary(), Schema.Command(); }
      return;
    }

    assert plannedStdout == [] by { hide *; }
    assert preStdout == emissionBeforeOut by { hide *; }
    var hadError, errOut := RunFiles(cmd.files, cmd.noCreate, cmd.followSymlink, selection, source, io);
    plannedStderr := plannedStderr + (errOut);
    exit := if hadError then 1 else 0;
    assert (emissionBeforeErr + plannedStderr) == preStderr + errOut by { hide *; }
    assert RunFilesSummaryFields(io.trustedNativeFailures(),
      preFilesystemObservations, cmd.files, cmd.noCreate,
      cmd.followSymlink, selection, source,
      preFs, preNow, preStdout, old(io.stdoutTimestamp()),
      io.fs(), (emissionBeforeOut + plannedStdout), io.stdoutTimestamp(), hadError, errOut
    ) by { hide *; }
    assert ResolvedRunSummaryFields(cmd, io, exit, emissionBeforeOut + plannedStdout, emissionBeforeErr + plannedStderr) by {
      hide *; reveal ResolvedRunSummaryFields();
      assert Spec.RequestedSelection(cmd, selection);
      assert Spec.RequestedSourceFields(
        preFilesystemObservations, cmd, preFs, preNow, preParses, source
      );
    }
    assert PreparedSummary(raw, io, exit, emissionBeforeOut + plannedStdout, emissionBeforeErr + plannedStderr) by { hide *; reveal PreparedSummary(), Schema.Command(); }
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

  method RunCore(raw: Schema.TouchCmdRaw, io: BenchIO.IO) returns (exit: int)
    modifies io.fsRegion, io.stdoutRegion, io.stderrRegion, io.stdoutTimestampRegion
    ensures CoreSummary(raw, io, exit)
    decreases *
  {
    var normalExit, output, diagnostics := Prepare(raw, io);
    exit := Flush(output, diagnostics, normalExit, io);
  }

  method SetPathTimes(
    path: BenchWorld.Path,
    followSymlink: bool,
    selection: Schema.TimeSelection,
    source: Schema.TimeSource,
    io: BenchIO.IO
  ) returns (ok: bool, err: int)
    modifies io.fsRegion
    ensures SetPathTimesSummaryFields(
              old(io.trustedFilesystem()), path, followSymlink, selection, source,
              old(io.fs()), old(io.now()), io.fs(), ok, err
            )
    decreases *
  {
    ok := false;
    err := 0;
    if source == Schema.TimeSourceCurrent && selection == Schema.TimeBoth {
      var setFileTimesNowResult := io.SetFileTimesNow(path, followSymlink);
      ok := setFileTimesNowResult.Ok?;
      err := IOContract.ResultErrno(setFileTimesNowResult);
      return;
    }
    if source == Schema.TimeSourceCurrent && selection == Schema.TimeAccess {
      var setFileAccessTimeNowResult := io.SetFileAccessTimeNow(path, followSymlink);
      ok := setFileAccessTimeNowResult.Ok?;
      err := IOContract.ResultErrno(setFileAccessTimeNowResult);
      return;
    }
    if source == Schema.TimeSourceCurrent && selection == Schema.TimeModify {
      var setFileModificationTimeNowResult := io.SetFileModificationTimeNow(path, followSymlink);
      ok := setFileModificationTimeNowResult.Ok?;
      err := IOContract.ResultErrno(setFileModificationTimeNowResult);
      return;
    }

    var atimeSec := 0;
    var atimeNsec := 0;
    var mtimeSec := 0;
    var mtimeNsec := 0;

    match source
    case TimeSourceCurrent =>
      var nowSec := io.Now();
      atimeSec := nowSec;
      mtimeSec := nowSec;
    case TimeSourceFixed(sourceAtimeSec, sourceAtimeNsec, sourceMtimeSec, sourceMtimeNsec) =>
      atimeSec := sourceAtimeSec;
      atimeNsec := sourceAtimeNsec;
      mtimeSec := sourceMtimeSec;
      mtimeNsec := sourceMtimeNsec;

      if selection != Schema.TimeBoth {
        var getFileTimesResult3 := io.GetFileTimes(path, followSymlink);
        var getOk := getFileTimesResult3.Ok?;
        var oldAtimeSec := IOContract.ResultValue(getFileTimesResult3, BenchWorld.FileTimeStatus(0, 0, 0, 0, false, false, 0, 0, 0)).atimeSec;
        var oldAtimeNsec := IOContract.ResultValue(getFileTimesResult3, BenchWorld.FileTimeStatus(0, 0, 0, 0, false, false, 0, 0, 0)).atimeNsec;
        var oldMtimeSec := IOContract.ResultValue(getFileTimesResult3, BenchWorld.FileTimeStatus(0, 0, 0, 0, false, false, 0, 0, 0)).mtimeSec;
        var oldMtimeNsec := IOContract.ResultValue(getFileTimesResult3, BenchWorld.FileTimeStatus(0, 0, 0, 0, false, false, 0, 0, 0)).mtimeNsec;
        var isDir := IOContract.ResultValue(getFileTimesResult3, BenchWorld.FileTimeStatus(0, 0, 0, 0, false, false, 0, 0, 0)).isDir;
        var isSymlink := IOContract.ResultValue(getFileTimesResult3, BenchWorld.FileTimeStatus(0, 0, 0, 0, false, false, 0, 0, 0)).isSymlink;
        var device := IOContract.ResultValue(getFileTimesResult3, BenchWorld.FileTimeStatus(0, 0, 0, 0, false, false, 0, 0, 0)).device;
        var inode := IOContract.ResultValue(getFileTimesResult3, BenchWorld.FileTimeStatus(0, 0, 0, 0, false, false, 0, 0, 0)).inode;
        var linkCount := IOContract.ResultValue(getFileTimesResult3, BenchWorld.FileTimeStatus(0, 0, 0, 0, false, false, 0, 0, 0)).linkCount;
        var getErr := IOContract.ResultErrno(getFileTimesResult3);
        if !getOk {
          ok := false;
          err := getErr;
          return;
        }
        if selection == Schema.TimeAccess {
          mtimeSec := oldMtimeSec;
          mtimeNsec := oldMtimeNsec;
        } else {
          atimeSec := oldAtimeSec;
          atimeNsec := oldAtimeNsec;
        }
      }

      var setFileTimesResult := io.SetFileTimes(
        path, followSymlink, atimeSec, atimeNsec, mtimeSec, mtimeNsec
      );
      ok := setFileTimesResult.Ok?;
      err := IOContract.ResultErrno(setFileTimesResult);
  }

  method SetStdoutTimesSelected(
    selection: Schema.TimeSelection,
    source: Schema.TimeSource,
    io: BenchIO.IO
  ) returns (ok: bool, err: int)
    modifies io.stdoutTimestampRegion
    ensures SetStdoutTimesSummaryFields(io.trustedNativeFailures(),
              selection, source, old(io.now()),
              old(io.stdoutTimestamp()), io.stdoutTimestamp(), ok, err
            )
    decreases *
  {
    ok := false;
    err := 0;
    if source == Schema.TimeSourceCurrent && selection == Schema.TimeBoth {
      var result := io.SetStdoutTimesNow();
      ok := result.Ok?;
      err := IOContract.ResultErrno(result);
      return;
    }
    if source == Schema.TimeSourceCurrent && selection == Schema.TimeAccess {
      var result := io.SetStdoutAccessTimeNow();
      ok := result.Ok?;
      err := IOContract.ResultErrno(result);
      return;
    }
    if source == Schema.TimeSourceCurrent && selection == Schema.TimeModify {
      var result := io.SetStdoutModificationTimeNow();
      ok := result.Ok?;
      err := IOContract.ResultErrno(result);
      return;
    }

    var atimeSec := 0;
    var atimeNsec := 0;
    var mtimeSec := 0;
    var mtimeNsec := 0;
    match source
    case TimeSourceCurrent =>
      var nowSec := io.Now();
      atimeSec := nowSec;
      mtimeSec := nowSec;
    case TimeSourceFixed(sourceAtimeSec, sourceAtimeNsec, sourceMtimeSec, sourceMtimeNsec) =>
      atimeSec := sourceAtimeSec;
      atimeNsec := sourceAtimeNsec;
      mtimeSec := sourceMtimeSec;
      mtimeNsec := sourceMtimeNsec;
      var setStdoutTimesResult := io.SetStdoutTimes(
        if selection == Schema.TimeModify then BenchWorld.Keep else BenchWorld.Exact(atimeSec, atimeNsec),
        if selection == Schema.TimeAccess then BenchWorld.Keep else BenchWorld.Exact(mtimeSec, mtimeNsec)
      );
      ok := setStdoutTimesResult.Ok?;
      err := IOContract.ResultErrno(setStdoutTimesResult);
  }

  method {:isolate_assertions} RunOne(
    path: BenchWorld.Path,
    noCreate: bool,
    followSymlink: bool,
    selection: Schema.TimeSelection,
    source: Schema.TimeSource,
    io: BenchIO.IO
  ) returns (stepError: bool, stepOut: BenchWorld.Bytes)
    modifies io.fsRegion, io.stdoutTimestampRegion
    ensures RunStepSummaryFields(io.trustedNativeFailures(),
      old(io.trustedFilesystem()), path, noCreate, followSymlink, selection, source,
      old(io.fs()), old(io.now()), old(io.stdout()), old(io.stdoutTimestamp()),
      io.fs(), io.stdout(), io.stdoutTimestamp(), stepError, stepOut)
    decreases *
  {
    stepError := false;
    stepOut := [];

    if path == "-" {
      var okStdout, stdoutErr := SetStdoutTimesSelected(selection, source, io);
      stepError := !okStdout;
      if stepError {
        stepOut := GetStdoutErrorMessage(stdoutErr, io);
      }
    } else {
      var pathExistsResult := io.PathExists(path, followSymlink);
      var found := pathExistsResult.Ok?;
      var existsErr := IOContract.ResultErrno(pathExistsResult);
      assert IOContract.TrustedPathExistsContractFields(io.trustedFilesystem(), old(io.fs()),
        path, followSymlink, found, existsErr) by { hide *; reveal IOContract.PathExistsSpec(); }
      if found {
        var okSet, setErr := SetPathTimes(path, followSymlink, selection, source, io);
        stepError := !okSet;
        if stepError {
          stepOut := GetTouchErrorMessage(path, setErr, io);
        }
      } else if noCreate {
        if existsErr == Errno.ENOENT {
          stepError := false;
        } else {
          stepError := true;
          stepOut := GetTouchErrorMessage(path, existsErr, io);
        }
      } else if !followSymlink {
        stepError := true;
        stepOut := GetSetTimesErrorMessage(path, existsErr, io);
      } else {
        var createFileResult := io.CreateFile(path);
        var okCreate := createFileResult.Ok?;
        var createErr := IOContract.ResultErrno(createFileResult);
        ghost var createdFs := io.fs();
        assert IOContract.TrustedCreateFileContractFields(io.trustedFilesystem(), old(io.fs()),
          old(io.now()), path, okCreate, createErr, createdFs) by { hide *; reveal IOContract.CreateFileSpec(); }
        if okCreate {
          if source == Schema.TimeSourceCurrent && selection == Schema.TimeBoth {
            stepError := false;
          } else {
            var okSet, setErr := SetPathTimes(path, followSymlink, selection, source, io);
            stepError := !okSet;
            if stepError {
              stepOut := GetTouchErrorMessage(path, setErr, io);
            }
          }
        } else {
          stepError := true;
          stepOut := GetTouchErrorMessage(path, createErr, io);
        }
      }
    }
    assert RunStepSummaryFields(io.trustedNativeFailures(), old(io.trustedFilesystem()),
      path, noCreate, followSymlink, selection, source,
      old(io.fs()), old(io.now()), old(io.stdout()), old(io.stdoutTimestamp()),
      io.fs(), io.stdout(), io.stdoutTimestamp(), stepError, stepOut) by {
      hide *; reveal RunStepSummaryFields();
    }

  }

  method {:isolate_assertions} RunFiles(
    files: seq<BenchWorld.Path>,
    noCreate: bool,
    followSymlink: bool,
    selection: Schema.TimeSelection,
    source: Schema.TimeSource,
    io: BenchIO.IO
  )
    returns (hadError: bool, errOut: BenchWorld.Bytes)
    modifies io.fsRegion, io.stdoutTimestampRegion
    ensures RunFilesSummaryFields(io.trustedNativeFailures(),
              old(io.trustedFilesystem()), files, noCreate,
              followSymlink, selection, source,
              old(io.fs()), old(io.now()), old(io.stdout()), old(io.stdoutTimestamp()),
              io.fs(), io.stdout(), io.stdoutTimestamp(), hadError, errOut
            )
    decreases *
  {
    ghost var preFs := io.fs();
    ghost var preNow := io.now();
    ghost var preStdout := io.stdout();
    ghost var preStdoutTarget := io.stdoutTimestamp();
    ghost var preFilesystemObservations := io.trustedFilesystem();
    hadError := false;
    errOut := [];
    var i := 0;
    RunFilesSummaryFieldsEmpty(io.trustedNativeFailures(),
      preFilesystemObservations, noCreate, followSymlink, selection, source,
      preFs, preNow, preStdout, preStdoutTarget
    );
    while i < |files|
      invariant 0 <= i <= |files|
      invariant RunFilesSummaryFields(io.trustedNativeFailures(),
                  preFilesystemObservations, files[..i], noCreate,
                  followSymlink, selection, source,
                  preFs, preNow, preStdout, preStdoutTarget,
                  io.fs(), io.stdout(), io.stdoutTimestamp(), hadError, errOut
                )
      decreases |files| - i
    {
      var prefixError := hadError;
      var prefixOut := errOut;
      ghost var stepFs := io.fs();
      ghost var stepStdout := io.stdout();
      ghost var stepStdoutTarget := io.stdoutTimestamp();
      var path := files[i];
      var stepError, stepOut := RunOne(path, noCreate, followSymlink, selection, source, io);

      hadError := prefixError || stepError;
      errOut := prefixOut + stepOut;
      assert RunStepSummaryFields(io.trustedNativeFailures(),
        preFilesystemObservations, path, noCreate, followSymlink, selection, source,
        stepFs, preNow, stepStdout, stepStdoutTarget,
        io.fs(), io.stdout(), io.stdoutTimestamp(), stepError, stepOut
      );
      RunFilesSummaryFieldsAppend(io.trustedNativeFailures(),
        preFilesystemObservations, files[..i], path,
        noCreate, followSymlink, selection, source,
        preFs, preNow, preStdout, preStdoutTarget,
        stepFs, stepStdout, stepStdoutTarget,
        io.fs(), io.stdout(), io.stdoutTimestamp(),
        prefixError, stepError, prefixOut, stepOut
      );
      assert files[..i] + [path] == files[..i + 1] by { hide *; }
      i := i + 1;
    }
    assert i == |files|;
    assert files[..i] == files;
  }
}
