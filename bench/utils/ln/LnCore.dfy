include "LnSpec.dfy"
include "../../core/IO.dfy"
include "../../core/IOContract.dfy"
include "LnSchema.dfy"

module LnCore {
  import Path = LnSpec
  import StreamWorld = BenchWorld
  import StreamContract = IOContract

  import BenchIO
  import BenchWorld
  import IOContract
  import Schema = LnSchema
  import Spec = LnSpec

  lemma DirectoryProbeMatchesCore(
    fs: BenchWorld.FileSystem, observations: Spec.ObservationContext, path: BenchWorld.Path,
    ok: bool, isDir: bool, err: int
  )
    requires Spec.DirectoryObservation(fs, observations, path, true, ok, isDir, err)
    ensures (ok && isDir) == Spec.ObservedDirectory(fs, observations, path, true)
  {
  }

  lemma StatusImpliesDirectory(
    fs: BenchWorld.FileSystem, observations: Spec.ObservationContext, path: string,
    follow: bool, ok: bool, status: BenchWorld.FileStatus, err: int, cursor: nat
  )
    requires IOContract.GetFileStatusSpec(observations.times, observations.failures,
                                          observations.cursor, cursor, fs, path, follow, ok, status, err)
    ensures Spec.DirectoryObservation(fs, observations, path, follow,
                                      ok, ok && status.kind == BenchWorld.DirectoryKind, err)
    ensures cursor == observations.cursor + 1
  {
    hide *;
    reveal IOContract.GetFileStatusSpec(), IOContract.ObservedNativeFileStatusContractFields();
    reveal Spec.DirectoryObservation(), Spec.ObservedDirectory(), IOContract.ResultErrno();
    match IOContract.ObservedNativeStatusResultFields(
        observations.times, observations.failures, observations.cursor, fs, path, follow)
    case Ok(_) =>
    case Err(_) =>
  }

  opaque ghost predicate CoreStepSummary(
    beforeFs: BenchWorld.FileSystem,
    afterFs: BenchWorld.FileSystem,
    now: int,
    trustedFilesystem: Spec.ObservationContext,
    source: BenchWorld.Path,
    destination: BenchWorld.Path,
    symbolic: bool,
    diagnostic: BenchWorld.Bytes,
    success: bool
  )
  {
    if symbolic then
      exists ok: bool, err: int ::
        IOContract.CreateSymlinkSpec(
          beforeFs, now, trustedFilesystem.credentials, trustedFilesystem.failures, afterFs, destination, source, ok, err) &&
        diagnostic == (if ok then [] else
                       Spec.CreateSymlinkErrorMessageSpec(destination, source, err)) &&
        success == ok
    else
      exists sourceOk: bool, sourceIsDir: bool, sourceErr: int ::
        Spec.DirectoryObservation(
          beforeFs, trustedFilesystem, source, false, sourceOk, sourceIsDir, sourceErr) &&
        (if !sourceOk then
           afterFs == beforeFs &&
           diagnostic == Spec.FailedAccessMessageSpec(source, sourceErr) &&
           !success
         else if sourceIsDir then
           afterFs == beforeFs &&
           diagnostic == Spec.HardDirectoryMessageSpec(source) &&
           !success
         else
           exists ok: bool, err: int ::
             IOContract.CreateHardLinkSpec(
               beforeFs, now, trustedFilesystem.filesystem, afterFs,
               source, destination, ok, err) &&
             diagnostic == (if ok then [] else
                            Spec.CreateHardLinkErrorMessageSpec(source, destination, err)) &&
             success == ok)
  }

  opaque ghost predicate CoreBatchSummary(
    beforeFs: BenchWorld.FileSystem,
    afterFs: BenchWorld.FileSystem,
    now: int,
    trustedFilesystem: Spec.ObservationContext,
    sources: seq<BenchWorld.Path>,
    directory: BenchWorld.Path,
    symbolic: bool,
    diagnostic: BenchWorld.Bytes,
    success: bool
  )
  {
    exists states: seq<BenchWorld.FileSystem>,
      diagnostics: seq<BenchWorld.Bytes>,
      results: seq<bool>,
      pieces: seq<BenchWorld.Bytes>,
      stepResults: seq<bool> ::
      |states| == |sources| + 1 &&
      |diagnostics| == |sources| + 1 &&
      |results| == |sources| + 1 &&
      |pieces| == |sources| &&
      |stepResults| == |sources| &&
      states[0] == beforeFs &&
      states[|sources|] == afterFs &&
      diagnostics[0] == [] &&
      diagnostics[|sources|] == diagnostic &&
      results[0] &&
      results[|sources|] == success &&
      (forall i: nat :: i < |sources| ==>
                          CoreStepSummary(
                            states[i], states[i + 1], now, Spec.AtCursor(trustedFilesystem, trustedFilesystem.cursor + (if symbolic then 0 else i)),
                            sources[i], Spec.InDirectory(directory, sources[i]), symbolic,
                            pieces[i], stepResults[i]) &&
                          diagnostics[i + 1] == diagnostics[i] + pieces[i] &&
                          results[i + 1] == (results[i] && stepResults[i]))
  }

  lemma AppendAssociative<T>(left: seq<T>, middle: seq<T>, right: seq<T>)
    ensures (left + middle) + right == left + (middle + right)
  {
  }

  opaque twostate predicate PreparedSummary(raw: Schema.LnCmdRaw, io: BenchIO.IO, exit: int, plannedStdout: StreamWorld.Bytes, plannedStderr: StreamWorld.Bytes)
    reads io.fsRegion, io.nowRegion, io.trustedFilesystemRegion, io.statusObservationsRegion, io.trustedNativeFailuresRegion, io.credentialsRegion
  {
    var cmd := Schema.Command(raw);
    io.statusCursor() == old(io.statusCursor()) + Spec.StatusReadCount(cmd, old(io.fs()), old(Spec.Context(io))) &&
    (if cmd.mode == Schema.ModeHelp then
       io.fs() == old(io.fs()) &&
       plannedStdout == [] + Spec.HelpTextSpec() &&
       plannedStderr == [] && exit == 0
     else if cmd.mode == Schema.ModeVersion then
       io.fs() == old(io.fs()) &&
       plannedStdout == [] + Spec.VersionTextSpec() &&
       plannedStderr == [] && exit == 0
     else if |cmd.operands| == 0 then
       io.fs() == old(io.fs()) &&
       plannedStdout == [] &&
       plannedStderr == [] + Spec.MissingOperandMessageSpec() && exit == 1
     else if |cmd.operands| > 2 then
       var target := cmd.operands[|cmd.operands| - 1];
       plannedStdout == [] &&
       (exists targetOk: bool, targetIsDir: bool, targetErr: int ::
          Spec.DirectoryObservation(
            old(io.fs()), old(Spec.Context(io)), target, true, targetOk, targetIsDir, targetErr) &&
          (if !(targetOk && targetIsDir) then
             io.fs() == old(io.fs()) &&
             plannedStderr == [] +
             Spec.TargetDirectoryErrorMessageSpec(target, if targetOk then 20 else targetErr) &&
             exit == 1
           else
             exists diagnostic: BenchWorld.Bytes, success: bool
               {:trigger CoreBatchSummary(old(io.fs()), io.fs(), old(io.now()), Spec.AtCursor(old(Spec.Context(io)), old(io.statusCursor()) + 1), cmd.operands[..|cmd.operands| - 1],
                                          target, cmd.symbolic, diagnostic, success)} ::
               CoreBatchSummary(
                 old(io.fs()), io.fs(), old(io.now()), Spec.AtCursor(old(Spec.Context(io)), old(io.statusCursor()) + 1),
                 cmd.operands[..|cmd.operands| - 1], target, cmd.symbolic,
                 diagnostic, success) &&
               plannedStderr == [] + diagnostic &&
               exit == (if success then 0 else 1)))
     else
       var source := cmd.operands[0];
       var destination := Spec.LinkDestination(old(io.fs()), old(Spec.Context(io)), cmd.operands);
       plannedStdout == [] &&
       (exists diagnostic: BenchWorld.Bytes, success: bool
          {:trigger CoreStepSummary(old(io.fs()), io.fs(), old(io.now()),
                                    Spec.AtCursor(old(Spec.Context(io)), old(io.statusCursor()) + Spec.DestinationReadCount(cmd.operands)), source, destination, cmd.symbolic,
                                    diagnostic, success)} ::
          CoreStepSummary(
            old(io.fs()), io.fs(), old(io.now()), Spec.AtCursor(old(Spec.Context(io)), old(io.statusCursor()) + Spec.DestinationReadCount(cmd.operands)),
            source, destination, cmd.symbolic, diagnostic, success) &&
          plannedStderr == [] + diagnostic &&
          exit == (if success then 0 else 1)))
  }

  opaque twostate predicate CoreSummary(raw: Schema.LnCmdRaw, io: BenchIO.IO, exit: int)
    reads io.fsRegion, io.nowRegion, io.trustedFilesystemRegion, io.statusObservationsRegion, io.trustedNativeFailuresRegion, io.credentialsRegion, io.stdoutRegion, io.stderrRegion, io.trustedStreamsRegion
  {
    exists output: StreamWorld.Bytes, diagnostics: StreamWorld.Bytes, normalExit: int ::
      PreparedSummary(raw, io, normalExit, output, diagnostics) &&
      Spec.EmissionFields(old(io.stdout()), old(io.stderr()), io.stdout(), io.stderr(),
                          io.trustedStreams(), output, diagnostics, normalExit, exit)
  }

  twostate lemma SinglePreparedWitness(raw: Schema.LnCmdRaw, io: BenchIO.IO,
                                       exit: int, output: BenchWorld.Bytes, diagnostics: BenchWorld.Bytes,
                                       success: bool)
    requires Schema.Command(raw).mode == Schema.ModeRun
    requires 1 <= |Schema.Command(raw).operands| <= 2
    requires io.statusCursor() == old(io.statusCursor()) +
                                  Spec.StatusReadCount(Schema.Command(raw), old(io.fs()), old(Spec.Context(io)))
    requires output == []
    requires exit == (if success then 0 else 1)
    requires CoreStepSummary(old(io.fs()), io.fs(), old(io.now()),
                             Spec.AtCursor(old(Spec.Context(io)), old(io.statusCursor()) +
                                           Spec.DestinationReadCount(Schema.Command(raw).operands)),
                             Schema.Command(raw).operands[0],
                             Spec.LinkDestination(old(io.fs()), old(Spec.Context(io)), Schema.Command(raw).operands),
                             Schema.Command(raw).symbolic, diagnostics, success)
    ensures PreparedSummary(raw, io, exit, output, diagnostics)
  {
    hide *;
    reveal PreparedSummary();
    var cmd := Schema.Command(raw);
    var source := cmd.operands[0];
    var destination := Spec.LinkDestination(old(io.fs()), old(Spec.Context(io)), cmd.operands);
    var context := Spec.AtCursor(old(Spec.Context(io)), old(io.statusCursor()) +
                                 Spec.DestinationReadCount(cmd.operands));
    assert CoreStepSummary(old(io.fs()), io.fs(), old(io.now()), context,
                           source, destination, cmd.symbolic, diagnostics, success);
    assert exists diagnostic: BenchWorld.Bytes, result: bool ::
        diagnostic == diagnostics && result == success &&
        CoreStepSummary(old(io.fs()), io.fs(), old(io.now()), context,
                        source, destination, cmd.symbolic, diagnostic, result) &&
        diagnostics == [] + diagnostic && exit == (if result then 0 else 1);
    assert exists diagnostic: BenchWorld.Bytes, result: bool
        {:trigger CoreStepSummary(old(io.fs()), io.fs(), old(io.now()), context,
                                  source, destination, cmd.symbolic, diagnostic, result)} ::
        CoreStepSummary(old(io.fs()), io.fs(), old(io.now()), context,
                        source, destination, cmd.symbolic, diagnostic, result) &&
        diagnostics == [] + diagnostic && exit == (if result then 0 else 1);
  }

  lemma CoreBatchWitness(
    beforeFs: BenchWorld.FileSystem, afterFs: BenchWorld.FileSystem, now: int,
    provider: Spec.ObservationContext,
    sources: seq<string>, target: string, symbolic: bool, diagnostic: BenchWorld.Bytes, success: bool,
    states: seq<BenchWorld.FileSystem>, diagnostics: seq<BenchWorld.Bytes>, results: seq<bool>,
    pieces: seq<BenchWorld.Bytes>, stepResults: seq<bool>
  )
    requires |states| == |sources| + 1 && |diagnostics| == |sources| + 1 && |results| == |sources| + 1
    requires |pieces| == |sources| && |stepResults| == |sources|
    requires states[0] == beforeFs && states[|sources|] == afterFs
    requires diagnostics[0] == [] && diagnostics[|sources|] == diagnostic
    requires results[0] && results[|sources|] == success
    requires forall j: nat | j < |sources| ::
               CoreStepSummary(states[j], states[j + 1], now, Spec.AtCursor(provider, provider.cursor + (if symbolic then 0 else j)), sources[j],
                               Spec.InDirectory(target, sources[j]), symbolic, pieces[j], stepResults[j]) &&
               diagnostics[j + 1] == diagnostics[j] + pieces[j] &&
               results[j + 1] == (results[j] && stepResults[j])
    ensures CoreBatchSummary(beforeFs, afterFs, now, provider, sources, target, symbolic, diagnostic, success)
  {
    hide *;
    reveal CoreBatchSummary();
  }

  method FailedAccessMessageCore(source: BenchWorld.Path, err: int, io: BenchIO.IO) returns (message: BenchWorld.Bytes)
    ensures message == Spec.FailedAccessMessageSpec(source, err)
  {
    var reason := io.GetCLocaleErrnoText(err);
    message := Path.FailedAccessMessageText(source, err, reason);
  }

  method CreateHardLinkErrorMessageCore(source: BenchWorld.Path, linkName: BenchWorld.Path, err: int, io: BenchIO.IO) returns (message: BenchWorld.Bytes)
    ensures message == Spec.CreateHardLinkErrorMessageSpec(source, linkName, err)
  {
    var reason := io.GetCLocaleErrnoText(err);
    message := Path.CreateHardLinkErrorMessageText(source, linkName, err, reason);
  }

  method CreateSymlinkErrorMessageCore(linkName: BenchWorld.Path, source: BenchWorld.Path, err: int, io: BenchIO.IO) returns (message: BenchWorld.Bytes)
    ensures message == Spec.CreateSymlinkErrorMessageSpec(linkName, source, err)
  {
    var reason := io.GetCLocaleErrnoText(err);
    message := Path.CreateSymlinkErrorMessageText(linkName, source, err, reason);
  }

  method TargetDirectoryErrorMessageCore(target: BenchWorld.Path, err: int, io: BenchIO.IO) returns (message: BenchWorld.Bytes)
    ensures message == Spec.TargetDirectoryErrorMessageSpec(target, err)
  {
    var reason := io.GetCLocaleErrnoText(err);
    message := Path.TargetDirectoryErrorMessageText(target, err, reason);
  }

  method {:isolate_assertions} RunBatch(
    sources: seq<string>, target: string, symbolic: bool, io: BenchIO.IO
  ) returns (diagnostic: BenchWorld.Bytes, allOk: bool)
    modifies io.fsRegion, io.statusObservationsRegion
    ensures CoreBatchSummary(
              old(io.fs()), io.fs(), old(io.now()), old(Spec.Context(io)),
              sources, target, symbolic, diagnostic, allOk)
    ensures io.statusCursor() == old(io.statusCursor()) + (if symbolic then 0 else |sources|)
  {
    hide *;
    ghost var preFs := io.fs();
    ghost var preNow := io.now();
    ghost var preTrusted := Spec.Context(io);
    ghost var states := [io.fs()];
    ghost var diagnostics: seq<BenchWorld.Bytes> := [[]];
    ghost var results := [true];
    ghost var pieces: seq<BenchWorld.Bytes> := [];
    ghost var stepResults: seq<bool> := [];
    diagnostic := [];
    allOk := true;
    var i := 0;
    while i < |sources|
      invariant 0 <= i <= |sources|
      invariant io.statusCursor() == preTrusted.cursor + (if symbolic then 0 else i)
      invariant |states| == i + 1 && states[0] == preFs && states[i] == io.fs()
      invariant |diagnostics| == i + 1 && diagnostics[0] == []
      invariant diagnostics[i] == diagnostic
      invariant |results| == i + 1 && results[0] && results[i] == allOk
      invariant |pieces| == i && |stepResults| == i
      invariant forall j: nat :: j < i ==>
                                   CoreStepSummary(
                                     states[j], states[j + 1], preNow, Spec.AtCursor(preTrusted, preTrusted.cursor + (if symbolic then 0 else j)),
                                     sources[j], Spec.InDirectory(target, sources[j]), symbolic,
                                     pieces[j], stepResults[j]) &&
                                   diagnostics[j + 1] == diagnostics[j] + pieces[j] &&
                                   results[j + 1] == (results[j] && stepResults[j])
      decreases |sources| - i
    {
      var source := sources[i];
      var destination := Path.InDirectory(target, source);
      assert destination == Spec.InDirectory(target, source) by {
        reveal Path.InDirectory();
      }
      ghost var beforeStepFs := io.fs();
      ghost var beforeStepContext := Spec.Context(io);
      assert beforeStepContext == Spec.AtCursor(preTrusted, preTrusted.cursor + (if symbolic then 0 else i));
      var piece: BenchWorld.Bytes := [];
      var stepOk := false;
      if symbolic {
        var createSymlinkResult := io.CreateSymlink(destination, source);
        var ok := createSymlinkResult.Ok?;
        var err := IOContract.ResultErrno(createSymlinkResult);
        stepOk := ok;
        if !ok {
          piece := CreateSymlinkErrorMessageCore(destination, source, err, io);
        }
        assert CoreStepSummary(
            beforeStepFs, io.fs(), preNow, beforeStepContext,
            source, destination, symbolic, piece, stepOk) by {
          hide *;
          reveal CoreStepSummary();
        }
      } else {
        var getFileStatusResult := io.GetFileStatus(source, false);
        var sourceOk := getFileStatusResult.Ok?;
        var sourceStatus := IOContract.ResultValue(getFileStatusResult, BenchWorld.DEFAULT_FILE_STATUS);
        var sourceErr := IOContract.ResultErrno(getFileStatusResult);
        var sourceIsDir := sourceOk && sourceStatus.kind == BenchWorld.DirectoryKind;
        StatusImpliesDirectory(beforeStepFs, beforeStepContext, source, false,
                               sourceOk, sourceStatus, sourceErr, io.statusCursor());
        if !sourceOk {
          piece := FailedAccessMessageCore(source, sourceErr, io);
        } else if sourceIsDir {
          piece := Path.HardDirectoryMessageSpec(source);
        } else {
          var createHardLinkResult := io.CreateHardLink(source, destination);
          var ok := createHardLinkResult.Ok?;
          var err := IOContract.ResultErrno(createHardLinkResult);
          stepOk := ok;
          if !ok {
            piece := CreateHardLinkErrorMessageCore(source, destination, err, io);
          }
          assert IOContract.CreateHardLinkSpec(
              beforeStepFs, preNow, preTrusted.filesystem,
              io.fs(), source, destination, ok, err) by {
            hide *;
            reveal IOContract.ResultErrno();
          }
        }
        assert Spec.DirectoryObservation(
            beforeStepFs, beforeStepContext, source, false, sourceOk, sourceIsDir, sourceErr);
        assert CoreStepSummary(
            beforeStepFs, io.fs(), preNow, beforeStepContext,
            source, destination, symbolic, piece, stepOk) by {
          hide *;
          reveal CoreStepSummary();
        }
      }
      ghost var previousStates := states;
      ghost var previousDiagnostics := diagnostics;
      ghost var previousResults := results;
      ghost var previousPieces := pieces;
      ghost var previousSteps := stepResults;
      states := states + [io.fs()];
      diagnostics := diagnostics + [diagnostics[i] + piece];
      results := results + [results[i] && stepOk];
      pieces := pieces + [piece];
      stepResults := stepResults + [stepOk];
      diagnostic := diagnostic + piece;
      allOk := allOk && stepOk;
      assert forall j: nat :: j < i + 1 ==>
                                CoreStepSummary(
                                  states[j], states[j + 1], preNow, Spec.AtCursor(preTrusted, preTrusted.cursor + (if symbolic then 0 else j)),
                                  sources[j], Spec.InDirectory(target, sources[j]), symbolic,
                                  pieces[j], stepResults[j]) &&
                                diagnostics[j + 1] == diagnostics[j] + pieces[j] &&
                                results[j + 1] == (results[j] && stepResults[j]) by {
        hide *;
        forall j: nat | j < i + 1
          ensures
            CoreStepSummary(
              states[j], states[j + 1], preNow, Spec.AtCursor(preTrusted, preTrusted.cursor + (if symbolic then 0 else j)),
              sources[j], Spec.InDirectory(target, sources[j]), symbolic,
              pieces[j], stepResults[j]) &&
            diagnostics[j + 1] == diagnostics[j] + pieces[j] &&
            results[j + 1] == (results[j] && stepResults[j])
        {
          if j < i {
            assert states[j] == previousStates[j] && states[j + 1] == previousStates[j + 1];
            assert diagnostics[j] == previousDiagnostics[j] && diagnostics[j + 1] == previousDiagnostics[j + 1];
            assert results[j] == previousResults[j] && results[j + 1] == previousResults[j + 1];
            assert pieces[j] == previousPieces[j] && stepResults[j] == previousSteps[j];
          } else {
            assert j == i;
            assert states[j] == beforeStepFs && states[j + 1] == io.fs();
          }
        }
      }
      i := i + 1;
    }
    CoreBatchWitness(preFs, io.fs(), preNow, preTrusted, sources, target, symbolic,
                     diagnostic, allOk, states, diagnostics, results, pieces, stepResults);
  }

  method {:isolate_assertions} Prepare(raw: Schema.LnCmdRaw, io: BenchIO.IO) returns (exit: int, plannedStdout: StreamWorld.Bytes, plannedStderr: StreamWorld.Bytes)
    modifies io.fsRegion, io.statusObservationsRegion
    ensures PreparedSummary(raw, io, exit, plannedStdout, plannedStderr)
    decreases *
  {
    label PrepareStart:
    hide *;
    reveal PreparedSummary();
    plannedStdout := [];
    plannedStderr := [];
    ghost var preFs := io.fs();
    ghost var preNow := io.now();
    ghost var preTrusted := Spec.Context(io);
    ghost var preStdout := (plannedStdout);
    ghost var preStderr := (plannedStderr);
    var cmd := Schema.Command(raw);
    if cmd.mode == Schema.ModeHelp {
      plannedStdout := plannedStdout + (Spec.HelpTextSpec());
      exit := 0;
      assert PreparedSummary(raw, io, exit, plannedStdout, plannedStderr) by {
        hide *;
        reveal PreparedSummary(), Spec.StatusReadCount(), Spec.DirectoryObservation(), Spec.ObservedDirectory();
      }
      return;
    }
    if cmd.mode == Schema.ModeVersion {
      plannedStdout := plannedStdout + (Spec.VersionTextSpec());
      exit := 0;
      assert PreparedSummary(raw, io, exit, plannedStdout, plannedStderr) by {
        hide *;
        reveal PreparedSummary(), Spec.StatusReadCount();
      }
      return;
    }
    if |cmd.operands| == 0 {
      plannedStderr := plannedStderr + (Spec.MissingOperandMessageSpec());
      exit := 1;
      assert PreparedSummary(raw, io, exit, plannedStdout, plannedStderr) by {
        hide *;
        reveal PreparedSummary(), Spec.StatusReadCount();
      }
      return;
    }
    if |cmd.operands| > 2 {
      var target := cmd.operands[|cmd.operands| - 1];
      var getFileStatusResult2 := io.GetFileStatus(target, true);
      var targetOk := getFileStatusResult2.Ok?;
      var targetStatus := IOContract.ResultValue(getFileStatusResult2, BenchWorld.DEFAULT_FILE_STATUS);
      var targetErr := IOContract.ResultErrno(getFileStatusResult2);
      var targetIsDir := targetOk && targetStatus.kind == BenchWorld.DirectoryKind;
      StatusImpliesDirectory(preFs, preTrusted, target, true,
                             targetOk, targetStatus, targetErr, io.statusCursor());
      if !(targetOk && targetIsDir) {
        var message := TargetDirectoryErrorMessageCore(target, if targetOk then 20 else targetErr, io);
        plannedStderr := plannedStderr + message;
        exit := 1;
        assert PreparedSummary(raw, io, exit, plannedStdout, plannedStderr) by {
          hide *;
          reveal PreparedSummary(), Spec.StatusReadCount(), Spec.DirectoryObservation(), Spec.ObservedDirectory();
        }
        return;
      }
      var sources := cmd.operands[..|cmd.operands| - 1];
      ghost var batchContext := Spec.Context(io);
      assert batchContext == Spec.AtCursor(preTrusted, preTrusted.cursor + 1);
      var diagnostic, allOk := RunBatch(sources, target, cmd.symbolic, io);
      plannedStderr := plannedStderr + diagnostic;
      exit := if allOk then 0 else 1;
      assert (plannedStdout) == preStdout;
      assert preTrusted == old(Spec.Context(io));
      assert batchContext == Spec.AtCursor(old(Spec.Context(io)), old(io.statusCursor()) + 1);
      assert io.statusCursor() == old(io.statusCursor()) + Spec.StatusReadCount(cmd, preFs, preTrusted) by {
        hide *;
        reveal Spec.StatusReadCount(), Spec.DirectoryObservation(), Spec.ObservedDirectory();
      }
      assert PreparedSummary(raw, io, exit, plannedStdout, plannedStderr) by {
        hide *;
        reveal PreparedSummary(), Spec.StatusReadCount(), Spec.DirectoryObservation(), Spec.ObservedDirectory();
      }
      return;
    }

    var source := cmd.operands[0];
    var destination: string;
    var dirOk := false;
    var dirIsDir := false;
    var dirErr := 0;
    if |cmd.operands| == 1 {
      destination := Path.InDirectory(".", source);
    } else if source == "" {
      destination := cmd.operands[1];
    } else {
      var status: BenchWorld.FileStatus;
      var getFileStatusResult3 := io.GetFileStatus(cmd.operands[1], true);
      dirOk := getFileStatusResult3.Ok?;
      status := IOContract.ResultValue(getFileStatusResult3, BenchWorld.DEFAULT_FILE_STATUS);
      dirErr := IOContract.ResultErrno(getFileStatusResult3);
      dirIsDir := dirOk && status.kind == BenchWorld.DirectoryKind;
      StatusImpliesDirectory(preFs, preTrusted, cmd.operands[1], true,
                             dirOk, status, dirErr, io.statusCursor());
      DirectoryProbeMatchesCore(preFs, preTrusted, cmd.operands[1], dirOk, dirIsDir, dirErr);
      destination := if dirOk && dirIsDir then
        Path.InDirectory(cmd.operands[1], source) else cmd.operands[1];
    }
    assert destination == Spec.LinkDestination(preFs, preTrusted, cmd.operands) by {
      reveal Spec.LinkDestination(), Path.InDirectory();
    }

    ghost var stepContext := Spec.Context(io);
    assert stepContext == Spec.AtCursor(preTrusted, preTrusted.cursor + Spec.DestinationReadCount(cmd.operands)) by {
      reveal Spec.DestinationReadCount();
    }
    if cmd.symbolic {
      var createSymlinkResult2 := io.CreateSymlink(destination, source);
      var ok := createSymlinkResult2.Ok?;
      var err := IOContract.ResultErrno(createSymlinkResult2);
      var diagnostic: BenchWorld.Bytes := [];
      if ok {
        exit := 0;
      } else {
        diagnostic := CreateSymlinkErrorMessageCore(destination, source, err, io);
        plannedStderr := plannedStderr + (diagnostic);
        exit := 1;
      }
      assert IOContract.CreateSymlinkSpec(
          preFs, preNow, stepContext.credentials, stepContext.failures, io.fs(), destination, source, ok, err) by {
        hide *;
        reveal IOContract.CreateSymlinkSpec();
      }
      assert (plannedStdout) == preStdout;
      assert CoreStepSummary(
          preFs, io.fs(), preNow, stepContext, source, destination,
          cmd.symbolic, diagnostic, ok) by {
        hide *;
        reveal CoreStepSummary();
      }
      assert (plannedStderr) == preStderr + diagnostic;
      assert preTrusted == old(Spec.Context(io));
      assert stepContext == Spec.AtCursor(old(Spec.Context(io)), old(io.statusCursor()) + Spec.DestinationReadCount(cmd.operands));
      assert destination == Spec.LinkDestination(old(io.fs()), old(Spec.Context(io)), cmd.operands);
      assert CoreStepSummary(old(io.fs()), io.fs(), old(io.now()),
                             Spec.AtCursor(old(Spec.Context(io)), old(io.statusCursor()) + Spec.DestinationReadCount(cmd.operands)),
                             source, destination, cmd.symbolic, diagnostic, ok);
      assert io.statusCursor() == old(io.statusCursor()) + Spec.StatusReadCount(cmd, preFs, preTrusted) by {
        hide *;
        reveal Spec.StatusReadCount(), Spec.DestinationReadCount();
      }
      assert plannedStderr == diagnostic;
      assert cmd == Schema.Command(raw);
      assert source == Schema.Command(raw).operands[0];
      assert destination == Spec.LinkDestination(old(io.fs()), old(Spec.Context(io)), Schema.Command(raw).operands);
      assert CoreStepSummary(old(io.fs()), io.fs(), old(io.now()),
                             Spec.AtCursor(old(Spec.Context(io)), old(io.statusCursor()) + Spec.DestinationReadCount(Schema.Command(raw).operands)),
                             Schema.Command(raw).operands[0],
                             Spec.LinkDestination(old(io.fs()), old(Spec.Context(io)), Schema.Command(raw).operands),
                             Schema.Command(raw).symbolic, plannedStderr, ok);
      SinglePreparedWitness@PrepareStart(raw, io, exit, plannedStdout, plannedStderr, ok);
      return;
    }

    var diagnostic: BenchWorld.Bytes := [];
    var success := false;
    var getFileStatusResult4 := io.GetFileStatus(source, false);
    var sourceOk := getFileStatusResult4.Ok?;
    var sourceStatus := IOContract.ResultValue(getFileStatusResult4, BenchWorld.DEFAULT_FILE_STATUS);
    var sourceErr := IOContract.ResultErrno(getFileStatusResult4);
    var sourceIsDir := sourceOk && sourceStatus.kind == BenchWorld.DirectoryKind;
    StatusImpliesDirectory(preFs, stepContext, source, false,
                           sourceOk, sourceStatus, sourceErr, io.statusCursor());
    if !sourceOk {
      diagnostic := FailedAccessMessageCore(source, sourceErr, io);
      plannedStderr := plannedStderr + (diagnostic);
      exit := 1;
    } else if sourceIsDir {
      diagnostic := Path.HardDirectoryMessageSpec(source);
      plannedStderr := plannedStderr + (diagnostic);
      exit := 1;
    } else {
      var createHardLinkResult2 := io.CreateHardLink(source, destination);
      var ok := createHardLinkResult2.Ok?;
      var err := IOContract.ResultErrno(createHardLinkResult2);
      assert IOContract.CreateHardLinkSpec(
          preFs, preNow, preTrusted.filesystem, io.fs(), source, destination, ok, err) by {
        hide *;
        reveal IOContract.ResultErrno();
      }
      success := ok;
      if ok {
        exit := 0;
      } else {
        diagnostic := CreateHardLinkErrorMessageCore(source, destination, err, io);
        plannedStderr := plannedStderr + (diagnostic);
        exit := 1;
      }
    }
    assert Spec.DirectoryObservation(
        preFs, stepContext, source, false, sourceOk, sourceIsDir, sourceErr);
    assert (plannedStdout) == preStdout;
    assert CoreStepSummary(
        preFs, io.fs(), preNow, stepContext, source, destination,
        cmd.symbolic, diagnostic, success) by {
      hide *;
      reveal CoreStepSummary();
    }
    assert (plannedStderr) == preStderr + diagnostic;
    assert preTrusted == old(Spec.Context(io));
    assert stepContext == Spec.AtCursor(old(Spec.Context(io)), old(io.statusCursor()) + Spec.DestinationReadCount(cmd.operands));
    assert destination == Spec.LinkDestination(old(io.fs()), old(Spec.Context(io)), cmd.operands);
    assert plannedStderr == diagnostic;
    assert cmd == Schema.Command(raw);
    assert source == Schema.Command(raw).operands[0];
    assert destination == Spec.LinkDestination(old(io.fs()), old(Spec.Context(io)), Schema.Command(raw).operands);
    assert CoreStepSummary(old(io.fs()), io.fs(), old(io.now()),
                           Spec.AtCursor(old(Spec.Context(io)), old(io.statusCursor()) + Spec.DestinationReadCount(cmd.operands)),
                           source, destination, cmd.symbolic, diagnostic, success);
    assert io.statusCursor() == old(io.statusCursor()) + Spec.StatusReadCount(cmd, preFs, preTrusted) by {
      hide *;
      reveal Spec.StatusReadCount(), Spec.DestinationReadCount();
    }
    assert CoreStepSummary(old(io.fs()), io.fs(), old(io.now()),
                           Spec.AtCursor(old(Spec.Context(io)), old(io.statusCursor()) + Spec.DestinationReadCount(Schema.Command(raw).operands)),
                           Schema.Command(raw).operands[0],
                           Spec.LinkDestination(old(io.fs()), old(Spec.Context(io)), Schema.Command(raw).operands),
                           Schema.Command(raw).symbolic, plannedStderr, success);
    SinglePreparedWitness@PrepareStart(raw, io, exit, plannedStdout, plannedStderr, success);
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
      finalDiagnostics := diagnostics + Path.WriteErrorText(reason);
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

  method RunCore(raw: Schema.LnCmdRaw, io: BenchIO.IO) returns (exit: int)
    modifies io.fsRegion, io.stdoutRegion, io.stderrRegion, io.statusObservationsRegion
    ensures CoreSummary(raw, io, exit)
    decreases *
  {
    reveal CoreSummary();
    var normalExit, output, diagnostics := Prepare(raw, io);
    exit := Flush(output, diagnostics, normalExit, io);
  }
}
