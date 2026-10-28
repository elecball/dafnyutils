include "../../../core/World.dfy"
include "../Spec/ChmodSchema.dfy"
include "../Spec/ChmodSpec.dfy"
include "../../../core/Errno.dfy"
include "../../../core/Utf8.dfy"
include "../../../core/IO.dfy"
include "../../../core/IOContract.dfy"

module ChmodCore {
  class Output {
    var stdout: BenchWorld.Bytes
    var stderr: BenchWorld.Bytes

    constructor()
      ensures stdout == [] && stderr == []
    {
      stdout := [];
      stderr := [];
    }
  }

  import Errno = Errnos
  import BenchIO
  import IOContract
  import BenchWorld
  import Utf8 = Utf8Semantics
  import Schema = ChmodSchema
  import Spec = ChmodSpec

  ghost function CorePathIsDanglingSymlinkFailure(
    fs: BenchWorld.FileSystem,
    actual: BenchWorld.Path,
    follow: bool,
    err: int
  ): bool
  {
    follow &&
    match IOContract.ResolvePathForMetadataFields(fs, actual, false)
    case Err(_) => false
    case Ok(resolved) =>
      BenchWorld.FsContainsPath(fs, resolved) &&
      Spec.SpecIsDanglingSymlinkFailure(
        match BenchWorld.FsNodeAt(fs, resolved)
        case Symlink(_, _, _, _) => true
        case _ => false,
        err
      )
  }

  function CoreModeAdjustFrom(
    changes: seq<Schema.ModeChange>,
    i: nat,
    current: bv32,
    isDir: bool,
    umask: bv32
  ): bv32
    requires i <= |changes|
    decreases |changes| - i
  {
    if i == |changes| then
      current
    else
      CoreModeAdjustFrom(
        changes,
        i + 1,
        Spec.SpecApplyChange(current, isDir, umask, changes[i]),
        isDir,
        umask
      )
  }

  function CoreModeAdjust(
    oldMode: bv32,
    isDir: bool,
    umask: bv32,
    changes: seq<Schema.ModeChange>
  ): bv32
  {
    CoreModeAdjustFrom(changes, 0, BenchWorld.NormalizeMode(oldMode), isDir, umask)
  }

  function CoreApplyModeExpr(expr: string, oldMode: bv32, isDir: bool, umask: bv32): bv32
  {
    var base := BenchWorld.NormalizeMode(oldMode);
    if |expr| == 0 then
      base
    else if BenchWorld.IsOctalDigit(expr[0]) then
      if BenchWorld.AllOctalDigits(expr, 0) then
        var raw := BenchWorld.OctalValue(expr, 0, 0);
        if raw > 4095 then
          base
        else
          var mode := BenchWorld.NormalizeMode(BenchWorld.ToBv32(raw));
          var mentioned :=
            if |expr| < 5 then
              (mode & (Schema.S_ISUID | Schema.S_ISGID)) | Schema.S_ISVTX | Schema.S_IRWXUGO
            else
              Schema.CHMOD_MODE_BITS;
          CoreModeAdjust(
            base,
            isDir,
            umask,
            [Schema.ModeChange('=', Schema.ModeOrdinary, Schema.CHMOD_MODE_BITS, mode, mentioned)]
          )
      else
        base
    else
      match Schema.ParseSymbolic(expr, 0)
      case Invalid => base
      case Parsed(changes, endIdx) =>
        if endIdx == |expr| then CoreModeAdjust(base, isDir, umask, changes) else base
  }

  datatype CoreModePlan =
    | CoreGeneralModePlan(expr: string, umask: bv32)
    | CoreReferenceModePlan(mode: bv32)

  datatype CorePathStatus =
    | CorePathChanged(before: bv32, after: bv32)
    | CorePathRetained(mode: bv32)
    | CorePathAccessFailed(err: int)
    | CorePathChangeFailed(before: bv32, desired: bv32, err: int)
    | CorePathSurprise(before: bv32, after: bv32, naive: bv32)

  datatype CorePathResult = CorePathResult(
    fs: BenchWorld.FileSystem,
    stdoutChunk: BenchWorld.Bytes,
    stderrChunk: BenchWorld.Bytes,
    ok: bool,
    status: CorePathStatus
  )

  datatype CoreBatchResult = CoreBatchResult(
    fs: BenchWorld.FileSystem,
    stdoutChunk: BenchWorld.Bytes,
    stderrChunk: BenchWorld.Bytes,
    allOk: bool
  )

  function CorePlannedMode(plan: CoreModePlan, before: bv32, isDir: bool): bv32
  {
    match plan
    case CoreGeneralModePlan(expr, umask) =>
      CoreApplyModeExpr(expr, before, isDir, umask)
    case CoreReferenceModePlan(mode) => BenchWorld.NormalizeMode(mode)
  }

  function CoreNaiveMode(plan: CoreModePlan, before: bv32, isDir: bool): bv32
  {
    match plan
    case CoreGeneralModePlan(expr, _) => CoreApplyModeExpr(expr, before, isDir, 0 as bv32)
    case CoreReferenceModePlan(mode) => BenchWorld.NormalizeMode(mode)
  }

  function CoreDiagnoseSurprise(
    cmd: Schema.ChmodCmd,
    plan: CoreModePlan,
    before: bv32,
    after: bv32,
    isDir: bool
  ): bool
  {
    var naive := CoreNaiveMode(plan, before, isDir);
    cmd.diagnoseSurprises && (after & Spec.SpecInvertModeBits(naive)) != 0 as bv32
  }

  ghost function CoreSuccessfulChangeResult(
    cmd: Schema.ChmodCmd,
    plan: CoreModePlan,
    path: string,
    actual: BenchWorld.Path,
    follow: bool,
    before: bv32,
    after: bv32,
    isDir: bool,
    fs: BenchWorld.FileSystem
  ): CorePathResult
  {
    if Spec.SpecPostChangeLookupNeeded(cmd, after) then
      match IOContract.ResolvePathForMetadataFields(fs, actual, follow)
      case Err(_) =>
        var err := IOContract.MetadataFailureErrFields(fs, actual, follow);
        var surprise := CoreDiagnoseSurprise(cmd, plan, before, after, isDir);
        var naive := CoreNaiveMode(plan, before, isDir);
        CorePathResult(
          fs,
          if cmd.verbose then Spec.RetainedMessageSpec(path, after) else [],
          (if cmd.silent then []
           else Spec.GettingNewAttributesMessageSpec(path, Spec.ErrnoTextSpec(err))) +
          (if surprise then Spec.SurpriseModeMessageSpec(path, after, naive) else []),
          !surprise,
          CorePathRetained(after)
        )
      case Ok(target) =>
        if !BenchWorld.FsContainsPath(fs, target) then
          var err := IOContract.MetadataFailureErrFields(fs, actual, follow);
          var surprise := CoreDiagnoseSurprise(cmd, plan, before, after, isDir);
          var naive := CoreNaiveMode(plan, before, isDir);
          CorePathResult(
            fs,
            if cmd.verbose then Spec.RetainedMessageSpec(path, after) else [],
            (if cmd.silent then []
             else Spec.GettingNewAttributesMessageSpec(path, Spec.ErrnoTextSpec(err))) +
            (if surprise then Spec.SurpriseModeMessageSpec(path, after, naive) else []),
            !surprise,
            CorePathRetained(after)
          )
        else
          var observed := BenchWorld.NodeMode(BenchWorld.FsNodeAt(fs, target));
          var surprise := CoreDiagnoseSurprise(cmd, plan, before, observed, isDir);
          var naive := CoreNaiveMode(plan, before, isDir);
          CorePathResult(
            fs,
            Spec.SpecSuccessStdout(cmd, path, before, observed),
            if surprise then Spec.SurpriseModeMessageSpec(path, observed, naive) else [],
            !surprise,
            if surprise then CorePathSurprise(before, observed, naive)
            else if before == observed then CorePathRetained(observed)
            else CorePathChanged(before, observed)
          )
    else
      var surprise := CoreDiagnoseSurprise(cmd, plan, before, after, isDir);
      var naive := CoreNaiveMode(plan, before, isDir);
      CorePathResult(
        fs,
        Spec.SpecSuccessStdout(cmd, path, before, after),
        if surprise then Spec.SurpriseModeMessageSpec(path, after, naive) else [],
        !surprise,
        if surprise then CorePathSurprise(before, after, naive)
        else if before == after then CorePathRetained(after)
        else CorePathChanged(before, after)
      )
  }

  method {:isolate_assertions} AppendSuccessfulChangeOutputCore(
    cmd: Schema.ChmodCmd, plan: CoreModePlan, path: string, before: bv32, requested: bv32,
    isDir: bool, postOk: bool, postMode: bv32, postErr: int, io: BenchIO.IO, output: Output
  ) returns (ok: bool)
    modifies output
    ensures var result := SuccessfulChangeResultForPost(cmd, plan, path, before, requested, isDir,
                                                        old(io.fs()), postOk, postMode, postErr);
            output.stdout == old(output.stdout) + result.stdoutChunk &&
            output.stderr == old(output.stderr) + result.stderrChunk && ok == result.ok
  {
    hide *;
    reveal SuccessfulChangeResultForPost();
    var after := requested;
    if Spec.SpecPostChangeLookupNeeded(cmd, requested) {
      if !postOk {
        if !cmd.silent {
          output.stderr := output.stderr + Spec.GettingNewAttributesMessageSpec(path, NativeErrnoTextCore(postErr, io));
        }
        if cmd.verbose { output.stdout := output.stdout + Spec.RetainedMessageSpec(path, requested); }
        var naive := CoreNaiveMode(plan, before, isDir);
        var surprise := CoreDiagnoseSurprise(cmd, plan, before, requested, isDir);
        if surprise { output.stderr := output.stderr + Spec.SurpriseModeMessageSpec(path, requested, naive); }
        ok := !surprise;
        return;
      }
      after := postMode;
    }
    output.stdout := output.stdout + Spec.SpecSuccessStdout(cmd, path, before, after);
    var naive := CoreNaiveMode(plan, before, isDir);
    var surprise := CoreDiagnoseSurprise(cmd, plan, before, after, isDir);
    if surprise { output.stderr := output.stderr + Spec.SurpriseModeMessageSpec(path, after, naive); }
    ok := !surprise;
  }

  ghost function CoreModeSetFs(
    fs: BenchWorld.FileSystem,
    follow: bool,
    target: BenchWorld.Path,
    desired: bv32,
    now: int
  ): BenchWorld.FileSystem
    requires BenchWorld.FsContainsPath(fs, target)
  {
    if CoreModeSetSuppressed(fs, target, follow) then
      fs
    else
      BenchWorld.FsSetPath(
        fs,
        target,
        BenchWorld.WithNodeChangeTime(
          BenchWorld.WithNodeMode(BenchWorld.FsNodeAt(fs, target), desired),
          now,
          0
        )
      )
  }

  ghost function CoreModeSetSuppressed(
    fs: BenchWorld.FileSystem,
    target: BenchWorld.Path,
    follow: bool
  ): bool
    requires BenchWorld.FsContainsPath(fs, target)
  {
    !follow &&
    match BenchWorld.FsNodeAt(fs, target)
    case Symlink(_, _, _, _) => true
    case _ => false
  }

  ghost function CoreNoDereferenceSymlink(
    fs: BenchWorld.FileSystem,
    path: BenchWorld.Path,
    follow: bool
  ): bool
  {
    !follow &&
    match IOContract.ResolvePathForMetadataFields(fs, path, false)
    case Err(_) => false
    case Ok(target) =>
      BenchWorld.FsContainsPath(fs, target) &&
      match BenchWorld.FsNodeAt(fs, target)
      case Symlink(_, _, _, _) => true
      case _ => false
  }

  ghost function CorePathAccessFailureResult(
    cmd: Schema.ChmodCmd,
    fs: BenchWorld.FileSystem,
    path: string,
    actual: BenchWorld.Path,
    follow: bool,
    err: int
  ): CorePathResult
  {
    CorePathResult(
      fs,
      if cmd.verbose then Spec.AccessFailureMessageSpec(path) else [],
      if cmd.silent then []
      else if Spec.SpecUsesExplicitPhysicalDereference(cmd) &&
              CoreNoDereferenceSymlink(fs, actual, false) then
        Spec.CannotDereferenceMessageSpec(path, err)
      else if CorePathIsDanglingSymlinkFailure(fs, actual, follow, err) then
        Spec.DanglingSymlinkMessageSpec(path)
      else Spec.AccessErrorMessageSpec(path, Spec.ErrnoTextSpec(err)),
      false,
      CorePathAccessFailed(err)
    )
  }

  ghost function CorePathStep(
    cmd: Schema.ChmodCmd,
    plan: CoreModePlan,
    cwd: BenchWorld.Path,
    fs: BenchWorld.FileSystem,
    path: string,
    now: int
  ): CorePathResult
  {
    var actual := Spec.MakeAbsolute(cwd, path);
    var follow := Spec.ShouldDereference(cmd);
    if Spec.SpecUsesPhysicalTopLevelMetadata(cmd) then
      match IOContract.ResolvePathForMetadataFields(fs, actual, false)
      case Err(_) =>
        var err := IOContract.MetadataFailureErrFields(fs, actual, false);
        CorePathAccessFailureResult(cmd, fs, path, actual, false, err)
      case Ok(metadataTarget) =>
        if !BenchWorld.FsContainsPath(fs, metadataTarget) then
          var err := IOContract.MetadataFailureErrFields(fs, actual, false);
          CorePathAccessFailureResult(cmd, fs, path, actual, false, err)
        else
          var node := BenchWorld.FsNodeAt(fs, metadataTarget);
          var before := BenchWorld.NodeMode(node);
          var isDir := Spec.SpecNodeIsDirectory(node);
          var desired := CorePlannedMode(plan, before, isDir);
          match IOContract.ResolvePathForMetadataFields(fs, actual, true)
          case Err(_) =>
            var err := IOContract.MetadataFailureErrFields(fs, actual, true);
            CorePathResult(
              fs,
              if cmd.verbose then Spec.FailedChangeMessageSpec(path, before, desired) else [],
              if cmd.silent then []
              else Spec.ChangeErrorMessageSpec(path, Spec.ErrnoTextSpec(err)),
              false,
              CorePathChangeFailed(before, desired, err)
            )
          case Ok(changeTarget) =>
            if !BenchWorld.FsContainsPath(fs, changeTarget) then
              var err := IOContract.MetadataFailureErrFields(fs, actual, true);
              CorePathResult(
                fs,
                if cmd.verbose then Spec.FailedChangeMessageSpec(path, before, desired) else [],
                if cmd.silent then []
                else Spec.ChangeErrorMessageSpec(path, Spec.ErrnoTextSpec(err)),
                false,
                CorePathChangeFailed(before, desired, err)
              )
            else
              var fs2 := CoreModeSetFs(
                           fs, true, changeTarget, desired, now
                         );
              var after := BenchWorld.NormalizeMode(desired);
              CoreSuccessfulChangeResult(
                cmd, plan, path, actual, true, before, after, isDir, fs2
              )
    else
      match IOContract.ResolvePathForMetadataFields(fs, actual, follow)
      case Err(_) =>
        var err := IOContract.MetadataFailureErrFields(fs, actual, follow);
        CorePathAccessFailureResult(cmd, fs, path, actual, follow, err)
      case Ok(target) =>
        if !BenchWorld.FsContainsPath(fs, target) then
          var err := IOContract.MetadataFailureErrFields(fs, actual, follow);
          CorePathAccessFailureResult(cmd, fs, path, actual, follow, err)
        else
          var before := BenchWorld.NodeMode(BenchWorld.FsNodeAt(fs, target));
          if CoreNoDereferenceSymlink(fs, actual, follow) then
            if Spec.SpecUsesFollowedTopLevelNoDereference(cmd) then
              var followed := IOContract.ResolvePathForMetadataFields(fs, actual, true);
              var followedOk :=
                match followed
                case Err(_) => false
                case Ok(followedTarget) =>
                  BenchWorld.FsContainsPath(fs, followedTarget);
              var err := IOContract.MetadataFailureErrFields(fs, actual, true);
              if !followedOk && err != Errno.ENOENT then
                CorePathAccessFailureResult(cmd, fs, path, actual, true, err)
              else
                CorePathResult(
                  fs,
                  if cmd.verbose then Spec.NeitherChangedMessageSpec(path) else [],
                  [],
                  true,
                  CorePathRetained(before)
                )
            else
              CorePathResult(
                fs,
                if cmd.verbose then Spec.NeitherChangedMessageSpec(path) else [],
                [],
                true,
                CorePathRetained(before)
              )
          else
            var isDir := Spec.SpecNodeIsDirectory(BenchWorld.FsNodeAt(fs, target));
            var desired := CorePlannedMode(plan, before, isDir);
            var fs2 := CoreModeSetFs(fs, follow, target, desired, now);
            var after :=
              if CoreModeSetSuppressed(fs, target, follow) then before
              else BenchWorld.NormalizeMode(desired);
            CoreSuccessfulChangeResult(
              cmd, plan, path, actual, follow, before, after, isDir, fs2
            )
  }

  ghost function CoreRunFilesFrom(
    files: seq<string>,
    i: nat,
    cmd: Schema.ChmodCmd,
    plan: CoreModePlan,
    cwd: BenchWorld.Path,
    fs: BenchWorld.FileSystem,
    now: int
  ): CoreBatchResult
    requires i <= |files|
    decreases |files| - i
  {
    if i == |files| then
      CoreBatchResult(fs, [], [], true)
    else
      var step := CorePathStep(cmd, plan, cwd, fs, files[i], now);
      var rest := CoreRunFilesFrom(
                    files, i + 1, cmd, plan, cwd, step.fs, now
                  );
      CoreBatchResult(
        rest.fs,
        step.stdoutChunk + rest.stdoutChunk,
        step.stderrChunk + rest.stderrChunk,
        step.ok && rest.allOk
      )
  }

  ghost function CoreRunFiles(
    cmd: Schema.ChmodCmd,
    plan: CoreModePlan,
    cwd: BenchWorld.Path,
    fs: BenchWorld.FileSystem,
    now: int
  ): CoreBatchResult
  {
    CoreRunFilesFrom(cmd.files, 0, cmd, plan, cwd, fs, now)
  }

  lemma AppendAssociative<T>(a: seq<T>, b: seq<T>, c: seq<T>)
    ensures (a + b) + c == a + (b + c)
  {
  }

  ghost predicate CoreBatchOutcome(
    cmd: Schema.ChmodCmd,
    plan: CoreModePlan,
    fs0: BenchWorld.FileSystem,
    cwd0: BenchWorld.Path,
    fs2: BenchWorld.FileSystem,
    stdout0: BenchWorld.Bytes,
    stdout2: BenchWorld.Bytes,
    stderr0: BenchWorld.Bytes,
    stderr2: BenchWorld.Bytes,
    exit: int,
    now: int
  )
  {
    var result := CoreRunFiles(cmd, plan, cwd0, fs0, now);
    fs2 == result.fs &&
    stdout2 == stdout0 + result.stdoutChunk &&
    stderr2 == stderr0 + result.stderrChunk &&
    exit == (if result.allOk then 0 else 1)
  }

  ghost predicate CoreReferenceFailure(
    cmd: Schema.ChmodCmd,
    fs: BenchWorld.FileSystem,
    cwd: BenchWorld.Path
  )
  {
    exists mode: bv32, err: int ::
      IOContract.GetFileModeContractFields(
        fs,
        Spec.MakeAbsolute(cwd, cmd.referenceFile),
        true,
        false,
        mode,
        err
      )
  }

  ghost predicate CoreReferenceFailureOutcome(
    cmd: Schema.ChmodCmd,
    fs0: BenchWorld.FileSystem,
    cwd0: BenchWorld.Path,
    fs2: BenchWorld.FileSystem,
    stdout0: BenchWorld.Bytes,
    stdout2: BenchWorld.Bytes,
    stderr0: BenchWorld.Bytes,
    stderr2: BenchWorld.Bytes,
    exit: int
  )
  {
    exists mode: bv32, err: int ::
      IOContract.GetFileModeContractFields(
        fs0,
        Spec.MakeAbsolute(cwd0, cmd.referenceFile),
        true,
        false,
        mode,
        err
      ) &&
      fs2 == fs0 && stdout2 == stdout0 &&
      stderr2 == stderr0 + Spec.ReferenceErrorMessageSpec(
        cmd.referenceFile,
        Spec.ErrnoTextSpec(err)
      ) && exit == 1
  }

  ghost predicate CoreReferenceBatchOutcome(
    cmd: Schema.ChmodCmd,
    fs0: BenchWorld.FileSystem,
    cwd0: BenchWorld.Path,
    fs2: BenchWorld.FileSystem,
    stdout0: BenchWorld.Bytes,
    stdout2: BenchWorld.Bytes,
    stderr0: BenchWorld.Bytes,
    stderr2: BenchWorld.Bytes,
    exit: int,
    now: int
  )
  {
    exists refMode: bv32 ::
      IOContract.GetFileModeContractFields(
        fs0,
        Spec.MakeAbsolute(cwd0, cmd.referenceFile),
        true,
        true,
        refMode,
        0
      ) &&
      CoreBatchOutcome(
        cmd,
        CoreReferenceModePlan(refMode),
        fs0,
        cwd0,
        fs2,
        stdout0,
        stdout2,
        stderr0,
        stderr2,
        exit,
        now
      )
  }

  ghost predicate CoreExternalDomain(raw: Schema.ChmodCmdRaw)
  {
    var cmd := Schema.Command(raw);
    Utf8.ValidExternalText(cmd.modeExpr) &&
    Utf8.ValidExternalText(cmd.referenceFile) &&
    forall i :: 0 <= i < |cmd.files| ==>
                  Utf8.ValidExternalText(cmd.files[i])
  }

  twostate predicate CoreSummary(raw: Schema.ChmodCmdRaw, io: BenchIO.IO, exit: int)
    reads io.Footprint()
  {
    var cmd := Schema.Command(raw);
    if cmd.mode == Schema.ModeHelp then
      io.fs() == old(io.fs()) && io.stdout() == old(io.stdout()) + Spec.HelpTextSpec() &&
      io.stderr() == old(io.stderr()) && exit == 0
    else if cmd.mode == Schema.ModeVersion then
      io.fs() == old(io.fs()) && io.stdout() == old(io.stdout()) + Spec.VersionTextSpec() &&
      io.stderr() == old(io.stderr()) && exit == 0
    else if cmd.seenReference && cmd.diagnoseSurprises then
      io.fs() == old(io.fs()) && io.stdout() == old(io.stdout()) &&
      io.stderr() == old(io.stderr()) + Spec.CombineModeReferenceMessageSpec() && exit == 1
    else if |cmd.files| == 0 then
      io.fs() == old(io.fs()) && io.stdout() == old(io.stdout()) &&
      io.stderr() == old(io.stderr()) + Spec.MissingOperandMessageSpec(cmd) && exit == 1
    else if cmd.seenReference &&
            CoreReferenceFailure(cmd, old(io.fs()), old(io.cwd())) then
      CoreReferenceFailureOutcome(
        cmd, old(io.fs()), old(io.cwd()), io.fs(),
        old(io.stdout()), io.stdout(), old(io.stderr()), io.stderr(), exit
      )
    else if !cmd.seenReference && !Schema.IsValidModeExpr(cmd.modeExpr) then
      io.fs() == old(io.fs()) && io.stdout() == old(io.stdout()) &&
      io.stderr() == old(io.stderr()) + Spec.InvalidModeMessageSpec(cmd.modeExpr) && exit == 1
    else if cmd.recursive then
      io.fs() == old(io.fs()) && io.stdout() == old(io.stdout()) &&
      io.stderr() == old(io.stderr()) + Spec.UnsupportedRecursiveMessageSpec() && exit == 1
    else if cmd.seenReference then
      CoreReferenceBatchOutcome(
        cmd, old(io.fs()), old(io.cwd()), io.fs(),
        old(io.stdout()), io.stdout(), old(io.stderr()), io.stderr(), exit,
        old(io.now())
      )
    else
      CoreBatchOutcome(
        cmd,
        CoreGeneralModePlan(
          cmd.modeExpr,
          IOContract.GetUmaskResultFields(old(io.props()))
        ),
        old(io.fs()),
        old(io.cwd()),
        io.fs(),
        old(io.stdout()),
        io.stdout(),
        old(io.stderr()),
        io.stderr(),
        exit,
        old(io.now())
      )
  }

  method Flush(output: BenchWorld.Bytes, diagnostics: BenchWorld.Bytes,
               normalExit: int, io: BenchIO.IO) returns (exit: int)
    modifies io.stdoutRegion, io.stderrRegion
    ensures Spec.EmissionFields(old(io.stdout()), old(io.stderr()), io.stdout(), io.stderr(),
                                io.trustedStreams(), output, diagnostics, normalExit, exit)
  {
    var committed: nat := 0;
    var outErr := 0;
    if |output| != 0 {
      var result := io.WriteStdout(output);
      committed := IOContract.WriteResultCommitted(result);
      outErr := IOContract.ResultErrno(result);
    }
    var finalDiagnostics := diagnostics;
    if outErr != 0 {
      var reason := io.GetCLocaleErrnoText(outErr);
      finalDiagnostics := diagnostics + Spec.WriteErrorText(reason);
    }
    assert finalDiagnostics == diagnostics + (if outErr == 0 then []
                                              else Spec.WriteErrorText(IOContract.CLocaleErrnoTextResult(outErr)));
    var errCommitted: nat := 0;
    var errErr := 0;
    if |finalDiagnostics| != 0 {
      var result := io.WriteStderr(finalDiagnostics);
      errCommitted := IOContract.WriteResultCommitted(result);
      errErr := IOContract.ResultErrno(result);
      assert IOContract.WriteStderrSpec(old(io.stderr()), io.trustedStreams(), io.stderr(),
                                        finalDiagnostics, errCommitted, errErr);
    }
    exit := if outErr != 0 || errErr != 0 then 1 else normalExit;
    assert Spec.EmissionOutcomeFields(old(io.stdout()), old(io.stderr()), io.stdout(), io.stderr(),
                                      io.trustedStreams(), output, diagnostics, normalExit, exit, committed, outErr, errCommitted, errErr);
  }

  function NativeErrnoTextCore(err: int, io: BenchIO.IO): (reason: string)
    ensures reason == IOContract.CLocaleErrnoTextResult(err)
  {
    IOContract.CLocaleErrnoTextResult(err)
  } by method {
    var nativeText := io.GetCLocaleErrnoText(err);
    return nativeText;
  }

  ghost function SuccessfulChangeResultForPost(cmd: Schema.ChmodCmd, plan: CoreModePlan,
                                               path: string, before: bv32,
                                               requested: bv32, isDir: bool, fs: BenchWorld.FileSystem, postOk: bool, postMode: bv32, postErr: int): CorePathResult
  {
    if Spec.SpecPostChangeLookupNeeded(cmd, requested) && !postOk then
      var naive := CoreNaiveMode(plan, before, isDir);
      var surprise := CoreDiagnoseSurprise(cmd, plan, before, requested, isDir);
      CorePathResult(fs,
                     if cmd.verbose then Spec.RetainedMessageSpec(path, requested) else [],
                     (if cmd.silent then [] else Spec.GettingNewAttributesMessageSpec(path,
                                                                                      IOContract.CLocaleErrnoTextResult(postErr))) +
                     (if surprise then Spec.SurpriseModeMessageSpec(path, requested, naive) else []),
                     !surprise, CorePathRetained(requested))
    else
      var after := if Spec.SpecPostChangeLookupNeeded(cmd, requested) && postOk then postMode else requested;
      var naive := CoreNaiveMode(plan, before, isDir);
      var surprise := CoreDiagnoseSurprise(cmd, plan, before, after, isDir);
      CorePathResult(fs, Spec.SpecSuccessStdout(cmd, path, before, after),
                     if surprise then Spec.SurpriseModeMessageSpec(path, after, naive) else [], !surprise,
                     if surprise then CorePathSurprise(before, after, naive)
                     else if before == after then CorePathRetained(after) else CorePathChanged(before, after))
  }
}
