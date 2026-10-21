include "ChmodDescriptorSpec.dfy"
include "ChmodOperandCore.dfy"
include "ChmodEntryProof.dfy"
include "ChmodModeProof.dfy"
include "ChmodPathProof.dfy"
include "ChmodContextProof.dfy"

module ChmodNonrecursiveProof {
  import W = BenchWorld
  import C = IOContract
  import R = Results
  import Schema = ChmodSchema
  import Base = ChmodSpec
  import Spec = ChmodDescriptorSpec
  import Operand = ChmodOperandSpec
  import Dispatch = ChmodOperandCore
  import Identity = ChmodOperandProof
  import Targets = ChmodEntryProof
  import Modes = ChmodModeProof
  import Paths = ChmodPathProof
  import Contexts = ChmodContextProof
  import Recursive = ChmodRecursiveSpec

  lemma {:isolate_assertions} StatusStructure(context: Base.ObservationContext,
                                              fs: W.FileSystem, native: W.CwdContext, operand: Operand.Operand, follow: bool)
    requires Operand.StatusAt(context, fs, native, operand, 0, follow).Ok?
    ensures C.CwdContextFields(fs, native)
    ensures Operand.StructureFields(fs, native, operand, follow, true,
                                    Operand.StatusAt(context, fs, native, operand, 0, follow).v, 0)
  {
    hide *;
    reveal Operand.StatusAt(), Operand.AtOffset(), Operand.StructureFields();
    reveal C.ObservedNativeStatusAtCwdResultFields(), C.ObservedNativeStatusAtDirResultFields(),
           C.GetFileStatusAtCwdStructureContractFields(), C.GetFileStatusAtDirContextStructureContractFields(),
           C.DirectoryStatusSameStructure();
    if operand.CwdOperand? {
      assert C.CwdContextFields(fs, native) by {
        reveal C.GetFileStatusFromCwdContextResultFields(), C.ResolvePathAtCwdForMetadataFields();
      }
    } else {
      assert C.CwdContextFields(fs, native) by {
        reveal C.GetFileStatusAtDirContextResultFields(), C.ResolvePathAtDirContextForMetadataFields();
      }
    }
  }

  lemma {:isolate_assertions} NamedStatus(scope: Spec.Scope, context: Base.ObservationContext,
                                          fs: W.FileSystem, native: W.CwdContext, operand: Operand.Operand, follow: bool)
    returns (path: W.Path)
    requires Operand.StatusAt(context, fs, native, operand, 0, follow).Ok?
    requires Spec.CompatibleResolution(scope, fs, native, operand, follow)
    ensures C.CwdContextFields(fs, native)
    ensures W.FsContainsPath(fs, path)
    ensures C.ResolvePathForMetadataFields(fs, Operand.ModelPath(scope.cwd, native, operand), follow) == R.Ok(path)
    ensures var status := Operand.StatusAt(context, fs, native, operand, 0, follow).v;
            status.mode == W.NodeMode(W.FsNodeAt(fs, path)) &&
            status.hostKey == fs.inodes[W.FsIdAt(fs, path)].hostKey &&
            (status.kind == W.DirectoryKind <==> W.FsNodeAt(fs, path).Directory?) &&
            (status.kind == W.SymlinkKind <==> W.FsNodeAt(fs, path).Symlink?)
  {
    hide *;
    StatusStructure(context, fs, native, operand, follow);
    var status := Operand.StatusAt(context, fs, native, operand, 0, follow).v;
    Dispatch.StructureTarget(fs, native, operand, follow, status);
    var target := Operand.ResolveTarget(fs, native, operand, follow).v;
    Targets.NamedTargetRecord(fs, native, target);
    reveal Spec.CompatibleResolution();
    path := C.CwdTargetNamedPathFields(native, target)[0];
  }

  lemma {:isolate_assertions} NamedModeChange(context: Base.ObservationContext, scope: Spec.Scope,
                                              fs: W.FileSystem, native: W.CwdContext, operand: Operand.Operand, follow: bool,
                                              desired: bv32, afterFs: W.FileSystem, afterNative: W.CwdContext)
    returns (path: W.Path)
    requires Operand.SetFields(context, scope.now, fs, native, operand, follow,
                               desired, afterFs, afterNative, true, 0)
    requires Spec.CompatibleResolution(scope, fs, native, operand, follow)
    ensures C.CwdContextFields(fs, native)
    ensures W.FsContainsPath(fs, path) && !W.FsNodeAt(fs, path).Symlink?
    ensures C.ResolvePathForMetadataFields(fs, Operand.ModelPath(scope.cwd, native, operand), follow) == R.Ok(path)
    ensures afterFs == Base.SpecModeSetFs(fs, follow, path, desired, scope.now)
    ensures W.FileSystemTopologyUnchangedExceptMode(fs, afterFs)
  {
    hide *;
    reveal Operand.SetFields(), Operand.ResolveTarget(), C.SetFileModeAtCwdSpec(), C.SetFileModeAtDirSpec();
    var resolved := Operand.ResolveTarget(fs, native, operand, follow);
    assert C.SetFileModeFromCwdTargetContractFields(fs, native, scope.now,
                                                    afterFs, afterNative, resolved, desired, true, 0);
    reveal C.SetFileModeFromCwdTargetContractFields(), C.CwdResolvedModeCanSucceedFields();
    Targets.NamedTargetRecord(fs, native, resolved.v);
    reveal Spec.CompatibleResolution();
    path := C.CwdTargetNamedPathFields(native, resolved.v)[0];
    Modes.ModeChangedNamedPath(fs, path, desired, scope.now);
    reveal Base.SpecModeSetFs(), Base.SpecModeSetSuppressed();
  }

  lemma {:isolate_assertions} SuccessfulResult(cmd: Schema.ChmodCmd, plan: Base.SpecModePlan,
                                               scope: Spec.Scope, entry: Spec.Entry, fs: W.FileSystem, native: W.CwdContext,
                                               cursor: nat, before: bv32, requested: bv32, afterCursor: nat,
                                               afterNative: W.CwdContext, result: Base.SpecPathResult)
    requires Spec.SuccessFields(cmd, plan, scope, entry, fs, native, cursor,
                                before, requested, afterCursor, afterNative, result)
    requires !Base.SpecPostChangeLookupNeeded(cmd, requested) ||
             (Operand.StatusAt(Base.AtCursor(scope.context, cursor), fs, native,
                               entry.identity.operand, 0, true).Ok? &&
              Spec.CompatibleResolution(scope, fs, native, entry.identity.operand, true))
    ensures result.fs == fs
    ensures Base.SpecSuccessfulChangeResultRelation(cmd, plan, entry.identity.displayPath,
                                                    Operand.ModelPath(scope.cwd, native, entry.identity.operand), true,
                                                    before, requested, entry.identity.isDirectory, fs, result)
  {
    hide *;
    reveal Spec.SuccessFields(), Base.SuccessOutputRelation(), Base.SpecSuccessfulChangeResultRelation(), C.ResultValue();
    var display := entry.identity.displayPath;
    var actual := Operand.ModelPath(scope.cwd, native, entry.identity.operand);
    var isDirectory := entry.identity.isDirectory;
    var context := Base.AtCursor(scope.context, cursor);
    var post := Operand.StatusAt(context, fs, native, entry.identity.operand, 0, true);
    var naive: bv32 :| Base.SpecNaiveModeRelation(plan, before, isDirectory, naive) &&
                       if Base.SpecPostChangeLookupNeeded(cmd, requested) then
                         var observed := post.v.mode;
                         var surprise := Base.SpecDiagnoseSurpriseForNaive(cmd, observed, naive);
                         result == Base.SpecPathResult(fs, Base.SpecSuccessStdout(cmd, display, before, observed),
                                                       if surprise then Base.SurpriseModeMessageSpec(display, observed, naive) else [], !surprise,
                                                       if surprise then Base.SpecPathSurprise(before, observed, naive)
                                                       else if before == observed then Base.SpecPathRetained(observed) else Base.SpecPathChanged(before, observed))
                       else
                         var surprise := Base.SpecDiagnoseSurpriseForNaive(cmd, requested, naive);
                         result == Base.SpecPathResult(fs, Base.SpecSuccessStdout(cmd, display, before, requested),
                                                       if surprise then Base.SurpriseModeMessageSpec(display, requested, naive) else [], !surprise,
                                                       if surprise then Base.SpecPathSurprise(before, requested, naive)
                                                       else if before == requested then Base.SpecPathRetained(requested) else Base.SpecPathChanged(before, requested));
    if Base.SpecPostChangeLookupNeeded(cmd, requested) {
      var target := NamedStatus(scope, context, fs, native, entry.identity.operand, true);
      assert post.v.mode == W.NodeMode(W.FsNodeAt(fs, target));
    }
    assert result == Base.SpecSuccessfulChangeResultForNaive(cmd, display, actual, true,
                                                             before, requested, naive, fs) by { reveal Base.SpecSuccessfulChangeResultForNaive(); }
  }

  lemma {:isolate_assertions} NonrecursiveVisit(cmd: Schema.ChmodCmd, plan: Base.SpecModePlan,
                                                scope: Spec.Scope, file: string, fs: W.FileSystem, native: W.CwdContext,
                                                cursor: nat, visit: Spec.Visit) returns (result: Base.SpecPathResult)
    requires !cmd.recursive
    requires scope.context.cwd == scope.cwd
    requires Spec.VisitFields(cmd, plan, scope, file, Operand.CwdOperand(file), true, {},
                              fs, native, cursor, visit)
    requires Spec.SuccessfulVisit(cmd, scope, visit) && Spec.CompatibleVisit(cmd, scope, {}, {}, visit)
    ensures Base.SpecPathStepRelation(cmd, plan, scope.cwd, fs, file, result, scope.now)
    ensures var observed := Spec.Result(visit);
            result.fs == observed.fs && result.stdoutChunk == observed.output &&
            result.stderrChunk == observed.diagnostics && result.ok == observed.ok
  {
    hide *;
    reveal Spec.VisitFields(), Spec.SuccessfulVisit(), Spec.CompatibleVisit();
    var entry := visit.entry;
    var operand := Operand.CwdOperand(file);
    var context := Base.AtCursor(scope.context, cursor);
    reveal Spec.EntryFields(), Spec.SuccessfulEntry(), Spec.CompatibleEntry();
    reveal Operand.ModelPath(), Base.ShouldDereference(), Base.SpecUsesPhysicalTopLevelMetadata();
    var raw := Operand.StatusAt(context, fs, native, operand, 0, false);
    assert raw.Ok? && entry.rawAttempts == 1;
    var rawPath := NamedStatus(scope, context, fs, native, operand, false);
    var actual := Operand.ModelPath(scope.cwd, native, operand);
    assert actual == Base.MakeAbsolute(scope.cwd, file) by {
      reveal Operand.ModelPath(), C.AtCwdPathFields(), Base.MakeAbsolute();
    }
    assert entry.decision.EntryReady? && visit.NodeVisit?;
    assert entry.result.cursor == cursor+2 && entry.result.native == Operand.AtOffset(native, 2);
    assert entry.identity.isSymlink == W.FsNodeAt(fs, rawPath).Symlink?;
    var change := visit.change;
    reveal Spec.SuccessfulChange(), Spec.CompatibleChange(), Spec.ChangeFields();
    var modeContext := Base.AtCursor(scope.context, entry.result.cursor);
    var mode := Operand.StatusAt(modeContext, fs, entry.result.native, operand, 0, entry.identity.metadataFollow);
    assert mode.Ok?;
    assert Spec.ModeFollow(cmd, true) == Base.ShouldDereference(cmd) by { reveal Spec.ModeFollow(); }
    Identity.OffsetAddition(native, 2, 1);
    if entry.identity.isSymlink && !Base.ShouldDereference(cmd) {
      StatusStructure(context, fs, native, operand, false);
      Dispatch.StructureTarget(fs, native, operand, false, raw.v);
      var target := Operand.ResolveTarget(fs, native, operand, false).v;
      Contexts.CwdOffset(fs, native, 3, file, false);
      Targets.OffsetTarget(fs, native, target, 3);
      assert change.setErr != 0 by {
        reveal Spec.ModeFollow(), Operand.SetFields(), Operand.ResolveTarget(), Operand.AtOffset(),
               C.SetFileModeAtCwdSpec(), C.SetFileModeFromCwdTargetContractFields(),
               C.CwdResolvedModeCanSucceedFields();
      }
      assert change.setFs == fs by {
        reveal Operand.SetFields(), C.SetFileModeAtCwdSpec(), C.SetFileModeFromCwdTargetContractFields();
      }
      result := Base.SpecPathResult(fs, change.result.output, change.result.diagnostics,
                                    change.result.ok, Base.SpecPathRetained(raw.v.mode));
      assert Base.SpecPathStepRelation(cmd, plan, scope.cwd, fs, file, result, scope.now) by {
        reveal Base.SpecPathStepRelation(), Base.SpecPathStepForResolutionRelation(),
               Base.SpecNoDereferenceSymlink(), Base.SpecUsesPhysicalTopLevelMetadata(),
               Base.SpecUsesFollowedTopLevelNoDereference(), Recursive.RecursiveSkipStdoutSpec(),
               Recursive.NeitherChangedMessageSpec();
        reveal Spec.MetadataFollow(), Spec.ModeFollow();
        if Base.SpecUsesFollowedTopLevelNoDereference(cmd) && entry.identity.metadataFollow {
          Identity.ShiftStatus(context, fs, native, operand, 1, true);
          var metadataContext := Base.AtCursor(context, cursor+1);
          var metadataNative := Operand.AtOffset(native, 1);
          var followed := NamedStatus(scope, metadataContext, fs, metadataNative, operand, true);
        }
      }
    } else {
      assert change.setErr == 0;
      var metadataPath := NamedStatus(scope, modeContext, fs, entry.result.native,
                                      operand, entry.identity.metadataFollow);
      assert entry.identity.metadataFollow == Spec.MetadataFollow(cmd, true);
      Identity.ShiftStatus(context, fs, native, operand, 1, Spec.MetadataFollow(cmd, true));
      var entryMetadata := NamedStatus(scope, Base.AtCursor(context, cursor+1), fs,
                                       Operand.AtOffset(native, 1), operand, Spec.MetadataFollow(cmd, true));
      assert entry.identity.isDirectory == W.FsNodeAt(fs, metadataPath).Directory?;
      var setContext := Base.AtCursor(modeContext, entry.result.cursor+1);
      var setNative := Operand.AtOffset(entry.result.native, 1);
      var changePath := NamedModeChange(setContext, scope, fs, setNative, operand,
                                        Spec.ModeFollow(cmd, true), change.desired, change.setFs, change.setNative);
      var step: Base.SpecPathResult :| Spec.SuccessFields(cmd, plan, scope, entry,
                                                          change.setFs, change.setNative, entry.result.cursor+1, mode.v.mode,
                                                          W.NormalizeMode(change.desired), change.result.cursor, change.result.native, step) &&
                                       change.result == Spec.State(change.setFs, change.result.cursor, change.result.native,
                                                                   step.stdoutChunk, step.stderrChunk, step.ok);
      SuccessfulResult(cmd, plan, scope, entry, change.setFs, change.setNative, entry.result.cursor+1,
                       mode.v.mode, W.NormalizeMode(change.desired), change.result.cursor, change.result.native, step);
      assert Operand.ModelPath(scope.cwd, setNative, operand) == actual &&
             Operand.ModelPath(scope.cwd, change.setNative, operand) == actual by {
        reveal Operand.ModelPath();
      }
      reveal Spec.MetadataFollow(), Spec.ModeFollow();
      if Base.SpecUsesPhysicalTopLevelMetadata(cmd) {
        assert metadataPath == rawPath && mode.v.mode == raw.v.mode;
        assert entry.identity.isDirectory == W.FsNodeAt(fs, rawPath).Directory?;
      } else {
        if !Base.ShouldDereference(cmd) {
          Paths.MetadataNonlinkFollow(fs, actual, rawPath);
          assert metadataPath == rawPath == changePath;
          if Base.SpecPostChangeLookupNeeded(cmd, W.NormalizeMode(change.desired)) {
            var postContext := Base.AtCursor(scope.context, entry.result.cursor+1);
            var postPath := NamedStatus(scope, postContext, change.setFs, change.setNative, operand, true);
            Paths.MetadataNonlinkModes(fs, change.setFs, actual, rawPath, postPath);
          }
          assert Base.SpecSuccessfulChangeResultRelation(cmd, plan, file, actual, false, mode.v.mode,
                                                         W.NormalizeMode(change.desired), entry.identity.isDirectory, change.setFs, step) by {
            reveal Base.SpecSuccessfulChangeResultRelation(), Base.SpecSuccessfulChangeResultForNaive();
          }
        } else {
          assert metadataPath == changePath;
        }
      }
      result := step;
      assert Base.SpecPathStepRelation(cmd, plan, scope.cwd, fs, file, result, scope.now) by {
        reveal Base.SpecPathStepRelation(), Base.SpecPathStepForResolutionRelation(),
               Base.SpecNoDereferenceSymlink(), Base.SpecNodeIsDirectory(), Base.SpecModeSetSuppressed();
      }
    }
    assert Spec.Result(visit) == change.result by { reveal Spec.Result(); }
  }
}
