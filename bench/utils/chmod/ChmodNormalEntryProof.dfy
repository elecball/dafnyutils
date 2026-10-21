include "ChmodNonrecursiveProof.dfy"

module ChmodNormalEntryProof {
  import W = BenchWorld
  import C = IOContract
  import Base = ChmodSpec
  import Spec = ChmodDescriptorSpec
  import Recursive = ChmodRecursiveSpec
  import Operand = ChmodOperandSpec
  import Schema = ChmodSchema
  import Steps = ChmodNonrecursiveProof
  import Identity = ChmodOperandProof
  import Targets = ChmodEntryProof
  import Paths = ChmodPathProof
  import Contexts = ChmodContextProof
  import Dispatch = ChmodOperandCore

  ghost predicate LogicalSkip(cmd: Schema.ChmodCmd, entry: Spec.Entry)
  {
    entry.identity.isSymlink && !Spec.ModeFollow(cmd, entry.identity.top) &&
    (!Recursive.TraversalFollowSpec(cmd, entry.identity.top) ||
     entry.identity.metadataFollow != Spec.MetadataFollow(cmd, entry.identity.top))
  }

  ghost function LogicalIdentity(cmd: Schema.ChmodCmd, scope: Spec.Scope,
                                 entry: Spec.Entry): Recursive.RecursiveIdentity
  {
    if LogicalSkip(cmd, entry) then
      Recursive.RecursiveIdentity(entry.identity.displayPath,
                                  Operand.ModelPath(scope.cwd, entry.native, entry.identity.operand), "",
                                  entry.identity.top, entry.identity.isSymlink, false)
    else Spec.MathematicalIdentity(scope, entry)
  }

  lemma {:isolate_assertions} SuccessfulEntry(cmd: Schema.ChmodCmd, scope: Spec.Scope,
                                              display: string, operand: Operand.Operand, top: bool, fs: W.FileSystem,
                                              native: W.CwdContext, cursor: nat, entry: Spec.Entry)
    requires cmd.recursive && scope.context.cwd == scope.cwd
    requires Spec.EntryFields(cmd, scope, display, operand, top, fs, native, cursor, entry)
    requires Spec.SuccessfulEntry(cmd, scope, entry) && Spec.CompatibleEntry(cmd, scope, entry)
    ensures entry.rawAttempts == 1 && !entry.decision.EntryFailed?
    ensures entry.decision.EntryReady? || entry.decision.EntryPreserved?
    ensures LogicalSkip(cmd, entry) ==> Recursive.SkipVisitSpec(cmd, LogicalIdentity(cmd, scope, entry), fs)
    ensures LogicalSkip(cmd, entry) ==> entry.decision.EntryReady? && !entry.identity.isDirectory
    ensures !LogicalSkip(cmd, entry) ==> Recursive.IdentityResolvesSpec(fs, LogicalIdentity(cmd, scope, entry))
    ensures !LogicalSkip(cmd, entry) ==> LogicalIdentity(cmd, scope, entry) == Spec.MathematicalIdentity(scope, entry)
    ensures var identity := LogicalIdentity(cmd, scope, entry);
            identity.displayPath == display && identity.accessPath == Operand.ModelPath(scope.cwd, native, operand) &&
            identity.isTopLevel == top && identity.isSymlink == entry.identity.isSymlink
    ensures entry.result.fs == fs && entry.result.cursor == cursor+2 &&
            entry.result.native == Operand.AtOffset(native, 2)
    ensures entry.decision.EntryReady? ==> entry.result.output == [] && entry.result.diagnostics == [] && entry.result.ok
    ensures entry.decision.EntryPreserved? ==>
              entry.result.output == [] && entry.result.diagnostics == Recursive.RootPreserveMessageSpec(display, display != "/") &&
              entry.decision.alias == (display != "/") && !entry.result.ok
  {
    hide *;
    reveal Spec.EntryFields(), Spec.SuccessfulEntry(), Spec.CompatibleEntry();
    var context := Base.AtCursor(scope.context, cursor);
    var raw := Operand.StatusAt(context, fs, native, operand, 0, false);
    assert raw.Ok? && entry.rawAttempts == 1;
    var rawPath := Steps.NamedStatus(scope, context, fs, native, operand, false);
    var actual := Operand.ModelPath(scope.cwd, native, operand);
    reveal LogicalSkip(), LogicalIdentity(), Spec.ModeFollow(), Spec.MetadataFollow(), Recursive.ChmodFollowSpec();
    if LogicalSkip(cmd, entry) {
      if entry.identity.metadataFollow == Spec.MetadataFollow(cmd, top) {
        assert !Spec.MetadataFollow(cmd, top);
        Identity.ShiftStatus(context, fs, native, operand, 1, false);
        var shifted := Operand.AtOffset(native, 1);
        var metadataPath := Steps.NamedStatus(scope, Base.AtCursor(context, cursor+1), fs, shifted, operand, false);
        assert Operand.ModelPath(scope.cwd, shifted, operand) == actual by {
          reveal Operand.ModelPath(), Operand.AtOffset();
        }
        assert metadataPath == rawPath && !entry.identity.isDirectory;
      }
      assert Recursive.SkipVisitSpec(cmd, LogicalIdentity(cmd, scope, entry), fs) by {
        reveal Recursive.SkipVisitSpec(), Base.SpecIsDanglingSymlinkFailure(), C.MetadataFailureErrFields();
      }
    } else {
      var metadata := Operand.StatusAt(context, fs, native, operand, 1, Spec.MetadataFollow(cmd, top));
      assert metadata.Ok? && entry.identity.metadataFollow == Spec.MetadataFollow(cmd, top);
      Identity.ShiftStatus(context, fs, native, operand, 1, Spec.MetadataFollow(cmd, top));
      var shifted := Operand.AtOffset(native, 1);
      var metadataPath := Steps.NamedStatus(scope, Base.AtCursor(context, cursor+1), fs,
                                            shifted, operand, Spec.MetadataFollow(cmd, top));
      assert Operand.ModelPath(scope.cwd, shifted, operand) == actual by {
        reveal Operand.ModelPath(), Operand.AtOffset();
      }
      Targets.OffsetTarget(fs, native, entry.targets[0], 1);
      assert Spec.NamedTarget(entry) == [metadataPath] by {
        reveal Spec.NamedTarget(), Spec.CompatibleResolution();
      }
      if !Spec.MetadataFollow(cmd, top) {
        assert !entry.identity.isSymlink;
        Paths.MetadataNonlinkFollow(fs, actual, rawPath);
        assert metadataPath == rawPath;
      }
      assert Recursive.IdentityResolvesSpec(fs, LogicalIdentity(cmd, scope, entry)) by {
        reveal Recursive.IdentityResolvesSpec(), Spec.MathematicalIdentity();
      }
    }
    reveal Spec.MathematicalIdentity();
  }

  lemma {:isolate_assertions} OperandOffset(fs: W.FileSystem, native: W.CwdContext,
                                            offset: nat, operand: Operand.Operand, follow: bool)
    requires C.CwdContextFields(fs, native)
    ensures Operand.ResolveTarget(fs, Operand.AtOffset(native, offset), operand, follow) ==
            Operand.ResolveTarget(fs, native, operand, follow)
  {
    hide *;
    Contexts.OffsetValid(fs, native, offset);
    reveal Operand.ResolveTarget(), Operand.AtOffset();
    if operand.CwdOperand? {
      Contexts.CwdOffset(fs, native, offset, operand.path, follow);
    } else {
      reveal C.ResolvePathAtDirContextForMetadataFields(), C.CwdNamedResultFields();
      if operand.path == "" || (0 as char) in operand.path || W.IsAbsolutePath(operand.path) {
        Contexts.CwdOffset(fs, native, offset, operand.path, follow);
      } else if operand.parent in native.capabilities &&
                C.DirectoryCapabilityAnchorCurrentFields(native.topology, native.capabilities[operand.parent]) {
        assert native.capabilities[operand.parent].position in native.topology.nodes by {
          reveal C.DirectoryCapabilityAnchorCurrentFields();
        }
        Contexts.LiveOffset(fs, native, offset, native.capabilities[operand.parent].position,
                            C.RawPathSegmentsFields(operand.path), 0, W.SYMLINK_MAX_DEPTH, follow, C.HasTrailingSlash(operand.path));
      }
    }
  }

  lemma {:isolate_assertions} SkipChange(cmd: Schema.ChmodCmd, plan: Base.SpecModePlan,
                                         scope: Spec.Scope, entry: Spec.Entry, change: Spec.Change)
    requires cmd.recursive
    requires Spec.EntryFields(cmd, scope, entry.identity.displayPath, entry.identity.operand,
                              entry.identity.top, entry.fs, entry.native, entry.cursor, entry)
    requires Spec.SuccessfulEntry(cmd, scope, entry)
    requires entry.identity.isSymlink && !Spec.ModeFollow(cmd, entry.identity.top)
    requires Spec.ChangeFields(cmd, plan, scope, entry, entry.fs, entry.result.native, entry.result.cursor, change)
    requires Spec.SuccessfulChange(cmd, scope, entry, change)
    ensures change.result.fs == entry.fs
    ensures change.result.output == Recursive.RecursiveSkipStdoutSpec(cmd, entry.identity.displayPath)
    ensures change.result.diagnostics == [] && change.result.ok
    ensures W.FileSystemTopologyUnchangedExceptMode(entry.fs, change.result.fs)
  {
    hide *;
    reveal Spec.EntryFields(), Spec.SuccessfulEntry(), Spec.ChangeFields(), Spec.SuccessfulChange();
    var operand := entry.identity.operand;
    var context := Base.AtCursor(scope.context, entry.cursor);
    var raw := Operand.StatusAt(context, entry.fs, entry.native, operand, 0, false);
    assert raw.Ok? && entry.rawAttempts == 1;
    Steps.StatusStructure(context, entry.fs, entry.native, operand, false);
    Dispatch.StructureTarget(entry.fs, entry.native, operand, false, raw.v);
    var target := Operand.ResolveTarget(entry.fs, entry.native, operand, false).v;
    OperandOffset(entry.fs, entry.native, 3, operand, false);
    Targets.OffsetTarget(entry.fs, entry.native, target, 3);
    Identity.OffsetAddition(entry.native, 2, 1);
    assert change.setErr != 0 by {
      reveal Operand.SetFields(), Operand.ResolveTarget(), Operand.AtOffset(), C.SetFileModeAtCwdSpec(),
             C.SetFileModeAtDirSpec(), C.SetFileModeFromCwdTargetContractFields(), C.CwdResolvedModeCanSucceedFields();
    }
    assert change.setFs == entry.fs by {
      reveal Operand.SetFields(), C.SetFileModeAtCwdSpec(), C.SetFileModeAtDirSpec(),
             C.SetFileModeFromCwdTargetContractFields();
    }
    Identity.TopologyReflexive(entry.fs);
  }

  lemma {:isolate_assertions} ModeModelPath(context: Base.ObservationContext, scope: Spec.Scope,
                                            fs: W.FileSystem, native: W.CwdContext, operand: Operand.Operand, follow: bool,
                                            desired: bv32, afterFs: W.FileSystem, afterNative: W.CwdContext, ok: bool, err: int)
    requires Operand.SetFields(context, scope.now, fs, native, operand, follow,
                               desired, afterFs, afterNative, ok, err)
    ensures Operand.ModelPath(scope.cwd, afterNative, operand) == Operand.ModelPath(scope.cwd, native, operand)
  {
    hide *;
    reveal Operand.SetFields(), Operand.ResolveTarget(), C.SetFileModeAtCwdSpec(), C.SetFileModeAtDirSpec(),
           C.SetFileModeFromCwdTargetContractFields(), C.CwdContextReadStepFields();
    if ok {
      reveal C.CwdResolvedModeCanSucceedFields();
      var resolved := Operand.ResolveTarget(fs, native, operand, follow);
      var key := C.CwdTargetRecordFields(fs, native, resolved.v).hostKey;
      Identity.ModeTopologyIdentity(native.topology, key, desired, scope.now);
    }
    reveal Operand.ModelPath();
  }

  lemma {:isolate_assertions} SuccessfulChange(cmd: Schema.ChmodCmd, plan: Base.SpecModePlan,
                                               scope: Spec.Scope, entry: Spec.Entry, change: Spec.Change) returns (result: Base.SpecPathResult)
    requires cmd.recursive && scope.context.cwd == scope.cwd
    requires Spec.EntryFields(cmd, scope, entry.identity.displayPath, entry.identity.operand,
                              entry.identity.top, entry.fs, entry.native, entry.cursor, entry)
    requires Spec.SuccessfulEntry(cmd, scope, entry) && Spec.CompatibleEntry(cmd, scope, entry)
    requires entry.decision.EntryReady? && !LogicalSkip(cmd, entry)
    requires Recursive.IdentityResolvesSpec(entry.fs, LogicalIdentity(cmd, scope, entry))
    requires Spec.ChangeFields(cmd, plan, scope, entry, entry.fs, entry.result.native, entry.result.cursor, change)
    requires Spec.SuccessfulChange(cmd, scope, entry, change) && Spec.CompatibleChange(cmd, scope, entry, change)
    ensures Recursive.ApplyResolvedSpecRelation(cmd, plan, LogicalIdentity(cmd, scope, entry), entry.fs, result, scope.now)
    ensures result.fs == change.result.fs && result.stdoutChunk == change.result.output &&
            result.stderrChunk == change.result.diagnostics && result.ok == change.result.ok
    ensures W.FileSystemTopologyUnchangedExceptMode(entry.fs, change.result.fs)
  {
    hide *;
    SuccessfulEntry(cmd, scope, entry.identity.displayPath, entry.identity.operand,
                    entry.identity.top, entry.fs, entry.native, entry.cursor, entry);
    var identity := LogicalIdentity(cmd, scope, entry);
    if entry.identity.isSymlink && !Spec.ModeFollow(cmd, entry.identity.top) {
      SkipChange(cmd, plan, scope, entry, change);
      result := Base.SpecPathResult(entry.fs, change.result.output, [], true, Base.SpecPathRetained(0 as bv32));
      assert Recursive.ApplyResolvedSpecRelation(cmd, plan, identity, entry.fs, result, scope.now) by {
        reveal Recursive.ApplyResolvedSpecRelation(), LogicalIdentity(), Spec.MathematicalIdentity(), Spec.ModeFollow();
      }
    } else {
      reveal Spec.ChangeFields(), Spec.SuccessfulChange(), Spec.CompatibleChange();
      var operand := entry.identity.operand;
      var fs := entry.fs;
      var native := entry.result.native;
      var context := Base.AtCursor(scope.context, entry.result.cursor);
      var mode := Operand.StatusAt(context, fs, native, operand, 0, entry.identity.metadataFollow);
      assert mode.Ok? && change.setErr == 0;
      var metadataPath := Steps.NamedStatus(scope, context, fs, native, operand, entry.identity.metadataFollow);
      var actual := Operand.ModelPath(scope.cwd, entry.native, operand);
      assert Operand.ModelPath(scope.cwd, native, operand) == actual && identity.accessPath == actual by {
        reveal Operand.ModelPath(), Operand.AtOffset(), LogicalIdentity(), Spec.MathematicalIdentity();
      }
      if !entry.identity.metadataFollow {
        assert !entry.identity.isSymlink by {
          reveal Spec.EntryFields(), Spec.MetadataFollow(), Spec.ModeFollow(), Recursive.ChmodFollowSpec();
        }
        assert !W.FsNodeAt(fs, metadataPath).Symlink? by { reveal Recursive.IdentityResolvesSpec(); }
        Paths.MetadataNonlinkFollow(fs, actual, metadataPath);
      }
      assert metadataPath == identity.resolvedPath by { reveal Recursive.IdentityResolvesSpec(); }
      var setContext := Base.AtCursor(context, entry.result.cursor+1);
      var setNative := Operand.AtOffset(native, 1);
      var changePath := Steps.NamedModeChange(setContext, scope, fs, setNative, operand,
                                              Spec.ModeFollow(cmd, entry.identity.top), change.desired, change.setFs, change.setNative);
      assert Operand.ModelPath(scope.cwd, setNative, operand) == actual by {
        reveal Operand.ModelPath(), Operand.AtOffset();
      }
      if !Spec.ModeFollow(cmd, entry.identity.top) {
        Paths.MetadataNonlinkFollow(fs, actual, changePath);
      }
      assert changePath == identity.resolvedPath by { reveal Recursive.IdentityResolvesSpec(); }
      assert change.setFs == Base.SpecModeSetFs(fs, true, identity.resolvedPath, change.desired, scope.now) by {
        reveal Base.SpecModeSetFs(), Base.SpecModeSetSuppressed();
      }
      var step: Base.SpecPathResult :| Spec.SuccessFields(cmd, plan, scope, entry, change.setFs,
                                                          change.setNative, entry.result.cursor+1, mode.v.mode, W.NormalizeMode(change.desired),
                                                          change.result.cursor, change.result.native, step) &&
                                       change.result == Spec.State(change.setFs, change.result.cursor, change.result.native,
                                                                   step.stdoutChunk, step.stderrChunk, step.ok);
      Steps.SuccessfulResult(cmd, plan, scope, entry, change.setFs, change.setNative, entry.result.cursor+1,
                             mode.v.mode, W.NormalizeMode(change.desired), change.result.cursor, change.result.native, step);
      ModeModelPath(setContext, scope, fs, setNative, operand, Spec.ModeFollow(cmd, entry.identity.top),
                    change.desired, change.setFs, change.setNative, true, 0);
      result := step;
      assert Recursive.ApplyResolvedSpecRelation(cmd, plan, identity, fs, result, scope.now) by {
        reveal Recursive.ApplyResolvedSpecRelation(), Recursive.IdentityResolvesSpec(), Spec.ModeFollow(),
               LogicalIdentity(), Spec.MathematicalIdentity();
      }
    }
  }
}
