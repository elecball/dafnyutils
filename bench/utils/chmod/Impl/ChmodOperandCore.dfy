include "../Spec/ChmodOperandSpec.dfy"
include "../Proof/ChmodOperandProof.dfy"

module ChmodOperandCore {
  import W = BenchWorld
  import BenchIO
  import C = IOContract
  import Base = ChmodSpec
  import Spec = ChmodOperandSpec
  import Proof = ChmodOperandProof

  lemma {:isolate_assertions} StatusProjection(context: Base.ObservationContext, fs: W.FileSystem,
                                               native: W.CwdContext, operand: Spec.Operand, follow: bool, afterCursor: nat, afterNative: W.CwdContext,
                                               ok: bool, status: W.FileStatus, err: int)
    requires Spec.StatusFields(context, fs, native, operand, follow, afterCursor, afterNative, ok, status, err)
    ensures afterCursor == context.cursor+1 && afterNative == Spec.AtOffset(native, 1)
    ensures var expected := Spec.StatusAt(context, fs, native, operand, 0, follow);
            ok == expected.Ok? && err == C.ResultErrno(expected) && (ok ==> status == expected.v)
    ensures Spec.StructureFields(fs, native, operand, follow, ok, status, err)
  {
    hide *;
    reveal Spec.StatusFields(), Spec.StatusAt(), Spec.AtOffset(), Spec.StructureFields(), C.ResultErrno();
    reveal C.CwdContextReadStepFields(), C.GetFileStatusAtCwdSpec(), C.GetFileStatusAtDirSpec(),
           C.ObservedNativeFileStatusAtCwdContractFields(), C.ObservedNativeFileStatusAtDirContractFields();
  }

  lemma {:isolate_assertions} StructureTarget(fs: W.FileSystem, native: W.CwdContext,
                                              operand: Spec.Operand, follow: bool, status: W.FileStatus)
    requires C.CwdContextFields(fs, native)
    requires Spec.StructureFields(fs, native, operand, follow, true, status, 0)
    ensures Spec.ResolveTarget(fs, native, operand, follow).Ok?
    ensures var target := Spec.ResolveTarget(fs, native, operand, follow).v;
            C.CwdTargetFields(fs, native, target) &&
            status.hostKey == C.CwdTargetRecordFields(fs, native, target).hostKey &&
            status.mode == W.NodeMode(C.CwdTargetRecordFields(fs, native, target).node) &&
            status.kind == C.CwdTargetRecordFields(fs, native, target).kind &&
            (status.kind == W.SymlinkKind <==> C.CwdTargetRecordFields(fs, native, target).node.Symlink?) &&
            (status.kind == W.DirectoryKind <==> C.CwdTargetRecordFields(fs, native, target).node.Directory?)
  {
    hide *;
    reveal Spec.StructureFields(), Spec.ResolveTarget(), C.GetFileStatusAtCwdStructureContractFields(),
           C.GetFileStatusAtDirContextStructureContractFields(), C.GetFileStatusFromCwdContextResultFields(),
           C.GetFileStatusAtDirContextResultFields();
    var resolved := Spec.ResolveTarget(fs, native, operand, follow);
    assert resolved.Ok? && C.CwdTargetFields(fs, native, resolved.v);
    Proof.TargetRecordValid(fs, native, resolved.v);
    reveal C.DirectoryStatusSameStructure(), W.FileStatusForRecord(), W.InodeKindConsistent(), W.NodeMode();
  }

  method {:isolate_assertions} ReadStatus(operand: Spec.Operand, follow: bool, io: BenchIO.IO)
    returns (result: W.IOResult<W.FileStatus>)
    requires Spec.AnchorFields(io, operand)
    modifies io.directoryStateRegion, io.statusObservationsRegion
    ensures io.dirHandles() == old(io.dirHandles()) && io.directoryOrigins() == old(io.directoryOrigins())
    ensures io.directoryObservations() == old(io.directoryObservations())
    ensures Spec.StatusFields(old(Base.Context(io)), old(io.fs()), old(io.cwdContext()), operand, follow,
                              io.statusCursor(), io.cwdContext(), result.Ok?, C.ResultValue(result, W.DEFAULT_FILE_STATUS), C.ResultErrno(result))
    ensures result.Ok? <==> C.ResultErrno(result) == 0
    ensures io.statusCursor() == old(io.statusCursor())+1
    ensures io.cwdContext() == Spec.AtOffset(old(io.cwdContext()), 1)
    ensures var expected := Spec.StatusAt(old(Base.Context(io)), old(io.fs()), old(io.cwdContext()), operand, 0, follow);
            result.Ok? == expected.Ok? && C.ResultErrno(result) == C.ResultErrno(expected) && (result.Ok? ==> result.v == expected.v)
    ensures Spec.StructureFields(old(io.fs()), old(io.cwdContext()), operand, follow,
                                 result.Ok?, C.ResultValue(result, W.DEFAULT_FILE_STATUS), C.ResultErrno(result))
    ensures Spec.AnchorFields(io, operand)
    ensures result.Ok? ==> Spec.ResolveTarget(old(io.fs()), old(io.cwdContext()), operand, follow).Ok?
    ensures result.Ok? ==> var target := Spec.ResolveTarget(old(io.fs()), old(io.cwdContext()), operand, follow).v;
                           C.CwdTargetFields(old(io.fs()), old(io.cwdContext()), target) &&
                           result.v.hostKey == C.CwdTargetRecordFields(old(io.fs()), old(io.cwdContext()), target).hostKey &&
                           result.v.mode == W.NodeMode(C.CwdTargetRecordFields(old(io.fs()), old(io.cwdContext()), target).node) &&
                           result.v.kind == C.CwdTargetRecordFields(old(io.fs()), old(io.cwdContext()), target).kind &&
                           (result.v.kind == W.SymlinkKind <==> C.CwdTargetRecordFields(old(io.fs()), old(io.cwdContext()), target).node.Symlink?) &&
                           (result.v.kind == W.DirectoryKind <==> C.CwdTargetRecordFields(old(io.fs()), old(io.cwdContext()), target).node.Directory?)
  {
    hide *;
    ghost var context := Base.Context(io);
    ghost var native := io.cwdContext();
    if operand.CwdOperand? { result := io.GetFileStatusAtCwd(operand.path, follow); }
    else {
      assert C.DirectoryParentAnchorForContextRequestFields(io.fs(), native, operand.parent, operand.path) by {
        reveal Spec.AnchorFields(), Spec.AnchorSnapshot();
      }
      result := io.GetFileStatusAtDir(operand.parent, operand.path, follow);
    }
    assert Spec.StatusFields(context, io.fs(), native, operand, follow, io.statusCursor(), io.cwdContext(),
                             result.Ok?, C.ResultValue(result, W.DEFAULT_FILE_STATUS), C.ResultErrno(result)) by {
      reveal Spec.StatusFields(), Base.Context();
    }
    StatusProjection(context, io.fs(), native, operand, follow, io.statusCursor(), io.cwdContext(),
                     result.Ok?, C.ResultValue(result, W.DEFAULT_FILE_STATUS), C.ResultErrno(result));
    assert Spec.AnchorSnapshot(io.fs(), native, operand) by { reveal Spec.AnchorFields(); }
    Proof.ReadPreservesAnchor(io.fs(), native, io.cwdContext(), operand);
    assert Spec.AnchorFields(io, operand) by { reveal Spec.AnchorFields(); }
    if result.Ok? {
      assert result.v == C.ResultValue(result, W.DEFAULT_FILE_STATUS) by { reveal C.ResultValue(); }
      StructureTarget(io.fs(), native, operand, follow, result.v);
    }
  }

  method {:isolate_assertions} SetMode(operand: Spec.Operand, follow: bool, mode: bv32, io: BenchIO.IO)
    returns (result: W.IOResult<W.Unit>)
    requires Spec.AnchorFields(io, operand)
    modifies io.fsRegion, io.directoryStateRegion
    ensures io.dirHandles() == old(io.dirHandles()) && io.directoryOrigins() == old(io.directoryOrigins())
    ensures io.directoryObservations() == old(io.directoryObservations())
    ensures io.cwdContext().capabilities == old(io.cwdContext()).capabilities
    ensures Spec.SetFields(old(Base.Context(io)), old(io.now()), old(io.fs()), old(io.cwdContext()), operand,
                           follow, mode, io.fs(), io.cwdContext(), result.Ok?, C.ResultErrno(result))
    ensures result.Ok? <==> C.ResultErrno(result) == 0
    ensures W.FileSystemTopologyUnchangedExceptMode(old(io.fs()), io.fs())
    ensures !result.Ok? ==> io.fs() == old(io.fs())
    ensures io.cwdContext().ordinal == old(io.cwdContext()).ordinal+1
    ensures Spec.AnchorFields(io, operand)
  {
    hide *;
    ghost var context := Base.Context(io);
    ghost var fs := io.fs();
    ghost var native := io.cwdContext();
    if operand.CwdOperand? { result := io.SetFileModeAtCwd(operand.path, follow, mode); }
    else {
      assert C.DirectoryParentAnchorForContextRequestFields(fs, native, operand.parent, operand.path) by {
        reveal Spec.AnchorFields(), Spec.AnchorSnapshot();
      }
      result := io.SetFileModeAtDir(operand.parent, operand.path, follow, mode);
    }
    assert Spec.SetFields(context, io.now(), fs, native, operand, follow, mode, io.fs(), io.cwdContext(),
                          result.Ok?, C.ResultErrno(result)) by { reveal Spec.SetFields(), Base.Context(); }
    ghost var resolved := Spec.ResolveTarget(fs, native, operand, follow);
    assert C.SetFileModeFromCwdTargetContractFields(fs, native, io.now(), io.fs(), io.cwdContext(),
                                                    resolved, mode, result.Ok?, C.ResultErrno(result)) by {
      reveal Spec.SetFields(), Spec.ResolveTarget(), C.SetFileModeAtCwdSpec(), C.SetFileModeAtDirSpec();
    }
    assert Spec.AnchorSnapshot(fs, native, operand) by { reveal Spec.AnchorFields(); }
    Proof.ModePreservesAnchor(fs, native, io.now(), io.fs(), io.cwdContext(), resolved,
                              mode, result.Ok?, C.ResultErrno(result), operand);
    assert Spec.AnchorFields(io, operand) by { reveal Spec.AnchorFields(); }
    assert !result.Ok? ==> io.fs() == fs by { reveal C.SetFileModeFromCwdTargetContractFields(); }
  }

  method {:isolate_assertions} Open(operand: Spec.Operand, io: BenchIO.IO) returns (result: W.IOResult<int>)
    requires Spec.AnchorFields(io, operand)
    modifies io.directoryStateRegion
    ensures io.dirHandles() == old(io.dirHandles()) && io.directoryOrigins() == old(io.directoryOrigins())
    ensures io.directoryObservations() == old(io.directoryObservations())
    ensures Spec.OpenFields(old(Base.Context(io)), old(io.fs()), old(io.cwdContext()), operand,
                            io.cwdContext(), result.Ok?, C.ResultValue(result, 0), C.ResultErrno(result))
    ensures result.Ok? <==> C.ResultErrno(result) == 0
    ensures io.cwdContext().ordinal == old(io.cwdContext()).ordinal+1
    ensures Spec.AnchorFields(io, operand)
    ensures !result.Ok? ==> io.cwdContext() == Spec.AtOffset(old(io.cwdContext()), 1)
    ensures result.Ok? ==> result.v !in old(io.cwdContext()).capabilities && result.v !in old(io.cwdContext()).legacyHandles
    ensures result.Ok? ==> (result.v in io.cwdContext().capabilities &&
                            io.cwdContext().capabilities.Keys == old(io.cwdContext()).capabilities.Keys+{result.v})
    ensures result.Ok? ==> forall other | other in old(io.cwdContext()).capabilities ::
                io.cwdContext().capabilities[other] == old(io.cwdContext()).capabilities[other]
    ensures result.Ok? ==> C.DirectoryCapabilityReadCurrentFields(io.cwdContext().topology, io.cwdContext().capabilities[result.v])
    ensures result.Ok? ==> !io.cwdContext().capabilities[result.v].includeDots
    ensures result.Ok? ==> C.Extends(old(io.cwdContext()).topology, io.cwdContext().topology)
  {
    hide *;
    ghost var context := Base.Context(io);
    ghost var native := io.cwdContext();
    if operand.CwdOperand? { result := io.OpenDirAtCwd(operand.path, false); }
    else {
      assert C.DirectoryParentAnchorForContextRequestFields(io.fs(), native, operand.parent, operand.path) by {
        reveal Spec.AnchorFields(), Spec.AnchorSnapshot();
      }
      result := io.OpenDirAtDir(operand.parent, operand.path, false);
    }
    assert Spec.OpenFields(context, io.fs(), native, operand, io.cwdContext(),
                           result.Ok?, C.ResultValue(result, 0), C.ResultErrno(result)) by { reveal Spec.OpenFields(), Base.Context(); }
    assert Spec.AnchorSnapshot(io.fs(), native, operand) by { reveal Spec.AnchorFields(); }
    if result.Ok? {
      assert C.ResultValue(result, 0) == result.v by { reveal C.ResultValue(); }
      Proof.FreshCapability(context, io.fs(), native, operand, io.cwdContext(), result.v);
      if operand.DirectoryOperand? && operand.path != "" && !((0 as char) in operand.path) &&
         !W.IsAbsolutePath(operand.path) {
        assert Spec.ResolveTarget(io.fs(), native, operand, true).Ok? by {
          reveal Spec.OpenFields(), C.OpenDirAtDirSpec(), C.OpenDirFromCwdTargetContractFields(), Spec.ResolveTarget();
        }
        assert operand.parent in native.capabilities || operand.parent in native.legacyHandles by {
          reveal Spec.ResolveTarget(), C.ResolvePathAtDirContextForMetadataFields();
        }
      }
      Proof.ContextAnchorFrame(io.fs(), native, io.cwdContext(), operand);
    } else {
      assert C.CwdContextReadStepFields(native, io.cwdContext()) by {
        reveal Spec.OpenFields(), C.OpenDirAtCwdSpec(), C.OpenDirAtDirSpec(), C.OpenDirFromCwdTargetContractFields();
      }
      Proof.ReadPreservesAnchor(io.fs(), native, io.cwdContext(), operand);
      assert io.cwdContext() == Spec.AtOffset(native, 1) by { reveal C.CwdContextReadStepFields(), Spec.AtOffset(); }
    }
    assert io.cwdContext().ordinal == native.ordinal+1 by {
      reveal Spec.OpenFields(), C.OpenDirAtCwdSpec(), C.OpenDirAtDirSpec(), C.OpenDirFromCwdTargetContractFields(),
             C.CwdContextReadStepFields();
    }
    assert Spec.AnchorFields(io, operand) by { reveal Spec.AnchorFields(); }
  }
}
