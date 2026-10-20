include "ChmodNormalEntryProof.dfy"
include "ChmodFollowProof.dfy"
include "ChmodObservationProof.dfy"

module ChmodOpenedProof {
  import W = BenchWorld
  import C = IOContract
  import R = Results
  import Base = ChmodSpec
  import Schema = ChmodSchema
  import Spec = ChmodDescriptorSpec
  import Operand = ChmodOperandSpec
  import Normal = ChmodNormalEntryProof
  import Contexts = ChmodContextProof
  import State = ChmodObservationProof
  import Frame = ChmodTraversalProof
  import FrameSpec = ChmodTraversalSpec
  import Follow = ChmodFollowProof
  import Resolution = ChmodResolutionProof
  import Identity = ChmodOperandProof
  import Targets = ChmodEntryProof

  lemma {:isolate_assertions} TargetNames(fs: W.FileSystem, before: W.CwdContext,
    after: W.CwdContext, target: W.CwdTarget)
    requires C.CwdTargetFields(fs, before, target)
    requires FrameSpec.FrameFields(before, after)
    ensures C.CwdTargetNamedPathFields(before, target) == C.CwdTargetNamedPathFields(after, target)
  {
    hide *;
    reveal C.CwdTargetFields(), C.CwdTargetNamedPathFields(), FrameSpec.FrameFields();
  }

  lemma {:isolate_assertions} PositionName(fs: W.FileSystem, before: W.CwdContext,
    after: W.CwdContext, target: W.CwdTarget, handle: int)
    requires C.OpenDirFromCwdTargetContractFields(fs, before, after, R.Ok(target), false, true, handle, 0)
    requires |C.CwdTargetNamedPathFields(before, target)| == 1
    ensures handle in after.capabilities
    ensures var position := after.capabilities[handle].position;
      position in after.topology.nodes &&
      after.topology.nodes[position].pathname == C.CwdTargetNamedPathFields(before, target) &&
      after.capabilities[handle].remaining == after.topology.nodes[position].entries.Keys
  {
    hide *;
    reveal C.OpenDirFromCwdTargetContractFields(), C.CwdResolvedModeCanSucceedFields(),
      C.CwdTargetNamedPathFields(), C.DirectoryCapabilityNamesFields();
    match target
    case CwdNamedTarget(path) =>
    case CwdDirectoryTarget(position) =>
      reveal C.CwdOpenedTopologyFields();
    case CwdEntryTarget(parent, name) =>
      assert false by { reveal C.CwdTargetFields(), C.CwdTargetRecordFields(); }
  }

  lemma {:isolate_assertions} OpenSnapshot(cmd: Schema.ChmodCmd, plan: Base.SpecModePlan,
    scope: Spec.Scope, entry: Spec.Entry, change: Spec.Change, afterOpen: W.CwdContext, handle: int)
    requires cmd.recursive && scope.context.cwd == scope.cwd
    requires C.CwdContextFields(entry.fs, entry.native)
    requires Spec.EntryFields(cmd, scope, entry.identity.displayPath, entry.identity.operand,
      entry.identity.top, entry.fs, entry.native, entry.cursor, entry)
    requires Spec.SuccessfulEntry(cmd, scope, entry) && Spec.CompatibleEntry(cmd, scope, entry)
    requires entry.decision.EntryReady? && !Normal.LogicalSkip(cmd, entry) && entry.identity.isDirectory
    requires Spec.ChangeFields(cmd, plan, scope, entry, entry.fs, entry.result.native, entry.result.cursor, change)
    requires Spec.SuccessfulChange(cmd, scope, entry, change) && Spec.CompatibleChange(cmd, scope, entry, change)
    requires Operand.OpenFields(Base.AtCursor(scope.context, change.result.cursor), change.result.fs,
      change.result.native, entry.identity.operand, afterOpen, true, handle, 0)
    ensures C.CwdContextFields(change.result.fs, afterOpen)
    ensures handle in afterOpen.capabilities && !afterOpen.capabilities[handle].includeDots
    ensures C.DirectoryCapabilityReadCurrentFields(afterOpen.topology, afterOpen.capabilities[handle])
    ensures var identity := Normal.LogicalIdentity(cmd, scope, entry);
      W.FsContainsPath(change.result.fs, identity.resolvedPath) &&
      afterOpen.topology.nodes[afterOpen.capabilities[handle].position].pathname == [identity.resolvedPath] &&
      afterOpen.capabilities[handle].remaining ==
        (set item | item in C.DirectoryEntriesForPathFields(change.result.fs, identity.resolvedPath) :: item.name)
  {
    hide *;
    var operand := entry.identity.operand;
    Normal.SuccessfulEntry(cmd, scope, entry.identity.displayPath, operand, entry.identity.top,
      entry.fs, entry.native, entry.cursor, entry);
    State.EntryState(cmd, scope, entry.identity.displayPath, operand, entry.identity.top,
      entry.fs, entry.native, entry.cursor, entry);
    State.ChangeState(cmd, plan, scope, entry, entry.fs, entry.result.native, entry.result.cursor, change);
    Frame.Transitive(entry.native, entry.result.native, change.result.native);
    var before := Operand.AtOffset(entry.native, entry.rawAttempts);
    Contexts.OffsetValid(entry.fs, entry.native, entry.rawAttempts);
    assert FrameSpec.FrameFields(before, change.result.native) &&
      before.capabilities == change.result.native.capabilities by {
      reveal FrameSpec.FrameFields(), Operand.AtOffset();
    }
    reveal Spec.EntryFields(), Spec.SuccessfulEntry(), Spec.CompatibleEntry(), Normal.LogicalSkip();
    assert entry.identity.metadataFollow == Spec.MetadataFollow(cmd, entry.identity.top);
    var target := entry.targets[0];
    Targets.OffsetTarget(entry.fs, entry.native, target, entry.rawAttempts);
    assert Operand.ResolveTarget(entry.fs, before, operand, entry.identity.metadataFollow) == R.Ok(target);
    if !entry.identity.metadataFollow {
      assert !C.CwdTargetRecordFields(entry.fs, before, target).node.Symlink? by {
        reveal Operand.AtOffset(), C.CwdTargetRecordFields();
      }
      Follow.Nonlink(entry.fs, before, operand, target);
    }
    assert Operand.ResolveTarget(entry.fs, before, operand, true) == R.Ok(target);
    var resolved := Operand.ResolveTarget(change.result.fs, change.result.native, operand, true);
    assert C.OpenDirFromCwdTargetContractFields(change.result.fs, change.result.native,
      afterOpen, resolved, false, true, handle, 0) by {
      reveal Operand.OpenFields(), C.OpenDirAtCwdSpec(), C.OpenDirAtDirSpec(), Operand.ResolveTarget();
    }
    assert resolved.Ok? by { reveal C.OpenDirFromCwdTargetContractFields(); }
    Resolution.TargetsEqual(entry.fs, change.result.fs, before, change.result.native, operand, true);
    TargetNames(entry.fs, before, change.result.native, target);
    assert |C.CwdTargetNamedPathFields(before, target)| == 1 by { reveal Spec.CompatibleResolution(); }
    assert C.CwdTargetNamedPathFields(before, target) == C.CwdTargetNamedPathFields(entry.native, target);
    assert C.CwdTargetNamedPathFields(change.result.native, target) ==
      [Normal.LogicalIdentity(cmd, scope, entry).resolvedPath] by {
      reveal Normal.LogicalIdentity(), Spec.MathematicalIdentity(), Spec.NamedTarget(), Operand.AtOffset(),
        C.CwdTargetNamedPathFields();
    }
    PositionName(change.result.fs, change.result.native, afterOpen, target, handle);
    Identity.FreshCapability(Base.AtCursor(scope.context, change.result.cursor), change.result.fs,
      change.result.native, operand, afterOpen, handle);
    assert C.CwdContextFields(change.result.fs, afterOpen) by { reveal C.OpenDirFromCwdTargetContractFields(); }
    var position := afterOpen.capabilities[handle].position;
    reveal C.CwdContextFields(), C.LiveDirectoryTopologyFields();
  }
}
