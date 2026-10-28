include "ChmodModelProof.dfy"
include "../Spec/ChmodTraversalSpec.dfy"
include "ChmodEntryProof.dfy"

module ChmodResolutionProof {
  import ModelProof = ChmodModelProof
  import W = BenchWorld
  import C = IOContract
  import R = Results
  import Operand = ChmodOperandSpec
  import Frame = ChmodTraversalSpec

  lemma {:isolate_assertions} RawTargetsEqual(beforeFs: W.FileSystem, afterFs: W.FileSystem,
                                              before: W.CwdContext, after: W.CwdContext, segments: seq<string>, index: nat,
                                              current: W.Path, seen: set<W.Path>, fuel: nat, follow: bool, requireDirectory: bool)
    requires W.FileSystemTopologyUnchangedExceptMode(beforeFs, afterFs)
    requires index <= |segments|
    requires C.ResolveRawSymlinkSegmentsFields(beforeFs, segments, index, current, seen, fuel,
                                               follow, false, requireDirectory).Ok?
    requires C.ResolveRawSymlinkSegmentsFields(afterFs, segments, index, current, seen, fuel,
                                               follow, false, requireDirectory).Ok?
    ensures C.CwdNamedResultFields(beforeFs, before,
                                   C.ResolveRawSymlinkSegmentsFields(beforeFs, segments, index, current, seen, fuel, follow, false, requireDirectory)) ==
            C.CwdNamedResultFields(afterFs, after,
                                   C.ResolveRawSymlinkSegmentsFields(afterFs, segments, index, current, seen, fuel, follow, false, requireDirectory))
  {
    hide *;
    var prior := C.ResolveRawSymlinkSegmentsFields(beforeFs, segments, index, current, seen, fuel,
                                                   follow, false, requireDirectory);
    var next := C.ResolveRawSymlinkSegmentsFields(afterFs, segments, index, current, seen, fuel,
                                                  follow, false, requireDirectory);
    ModelProof.ResolveRawSuccessfulTargetsEqualExceptModeFieldsInternal(beforeFs, afterFs, segments, index,
                                                                        current, seen, fuel, follow, requireDirectory, prior.v, next.v);
    reveal C.CwdNamedResultFields();
  }

  lemma {:isolate_assertions} RootTargetsEqual(beforeFs: W.FileSystem, afterFs: W.FileSystem,
                                               before: W.CwdContext, after: W.CwdContext, path: W.Path, follow: bool)
    requires W.FileSystemTopologyUnchangedExceptMode(beforeFs, afterFs)
    requires C.ResolvePathForMetadataFields(beforeFs, path, follow).Ok?
    requires C.ResolvePathForMetadataFields(afterFs, path, follow).Ok?
    ensures C.CwdNamedResultFields(beforeFs, before, C.ResolvePathForMetadataFields(beforeFs, path, follow)) ==
            C.CwdNamedResultFields(afterFs, after, C.ResolvePathForMetadataFields(afterFs, path, follow))
  {
    hide *;
    var prior := C.ResolvePathForMetadataFields(beforeFs, path, follow);
    var next := C.ResolvePathForMetadataFields(afterFs, path, follow);
    ModelProof.ResolvePathForMetadataSuccessfulTargetsEqualExceptModeFields(beforeFs, afterFs, path, follow, prior.v, next.v);
    reveal C.CwdNamedResultFields();
  }

  lemma {:isolate_assertions} PositionFacts(fs: W.FileSystem, native: W.CwdContext,
                                            position: W.DirectoryPosition)
    requires C.CwdContextFields(fs, native) && position in native.topology.nodes
    ensures native.topology.nodes[position].parent in native.topology.nodes
    ensures |native.topology.nodes[position].pathname| <= 1
    ensures forall name | name in native.topology.nodes[position].entries ::
              var entry := native.topology.nodes[position].entries[name];
              entry.status.hostKey in native.topology.objects &&
              (native.topology.objects[entry.status.hostKey].node.Directory? &&
               native.topology.nodes[position].pathname == [] ==>
                 |entry.directory| == 1 && entry.directory[0] in native.topology.nodes)
  {
    hide *;
    reveal C.CwdContextFields(), C.LiveDirectoryTopologyFields(), C.LiveRecordStatusFields(),
           C.LiveObjectRecordsFields(), C.DirectoryStatusSameStructure(), W.FileStatusForRecord(), W.InodeKindConsistent();
  }

  lemma {:isolate_assertions} LiveTargetsEqual(beforeFs: W.FileSystem, afterFs: W.FileSystem,
                                               before: W.CwdContext, after: W.CwdContext, position: W.DirectoryPosition,
                                               segments: seq<string>, index: nat, fuel: nat, follow: bool, requireDirectory: bool)
    requires C.CwdContextFields(beforeFs, before) && C.CwdContextFields(afterFs, after)
    requires W.FileSystemTopologyUnchangedExceptMode(beforeFs, afterFs)
    requires Frame.FrameFields(before, after)
    requires position in before.topology.nodes && index <= |segments|
    requires C.ResolveLiveDirectorySegmentsFields(beforeFs, before, position, segments, index,
                                                  fuel, follow, requireDirectory).Ok?
    requires C.ResolveLiveDirectorySegmentsFields(afterFs, after, position, segments, index,
                                                  fuel, follow, requireDirectory).Ok?
    ensures C.ResolveLiveDirectorySegmentsFields(beforeFs, before, position, segments, index,
                                                 fuel, follow, requireDirectory) ==
            C.ResolveLiveDirectorySegmentsFields(afterFs, after, position, segments, index,
                                                 fuel, follow, requireDirectory)
    decreases fuel, |segments|-index
  {
    hide *;
    reveal Frame.FrameFields(), C.ResolveLiveDirectorySegmentsFields();
    PositionFacts(beforeFs, before, position);
    PositionFacts(afterFs, after, position);
    var node := before.topology.nodes[position];
    var next := after.topology.nodes[position];
    if |node.pathname| == 1 {
      reveal C.CwdNamedResultFields();
      RawTargetsEqual(beforeFs, afterFs, before, after, segments, index, node.pathname[0], {},
                      fuel, follow, requireDirectory);
    } else if index == |segments| {
    } else {
      if segments[index] == "." || segments[index] == ".." {
        LiveTargetsEqual(beforeFs, afterFs, before, after,
                         if segments[index] == ".." then node.parent else position,
                         segments, index+1, fuel, follow, requireDirectory);
      } else {
        assert segments[index] in node.entries;
        var name := segments[index];
        var entry := node.entries[name];
        var record := before.topology.objects[entry.status.hostKey];
        var nextRecord := after.topology.objects[entry.status.hostKey];
        assert W.NodeShapeUnchangedExceptMode(record.node, nextRecord.node);
        reveal W.NodeShapeUnchangedExceptMode();
        match record.node
        case Inaccessible(_) =>
        case Regular(_, _, _, _) =>
        case Directory(_, _, _) =>
          LiveTargetsEqual(beforeFs, afterFs, before, after, entry.directory[0],
                           segments, index+1, fuel, follow, requireDirectory);
        case Symlink(target, _, _, _) =>
          if index+1 == |segments| && !follow && !requireDirectory {
          } else {
            assert fuel > 0;
            var tail := segments[index+1..];
            var substituted := C.RawPathSegmentsFields(target)+tail;
            var directoryRequired := requireDirectory || (|tail| == 0 && C.HasTrailingSlash(target));
            if W.IsAbsolutePath(target) {
              reveal C.CwdNamedResultFields();
              RawTargetsEqual(beforeFs, afterFs, before, after, substituted, 0, "/", {}, fuel-1,
                              follow, directoryRequired);
            } else {
              LiveTargetsEqual(beforeFs, afterFs, before, after, position, substituted, 0, fuel-1,
                               follow, directoryRequired);
            }
          }
      }
    }
  }

  lemma {:isolate_assertions} TargetsEqual(beforeFs: W.FileSystem, afterFs: W.FileSystem,
                                           before: W.CwdContext, after: W.CwdContext, operand: Operand.Operand, follow: bool)
    requires C.CwdContextFields(beforeFs, before) && C.CwdContextFields(afterFs, after)
    requires W.FileSystemTopologyUnchangedExceptMode(beforeFs, afterFs)
    requires Frame.FrameFields(before, after)
    requires before.capabilities == after.capabilities
    requires Operand.ResolveTarget(beforeFs, before, operand, follow).Ok?
    requires Operand.ResolveTarget(afterFs, after, operand, follow).Ok?
    ensures Operand.ResolveTarget(beforeFs, before, operand, follow) ==
            Operand.ResolveTarget(afterFs, after, operand, follow)
  {
    hide *;
    reveal Frame.FrameFields(), Operand.ResolveTarget(), C.ResolvePathAtCwdForMetadataFields(),
           C.ResolvePathAtDirContextForMetadataFields(), C.CwdContextFields();
    var path := operand.path;
    assert path != "" && !((0 as char) in path);
    if W.IsAbsolutePath(path) {
      reveal C.CwdNamedResultFields();
      RootTargetsEqual(beforeFs, afterFs, before, after, path, follow);
    } else if operand.CwdOperand? {
      LiveTargetsEqual(beforeFs, afterFs, before, after, before.position,
                       C.RawPathSegmentsFields(path), 0, W.SYMLINK_MAX_DEPTH, follow, C.HasTrailingSlash(path));
    } else if operand.parent in before.capabilities {
      assert before.capabilities[operand.parent].position in before.topology.nodes by {
        reveal C.DirectoryCapabilityAnchorCurrentFields();
      }
      LiveTargetsEqual(beforeFs, afterFs, before, after, before.capabilities[operand.parent].position,
                       C.RawPathSegmentsFields(path), 0, W.SYMLINK_MAX_DEPTH, follow, C.HasTrailingSlash(path));
    } else {
      assert operand.parent in before.legacyHandles;
      reveal C.CwdNamedResultFields(), C.ResolvePathAtDirForMetadataFields();
      RawTargetsEqual(beforeFs, afterFs, before, after, C.RawPathSegmentsFields(path), 0,
                      before.legacyHandles[operand.parent].path, {}, W.SYMLINK_MAX_DEPTH, follow, C.HasTrailingSlash(path));
    }
  }
}
