include "ChmodResolutionProof.dfy"
include "ChmodPathProof.dfy"

module ChmodFollowProof {
  import W = BenchWorld
  import C = IOContract
  import R = Results
  import Operand = ChmodOperandSpec
  import Paths = ChmodPathProof
  import Targets = ChmodEntryProof
  import Resolution = ChmodResolutionProof

  lemma {:isolate_assertions} RawNonlink(fs: W.FileSystem, native: W.CwdContext,
    segments: seq<string>, index: nat, current: W.Path, seen: set<W.Path>, fuel: nat,
    directory: bool, target: W.CwdTarget)
    requires C.CwdContextFields(fs, native) && index <= |segments|
    requires C.CwdNamedResultFields(fs, native,
      C.ResolveRawSymlinkSegmentsFields(fs, segments, index, current, seen, fuel, false, false, directory)) == R.Ok(target)
    requires !C.CwdTargetRecordFields(fs, native, target).node.Symlink?
    ensures C.CwdNamedResultFields(fs, native,
      C.ResolveRawSymlinkSegmentsFields(fs, segments, index, current, seen, fuel, true, false, directory)) == R.Ok(target)
  {
    hide *;
    reveal C.CwdNamedResultFields(), C.CwdTargetRecordFields();
    var raw := C.ResolveRawSymlinkSegmentsFields(fs, segments, index, current, seen, fuel, false, false, directory);
    assert raw.Ok?;
    var canonical := C.CanonicalExistingPathFields(fs, raw.v);
    assert target == W.CwdNamedTarget(canonical);
    Targets.NamedTargetRecord(fs, native, target);
    reveal C.CwdTargetNamedPathFields();
    assert !W.FsNodeAt(fs, raw.v).Symlink?;
    Paths.RawNonlinkFollow(fs, segments, index, current, seen, fuel, directory, raw.v);
  }

  lemma {:isolate_assertions} LiveNonlink(fs: W.FileSystem, native: W.CwdContext,
    position: W.DirectoryPosition, segments: seq<string>, index: nat, fuel: nat,
    directory: bool, target: W.CwdTarget)
    requires C.CwdContextFields(fs, native) && position in native.topology.nodes && index <= |segments|
    requires C.ResolveLiveDirectorySegmentsFields(fs, native, position, segments, index,
      fuel, false, directory) == R.Ok(target)
    requires !C.CwdTargetRecordFields(fs, native, target).node.Symlink?
    ensures C.ResolveLiveDirectorySegmentsFields(fs, native, position, segments, index,
      fuel, true, directory) == R.Ok(target)
    decreases fuel, |segments|-index
  {
    hide *;
    Resolution.PositionFacts(fs, native, position);
    reveal C.ResolveLiveDirectorySegmentsFields();
    var node := native.topology.nodes[position];
    if |node.pathname| == 1 {
      RawNonlink(fs, native, segments, index, node.pathname[0], {}, fuel, directory, target);
    } else if index < |segments| {
      if segments[index] == "." || segments[index] == ".." {
        LiveNonlink(fs, native, if segments[index] == ".." then node.parent else position,
          segments, index+1, fuel, directory, target);
      } else {
        assert segments[index] in node.entries;
        var name := segments[index];
        var entry := node.entries[name];
        var record := native.topology.objects[entry.status.hostKey];
        match record.node
        case Inaccessible(_) =>
        case Regular(_, _, _, _) =>
        case Directory(_, _, _) =>
          LiveNonlink(fs, native, entry.directory[0], segments, index+1, fuel, directory, target);
        case Symlink(link, _, _, _) =>
          if index+1 == |segments| && !directory {
            assert false by { reveal C.CwdTargetRecordFields(); }
          } else {
            assert fuel > 0;
            var tail := segments[index+1..];
            var substituted := C.RawPathSegmentsFields(link)+tail;
            var directoryRequired := directory || (|tail| == 0 && C.HasTrailingSlash(link));
            if W.IsAbsolutePath(link) {
              RawNonlink(fs, native, substituted, 0, "/", {}, fuel-1, directoryRequired, target);
            } else {
              LiveNonlink(fs, native, position, substituted, 0, fuel-1, directoryRequired, target);
            }
          }
      }
    }
  }

  lemma {:isolate_assertions} Nonlink(fs: W.FileSystem, native: W.CwdContext,
    operand: Operand.Operand, target: W.CwdTarget)
    requires C.CwdContextFields(fs, native)
    requires Operand.ResolveTarget(fs, native, operand, false) == R.Ok(target)
    requires !C.CwdTargetRecordFields(fs, native, target).node.Symlink?
    ensures Operand.ResolveTarget(fs, native, operand, true) == R.Ok(target)
  {
    hide *;
    reveal Operand.ResolveTarget(), C.ResolvePathAtCwdForMetadataFields(), C.ResolvePathAtDirContextForMetadataFields();
    var path := operand.path;
    assert path != "" && !((0 as char) in path);
    if W.IsAbsolutePath(path) {
      reveal C.CwdNamedResultFields();
      var raw := C.ResolvePathForMetadataFields(fs, path, false);
      assert raw.Ok?;
      var canonical := C.CanonicalExistingPathFields(fs, raw.v);
      assert target == W.CwdNamedTarget(canonical);
      Targets.NamedTargetRecord(fs, native, target);
      reveal C.CwdTargetNamedPathFields();
      assert !W.FsNodeAt(fs, raw.v).Symlink?;
      Paths.MetadataNonlinkFollow(fs, path, raw.v);
    } else if operand.CwdOperand? {
      assert native.position in native.topology.nodes by { reveal C.CwdContextFields(); }
      LiveNonlink(fs, native, native.position, C.RawPathSegmentsFields(path), 0,
        W.SYMLINK_MAX_DEPTH, C.HasTrailingSlash(path), target);
    } else if operand.parent in native.capabilities {
      assert native.capabilities[operand.parent].position in native.topology.nodes by {
        reveal C.DirectoryCapabilityAnchorCurrentFields();
      }
      LiveNonlink(fs, native, native.capabilities[operand.parent].position, C.RawPathSegmentsFields(path), 0,
        W.SYMLINK_MAX_DEPTH, C.HasTrailingSlash(path), target);
    } else {
      reveal C.ResolvePathAtDirForMetadataFields();
      assert operand.parent in native.legacyHandles;
      RawNonlink(fs, native, C.RawPathSegmentsFields(path), 0, native.legacyHandles[operand.parent].path,
        {}, W.SYMLINK_MAX_DEPTH, C.HasTrailingSlash(path), target);
    }
  }
}
