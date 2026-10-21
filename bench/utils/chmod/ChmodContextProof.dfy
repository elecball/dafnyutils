include "ChmodOperandProof.dfy"

module ChmodContextProof {
  import W = BenchWorld
  import C = IOContract
  import Operand = ChmodOperandSpec

  lemma {:isolate_assertions} OffsetValid(fs: W.FileSystem, native: W.CwdContext, offset: nat)
    requires C.CwdContextFields(fs, native)
    ensures C.CwdContextFields(fs, Operand.AtOffset(native, offset))
  {
    hide *;
    reveal Operand.AtOffset(), C.CwdContextFields();
  }

  lemma {:isolate_assertions} LiveOffset(fs: W.FileSystem, native: W.CwdContext,
                                         offset: nat, position: W.DirectoryPosition, segments: seq<string>, index: nat,
                                         fuel: nat, follow: bool, directory: bool)
    requires C.CwdContextFields(fs, native)
    requires position in native.topology.nodes && index <= |segments|
    ensures C.ResolveLiveDirectorySegmentsFields(fs, Operand.AtOffset(native, offset),
                                                 position, segments, index, fuel, follow, directory) ==
            C.ResolveLiveDirectorySegmentsFields(fs, native, position, segments, index, fuel, follow, directory)
    decreases fuel, |segments|-index
  {
    hide *;
    OffsetValid(fs, native, offset);
    reveal Operand.AtOffset(), C.ResolveLiveDirectorySegmentsFields(), C.CwdNamedResultFields();
    reveal C.CwdContextFields(), C.LiveDirectoryTopologyFields(), C.LiveRecordStatusFields(),
           C.LiveObjectRecordsFields(), C.DirectoryStatusSameStructure(), W.FileStatusForRecord(), W.InodeKindConsistent();
    var node := native.topology.nodes[position];
    if |node.pathname| != 1 && index < |segments| {
      if segments[index] == "." || segments[index] == ".." {
        LiveOffset(fs, native, offset, if segments[index] == ".." then node.parent else position,
                   segments, index+1, fuel, follow, directory);
      } else if segments[index] in node.entries {
        var name := segments[index];
        var record := native.topology.objects[node.entries[name].status.hostKey];
        if record.node.Directory? {
          LiveOffset(fs, native, offset, node.entries[name].directory[0], segments,
                     index+1, fuel, follow, directory);
        } else if record.node.Symlink? && !(index+1 == |segments| && !follow && !directory) &&
                  record.node.target != "" && fuel > 0 && !W.IsAbsolutePath(record.node.target) {
          var tail := segments[index+1..];
          LiveOffset(fs, native, offset, position, C.RawPathSegmentsFields(record.node.target)+tail,
                     0, fuel-1, follow, directory || (|tail| == 0 && C.HasTrailingSlash(record.node.target)));
        }
      }
    }
  }

  lemma {:isolate_assertions} CwdOffset(fs: W.FileSystem, native: W.CwdContext,
                                        offset: nat, path: W.Path, follow: bool)
    requires C.CwdContextFields(fs, native)
    ensures C.ResolvePathAtCwdForMetadataFields(fs, Operand.AtOffset(native, offset), path, follow) ==
            C.ResolvePathAtCwdForMetadataFields(fs, native, path, follow)
  {
    hide *;
    OffsetValid(fs, native, offset);
    reveal Operand.AtOffset(), C.ResolvePathAtCwdForMetadataFields(), C.CwdNamedResultFields();
    if path != "" && !W.IsAbsolutePath(path) && !((0 as char) in path) {
      assert native.position in native.topology.nodes by { reveal C.CwdContextFields(); }
      LiveOffset(fs, native, offset, native.position, C.RawPathSegmentsFields(path),
                 0, W.SYMLINK_MAX_DEPTH, follow, C.HasTrailingSlash(path));
    }
  }
}
