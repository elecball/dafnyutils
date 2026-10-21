include "ChmodOperandProof.dfy"

module ChmodEntryProof {
  import W = BenchWorld
  import C = IOContract
  import Operand = ChmodOperandSpec
  import Proof = ChmodOperandProof

  lemma {:isolate_assertions} SameTopologyTarget(fs: W.FileSystem, before: W.CwdContext,
                                                 after: W.CwdContext, target: W.CwdTarget)
    requires before.topology == after.topology
    requires C.CwdTargetFields(fs, before, target)
    ensures C.CwdTargetFields(fs, after, target)
    ensures C.CwdTargetRecordFields(fs, after, target) == C.CwdTargetRecordFields(fs, before, target)
    ensures C.CwdTargetNamedPathFields(after, target) == C.CwdTargetNamedPathFields(before, target)
  {
    hide *;
    reveal C.CwdTargetFields(), C.CwdTargetRecordFields(), C.CwdTargetNamedPathFields();
  }

  lemma {:isolate_assertions} OffsetTarget(fs: W.FileSystem, native: W.CwdContext,
                                           target: W.CwdTarget, offset: nat)
    requires C.CwdTargetFields(fs, native, target)
    ensures C.CwdTargetFields(fs, Operand.AtOffset(native, offset), target)
    ensures C.CwdTargetRecordFields(fs, Operand.AtOffset(native, offset), target) ==
            C.CwdTargetRecordFields(fs, native, target)
    ensures C.CwdTargetNamedPathFields(Operand.AtOffset(native, offset), target) ==
            C.CwdTargetNamedPathFields(native, target)
  {
    hide *;
    reveal C.CwdTargetFields(), C.CwdTargetRecordFields(), C.CwdTargetNamedPathFields(),
           Operand.AtOffset();
  }

  // Preserve the original namespace guarantees whenever the live target has a
  // pathname, while retaining the full authenticated object for detached ones.
  lemma {:isolate_assertions} NamedTargetRecord(fs: W.FileSystem, native: W.CwdContext,
                                                target: W.CwdTarget)
    requires C.CwdContextFields(fs, native)
    requires C.CwdTargetFields(fs, native, target)
    ensures |C.CwdTargetNamedPathFields(native, target)| <= 1
    ensures var paths := C.CwdTargetNamedPathFields(native, target);
            |paths| == 1 ==> (W.FsContainsPath(fs, paths[0]) && C.CwdTargetRecordFields(fs, native, target) == fs.inodes[W.FsIdAt(fs, paths[0])])
    ensures var paths := C.CwdTargetNamedPathFields(native, target);
            |paths| == 1 ==> W.FsNodeAt(fs, paths[0]) == C.CwdTargetRecordFields(fs, native, target).node
  {
    hide *;
    reveal C.CwdContextFields(), C.CwdTargetFields(), C.CwdTargetRecordFields(),
           C.CwdTargetNamedPathFields(), C.LiveDirectoryTopologyFields(), C.LiveObjectRecordsFields();
    match target
    case CwdNamedTarget(path) =>
      Proof.PathRecord(fs, path);
    case CwdDirectoryTarget(position) =>
      var node := native.topology.nodes[position];
      if |node.pathname| == 1 {
        var path := node.pathname[0];
        Proof.PathRecord(fs, path);
        assert fs.inodes[W.FsIdAt(fs, path)].hostKey in native.topology.objects;
      }
    case CwdEntryTarget(parent, name) =>
      var node := native.topology.nodes[parent];
      if |node.pathname| == 1 {
        var path := W.AppendPath(node.pathname[0], name);
        assert W.FsContainsPath(fs, path);
        Proof.PathRecord(fs, path);
        assert fs.inodes[W.FsIdAt(fs, path)].hostKey in native.topology.objects;
      }
  }
}
