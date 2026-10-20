include "ChmodOperandSpec.dfy"
module ChmodOperandProof {
  import W = BenchWorld
  import C = IOContract
  import Lookup = WorldLookupProof
  import R = Results
  import Operand = ChmodOperandSpec
  import Base = ChmodSpec

  ghost function Target(fs: W.FileSystem, path: W.Path, follow: bool): W.Path
  {
    C.ResultValue(C.ResolvePathForMetadataFields(fs, path, follow), "")
  }

  lemma StatusIdentity(fs: W.FileSystem, path: W.Path, follow: bool, status: W.FileStatus)
    requires C.FileStatusStructureContractFields(fs, path, follow, true, status, 0)
    ensures C.ResolvePathForMetadataFields(fs, path, follow).Ok?
    ensures W.FsContainsPath(fs, Target(fs, path, follow))
    ensures W.FsIdAt(fs, Target(fs, path, follow)) in fs.inodes
    ensures status.hostKey == fs.inodes[W.FsIdAt(fs, Target(fs, path, follow))].hostKey
    ensures status.kind == fs.inodes[W.FsIdAt(fs, Target(fs, path, follow))].kind
  {
    hide *;
    reveal Target(), C.ResultValue(), C.FileStatusStructureContractFields(),
      C.GetFileStatusResultFields(), W.FileStatusForRecord(), W.FsIdAt(),
      W.InodeFsLookupId(), W.FsContainsPath(), W.InodeFsContainsPath();
  }

  lemma HostKeyIdentity(fs: W.FileSystem, left: W.Path, right: W.Path,
    leftStatus: W.FileStatus, rightStatus: W.FileStatus)
    requires C.FileStatusStructureContractFields(fs, left, true, true, leftStatus, 0)
    requires C.FileStatusStructureContractFields(fs, right, true, true, rightStatus, 0)
    ensures (leftStatus.hostKey == rightStatus.hostKey) <==>
      (W.FsIdAt(fs, Target(fs, left, true)) == W.FsIdAt(fs, Target(fs, right, true)))
  {
    hide *;
    StatusIdentity(fs, left, true, leftStatus);
    StatusIdentity(fs, right, true, rightStatus);
    assert W.ValidInodeFileSystemData(fs);
    reveal W.ValidInodeFileSystemData(), W.InodeUniqueHostKeys();
    assert W.InodeUniqueHostKeys(fs);
    var leftId := W.FsIdAt(fs, Target(fs, left, true));
    var rightId := W.FsIdAt(fs, Target(fs, right, true));
    assert leftId in fs.inodes && rightId in fs.inodes;
    if leftStatus.hostKey == rightStatus.hostKey {
      assert fs.inodes[leftId].hostKey == fs.inodes[rightId].hostKey;
      assert leftId == rightId;
    }
  }

  lemma PathInNamespace(fs: W.FileSystem, path: W.Path)
    requires W.FsContainsPath(fs, path)
    ensures W.PathSegments(path) in W.InodeNamespaceIdPaths(fs.namespace, W.FsIdAt(fs, path))
  {
    hide *;
    reveal W.FsContainsPath(), W.InodeFsContainsPath(), W.FsIdAt(), W.InodeFsLookupId();
    var found := W.InodeFsLookupTreeSegments(fs.inodes, fs.namespace, W.PathSegments(path)).v;
    Lookup.InodeLookupTreePathWitness(fs.inodes, fs.namespace, W.PathSegments(path), found);
  }

  lemma DirectoryPathIdentity(fs: W.FileSystem, left: W.Path, right: W.Path)
    requires W.FsContainsPath(fs, left) && W.FsContainsPath(fs, right)
    requires W.FsIdAt(fs, left) == W.FsIdAt(fs, right)
    requires fs.inodes[W.FsIdAt(fs, left)].node.Directory?
    ensures W.PathSegments(left) == W.PathSegments(right)
  {
    hide *;
    PathInNamespace(fs, left);
    PathInNamespace(fs, right);
    var id := W.FsIdAt(fs, left);
    assert W.ValidInodeFileSystemData(fs);
    reveal W.ValidInodeFileSystemData(), W.InodeNamespaceWellFormed(),
      W.FsNodeCanHaveChildren(), W.InodeNamespaceRefCount();
    assert W.InodeNamespaceWellFormed(fs);
    reveal W.FsIdAt(), W.FsContainsPath(), W.InodeFsContainsPath(), W.InodeFsLookupId();
    assert id in fs.inodes;
    assert W.FsNodeCanHaveChildren(fs.inodes[id].node);
    assert W.InodeNamespaceRefCount(fs.namespace, id) == 1;
    Lookup.FiniteSetSingleton(W.InodeNamespaceIdPaths(fs.namespace, id), W.PathSegments(left));
    assert W.PathSegments(right) in {W.PathSegments(left)};
  }

  lemma {:isolate_assertions} PathRecord(fs: W.FileSystem, path: W.Path)
    requires W.FsContainsPath(fs,path)
    ensures W.FsIdAt(fs,path) in fs.inodes
    ensures W.FsNodeAt(fs,path) == fs.inodes[W.FsIdAt(fs,path)].node
  {
    hide *;
    reveal W.FsContainsPath(), W.InodeFsContainsPath(), W.FsIdAt(), W.InodeFsLookupId(),
      W.FsNodeAt(), W.InodeFsNodeAt(), W.InodeFsLookupNode();
  }









  lemma {:isolate_assertions} ActiveMembership(fs: W.FileSystem, paths: set<W.Path>, path: W.Path)
    requires Operand.ActivePathsFields(fs,paths)
    requires W.FsContainsPath(fs,path) && W.FsNodeAt(fs,path).Directory?
    ensures (Operand.DirectoryKey(fs,path) in Operand.ActiveKeys(fs,paths)) <==>
      (W.PathSegments(path) in Operand.ActiveSegments(paths))
  {
    hide *;
    reveal Operand.ActivePathsFields(), Operand.ActiveKeys(), Operand.ActiveSegments();
    assert W.ValidInodeFileSystemData(fs);
    reveal W.ValidInodeFileSystemData(), W.InodeUniqueHostKeys();
    PathRecord(fs,path);
    reveal Operand.DirectoryKey();
    if Operand.DirectoryKey(fs,path) in Operand.ActiveKeys(fs,paths) {
      var ancestor: W.Path :| ancestor in paths && W.FsContainsPath(fs,ancestor) &&
        Operand.DirectoryKey(fs,ancestor) == Operand.DirectoryKey(fs,path);
      PathRecord(fs,ancestor);
      assert W.FsIdAt(fs,ancestor) in fs.inodes && W.FsIdAt(fs,path) in fs.inodes by {
        reveal W.FsIdAt(), W.InodeFsLookupId(), W.FsContainsPath(), W.InodeFsContainsPath();
      }
      assert W.FsIdAt(fs,ancestor) == W.FsIdAt(fs,path);
      assert fs.inodes[W.FsIdAt(fs,path)].node.Directory? by { reveal W.FsNodeAt(), W.InodeFsNodeAt(); }
      DirectoryPathIdentity(fs,path,ancestor);
    }
    if W.PathSegments(path) in Operand.ActiveSegments(paths) {
      var ancestor: W.Path :| ancestor in paths && W.PathSegments(ancestor) == W.PathSegments(path);
      assert W.FsIdAt(fs,ancestor) == W.FsIdAt(fs,path) by { reveal W.FsIdAt(), W.InodeFsLookupId(); }
    }
  }

  lemma {:isolate_assertions} PreserveActivePaths(before: W.FileSystem, after: W.FileSystem, paths: set<W.Path>)
    requires W.FileSystemTopologyUnchangedExceptMode(before,after)
    requires Operand.ActivePathsFields(before,paths)
    ensures Operand.ActivePathsFields(after,paths)
    ensures Operand.ActiveKeys(before,paths) == Operand.ActiveKeys(after,paths)
  {
    hide *;
    reveal Operand.ActivePathsFields(), Operand.ActiveKeys();
    forall path | path in paths
      ensures W.FsContainsPath(after,path) && W.FsNodeAt(after,path).Directory? &&
        Operand.DirectoryKey(before,path) == Operand.DirectoryKey(after,path)
    {
      PathRecord(before,path);
      C.FileSystemTopologyPathFields(before,after,path);
      PathRecord(after,path);
      reveal Operand.DirectoryKey();
      C.FileSystemTopologyLookupSegmentsFields(before,after,W.PathSegments(path));
      assert W.FsIdAt(before,path) == W.FsIdAt(after,path) by {
        reveal W.FsIdAt(), W.InodeFsLookupId(), W.FsLookupSegments();
      }
      reveal W.FileSystemTopologyUnchangedExceptMode(), W.NodeShapeUnchangedExceptMode();
    }
  }

  lemma {:isolate_assertions} ExtendActive(fs: W.FileSystem, paths: set<W.Path>, path: W.Path)
    requires Operand.ActivePathsFields(fs,paths)
    requires W.FsContainsPath(fs,path) && W.FsNodeAt(fs,path).Directory?
    ensures Operand.ActivePathsFields(fs,paths+{path})
    ensures Operand.ActiveKeys(fs,paths+{path}) == Operand.ActiveKeys(fs,paths) + {Operand.DirectoryKey(fs,path)}
    ensures Operand.ActiveSegments(paths+{path}) == Operand.ActiveSegments(paths) + {W.PathSegments(path)}
  {
    hide *;
    reveal Operand.ActivePathsFields(), Operand.ActiveKeys(), Operand.ActiveSegments();
  }

  lemma {:isolate_assertions} PreserveAnchor(before:W.FileSystem,after:W.FileSystem,handles:map<int,W.DirHandleState>,
    origins:map<int,W.FileSystem>,parent:int,path:W.Path)
    requires W.FileSystemTopologyUnchangedExceptMode(before,after)
    requires C.DirectoryParentAnchorForRequestFields(before,handles,origins,parent,path)
    ensures C.DirectoryParentAnchorForRequestFields(after,handles,origins,parent,path)
  {
    hide *;
    reveal C.DirectoryParentAnchorForRequestFields();
    if path!="" && !((0 as char) in path) && !W.IsAbsolutePath(path) && parent in handles {
      reveal C.DirectoryParentAnchorCurrentFields();
      var target:=handles[parent].path;
      PathRecord(before,target);
      C.FileSystemTopologyPathFields(before,after,target);
      C.FileSystemTopologyLookupSegmentsFields(before,after,W.PathSegments(target));
      PathRecord(after,target);
      assert W.FsIdAt(before,target)==W.FsIdAt(after,target) by { reveal W.FsIdAt(),W.InodeFsLookupId(),W.FsLookupSegments(); }
      reveal W.FileSystemTopologyUnchangedExceptMode(),W.NodeShapeUnchangedExceptMode();
    }
  }

  lemma TopologyReflexive(fs:W.FileSystem)
    ensures W.FileSystemTopologyUnchangedExceptMode(fs,fs)
  {
    hide *;
    reveal W.FileSystemTopologyUnchangedExceptMode(),W.NodeShapeUnchangedExceptMode();
  }

  lemma {:isolate_assertions} TopologyTransitive(first:W.FileSystem,middle:W.FileSystem,last:W.FileSystem)
    requires W.FileSystemTopologyUnchangedExceptMode(first,middle)
    requires W.FileSystemTopologyUnchangedExceptMode(middle,last)
    ensures W.FileSystemTopologyUnchangedExceptMode(first,last)
  {
    hide *;
    reveal W.FileSystemTopologyUnchangedExceptMode();
    forall id | id in first.inodes
      ensures W.NodeShapeUnchangedExceptMode(first.inodes[id].node,last.inodes[id].node)
    {
      assert W.NodeShapeUnchangedExceptMode(first.inodes[id].node,middle.inodes[id].node);
      assert W.NodeShapeUnchangedExceptMode(middle.inodes[id].node,last.inodes[id].node);
      reveal W.NodeShapeUnchangedExceptMode();
    }
  }

  lemma TopologyPaths(before:W.FileSystem,after:W.FileSystem)
    requires W.FileSystemTopologyUnchangedExceptMode(before,after)
    ensures W.FsPathSegments(before)==W.FsPathSegments(after)
  {
    hide *;
    reveal W.FileSystemTopologyUnchangedExceptMode(),W.FsPathSegments();
  }

  lemma {:isolate_assertions} PathKeyPreserved(before:W.FileSystem,after:W.FileSystem,path:W.Path)
    requires W.FileSystemTopologyUnchangedExceptMode(before,after)
    requires W.FsContainsPath(before,path)
    ensures W.FsContainsPath(after,path)
    ensures Operand.DirectoryKey(before,path)==Operand.DirectoryKey(after,path)
    ensures W.NodeShapeUnchangedExceptMode(W.FsNodeAt(before,path),W.FsNodeAt(after,path))
  {
    hide *;
    PathRecord(before,path);
    C.FileSystemTopologyPathFields(before,after,path);
    C.FileSystemTopologyLookupSegmentsFields(before,after,W.PathSegments(path));
    PathRecord(after,path);
    assert W.FsIdAt(before,path)==W.FsIdAt(after,path) by { reveal W.FsIdAt(),W.InodeFsLookupId(),W.FsLookupSegments(); }
    reveal Operand.DirectoryKey(),W.FileSystemTopologyUnchangedExceptMode();
  }

  lemma SegmentsAdd(paths:set<W.Path>,path:W.Path)
    ensures Operand.ActiveSegments(paths+{path})==Operand.ActiveSegments(paths)+{W.PathSegments(path)}
  {
    hide *;
    reveal Operand.ActiveSegments();
  }

  lemma {:isolate_assertions} ListedNameRelative(fs:W.FileSystem,path:W.Path,entry:W.DirEntry)
    requires W.FsContainsPath(fs,path)
    requires entry in C.DirectoryEntriesForPathFields(fs,path)
    ensures entry.name!="" && !W.IsAbsolutePath(entry.name)
  {
    hide *;
    reveal C.DirectoryEntriesForPathFields(),C.DirectoryEntriesForTreeFields(),C.EntryForNode(),C.ValidLeafName(),W.LeafName();
  }
  lemma ShiftStatus(context: Base.ObservationContext, fs: W.FileSystem, native: W.CwdContext,
    operand: Operand.Operand, offset: nat, follow: bool)
    ensures Operand.StatusAt(context, fs, native, operand, offset, follow) ==
      Operand.StatusAt(Base.AtCursor(context, context.cursor+offset), fs,
        Operand.AtOffset(native, offset), operand, 0, follow)
  {
    hide *;
    reveal Operand.StatusAt(), Base.AtCursor(), Operand.AtOffset();
  }

  lemma OffsetAddition(native: W.CwdContext, first: nat, second: nat)
    ensures Operand.AtOffset(Operand.AtOffset(native, first), second) == Operand.AtOffset(native, first+second)
  {
    hide *;
    reveal Operand.AtOffset();
  }

  lemma {:isolate_assertions} TargetRecordValid(fs: W.FileSystem, native: W.CwdContext, target: W.CwdTarget)
    requires C.CwdContextFields(fs, native) && C.CwdTargetFields(fs, native, target)
    ensures W.InodeStorageConsistent(C.CwdTargetRecordFields(fs, native, target))
    ensures W.InodeKindConsistent(C.CwdTargetRecordFields(fs, native, target))
  {
    hide *;
    reveal C.CwdContextFields(), C.CwdTargetFields(), C.CwdTargetRecordFields();
    if target.CwdNamedTarget? {
      PathRecord(fs, target.path);
      assert W.ValidInodeFileSystemData(fs);
      reveal W.ValidInodeFileSystemData();
    } else {
      reveal C.LiveDirectoryTopologyFields(), C.LiveObjectRecordsFields();
    }
  }

  lemma ReadPreservesAnchor(fs: W.FileSystem, before: W.CwdContext, after: W.CwdContext, operand: Operand.Operand)
    requires C.CwdContextReadStepFields(before, after)
    requires Operand.AnchorSnapshot(fs, before, operand)
    ensures Operand.AnchorSnapshot(fs, after, operand)
  {
    hide *;
    reveal C.CwdContextReadStepFields(), Operand.AnchorSnapshot(),
      C.DirectoryParentAnchorForContextRequestFields();
  }

  lemma {:isolate_assertions} ModeTopologyIdentity(topology: W.LiveDirectoryTopology,
    key: W.HostInodeKey, mode: bv32, now: int)
    ensures var after := C.ModeChangedTopologyFields(topology, key, mode, now);
      after.root == topology.root && after.nodes.Keys == topology.nodes.Keys
    ensures forall position | position in topology.nodes ::
      var after := C.ModeChangedTopologyFields(topology, key, mode, now).nodes[position];
      var before := topology.nodes[position];
      after.status.hostKey == before.status.hostKey && after.parent == before.parent &&
      after.pathname == before.pathname && after.entries.Keys == before.entries.Keys &&
      after.selfRawInode == before.selfRawInode && after.parentRawInode == before.parentRawInode &&
      after.parentMountBoundary == before.parentMountBoundary
  {
    hide *;
    reveal C.ModeChangedTopologyFields(), C.ModeChangedDirectoryFields(), C.ModeChangedStatusFields();
  }

  lemma {:isolate_assertions} ModePreservesAnchor(fs: W.FileSystem, before: W.CwdContext, now: int,
    afterFs: W.FileSystem, after: W.CwdContext, resolved: W.IOResult<W.CwdTarget>,
    mode: bv32, ok: bool, err: int, operand: Operand.Operand)
    requires C.SetFileModeFromCwdTargetContractFields(fs, before, now, afterFs, after, resolved, mode, ok, err)
    requires Operand.AnchorSnapshot(fs, before, operand)
    ensures Operand.AnchorSnapshot(afterFs, after, operand)
    ensures W.FileSystemTopologyUnchangedExceptMode(fs, afterFs)
    ensures after.capabilities == before.capabilities && after.legacyHandles == before.legacyHandles &&
      after.legacyOrigins == before.legacyOrigins && after.position == before.position && after.hint == before.hint
    ensures after.ordinal == before.ordinal+1
  {
    hide *;
    reveal C.SetFileModeFromCwdTargetContractFields(), C.CwdContextReadStepFields();
    if !ok {
      TopologyReflexive(fs);
      ReadPreservesAnchor(fs, before, after, operand);
    } else {
      reveal C.CwdResolvedModeCanSucceedFields();
      var key := C.CwdTargetRecordFields(fs, before, resolved.v).hostKey;
      ModeTopologyIdentity(before.topology, key, mode, now);
      reveal Operand.AnchorSnapshot(), C.DirectoryParentAnchorForContextRequestFields();
      if operand.DirectoryOperand? && operand.path != "" && !((0 as char) in operand.path) &&
        !W.IsAbsolutePath(operand.path) {
        if operand.parent in before.capabilities {
          reveal C.DirectoryCapabilityAnchorCurrentFields();
        } else if operand.parent in before.legacyHandles {
          reveal C.DirectoryParentAnchorForRequestFields();
          PreserveAnchor(fs, afterFs, before.legacyHandles, before.legacyOrigins, operand.parent, operand.path);
        }
      }
    }
  }

  lemma {:isolate_assertions} FreshCapability(context: Base.ObservationContext, fs: W.FileSystem,
    before: W.CwdContext, operand: Operand.Operand, after: W.CwdContext, handle: int)
    requires Operand.OpenFields(context, fs, before, operand, after, true, handle, 0)
    ensures handle !in before.capabilities && handle !in before.legacyHandles && handle in after.capabilities
    ensures after.capabilities.Keys == before.capabilities.Keys+{handle}
    ensures forall other | other in before.capabilities :: after.capabilities[other] == before.capabilities[other]
    ensures C.DirectoryCapabilityAnchorCurrentFields(after.topology, after.capabilities[handle])
    ensures C.DirectoryCapabilityReadCurrentFields(after.topology, after.capabilities[handle])
    ensures !after.capabilities[handle].includeDots
    ensures after.legacyHandles == before.legacyHandles && after.legacyOrigins == before.legacyOrigins
    ensures C.Extends(before.topology, after.topology)
  {
    hide *;
    reveal Operand.OpenFields(), C.OpenDirAtCwdSpec(), C.OpenDirAtDirSpec(), C.OpenDirFromCwdTargetContractFields();
    reveal C.DirectoryCapabilityAnchorCurrentFields(), C.DirectoryCapabilityReadCurrentFields();
  }

  lemma {:isolate_assertions} ContextAnchorFrame(fs: W.FileSystem, before: W.CwdContext, after: W.CwdContext,
    operand: Operand.Operand)
    requires Operand.AnchorSnapshot(fs, before, operand)
    requires C.Extends(before.topology, after.topology)
    requires after.legacyHandles == before.legacyHandles && after.legacyOrigins == before.legacyOrigins
    requires (operand.DirectoryOperand? && operand.path != "" && !((0 as char) in operand.path) &&
      !W.IsAbsolutePath(operand.path)) ==>
      (operand.parent in after.capabilities <==> operand.parent in before.capabilities)
    requires operand.DirectoryOperand? && operand.parent in before.capabilities ==>
      operand.parent in after.capabilities &&
      after.capabilities[operand.parent].position == before.capabilities[operand.parent].position &&
      after.capabilities[operand.parent].anchorTopology == before.capabilities[operand.parent].anchorTopology
    ensures Operand.AnchorSnapshot(fs, after, operand)
  {
    hide *;
    reveal Operand.AnchorSnapshot(), C.DirectoryParentAnchorForContextRequestFields(), C.Extends(),
      C.DirectoryCapabilityAnchorCurrentFields();
  }

  lemma {:isolate_assertions} ModePreservesReadCurrent(topology: W.LiveDirectoryTopology,
    capability: W.DirectoryCapabilityState, key: W.HostInodeKey, mode: bv32, now: int)
    requires C.DirectoryCapabilityReadCurrentFields(topology, capability)
    ensures C.DirectoryCapabilityReadCurrentFields(C.ModeChangedTopologyFields(topology, key, mode, now), capability)
  {
    hide *;
    ModeTopologyIdentity(topology, key, mode, now);
    reveal C.DirectoryCapabilityReadCurrentFields(), C.DirectoryCapabilityAnchorCurrentFields(),
      C.DirectoryCapabilityNamesFields();
  }

  lemma {:isolate_assertions} ExtensionPreservesReadCurrent(before: W.LiveDirectoryTopology,
    after: W.LiveDirectoryTopology, capability: W.DirectoryCapabilityState)
    requires C.Extends(before, after)
    requires C.DirectoryCapabilityReadCurrentFields(before, capability)
    ensures C.DirectoryCapabilityReadCurrentFields(after, capability)
  {
    hide *;
    reveal C.Extends(), C.DirectoryCapabilityReadCurrentFields(), C.DirectoryCapabilityAnchorCurrentFields(),
      C.DirectoryCapabilityNamesFields();
  }
}
