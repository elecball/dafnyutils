include "../../../core/IOContract.dfy"

module PwdDirectoryModelProof {
  import Result = Results
  import opened BenchWorld
  import opened C = IOContract

  lemma RootDirectorySnapshotFields(fs: FileSystem)
    ensures FsContainsPath(fs,"/")
    ensures FsNodeAt(fs,"/").Directory?
    ensures FsIdAt(fs,"/") == fs.namespace.id
    ensures fs.namespace.id in fs.inodes && fs.inodes[fs.namespace.id].kind == DirectoryKind
    ensures fs.inodes[fs.namespace.id].node.Directory?
    ensures InodeTreeWellFormed(fs.namespace,fs.inodes)
    ensures PathSegments("/") == []
    ensures InodeFsLookupTreeSegments(fs.inodes,fs.namespace,[]) == Result.Ok(fs.namespace)
    ensures GetFileStatusResultFields(fs,"/",false).Ok?
    ensures GetFileStatusResultFields(fs,"/",false).v.kind == DirectoryKind
    ensures forall entry | entry in DirectoryEntriesForPathFields(fs,"/") ::
              InodeChildNameValid(entry.name)
  {
    reveal ValidInodeFileSystemData(), InodeNamespaceWellFormed();
    reveal FsContainsPath(), InodeFsContainsPath(), InodeFsLookupId();
    reveal InodeFsLookupTreeSegments(), PathSegments();
    assert PathSegments("/") == [];
    assert InodeFsLookupTreeSegments(fs.inodes,fs.namespace,[]) == Result.Ok(fs.namespace);
    reveal FsNodeAt(), InodeFsNodeAt(), InodeFsLookupNode();
    reveal GetFileStatusResultFields(), ResolvePathForMetadataFields();
    reveal ResolvePathThroughSymlinkComponentsFields(), ResolvePathThroughSymlinkComponentsWithVisitedFields();
    reveal ResolveRawSymlinkSegmentsFields(), RawPathSegmentsFields();
    reveal StripLeadingSlash(), SplitSegments();
    assert RawPathSegmentsFields("/") == [];
    assert ResolvePathForMetadataFields(fs,"/",false) == Result.Ok("/");
    reveal FsIdAt(), InodeKindConsistent(), InodeValidLinkObservations();
    assert fs.inodes[fs.namespace.id].kind == DirectoryKind;
    assert fs.inodes[fs.namespace.id].links.LinkCountKnown?;
    reveal FileStatusForRecord();
    reveal DirectoryEntriesForPathFields(), DirectoryEntriesForTreeFields();
    forall entry | entry in DirectoryEntriesForPathFields(fs,"/")
      ensures InodeChildNameValid(entry.name)
    {
      var name :| name in fs.namespace.children && ValidLeafName(name) &&
                  entry == EntryForNode(name,InodeTreeChildNodeFields(fs,fs.namespace,name));
      reveal InodeTreeWellFormed(), EntryForNode(), LeafName();
      assert InodeChildNameValid(name);
      assert LeafName(name) == name;
    }
  }
}
