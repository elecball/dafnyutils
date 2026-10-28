include "../../../core/IOContract.dfy"

module MvMetadataProof {
  import opened BenchWorld
  import opened C = IOContract

  lemma FileStatusStructureImpliesMetadata(
    fs: FileSystem, path: Path, followSymlink: bool,
    ok: bool, status: FileStatus, err: int
  )
    requires FileStatusStructureContractFields(
               fs, path, followSymlink, ok, status, err
             )
    ensures ok ==> PathExistsContractFields(fs, path, followSymlink, ok, err)
    ensures IsDirectoryStrictContractFields(
              fs, path, followSymlink, ok, status.kind == DirectoryKind, err)
    ensures !followSymlink ==>
              IsSymlinkContractFields(fs, path, ok, status.kind == SymlinkKind, err)
  {
    var resolved := ResolvePathForMetadataFields(fs, path, followSymlink);
    if ok && resolved.Ok? {
      var id := FsIdAt(fs, resolved.v);
      assert fs.inodes[id].links.LinkCountKnown?;
      assert FsNodeAt(fs, resolved.v) == fs.inodes[id].node;
      assert InodeKindConsistent(fs.inodes[id]);
    }
  }

  // These are ghost consequences of stat fields, not executable convenience calls.
}
