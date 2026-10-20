include "World.dfy"

module SecurityModel {
  import opened BenchWorld

  // IDs used by filesystem checks can differ from effective process IDs.
  datatype FilesystemIdentity = FilesystemIdentity(fsuid: nat, fsgid: nat)

  // Permission checks use filesystem IDs, supplementary groups, and capabilities.
  // Access/default ACLs, additional LSM restrictions, and grpid mounts need separate models.
  datatype FilesystemSecurityContext = FilesystemSecurityContext(
    fsuid: nat,
    fsgid: nat,
    supplementaryGroups: set<nat>,
    dacOverride: bool,
    dacReadSearch: bool,
    fowner: bool,
    fsetid: bool
  )

  ghost predicate DirectoryAccessAllowed(
    record: InodeRecord, security: FilesystemSecurityContext, requested: bv32
  )
  {
    record.node.Directory? && requested <= (7 as bv32) &&
    (security.dacOverride ||
     (security.dacReadSearch && (requested & (2 as bv32)) == (0 as bv32)) ||
     (var mode := NodeMode(record.node);
      var permission :=
        if security.fsuid == record.ownership.uid then mode >> 6
        else if security.fsgid == record.ownership.gid ||
                record.ownership.gid in security.supplementaryGroups then mode >> 3
        else mode;
      (permission & requested) == requested))
  }

  ghost predicate StickyRemovalAllowed(
    parent: InodeRecord, target: InodeRecord, security: FilesystemSecurityContext
  )
  {
    (NodeMode(parent.node) & (512 as bv32)) == (0 as bv32) ||
    security.fsuid == parent.ownership.uid ||
    security.fsuid == target.ownership.uid || security.fowner
  }

  // Linux generic_permission for non-directories, without ACL/idmapped-mount
  // adjustments. Capabilities do not bypass an absent executable bit on files.
  ghost predicate FileAccessAllowed(
    record: InodeRecord, security: FilesystemSecurityContext, requested: bv32
  )
  {
    !record.node.Directory? && requested <= (7 as bv32) &&
    ((security.dacReadSearch && requested == (4 as bv32)) ||
     (security.dacOverride &&
      ((requested & (1 as bv32)) == (0 as bv32) ||
       (NodeMode(record.node) & (73 as bv32)) != (0 as bv32))) ||
     (var mode := NodeMode(record.node);
      var permission :=
        if security.fsuid == record.ownership.uid then mode >> 6
        else if security.fsgid == record.ownership.gid ||
                record.ownership.gid in security.supplementaryGroups then mode >> 3
        else mode;
      (permission & requested) == requested))
  }


  ghost function DirectorySearchRecord(
    record: InodeRecord, security: FilesystemSecurityContext
  ): InodeRecord
  {
    if !record.node.Directory? then record else
    var mode := NodeMode(record.node);
    var viewedMode := if DirectoryAccessAllowed(record, security, 1 as bv32)
                      then mode | OWNER_EXECUTE_MODE_BIT
                      else mode & (ALL_MODE_BITS ^ OWNER_EXECUTE_MODE_BIT);
    InodeRecordWithNode(record, WithNodeMode(record.node, viewedMode))
  }

  ghost function DirectorySearchInodes(
    inodes: map<InodeId, InodeRecord>, security: FilesystemSecurityContext
  ): map<InodeId, InodeRecord>
  {
    map id | id in inodes :: DirectorySearchRecord(inodes[id], security)
  }


  lemma SearchTreeWellFormed(
    tree: InodeTree, inodes: map<InodeId, InodeRecord>,
    security: FilesystemSecurityContext
  )
    requires InodeTreeWellFormed(tree, inodes)
    ensures InodeTreeWellFormed(tree, DirectorySearchInodes(inodes, security))
    decreases tree
  {
    forall name | name in tree.children
      ensures InodeTreeWellFormed(tree.children[name],
                                  DirectorySearchInodes(inodes, security))
    {
      SearchTreeWellFormed(tree.children[name], inodes, security);
    }
  }

  ghost function DirectorySearchData(
    fs: FileSystem, security: FilesystemSecurityContext
  ): InodeFileSystemData
  {
    InodeFileSystemData(fs.namespace, DirectorySearchInodes(fs.inodes, security))
  }

  lemma DirectorySearchDataValid(fs: FileSystem, security: FilesystemSecurityContext)
    ensures ValidInodeFileSystemData(DirectorySearchData(fs, security))
  {
    var viewed := DirectorySearchData(fs, security);
    SearchTreeWellFormed(fs.namespace, fs.inodes, security);
    assert viewed.inodes.Keys == fs.inodes.Keys;
    forall id | id in fs.inodes
      ensures viewed.inodes[id].hostKey == fs.inodes[id].hostKey
      ensures viewed.inodes[id].links == fs.inodes[id].links
      ensures InodeSameNodeKind(viewed.inodes[id].node, fs.inodes[id].node)
      ensures InodeStorageConsistent(viewed.inodes[id])
      ensures InodeKindConsistent(viewed.inodes[id])
    {
      assert InodeStorageConsistent(fs.inodes[id]);
      assert InodeKindConsistent(fs.inodes[id]);
    }
    assert InodeNamespaceWellFormed(viewed) by {
      assert InodeNamespaceWellFormed(fs);
      forall id | id in viewed.inodes && FsNodeCanHaveChildren(viewed.inodes[id].node)
        ensures InodeNamespaceRefCount(viewed.namespace, id) == 1
      {
        assert FsNodeCanHaveChildren(fs.inodes[id].node);
      }
    }
    assert InodeUniqueHostKeys(viewed) by {
      forall left, right | left in viewed.inodes && right in viewed.inodes &&
        viewed.inodes[left].hostKey == viewed.inodes[right].hostKey
        ensures left == right
      {
        assert fs.inodes[left].hostKey == fs.inodes[right].hostKey;
      }
    }
    assert InodeValidLinkObservations(viewed) by {
      forall id | id in viewed.inodes
        ensures viewed.inodes[id].links.LinkCountKnown? &&
          0 < viewed.inodes[id].links.count &&
          InodeNamespaceRefCount(viewed.namespace, id) <= viewed.inodes[id].links.count
      {
        assert fs.inodes[id].links.LinkCountKnown?;
        assert 0 < fs.inodes[id].links.count;
        assert InodeNamespaceRefCount(fs.namespace, id) <= fs.inodes[id].links.count;
      }
    }
    assert viewed.namespace.id in viewed.inodes;
    assert viewed.inodes[viewed.namespace.id].node.Directory?;
    hide *;
    reveal ValidInodeFileSystemData();
  }

  ghost function DirectorySearchView(
    fs: FileSystem, security: FilesystemSecurityContext
  ): FileSystem
  {
    DirectorySearchDataValid(fs, security);
    DirectorySearchData(fs, security)
  }






}
