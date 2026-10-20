include "ChmodOperandProof.dfy"

module ChmodModeProof {
  import W = BenchWorld
  import C = IOContract
  import Paths = ChmodOperandProof

  lemma {:isolate_assertions} ModeChangedNamedPath(fs: W.FileSystem, path: W.Path,
    mode: bv32, now: int)
    requires W.FsContainsPath(fs, path)
    ensures C.ModeChangedFilesystemFields(fs, fs.inodes[W.FsIdAt(fs, path)].hostKey, mode, now) ==
      W.FsSetPath(fs, path, W.WithNodeChangeTime(W.WithNodeMode(W.FsNodeAt(fs, path), mode), now, 0))
  {
    hide *;
    Paths.PathRecord(fs, path);
    var id := W.FsIdAt(fs, path);
    var key := fs.inodes[id].hostKey;
    var node := W.WithNodeChangeTime(W.WithNodeMode(W.FsNodeAt(fs, path), mode), now, 0);
    var after := C.ModeChangedFilesystemFields(fs, key, mode, now);
    assert W.ValidInodeFileSystemData(fs);
    reveal W.ValidInodeFileSystemData(), W.InodeUniqueHostKeys();
    C.ModeChangedRecordFacts(fs.inodes[id], mode, now);
    reveal C.ModeChangedRecordFields(), C.ModeChangedRecordsFields(), W.InodeRecordWithNode();
    var record := W.InodeRecordWithNode(fs.inodes[id], node);
    assert C.ModeChangedRecordsFields(fs.inodes, key, mode, now) == fs.inodes[id := record] by {
      forall other | other in fs.inodes
        ensures C.ModeChangedRecordsFields(fs.inodes, key, mode, now)[other] == (fs.inodes[id := record])[other]
      {
        if other != id { assert fs.inodes[other].hostKey != key; }
      }
    }
    assert after == fs.(inodes := fs.inodes[id := record]);
    assert W.InodeSameNodeKind(W.FsNodeAt(fs, path), node);
    assert W.InodeFsUpdateNode(fs, path, node) == after by {
      reveal W.InodeFsUpdateNode(), W.FsContainsPath(), W.FsIdAt();
      reveal W.InodeFsContainsPath(), W.InodeFsLookupId(), W.FsNodeAt(), W.InodeFsNodeAt(), W.InodeFsLookupNode();
    }
    assert W.ValidInodeFileSystemData(after);
    reveal W.FsSetPath();
  }
}
