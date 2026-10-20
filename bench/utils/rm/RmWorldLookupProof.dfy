include "../../core/World.dfy"

module RmWorldLookupProof {
  import Result = Results
  import opened BenchWorld

  lemma InodeLookupTreeWellFormed(
    inodes: map<InodeId, InodeRecord>,
    tree: InodeTree,
    segs: seq<string>,
    subtree: InodeTree
  )
    requires InodeTreeWellFormed(tree, inodes)
    requires InodeFsLookupTreeSegments(inodes, tree, segs) ==
             Result.Ok(subtree)
    ensures InodeTreeWellFormed(subtree, inodes)
    decreases |segs|
  {
    if |segs| > 0 {
      InodeLookupTreeWellFormed(
        inodes, tree.children[segs[0]], segs[1..], subtree
      );
    }
  }
}
