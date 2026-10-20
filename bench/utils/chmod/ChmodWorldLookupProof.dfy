include "../../core/World.dfy"

module ChmodWorldLookupProof {
  import Result = Results
  import opened BenchWorld

  lemma InodeLookupTreePathWitness(
    inodes: map<InodeId, InodeRecord>,
    tree: InodeTree,
    segs: seq<string>,
    found: InodeTree
  )
    requires InodeFsLookupTreeSegments(inodes, tree, segs) == Result.Ok(found)
    ensures segs in InodeNamespaceIdPaths(tree, found.id)
    decreases |segs|
  {
    if |segs| > 0 {
      InodeLookupTreePathWitness(
        inodes, tree.children[segs[0]], segs[1..], found
      );
      assert [segs[0]] + segs[1..] == segs;
      assert segs in InodeNamespaceIdPaths(tree, found.id);
    }
  }

  lemma FiniteSetSingleton<T>(values: set<T>, value: T)
    requires value in values
    requires |values| == 1
    ensures values == {value}
  {
    assert values == {value} + (values - {value});
    assert |values| == |{value}| + |values - {value}|;
    assert |values - {value}| == 0;
    assert values - {value} == {};
  }

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

  lemma InodeLookupUnchangedByRecordUpdate(
    inodes: map<InodeId, InodeRecord>,
    tree: InodeTree,
    segs: seq<string>,
    id: InodeId,
    record: InodeRecord
  )
    requires id in inodes
    requires InodeSameNodeKind(inodes[id].node, record.node)
    ensures InodeFsLookupTreeSegments(
              inodes[id := record], tree, segs
            ) == InodeFsLookupTreeSegments(inodes, tree, segs)
    decreases |segs|
  {
    if tree.id in inodes && |segs| > 0 {
      if inodes[tree.id].node.Directory? &&
         segs[0] in tree.children
      {
        InodeLookupUnchangedByRecordUpdate(
          inodes, tree.children[segs[0]], segs[1..], id, record
        );
      }
    }
  }

  lemma InodeTreeWellFormedAfterNodeUpdate(
    tree: InodeTree,
    inodes: map<InodeId, InodeRecord>,
    id: InodeId,
    record: InodeRecord
  )
    requires InodeTreeWellFormed(tree, inodes)
    requires id in inodes
    requires InodeSameNodeKind(inodes[id].node, record.node)
    ensures InodeTreeWellFormed(tree, inodes[id := record])
    decreases tree
  {
    assert FsNodeCanHaveChildren(inodes[id].node) ==
           FsNodeCanHaveChildren(record.node);
    forall name | name in tree.children
      ensures InodeTreeWellFormed(
                tree.children[name], inodes[id := record]
              )
    {
      InodeTreeWellFormedAfterNodeUpdate(
        tree.children[name], inodes, id, record
      );
    }
  }
}
