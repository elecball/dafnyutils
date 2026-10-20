include "ChmodOperandSpec.dfy"

module ChmodTraversalSpec {
  import W = BenchWorld

  // Traversal may learn additional named directory positions. Permission
  // changes preserve the identity and entry layout of every prior position.
  ghost predicate FrameFields(before: W.CwdContext, after: W.CwdContext)
  {
    after.hint == before.hint && after.position == before.position &&
    after.legacyHandles == before.legacyHandles && after.legacyOrigins == before.legacyOrigins &&
    after.topology.root == before.topology.root &&
    before.topology.nodes.Keys <= after.topology.nodes.Keys &&
    after.topology.objects.Keys == before.topology.objects.Keys &&
    (forall key | key in before.topology.objects ::
      W.NodeShapeUnchangedExceptMode(before.topology.objects[key].node, after.topology.objects[key].node)) &&
    forall position | position in before.topology.nodes ::
      var prior := before.topology.nodes[position];
      var next := after.topology.nodes[position];
      next.status.hostKey == prior.status.hostKey && next.status.kind == prior.status.kind &&
      next.parent == prior.parent && next.pathname == prior.pathname &&
      next.selfRawInode == prior.selfRawInode && next.parentRawInode == prior.parentRawInode &&
      next.parentMountBoundary == prior.parentMountBoundary && next.entries.Keys == prior.entries.Keys &&
      forall name | name in prior.entries ::
        var oldEntry := prior.entries[name];
        var newEntry := next.entries[name];
        newEntry.rawInode == oldEntry.rawInode && newEntry.kind == oldEntry.kind &&
        newEntry.directory == oldEntry.directory && newEntry.mountBoundary == oldEntry.mountBoundary &&
        newEntry.status.hostKey == oldEntry.status.hostKey && newEntry.status.kind == oldEntry.status.kind
  }
}
