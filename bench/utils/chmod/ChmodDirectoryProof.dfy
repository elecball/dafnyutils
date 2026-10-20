include "ChmodWorldLookupProof.dfy"
include "ChmodOpenedProof.dfy"
include "ChmodVisitFrameProof.dfy"
include "ChmodRecursiveCore.dfy"

module ChmodDirectoryProof {
  import W = BenchWorld
  import C = IOContract
  import Base = ChmodSpec
  import Schema = ChmodSchema
  import Spec = ChmodDescriptorSpec
  import Recursive = ChmodRecursiveSpec
  import Legacy = ChmodRecursiveCore
  import Operand = ChmodOperandSpec
  import Normal = ChmodNormalEntryProof
  import Identity = ChmodOperandProof
  import Opened = ChmodOpenedProof
  import Directory = ChmodDirectoryRuntime
  import State = ChmodObservationProof
  import Visits = ChmodVisitFrameProof
  import Frame = ChmodTraversalProof
  import FrameSpec = ChmodTraversalSpec
  import Lookup = ChmodWorldLookupProof

  ghost function Names(entries: seq<W.DirEntry>): set<string>
  {
    set i | 0 <= i < |entries| :: entries[i].name
  }

  lemma NamesSnoc(entries: seq<W.DirEntry>, entry: W.DirEntry)
    ensures Names(entries+[entry]) == Names(entries)+{entry.name}
  {
    hide *;
    reveal Names();
    forall name: string
      ensures name in Names(entries+[entry]) <==> name in Names(entries)+{entry.name}
    {
      if name in Names(entries+[entry]) {
        var i :| 0 <= i < |entries+[entry]| && (entries+[entry])[i].name == name;
        if i < |entries| { assert entries[i].name == name; }
        else { assert i == |entries| && name == entry.name; }
      } else if name == entry.name {
        assert (entries+[entry])[|entries|].name == name;
      } else if name in Names(entries) {
        var i :| 0 <= i < |entries| && entries[i].name == name;
        assert (entries+[entry])[i].name == name;
      }
    }
  }

  lemma {:isolate_assertions} UniqueName(fs: W.FileSystem, path: W.Path,
    left: W.DirEntry, right: W.DirEntry)
    requires W.FsContainsPath(fs, path)
    requires left in C.DirectoryEntriesForPathFields(fs, path) && right in C.DirectoryEntriesForPathFields(fs, path)
    requires left.name == right.name
    ensures left == right
  {
    hide *;
    reveal C.DirectoryEntriesForPathFields(), C.DirectoryEntriesForTreeFields();
    assert W.ValidInodeFileSystemData(fs);
    reveal W.ValidInodeFileSystemData(), W.InodeNamespaceWellFormed(), W.FsContainsPath(),
      W.InodeFsContainsPath(), W.InodeFsLookupId();
    var tree := W.InodeFsLookupTreeSegments(fs.inodes, fs.namespace, W.PathSegments(path)).v;
    Lookup.InodeLookupTreeWellFormed(fs.inodes, fs.namespace, W.PathSegments(path), tree);
    var lname :| lname in tree.children && C.ValidLeafName(lname) &&
      left == C.EntryForNode(lname, C.InodeTreeChildNodeFields(fs, tree, lname));
    var rname :| rname in tree.children && C.ValidLeafName(rname) &&
      right == C.EntryForNode(rname, C.InodeTreeChildNodeFields(fs, tree, rname));
    reveal C.EntryForNode(), C.ValidLeafName(), W.LeafName();
    assert lname == left.name && rname == right.name;
  }

  lemma {:isolate_assertions} CompleteNames(fs: W.FileSystem, path: W.Path, entries: seq<W.DirEntry>)
    requires W.FsContainsPath(fs, path)
    requires forall i: nat | i < |entries| :: entries[i] in C.DirectoryEntriesForPathFields(fs, path)
    requires (set item | item in C.DirectoryEntriesForPathFields(fs, path) :: item.name) == Names(entries)
    ensures Legacy.EntriesSet(entries) == C.DirectoryEntriesForPathFields(fs, path)
  {
    hide *;
    reveal Legacy.EntriesSet(), Names();
    forall item | item in C.DirectoryEntriesForPathFields(fs, path)
      ensures item in Legacy.EntriesSet(entries)
    {
      assert item.name in (set entry | entry in C.DirectoryEntriesForPathFields(fs, path) :: entry.name);
      assert item.name in Names(entries);
      var i :| 0 <= i < |entries| && entries[i].name == item.name;
      UniqueName(fs, path, item, entries[i]);
    }
  }

  lemma AppendLeafNotRoot(parent: string, name: string)
    requires W.InodeChildNameValid(name)
    ensures W.AppendPath(parent, name) != "/"
    ensures name != "" && !W.IsAbsolutePath(name)
  {
    hide *;
    reveal W.InodeChildNameValid(), W.AppendPath(), W.IsAbsolutePath();
  }

  lemma {:isolate_assertions} Schedule(cmd: Schema.ChmodCmd, plan: Base.SpecModePlan,
    scope: Spec.Scope, display: string, operand: Operand.Operand, top: bool,
    keys: set<W.HostInodeKey>, fs: W.FileSystem, native: W.CwdContext, cursor: nat,
    visit: Spec.Visit) returns (entries: seq<W.DirEntry>)
    requires cmd.recursive && scope.context.cwd == scope.cwd
    requires C.CwdContextFields(fs, native)
    requires Spec.VisitFields(cmd, plan, scope, display, operand, top, keys, fs, native, cursor, visit)
    requires visit.NodeVisit? && visit.listing.ListingOpened?
    requires Spec.SuccessfulVisit(cmd, scope, visit)
    requires Spec.CompatibleEntry(cmd, scope, visit.entry) && Spec.CompatibleChange(cmd, scope, visit.entry, visit.change)
    requires !Normal.LogicalSkip(cmd, visit.entry)
    ensures |entries| == |visit.listing.children|
    ensures W.FsContainsPath(visit.change.result.fs, Normal.LogicalIdentity(cmd, scope, visit.entry).resolvedPath)
    ensures Recursive.ValidOpenSchedule(C.DirectoryEntriesForPathFields(visit.change.result.fs,
      Normal.LogicalIdentity(cmd, scope, visit.entry).resolvedPath), entries, Recursive.RecursiveEof)
    ensures forall i: nat | i < |entries| :: visit.listing.readSteps[i].response.read.DirectoryItem?
    ensures forall i: nat | i < |entries| ::
      entries[i].name == visit.listing.readSteps[i].response.read.name && W.InodeChildNameValid(entries[i].name)
    ensures forall i: nat | i < |entries| ::
      var read := visit.listing.readSteps[i];
      Operand.ModelPath(scope.cwd, read.after, Operand.DirectoryOperand(visit.listing.handle, entries[i].name)) ==
        W.AppendPath(Normal.LogicalIdentity(cmd, scope, visit.entry).resolvedPath, entries[i].name)
    ensures forall i: nat | i <= |entries| ::
      C.CwdContextFields(visit.listing.states[i].fs, visit.listing.states[i].native)
  {
    hide *;
    reveal Spec.VisitFields(), Spec.SuccessfulVisit(), Spec.CompatibleVisit();
    var entry := visit.entry;
    var identity := Normal.LogicalIdentity(cmd, scope, entry);
    var change := visit.change;
    var listing := visit.listing;
    var handle := listing.handle;
    assert entry.fs == fs && entry.native == native && entry.cursor == cursor &&
      entry.identity.displayPath == display && entry.identity.operand == operand && entry.identity.top == top by {
      reveal Spec.EntryFields();
    }
    assert entry.identity.isDirectory;
    Opened.OpenSnapshot(cmd, plan, scope, entry, change, listing.afterOpen, handle);
    var position := listing.afterOpen.capabilities[handle].position;
    assert position in listing.afterOpen.topology.nodes by {
      reveal C.DirectoryCapabilityReadCurrentFields(), C.DirectoryCapabilityAnchorCurrentFields();
    }
    assert listing.afterOpen.topology.nodes[position].pathname == [identity.resolvedPath];
    var snapshot := C.DirectoryEntriesForPathFields(change.result.fs, identity.resolvedPath);
    var snapshotNames := set item | item in snapshot :: item.name;
    var n := |listing.children|;
    entries := [];
    var i: nat := 0;
    Frame.Reflexive(listing.afterOpen);
    Identity.TopologyReflexive(change.result.fs);
    assert Recursive.DuplicateFreePrefix(entries) && Names(entries) == {} by {
      reveal Recursive.DuplicateFreePrefix(), Names();
    }
    while i < n
      invariant i <= n && |entries| == i
      invariant Recursive.DuplicateFreePrefix(entries)
      invariant forall j: nat | j < i :: (listing.readSteps[j].response.read.DirectoryItem? && entries[j] in snapshot &&
        entries[j].name == listing.readSteps[j].response.read.name && W.InodeChildNameValid(entries[j].name))
      invariant forall j: nat | j < i ::
        Operand.ModelPath(scope.cwd, listing.readSteps[j].after, Operand.DirectoryOperand(handle, entries[j].name)) ==
          W.AppendPath(identity.resolvedPath, entries[j].name)
      invariant forall j: nat | j <= i :: C.CwdContextFields(listing.states[j].fs, listing.states[j].native)
      invariant FrameSpec.FrameFields(listing.afterOpen, listing.states[i].native)
      invariant W.FileSystemTopologyUnchangedExceptMode(change.result.fs, listing.states[i].fs)
      invariant handle in listing.states[i].native.capabilities
      invariant listing.states[i].native.capabilities[handle].position == position
      invariant !listing.states[i].native.capabilities[handle].includeDots
      invariant listing.states[i].native.capabilities[handle].remaining == snapshotNames-Names(entries)
      invariant C.DirectoryCapabilityReadCurrentFields(listing.states[i].native.topology,
        listing.states[i].native.capabilities[handle])
      decreases n-i
    {
      var before := listing.states[i];
      var read := listing.readSteps[i];
      var child := listing.children[i];
      assert Spec.DirectoryStepFields(cmd, plan, scope, entry.identity, keys, handle,
        before, listing.states[i+1], read, child);
      reveal Spec.DirectoryStepFields(), Spec.ReadFields();
      Directory.ReadShape(before.fs, read.before, scope.directories, handle, before.cursor, read.response, read.after);
      State.DirectoryState(before.fs, read.before, scope.directories, W.DirectoryReadNext,
        handle, before.cursor, read.response, read.after);
      Frame.Transitive(listing.afterOpen, read.before, read.after);
      Frame.Projection(listing.afterOpen, read.after);
      var name := read.response.read.name;
      var item :| item in snapshot && item.name == name;
      assert name !in Names(entries);
      assert item !in Legacy.EntriesSet(entries) by { reveal Names(), Legacy.EntriesSet(); }
      assert Legacy.DuplicateFreePrefix(entries) by { reveal Legacy.DuplicateFreePrefix(), Recursive.DuplicateFreePrefix(); }
      Legacy.DuplicateFreeSnoc(entries, item);
      assert Recursive.DuplicateFreePrefix(entries+[item]) by {
        reveal Legacy.DuplicateFreePrefix(), Recursive.DuplicateFreePrefix();
      }
      assert read.after.topology.nodes[position].pathname == [identity.resolvedPath] by { reveal FrameSpec.FrameFields(); }
      AppendLeafNotRoot(display, name);
      assert Operand.ModelPath(scope.cwd, read.after, Operand.DirectoryOperand(handle, name)) ==
        W.AppendPath(identity.resolvedPath, name) by { reveal Operand.ModelPath(); }
      Visits.VisitFrame(cmd, plan, scope, W.AppendPath(display, name), Operand.DirectoryOperand(handle, name),
        false, keys+{entry.identity.key}, before.fs, read.after, before.cursor, child);
      var childResult := Spec.Result(child);
      assert listing.states[i+1].fs == childResult.fs && listing.states[i+1].native == childResult.native;
      assert childResult.native.capabilities == read.after.capabilities;
      assert read.after.capabilities[handle].position == position;
      assert read.after.capabilities[handle].remaining == (snapshotNames-Names(entries))-{name};
      assert (snapshotNames-Names(entries))-{name} == snapshotNames-(Names(entries)+{name});
      Frame.Transitive(listing.afterOpen, read.after, childResult.native);
      Frame.ReadCurrent(read.after, childResult.native, read.after.capabilities[handle]);
      Identity.TopologyTransitive(change.result.fs, before.fs, childResult.fs);
      NamesSnoc(entries, item);
      entries := entries+[item];
      i := i+1;
    }
    var terminal := listing.readSteps[n];
    var last := listing.states[n];
    assert terminal.before == last.native && terminal.response.err == 0 && terminal.response.read.DirectoryEnd?;
    assert last.native.capabilities[handle].remaining == {} by {
      reveal Spec.ReadFields(), C.ContextOperationSpec(), C.DirectoryRequestForContextFields(),
        C.DirectoryOperationSpec(), C.DirectoryResponseFields();
    }
    assert snapshotNames == Names(entries) by { reveal Names(); }
    CompleteNames(change.result.fs, identity.resolvedPath, entries);
    reveal Recursive.ValidOpenSchedule(), Legacy.EntriesSet();
  }
}
