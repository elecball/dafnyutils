include "LsNativeDirectorySpec.dfy"
include "../../core/IOContract.dfy"

module LsNativeDirectoryProof {
  import W = BenchWorld
  import C = IOContract
  import Spec = LsNativeDirectorySpec

  lemma EntryInjective(topology: W.LiveDirectoryTopology, position: W.DirectoryPosition,
    left: string, right: string)
    requires position in topology.nodes
    requires left in topology.nodes[position].entries.Keys + {".", ".."}
    requires right in topology.nodes[position].entries.Keys + {".", ".."}
    ensures Spec.EntryForName(topology, position, left) == Spec.EntryForName(topology, position, right) <==> left == right
  {
    hide *;
    var leftEntry := Spec.EntryForName(topology, position, left);
    var rightEntry := Spec.EntryForName(topology, position, right);
    assert leftEntry.name == left;
    assert rightEntry.name == right;
    if leftEntry == rightEntry { assert left == right; }
  }

  lemma {:isolate_assertions} Membership(topology: W.LiveDirectoryTopology, position: W.DirectoryPosition,
    names: set<string>, entry: W.DirEntry)
    requires position in topology.nodes
    requires names <= topology.nodes[position].entries.Keys + {".", ".."}
    ensures entry in Spec.EntriesForNames(topology, position, names) <==> (entry.name in names && entry == Spec.EntryForName(topology, position, entry.name))
  {
    hide *;
    reveal Spec.EntriesForNames();
    if entry in Spec.EntriesForNames(topology, position, names) {
      var name :| name in names && Spec.EntryForName(topology, position, name) == entry;
      assert name == entry.name;
    }
  }

  lemma {:isolate_assertions} NameProjection(topology: W.LiveDirectoryTopology,
    position: W.DirectoryPosition, names: set<string>)
    requires position in topology.nodes
    requires names <= topology.nodes[position].entries.Keys + {".", ".."}
    ensures (set entry | entry in Spec.EntriesForNames(topology, position, names) :: entry.name) == names
  {
    hide *;
    var entries := Spec.EntriesForNames(topology, position, names);
    var projected := set entry | entry in entries :: entry.name;
    forall name | name in names
      ensures name in projected
    {
      var entry := Spec.EntryForName(topology, position, name);
      Membership(topology, position, names, entry);
    }
    forall name | name in projected
      ensures name in names
    {
      var entry :| entry in entries && entry.name == name;
      Membership(topology, position, names, entry);
    }
  }

  lemma {:isolate_assertions} RemoveName(topology: W.LiveDirectoryTopology,
    position: W.DirectoryPosition, names: set<string>, name: string)
    requires position in topology.nodes
    requires names <= topology.nodes[position].entries.Keys + {".", ".."}
    requires name in topology.nodes[position].entries.Keys + {".", ".."}
    ensures Spec.EntriesForNames(topology, position, names-{name}) ==
      Spec.EntriesForNames(topology, position, names)-{Spec.EntryForName(topology, position, name)}
  {
    hide *;
    var before := Spec.EntriesForNames(topology, position, names);
    var after := Spec.EntriesForNames(topology, position, names-{name});
    var removed := Spec.EntryForName(topology, position, name);
    forall entry | entry in before + after
      ensures (entry in after) <==> (entry in before-{removed})
    {
      Membership(topology, position, names, entry);
      Membership(topology, position, names-{name}, entry);
      if entry.name in names { EntryInjective(topology, position, entry.name, name); }
    }
    assert after == before-{removed};
  }

  lemma {:isolate_assertions} Subset(topology: W.LiveDirectoryTopology,
    position: W.DirectoryPosition, before: set<string>, after: set<string>)
    requires position in topology.nodes
    requires before <= topology.nodes[position].entries.Keys + {".", ".."}
    requires after <= before
    ensures Spec.EntriesForNames(topology, position, after) <= Spec.EntriesForNames(topology, position, before)
  {
    hide *;
    forall entry | entry in Spec.EntriesForNames(topology, position, after)
      ensures entry in Spec.EntriesForNames(topology, position, before)
    {
      Membership(topology, position, after, entry);
      Membership(topology, position, before, entry);
    }
  }

  lemma Empty(topology: W.LiveDirectoryTopology, position: W.DirectoryPosition)
    requires position in topology.nodes
    ensures Spec.EntriesForNames(topology, position, {}) == {}
  {
    reveal Spec.EntriesForNames();
  }

  lemma {:isolate_assertions} RawKindMatchesEntry(fs: W.FileSystem, topology: W.LiveDirectoryTopology,
    position: W.DirectoryPosition, name: string, kind: W.DirectoryEntryKind)
    requires C.LiveDirectoryTopologyFields(fs, topology)
    requires position in topology.nodes
    requires name == "." || name == ".." || name in topology.nodes[position].entries
    requires if name == "." || name == ".." then kind == W.DirectoryDirentKind
      else kind == topology.nodes[position].entries[name].kind
    ensures C.DirectoryEntryKindMatchesEntry(kind, Spec.EntryForName(topology, position, name))
  {
    hide *;
    reveal C.LiveDirectoryTopologyFields(), C.DirectoryEntryKindMatchesEntry(),
      C.DirectoryEntryKindForFileKind(), Spec.EntryForName();
  }
}
