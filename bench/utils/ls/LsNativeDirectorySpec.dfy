include "../../core/World.dfy"

module LsNativeDirectorySpec {
  import W = BenchWorld

  ghost function EntryForName(topology: W.LiveDirectoryTopology,
    position: W.DirectoryPosition, name: string): (entry: W.DirEntry)
    requires position in topology.nodes
    requires name == "." || name == ".." || name in topology.nodes[position].entries
    ensures entry.name == name
  {
    if name == "." || name == ".." then W.DirEntry(name, true, false)
    else
      var kind := topology.nodes[position].entries[name].status.kind;
      W.DirEntry(name, kind == W.DirectoryKind, kind == W.SymlinkKind)
  }

  ghost function EntriesForNames(topology: W.LiveDirectoryTopology,
    position: W.DirectoryPosition, names: set<string>): set<W.DirEntry>
    requires position in topology.nodes
    requires names <= topology.nodes[position].entries.Keys + {".", ".."}
  {
    set name | name in names :: EntryForName(topology, position, name)
  }
}
