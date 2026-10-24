include "../../core/World.dfy"

module TsortState {
  import BenchWorld

  class SortState {
    var queue: seq<BenchWorld.Bytes>
    var visited: map<BenchWorld.Bytes, bool>
    var indeg: map<BenchWorld.Bytes, nat>

    predicate WellFormed(graph: map<BenchWorld.Bytes, seq<BenchWorld.Bytes>>)
      reads this`queue, this`visited, this`indeg
    {
      visited.Keys == graph.Keys && indeg.Keys == graph.Keys &&
      (forall vertex | vertex in queue :: vertex in graph) &&
      (forall source | source in graph ::
         forall target | target in graph[source] :: target in graph)
    }

    constructor(vertices: seq<BenchWorld.Bytes>)
      ensures queue == []
      ensures visited == (map vertex | vertex in vertices :: false)
      ensures indeg == (map vertex | vertex in vertices :: 0)
    {
      queue := [];
      visited := map vertex | vertex in vertices :: false;
      indeg := map vertex | vertex in vertices :: 0;
    }
  }
}
