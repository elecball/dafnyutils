include "TsortSortSpec.dfy"

module TsortCycleSpec {
  import BenchWorld
  import SortSpec = TsortSortSpec

  function Distance(size: nat, anchor: nat, index: nat): nat
    requires anchor < size && index < size
  {
    if index > anchor then index - anchor else size - anchor + index
  }

  ghost opaque predicate Rejected(
    vertices: seq<BenchWorld.Bytes>,
    graph: map<BenchWorld.Bytes, seq<BenchWorld.Bytes>>,
    indeg: map<BenchWorld.Bytes, nat>,
    anchor: nat,
    distance: nat
  )
    requires indeg.Keys == graph.Keys && (set v | v in vertices) == graph.Keys
    requires anchor < |vertices|
  {
    var candidate := vertices[(anchor + distance) % |vertices|];
    indeg[candidate] == 0 || vertices[anchor] !in graph[candidate]
  }

  ghost opaque predicate Walk(
    graph: map<BenchWorld.Bytes, seq<BenchWorld.Bytes>>,
    indeg: map<BenchWorld.Bytes, nat>,
    vertices: seq<BenchWorld.Bytes>,
    indices: seq<nat>
  ) {
    indeg.Keys == graph.Keys && (set v | v in vertices) == graph.Keys && |indices| > 0 &&
    (forall i: nat | i < |indices| :: indices[i] < |vertices| && indeg[vertices[indices[i]]] > 0) &&
    (forall j: nat | j < indices[0] :: indeg[vertices[j]] == 0) &&
    (forall i: nat | 0 < i < |indices| ::
       vertices[indices[i - 1]] in graph[vertices[indices[i]]] &&
       (forall j: nat | j < |vertices| && indeg[vertices[j]] > 0 &&
                        vertices[indices[i - 1]] in graph[vertices[j]] ::
          Distance(|vertices|, indices[i - 1], indices[i]) <= Distance(|vertices|, indices[i - 1], j)))
  }

  ghost opaque predicate SelectionFields(
    graph: map<BenchWorld.Bytes, seq<BenchWorld.Bytes>>,
    indeg: map<BenchWorld.Bytes, nat>,
    vertices: seq<BenchWorld.Bytes>,
    indices: seq<nat>,
    begin: nat,
    cycle: seq<BenchWorld.Bytes>
  ) {
    Walk(graph, indeg, vertices, indices) && |indices| >= 3 &&
    (forall i: nat | i < |indices| :: indices[i] < |vertices|) &&
    1 <= begin < |indices| - 1 &&
    (forall i: nat, j: nat | 1 <= i < j < |indices| - 1 :: indices[i] != indices[j]) &&
    indices[|indices| - 1] == indices[begin] && |cycle| == |indices| - 1 - begin &&
    (forall i: nat | i < |cycle| :: cycle[i] == vertices[indices[|indices| - 2 - i]])
  }

  ghost opaque predicate Selected(
    graph: map<BenchWorld.Bytes, seq<BenchWorld.Bytes>>,
    indeg: map<BenchWorld.Bytes, nat>,
    cycle: seq<BenchWorld.Bytes>
  ) {
    exists vertices: seq<BenchWorld.Bytes>, indices: seq<nat>, begin: nat ::
      SortSpec.Ordered(vertices) &&
      (forall i: nat, j: nat | i < j < |vertices| :: vertices[i] != vertices[j]) &&
      SelectionFields(graph, indeg, vertices, indices, begin, cycle)
  }

  ghost opaque predicate Path(
    graph: map<BenchWorld.Bytes, seq<BenchWorld.Bytes>>,
    indeg: map<BenchWorld.Bytes, nat>,
    path: seq<BenchWorld.Bytes>
  )
  {
    |path| > 0 &&
    (forall v | v in path :: v in graph && v in indeg && indeg[v] > 0) &&
    (forall i: nat | i + 1 < |path| :: path[i + 1] in graph[path[i]]) &&
    (forall i: nat, j: nat | i < j < |path| - 1 :: path[i] != path[j])
  }

  ghost predicate Cycle(
    graph: map<BenchWorld.Bytes, seq<BenchWorld.Bytes>>,
    cycle: seq<BenchWorld.Bytes>
  )
  {
    |cycle| > 0 && (forall v | v in cycle :: v in graph) &&
    (forall i: nat, j: nat | i < j < |cycle| :: cycle[i] != cycle[j]) &&
    (forall i: nat | i + 1 < |cycle| :: cycle[i + 1] in graph[cycle[i]]) &&
    cycle[0] in graph[cycle[|cycle| - 1]]
  }

  ghost opaque predicate Recovery(
    before: map<BenchWorld.Bytes, seq<BenchWorld.Bytes>>,
    after: map<BenchWorld.Bytes, seq<BenchWorld.Bytes>>,
    beforeIndeg: map<BenchWorld.Bytes, nat>,
    afterIndeg: map<BenchWorld.Bytes, nat>,
    cycle: seq<BenchWorld.Bytes>,
    position: nat
  )
  {
    Cycle(before, cycle) && beforeIndeg.Keys == before.Keys &&
    var source := cycle[|cycle| - 1];
    var target := cycle[0];
    position < |before[source]| && before[source][position] == target &&
    (forall i: nat | i < position :: before[source][i] != target) &&
    after == before[source := before[source][..position] + before[source][position + 1..]] &&
    beforeIndeg[target] > 0 && afterIndeg == beforeIndeg[target := beforeIndeg[target] - 1]
  }
}
