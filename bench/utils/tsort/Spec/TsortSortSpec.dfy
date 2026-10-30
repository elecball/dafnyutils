include "../../../core/World.dfy"

module TsortSortSpec {
  import BenchWorld

  ghost function EdgeCount(vertices: seq<BenchWorld.Bytes>, graph: map<BenchWorld.Bytes, seq<BenchWorld.Bytes>>): nat
    requires forall v | v in vertices :: v in graph
    decreases |vertices|
  {
    if |vertices| == 0 then 0 else |graph[vertices[0]]| + EdgeCount(vertices[1..], graph)
  }

  ghost predicate TopologicalPrefix(
    graph: map<BenchWorld.Bytes, seq<BenchWorld.Bytes>>,
    ordered: seq<BenchWorld.Bytes>
  )
  {
    (set vertex | vertex in ordered) <= graph.Keys &&
    (forall i: nat, j: nat | i < j < |ordered| :: ordered[i] != ordered[j]) &&
    (forall i: nat | i < |ordered| ::
       forall source | source in graph && ordered[i] in graph[source] :: source in ordered[..i])
  }

  ghost predicate TopologicalResult(
    graph: map<BenchWorld.Bytes, seq<BenchWorld.Bytes>>,
    ordered: seq<BenchWorld.Bytes>,
    valid: bool
  )
  {
    TopologicalPrefix(graph, ordered) && valid == ((set vertex | vertex in ordered) == graph.Keys) &&
    (forall target | target in graph && target !in ordered ::
       exists source | source in graph && source !in ordered :: target in graph[source])
  }

  function BytesLe(a: BenchWorld.Bytes, b: BenchWorld.Bytes): bool
    decreases |a| + |b|
  {
    |a| == 0 || (|b| > 0 &&
                 (a[0] < b[0] || (a[0] == b[0] && BytesLe(a[1..], b[1..]))))
  }

  ghost predicate Ordered(queue: seq<BenchWorld.Bytes>)
  {
    forall i: nat, j: nat | i <= j < |queue| :: BytesLe(queue[i], queue[j])
  }

  ghost predicate InitialQueue(
    indeg: map<BenchWorld.Bytes, nat>,
    queue: seq<BenchWorld.Bytes>
  )
  {
    (set vertex | vertex in queue) == (set vertex | vertex in indeg && indeg[vertex] == 0) &&
    (forall i: nat, j: nat | i < j < |queue| :: queue[i] != queue[j]) && Ordered(queue)
  }

  ghost function Edges(graph: map<BenchWorld.Bytes, seq<BenchWorld.Bytes>>): set<(BenchWorld.Bytes, nat)>
  {
    set source: BenchWorld.Bytes, index: nat |
      source in graph.Keys && index < |graph[source]| :: (source, index)
  }

  ghost function Incoming(
    graph: map<BenchWorld.Bytes, seq<BenchWorld.Bytes>>,
    edges: set<(BenchWorld.Bytes, nat)>,
    target: BenchWorld.Bytes
  ): set<(BenchWorld.Bytes, nat)>
  {
    set edge | edge in edges && edge.0 in graph && edge.1 < |graph[edge.0]| &&
               graph[edge.0][edge.1] == target
  }

  ghost function ActiveEdges(
    graph: map<BenchWorld.Bytes, seq<BenchWorld.Bytes>>,
    visited: map<BenchWorld.Bytes, bool>
  ): set<(BenchWorld.Bytes, nat)>
  {
    set edge | edge in Edges(graph) && edge.0 in visited && !visited[edge.0]
  }

  ghost opaque predicate Counts(
    graph: map<BenchWorld.Bytes, seq<BenchWorld.Bytes>>,
    edges: set<(BenchWorld.Bytes, nat)>,
    indeg: map<BenchWorld.Bytes, nat>
  )
  {
    edges <= Edges(graph) && indeg.Keys == graph.Keys &&
    (forall target | target in graph.Keys :: indeg[target] == |Incoming(graph, edges, target)|)
  }

  ghost predicate LiveDegrees(
    graph: map<BenchWorld.Bytes, seq<BenchWorld.Bytes>>,
    visited: map<BenchWorld.Bytes, bool>,
    indeg: map<BenchWorld.Bytes, nat>
  )
  {
    visited.Keys == graph.Keys && indeg.Keys == graph.Keys &&
    Counts(graph, ActiveEdges(graph, visited), indeg)
  }

  ghost predicate Indegrees(
    graph: map<BenchWorld.Bytes, seq<BenchWorld.Bytes>>,
    indeg: map<BenchWorld.Bytes, nat>
  )
  {
    Counts(graph, Edges(graph), indeg)
  }
}
