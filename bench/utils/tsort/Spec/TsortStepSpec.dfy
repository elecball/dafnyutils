include "../../../core/World.dfy"
include "TsortSortSpec.dfy"

module TsortStepSpec {
  import BenchWorld
  import SortSpec = TsortSortSpec

  ghost predicate Ready(
    graph: map<BenchWorld.Bytes, seq<BenchWorld.Bytes>>,
    queue: seq<BenchWorld.Bytes>,
    visited: map<BenchWorld.Bytes, bool>,
    indeg: map<BenchWorld.Bytes, nat>
  )
  {
    SortSpec.LiveDegrees(graph, visited, indeg) &&
    (forall source | source in graph ::
       forall target | target in graph[source] ::
         target in graph) &&
    (forall vertex | vertex in graph && visited[vertex] :: indeg[vertex] == 0) &&
    (forall vertex | vertex in queue :: vertex in graph && indeg[vertex] == 0) &&
    (forall i: nat, j: nat | i < j < |queue| :: queue[i] != queue[j]) &&
    (forall vertex | vertex in graph && !visited[vertex] && indeg[vertex] == 0 :: vertex in queue)
  }

  ghost opaque predicate Released(
    successors: seq<BenchWorld.Bytes>,
    before: map<BenchWorld.Bytes, nat>,
    added: seq<BenchWorld.Bytes>,
    positions: seq<nat>
  )
    requires forall vertex | vertex in successors :: vertex in before
  {
    |added| == |positions| &&
    (forall j: nat | j < |positions| ::
       positions[j] < |successors| &&
       added[j] == successors[positions[j]] &&
       before[successors[positions[j]]] == multiset(successors[..positions[j] + 1])[successors[positions[j]]]) &&
    (forall j: nat | 0 < j < |positions| :: positions[j - 1] < positions[j]) &&
    (forall p: nat |
       p < |successors| &&
       before[successors[p]] == multiset(successors[..p + 1])[successors[p]] ::
       p in positions)
  }

  ghost predicate Step(
    beforeQueue: seq<BenchWorld.Bytes>,
    beforeVisited: map<BenchWorld.Bytes, bool>,
    beforeIndeg: map<BenchWorld.Bytes, nat>,
    graph: map<BenchWorld.Bytes, seq<BenchWorld.Bytes>>,
    afterQueue: seq<BenchWorld.Bytes>,
    afterVisited: map<BenchWorld.Bytes, bool>,
    afterIndeg: map<BenchWorld.Bytes, nat>
  )
    requires beforeVisited.Keys == graph.Keys && beforeIndeg.Keys == graph.Keys
    requires |beforeQueue| > 0 && beforeQueue[0] in graph
    requires !beforeVisited[beforeQueue[0]]
    requires forall source | source in graph ::
               forall target | target in graph[source] ::
                 target in graph
  {
    var vertex := beforeQueue[0];
    afterVisited == beforeVisited[vertex := true] && afterIndeg.Keys == graph.Keys &&
    (forall target | target in graph ::
       afterIndeg[target] + multiset(graph[vertex])[target] == beforeIndeg[target]) &&
    (exists added: seq<BenchWorld.Bytes>, positions: seq<nat> ::
       afterQueue == beforeQueue[1..] + added && Released(graph[vertex], beforeIndeg, added, positions))
  }
}
