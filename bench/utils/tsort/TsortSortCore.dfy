include "TsortState.dfy"
include "TsortStepSpec.dfy"
include "TsortSortSpec.dfy"
include "TsortSortProof.dfy"

module TsortSortCore {
  import BenchWorld
  import State = TsortState
  import Spec = TsortSortSpec
  import Proof = TsortSortProof
  import StepSpec = TsortStepSpec

  method SortVertices(vertices: seq<BenchWorld.Bytes>) returns (sorted: seq<BenchWorld.Bytes>)
    requires forall i: nat, j: nat | i < j < |vertices| :: vertices[i] != vertices[j]
    ensures Spec.Ordered(sorted) && (set v | v in sorted) == (set v | v in vertices)
    ensures forall i: nat, j: nat | i < j < |sorted| :: sorted[i] != sorted[j]
  {
    sorted := [];
    var i := 0;
    while i < |vertices|
      invariant 0 <= i <= |vertices| && Spec.Ordered(sorted)
      invariant (set v | v in sorted) == (set v | v in vertices[..i])
      invariant forall v | v in sorted :: v in vertices[..i]
      invariant forall j: nat, k: nat | j < k < |sorted| :: sorted[j] != sorted[k]
      decreases |vertices| - i
    {
      assert vertices[i] !in vertices[..i];
      sorted := Insert(sorted, vertices[i]);
      assert vertices[..i + 1] == vertices[..i] + [vertices[i]];
      i := i + 1;
    }
  }

  method BuildPendingQueue(
    state: State.SortState,
    vertices: seq<BenchWorld.Bytes>,
    graph: map<BenchWorld.Bytes, seq<BenchWorld.Bytes>>
  )
    requires state.WellFormed(graph)
    requires Spec.LiveDegrees(graph, state.visited, state.indeg)
    requires forall v | v in graph && state.visited[v] :: state.indeg[v] == 0
    requires (set v | v in vertices) == graph.Keys && Spec.Ordered(vertices)
    requires forall i: nat, j: nat | i < j < |vertices| :: vertices[i] != vertices[j]
    modifies state`queue
    ensures state.WellFormed(graph) && Spec.Ordered(state.queue)
    ensures StepSpec.Ready(graph, state.queue, state.visited, state.indeg)
    ensures forall v | v in state.queue :: !state.visited[v]
  {
    state.queue := [];
    var i := 0;
    while i < |vertices|
      modifies state`queue
      invariant 0 <= i <= |vertices|
      invariant Spec.Ordered(state.queue)
      invariant forall v | v in state.queue :: v in vertices[..i] && !state.visited[v] && state.indeg[v] == 0
      invariant forall v | v in vertices[..i] && !state.visited[v] && state.indeg[v] == 0 :: v in state.queue
      invariant forall j: nat, k: nat | j < k < |state.queue| :: state.queue[j] != state.queue[k]
      decreases |vertices| - i
    {
      var vertex := vertices[i];
      if !state.visited[vertex] && state.indeg[vertex] == 0 {
        assert vertex !in vertices[..i];
        Proof.AppendOrdered(vertices, state.queue, i);
        state.queue := state.queue + [vertex];
      }
      assert vertices[..i + 1] == vertices[..i] + [vertex];
      i := i + 1;
    }
  }

  method CompareBytes(a: BenchWorld.Bytes, b: BenchWorld.Bytes) returns (le: bool)
    ensures le == Spec.BytesLe(a, b)
  {
    var i := 0;
    while i < |a| && i < |b| && a[i] == b[i]
      invariant 0 <= i <= |a| && i <= |b|
      invariant forall j: nat | j < i :: a[j] == b[j]
      decreases |a| - i
    {
      i := i + 1;
    }
    Proof.CommonPrefix(a, b, i);
    le := i == |a| || (i < |b| && a[i] < b[i]);
  }

  method Insert(queue: seq<BenchWorld.Bytes>, vertex: BenchWorld.Bytes)
    returns (result: seq<BenchWorld.Bytes>)
    requires Spec.Ordered(queue) && vertex !in queue
    requires forall i: nat, j: nat | i < j < |queue| :: queue[i] != queue[j]
    ensures Spec.Ordered(result)
    ensures (set v | v in result) == (set v | v in queue) + {vertex}
    ensures forall v | v in result :: v == vertex || v in queue
    ensures forall i: nat, j: nat | i < j < |result| :: result[i] != result[j]
  {
    var index := 0;
    while index < |queue|
      invariant 0 <= index <= |queue|
      invariant forall i: nat | i < index :: Spec.BytesLe(queue[i], vertex)
      decreases |queue| - index
    {
      var before := CompareBytes(vertex, queue[index]);
      if before { break; }
      Proof.Total(vertex, queue[index]);
      index := index + 1;
    }
    Proof.InsertOrdered(queue, vertex, index);
    result := queue[..index] + [vertex] + queue[index..];
  }

  method ComputeIndegrees(
    state: State.SortState,
    graph: map<BenchWorld.Bytes, seq<BenchWorld.Bytes>>
  )
    requires state.WellFormed(graph)
    modifies state`indeg
    ensures Spec.Indegrees(graph, state.indeg)
    ensures state.WellFormed(graph)
  {
    state.indeg := map vertex | vertex in graph.Keys :: 0;
    assert Spec.Counts(graph, {}, state.indeg) by { reveal Spec.Counts(); }
    var todo := graph.Keys;
    ghost var done: set<(BenchWorld.Bytes, nat)> := {};
    while todo != {}
      invariant todo <= graph.Keys
      invariant Spec.Counts(graph, done, state.indeg)
      invariant state.indeg.Keys == graph.Keys
      invariant done == (set edge | edge in Spec.Edges(graph) && edge.0 !in todo)
      decreases todo
    {
      var source :| source in todo;
      var j := 0;
      while j < |graph[source]|
        invariant 0 <= j <= |graph[source]|
        invariant Spec.Counts(graph, done, state.indeg)
        invariant state.indeg.Keys == graph.Keys
        invariant done == (set edge | edge in Spec.Edges(graph) &&
                                      (edge.0 !in todo || (edge.0 == source && edge.1 < j)))
        decreases |graph[source]| - j
      {
        var target := graph[source][j];
        Proof.AddEdge(graph, done, state.indeg, (source, j));
        state.indeg := state.indeg[target := state.indeg[target] + 1];
        done := done + {(source, j)};
        j := j + 1;
      }
      todo := todo - {source};
    }
    assert done == Spec.Edges(graph);
    assert Spec.Counts(graph, Spec.Edges(graph), state.indeg);
  }
}
