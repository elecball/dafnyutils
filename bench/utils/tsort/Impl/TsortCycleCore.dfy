include "TsortState.dfy"
include "../Spec/TsortCycleSpec.dfy"
include "../Proof/TsortCycleProof.dfy"
include "../Proof/TsortSortProof.dfy"
include "../Spec/TsortStepSpec.dfy"

module TsortCycleCore {
  import BenchWorld
  import State = TsortState
  import Spec = TsortCycleSpec
  import Proof = TsortCycleProof
  import SortSpec = TsortSortSpec
  import Step = TsortStepSpec
  import SortProof = TsortSortProof

  method BreakStalledCycle(
    state: State.SortState,
    vertices: seq<BenchWorld.Bytes>,
    graph: map<BenchWorld.Bytes, seq<BenchWorld.Bytes>>
  ) returns (remaining: map<BenchWorld.Bytes, seq<BenchWorld.Bytes>>,
             cycle: seq<BenchWorld.Bytes>, position: nat)
    requires state.WellFormed(graph) && Step.Ready(graph, [], state.visited, state.indeg)
    requires (set v | v in vertices) == graph.Keys && SortSpec.Ordered(vertices)
    requires forall i: nat, j: nat | i < j < |vertices| :: vertices[i] != vertices[j]
    requires exists v | v in graph :: !state.visited[v]
    modifies state`indeg
    ensures Spec.Recovery(graph, remaining, old(state.indeg), state.indeg, cycle, position)
    ensures Spec.Selected(graph, old(state.indeg), cycle)
    ensures forall v | v in cycle :: v in graph && old(state.indeg)[v] > 0
    ensures state.WellFormed(remaining)
  {
    Proof.StalledDegrees(graph, state.visited, state.indeg);
    remaining, cycle, position := BreakCycle(state, vertices, graph);
    assert Spec.Recovery(graph, remaining, old(state.indeg), state.indeg, cycle, position) by { hide *; }
  }

  method IndexOf(values: seq<BenchWorld.Bytes>, target: BenchWorld.Bytes) returns (index: nat)
    ensures index <= |values|
    ensures index < |values| ==> values[index] == target
    ensures index == |values| ==> target !in values
    ensures forall j: nat | j < index :: values[j] != target
  {
    index := 0;
    while index < |values| && values[index] != target
      invariant 0 <= index <= |values|
      invariant forall j: nat | j < index :: values[j] != target
      decreases |values| - index
    {
      index := index + 1;
    }
  }

  method {:isolate_assertions} FindCycle(
    vertices: seq<BenchWorld.Bytes>,
    graph: map<BenchWorld.Bytes, seq<BenchWorld.Bytes>>,
    indeg: map<BenchWorld.Bytes, nat>
  ) returns (cycle: seq<BenchWorld.Bytes>)
    requires indeg.Keys == graph.Keys
    requires (set v | v in vertices) == graph.Keys && SortSpec.Ordered(vertices)
    requires forall i: nat, j: nat | i < j < |vertices| :: vertices[i] != vertices[j]
    requires exists v | v in graph :: indeg[v] > 0
    requires forall target | target in graph && indeg[target] > 0 ::
               exists source | source in graph && indeg[source] > 0 :: target in graph[source]
    ensures Spec.Cycle(graph, cycle) && Spec.Selected(graph, indeg, cycle)
    ensures forall v | v in cycle :: indeg[v] > 0
  {
    var found, indices, begin := SearchCycle(vertices, graph, indeg);
    cycle := found;
    reveal Spec.Selected();
  }

  method {:isolate_assertions} SearchCycle(
    vertices: seq<BenchWorld.Bytes>,
    graph: map<BenchWorld.Bytes, seq<BenchWorld.Bytes>>,
    indeg: map<BenchWorld.Bytes, nat>
  ) returns (cycle: seq<BenchWorld.Bytes>, ghost indices: seq<nat>, ghost begin: nat)
    requires indeg.Keys == graph.Keys && (set v | v in vertices) == graph.Keys
    requires forall i: nat, j: nat | i < j < |vertices| :: vertices[i] != vertices[j]
    requires exists v | v in graph :: indeg[v] > 0
    requires forall target | target in graph && indeg[target] > 0 ::
               exists source | source in graph && indeg[source] > 0 :: target in graph[source]
    ensures Spec.Cycle(graph, cycle)
    ensures forall v | v in cycle :: v in indeg && indeg[v] > 0
    ensures Spec.SelectionFields(graph, indeg, vertices, indices, begin, cycle)
  {
    var start: nat := 0;
    while start < |vertices| && indeg[vertices[start]] == 0
      invariant 0 <= start <= |vertices|
      invariant forall i: nat | i < start :: indeg[vertices[i]] == 0
      decreases |vertices| - start
    {
      assert forall i: nat | i < start + 1 :: indeg[vertices[i]] == 0 by {
        hide *;
        forall i: nat | i < start + 1
          ensures indeg[vertices[i]] == 0
        { if i >= start { assert i == start; } }
      }
      start := start + 1;
    }
    assert start < |vertices|;
    var path := [vertices[start]];
    ghost var walk: seq<nat> := [start];
    assert Proof.Reversed(vertices, walk, path) by { reveal Proof.Reversed(); }
    assert Spec.Walk(graph, indeg, vertices, walk) by { reveal Spec.Walk(); }
    var cursor: nat := start;
    var checked: nat := 0;
    assert Spec.Path(graph, indeg, path) by { reveal Spec.Path(); }
    Proof.Bound(graph, indeg, path);
    assert Proof.CursorPath(vertices, walk, path, cursor) by { hide *; reveal Proof.CursorPath(); }
    while true
      invariant Spec.Path(graph, indeg, path)
      invariant 0 < |path| <= |graph| + 1
      invariant Spec.Walk(graph, indeg, vertices, walk)
      invariant Proof.CursorPath(vertices, walk, path, cursor)
      invariant cursor < |vertices|
      invariant checked < |vertices|
      invariant forall d: nat | 0 < d <= checked ::
                  Spec.Rejected(vertices, graph, indeg, cursor, d)
      decreases |graph| + 1 - |path|, |vertices| - checked
    {
      Proof.Head(graph, indeg, path);
      Proof.CursorHead(vertices, walk, path, cursor);
      var next: nat := (cursor + checked + 1) % |vertices|;
      var source := vertices[next];
      if indeg[source] > 0 && path[0] in graph[source] {
        Proof.Choose(vertices, graph, indeg, cursor, checked);
        Proof.AppendWalk(graph, indeg, vertices, walk, next);
        var index := IndexOf(path[..|path| - 1], source);
        if index < |path| - 1 {
          Proof.Close(graph, indeg, path, index);
          assert Spec.SelectionFields(graph, indeg, vertices, walk + [next], |walk| - 1 - index, path[..index + 1]) by {
            hide *;
            Proof.SelectedWalk(graph, indeg, vertices, walk, path, next, index);
          }
          cycle := path[..index + 1];
          indices := walk + [next];
          begin := |walk| - 1 - index;
          assert Spec.SelectionFields(graph, indeg, vertices, indices, begin, cycle) by { hide *; }
          return;
        }
        Proof.Extend(graph, indeg, path, source);
        Proof.CursorPrepend(vertices, walk, path, cursor, next);
        path := [source] + path;
        walk := walk + [next];
        cursor := next;
        checked := 0;
      } else {
        Proof.Reject(vertices, graph, indeg, cursor, checked);
        assert forall d: nat | 0 < d <= checked + 1 ::
            Spec.Rejected(vertices, graph, indeg, cursor, d) by {
          hide *;
          forall d: nat | 0 < d <= checked + 1
            ensures Spec.Rejected(vertices, graph, indeg, cursor, d)
          {
            if d > checked { assert d == checked + 1; }
          }
        }
        Proof.NotExhausted(vertices, graph, indeg, cursor, checked);
        checked := checked + 1;
      }
    }
  }

  method {:isolate_assertions} BreakCycle(
    state: State.SortState,
    vertices: seq<BenchWorld.Bytes>,
    graph: map<BenchWorld.Bytes, seq<BenchWorld.Bytes>>
  ) returns (remaining: map<BenchWorld.Bytes, seq<BenchWorld.Bytes>>,
             cycle: seq<BenchWorld.Bytes>, position: nat)
    requires state.WellFormed(graph)
    requires (set v | v in vertices) == graph.Keys && SortSpec.Ordered(vertices)
    requires forall i: nat, j: nat | i < j < |vertices| :: vertices[i] != vertices[j]
    requires exists v | v in graph :: state.indeg[v] > 0
    requires forall target | target in graph && state.indeg[target] > 0 ::
               exists source | source in graph && state.indeg[source] > 0 :: target in graph[source]
    modifies state`indeg
    ensures Spec.Recovery(graph, remaining, old(state.indeg), state.indeg, cycle, position)
    ensures Spec.Selected(graph, old(state.indeg), cycle)
    ensures forall v | v in cycle :: v in graph && old(state.indeg)[v] > 0
    ensures state.WellFormed(remaining)
  {
    cycle := FindCycle(vertices, graph, state.indeg);
    remaining, position := RemoveCycleEdge(state, graph, cycle);
  }

  method RemoveCycleEdge(
    state: State.SortState,
    graph: map<BenchWorld.Bytes, seq<BenchWorld.Bytes>>,
    cycle: seq<BenchWorld.Bytes>
  ) returns (remaining: map<BenchWorld.Bytes, seq<BenchWorld.Bytes>>, position: nat)
    requires state.WellFormed(graph) && Spec.Cycle(graph, cycle)
    requires state.indeg[cycle[0]] > 0
    modifies state`indeg
    ensures Spec.Recovery(graph, remaining, old(state.indeg), state.indeg, cycle, position)
    ensures state.WellFormed(remaining)
  {
    reveal Spec.Recovery();
    var source := cycle[|cycle| - 1];
    var target := cycle[0];
    position := IndexOf(graph[source], target);
    remaining := graph[source := graph[source][..position] + graph[source][position + 1..]];
    state.indeg := state.indeg[target := state.indeg[target] - 1];
  }
}
