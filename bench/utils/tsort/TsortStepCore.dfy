include "TsortState.dfy"
include "TsortStepSpec.dfy"
include "TsortStepProof.dfy"
include "TsortSortProof.dfy"

module TsortStepCore {
  import BenchWorld
  import State = TsortState
  import Spec = TsortStepSpec
  import Proof = TsortStepProof
  import SortSpec = TsortSortSpec
  import SortProof = TsortSortProof

  method Step(
    state: State.SortState,
    graph: map<BenchWorld.Bytes, seq<BenchWorld.Bytes>>
  )
    requires state.WellFormed(graph)
    requires |state.queue| > 0
    requires !state.visited[state.queue[0]]
    requires Spec.Ready(graph, state.queue, state.visited, state.indeg)
    modifies state`queue, state`visited, state`indeg
    ensures state.WellFormed(graph)
    ensures Spec.Ready(graph, state.queue, state.visited, state.indeg)
    ensures state.visited == old(state.visited)[old(state.queue[0]) := true]
    ensures old(forall vertex | vertex in state.queue :: !state.visited[vertex]) ==>
              (forall vertex | vertex in state.queue :: !state.visited[vertex])
    ensures Spec.Step(old(state.queue), old(state.visited), old(state.indeg), graph,
                      state.queue, state.visited, state.indeg)
  {
    var vertex := state.queue[0];
    ghost var beforeQueue := state.queue;
    ghost var beforeVisited := state.visited;
    ghost var beforeIndeg := state.indeg;
    ghost var live := SortSpec.ActiveEdges(graph, beforeVisited);
    ghost var added: seq<BenchWorld.Bytes> := [];
    ghost var positions: seq<nat> := [];
    var successors := graph[vertex];
    state.queue := state.queue[1..];
    assert Spec.Released([], beforeIndeg, [], []) by { reveal Spec.Released(); }
    var j := 0;
    while j < |successors|
      invariant 0 <= j <= |successors|
      invariant state.visited == beforeVisited
      invariant state.queue == beforeQueue[1..] + added
      invariant SortSpec.Counts(graph, live, state.indeg)
      invariant state.indeg.Keys == graph.Keys
      invariant live == SortSpec.ActiveEdges(graph, beforeVisited) -
                        (set index: nat | index < j :: (vertex, index))
      invariant Spec.Released(successors[..j], beforeIndeg, added, positions)
      invariant forall target | target in graph ::
                  state.indeg[target] + multiset(successors[..j])[target] == beforeIndeg[target]
      invariant state.indeg[vertex] == 0
      invariant forall target | target in graph && beforeVisited[target] :: state.indeg[target] == 0
      invariant forall target | target in state.queue :: target in graph && state.indeg[target] == 0
      invariant forall a: nat, b: nat | a < b < |state.queue| :: state.queue[a] != state.queue[b]
      invariant forall target | target in graph && !beforeVisited[target] && state.indeg[target] == 0 ::
                  target == vertex || target in state.queue
      invariant (forall target | target in beforeQueue :: !beforeVisited[target]) ==>
                  (forall target | target in state.queue :: !beforeVisited[target] && target != vertex)
      modifies state`queue, state`indeg
      decreases |successors| - j
    {
      var target := successors[j];
      assert (vertex, j) in live;
      SortProof.RemoveEdge(graph, live, state.indeg, (vertex, j));
      assert target !in state.queue && target != vertex && !beforeVisited[target];
      assert successors[..j + 1] == successors[..j] + [target];
      Proof.ExtendReleased(successors, j, beforeIndeg, added, positions);
      state.indeg := state.indeg[target := state.indeg[target] - 1];
      live := live - {(vertex, j)};
      if state.indeg[target] == 0 {
        state.queue := state.queue + [target];
        added := added + [target];
        positions := positions + [j];
      }
      assert (set index: nat | index < j + 1 :: (vertex, index)) ==
             (set index: nat | index < j :: (vertex, index)) + {(vertex, j)};
      j := j + 1;
    }
    Proof.FinishLive(graph, beforeVisited, vertex);
    assert successors[..j] == graph[vertex];
    assert Spec.Released(graph[vertex], beforeIndeg, added, positions);
    state.visited := state.visited[vertex := true];
    Proof.CompletedStep(beforeQueue, beforeVisited, beforeIndeg, graph,
                        state.queue, state.visited, state.indeg, added, positions);
  }
}
