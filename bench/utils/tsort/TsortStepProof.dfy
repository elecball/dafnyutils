include "TsortStepSpec.dfy"
include "TsortSpec.dfy"

module TsortStepProof {
  import BenchWorld
  import Spec = TsortStepSpec
  import SortSpec = TsortSortSpec
  import Output = TsortSpec

  lemma ExtendReleased(
    successors: seq<BenchWorld.Bytes>,
    count: nat,
    before: map<BenchWorld.Bytes, nat>,
    added: seq<BenchWorld.Bytes>,
    positions: seq<nat>
  )
    requires count < |successors|
    requires forall vertex | vertex in successors :: vertex in before
    requires Spec.Released(successors[..count], before, added, positions)
    ensures Spec.Released(
              successors[..count + 1], before,
              if before[successors[count]] == multiset(successors[..count + 1])[successors[count]]
              then added + [successors[count]] else added,
              if before[successors[count]] == multiset(successors[..count + 1])[successors[count]]
              then positions + [count] else positions
            )
  {
    reveal Spec.Released();
    assert successors[..count + 1] == successors[..count] + [successors[count]];
    var ready := before[successors[count]] == multiset(successors[..count + 1])[successors[count]];
    var nextAdded := if ready then added + [successors[count]] else added;
    var nextPositions := if ready then positions + [count] else positions;
    var next := successors[..count + 1];
    forall j: nat | j < |nextPositions|
      ensures nextPositions[j] < |next| && nextAdded[j] == next[nextPositions[j]] &&
              before[next[nextPositions[j]]] == multiset(next[..nextPositions[j] + 1])[next[nextPositions[j]]]
    {
      if j < |positions| {
        assert (successors[..count])[..positions[j] + 1] == successors[..positions[j] + 1];
      }
      assert next[..nextPositions[j] + 1] == successors[..nextPositions[j] + 1];
    }
    forall j: nat | 0 < j < |nextPositions|
      ensures nextPositions[j - 1] < nextPositions[j]
    {
      if j == |positions| {
        assert positions[j - 1] < count;
      }
    }
    forall p: nat | p < |next| &&
                    before[next[p]] == multiset(next[..p + 1])[next[p]]
      ensures p in nextPositions
    {
      assert next[..p + 1] == successors[..p + 1];
      if p < count {
        assert (successors[..count])[..p + 1] == successors[..p + 1];
        assert p in positions;
      }
    }
    assert Spec.Released(next, before, nextAdded, nextPositions) by {
      hide *;
      reveal Spec.Released();
    }
  }

  lemma FinishLive(
    graph: map<BenchWorld.Bytes, seq<BenchWorld.Bytes>>,
    visited: map<BenchWorld.Bytes, bool>,
    vertex: BenchWorld.Bytes
  )
    requires visited.Keys == graph.Keys && vertex in graph
    ensures SortSpec.ActiveEdges(graph, visited[vertex := true]) ==
            SortSpec.ActiveEdges(graph, visited) - (set index: nat | index < |graph[vertex]| :: (vertex, index))
  {
  }

  lemma CompletedStep(
    beforeQueue: seq<BenchWorld.Bytes>,
    beforeVisited: map<BenchWorld.Bytes, bool>,
    beforeIndeg: map<BenchWorld.Bytes, nat>,
    graph: map<BenchWorld.Bytes, seq<BenchWorld.Bytes>>,
    afterQueue: seq<BenchWorld.Bytes>,
    afterVisited: map<BenchWorld.Bytes, bool>,
    afterIndeg: map<BenchWorld.Bytes, nat>,
    added: seq<BenchWorld.Bytes>,
    positions: seq<nat>
  )
    requires beforeVisited.Keys == graph.Keys && beforeIndeg.Keys == graph.Keys
    requires |beforeQueue| > 0 && beforeQueue[0] in graph && !beforeVisited[beforeQueue[0]]
    requires forall source | source in graph ::
               forall target | target in graph[source] ::
                 target in graph
    requires afterVisited == beforeVisited[beforeQueue[0] := true] && afterIndeg.Keys == graph.Keys
    requires forall target | target in graph ::
               afterIndeg[target] + multiset(graph[beforeQueue[0]])[target] == beforeIndeg[target]
    requires afterQueue == beforeQueue[1..] + added
    requires Spec.Released(graph[beforeQueue[0]], beforeIndeg, added, positions)
    ensures Spec.Step(beforeQueue, beforeVisited, beforeIndeg, graph, afterQueue, afterVisited, afterIndeg)
  {
    assert exists more: seq<BenchWorld.Bytes>, ps: seq<nat> ::
        afterQueue == beforeQueue[1..] + more && Spec.Released(graph[beforeQueue[0]], beforeIndeg, more, ps);
  }

  lemma ZeroPredecessors(
    graph: map<BenchWorld.Bytes, seq<BenchWorld.Bytes>>,
    visited: map<BenchWorld.Bytes, bool>,
    indeg: map<BenchWorld.Bytes, nat>,
    target: BenchWorld.Bytes
  )
    requires SortSpec.LiveDegrees(graph, visited, indeg) && target in graph && indeg[target] == 0
    ensures forall source | source in graph && target in graph[source] :: visited[source]
  {
    reveal SortSpec.Counts();
    var incoming := SortSpec.Incoming(graph, SortSpec.ActiveEdges(graph, visited), target);
    assert incoming == {};
    forall source | source in graph && target in graph[source]
      ensures visited[source]
    {
      if !visited[source] {
        var index: nat :| index < |graph[source]| && graph[source][index] == target;
        assert (source, index) in incoming;
      }
    }
  }

  lemma PositivePredecessor(
    graph: map<BenchWorld.Bytes, seq<BenchWorld.Bytes>>,
    visited: map<BenchWorld.Bytes, bool>,
    indeg: map<BenchWorld.Bytes, nat>,
    target: BenchWorld.Bytes
  )
    requires SortSpec.LiveDegrees(graph, visited, indeg) && target in graph && indeg[target] > 0
    ensures exists source | source in graph && !visited[source] :: target in graph[source]
  {
    reveal SortSpec.Counts();
    var incoming := SortSpec.Incoming(graph, SortSpec.ActiveEdges(graph, visited), target);
    assert incoming != {};
    var edge :| edge in incoming;
    assert edge.0 in graph && !visited[edge.0] && target in graph[edge.0];
  }

  ghost predicate Projection(initial: Graph, graph: Graph, origins: Origins) {
    initial.Keys == graph.Keys == origins.Keys &&
    (forall source | source in graph ::
       |origins[source]| == |graph[source]| &&
       (forall j: nat | j < |graph[source]| ::
          origins[source][j] < |initial[source]| &&
          graph[source][j] == initial[source][origins[source][j]]) &&
       (forall i: nat, j: nat | i < j < |origins[source]| :: origins[source][i] < origins[source][j]))
  }

  lemma ProjectCut(initial: Graph, graph: Graph, origins: Origins, source: Bytes, index: nat)
    requires Projection(initial, graph, origins) && source in graph && index < |graph[source]|
    ensures Projection(initial, graph[source := graph[source][..index] + graph[source][index + 1..]],
                       origins[source := origins[source][..index] + origins[source][index + 1..]])
  {

  }

  ghost opaque predicate Selection(graph: Graph, pending: set<Bytes>, active: set<Edge>, cycle: seq<Bytes>) {
    Output.SelectedCycle(graph, map v | v in graph :: if v in pending then 2 else 0,
                         map edge | edge in SortSpec.Edges(graph) :: if edge in active then 1 else 0, 1, cycle)
  }

  type Bytes = BenchWorld.Bytes

  type Graph = map<Bytes, seq<Bytes>>

  type Edge = (Bytes, nat)

  type Origins = map<Bytes, seq<nat>>

  datatype Snapshot = Snapshot(pending: set<Bytes>, active: set<Edge>, queue: seq<Bytes>)

  datatype Run = Run(events: seq<Output.Event>, states: seq<Snapshot>,
                     ranks: map<Bytes, nat>, removed: map<Edge, nat>)

  ghost opaque function SnapshotOf(
    initial: Graph,
    origins: Origins,
    visited: map<Bytes, bool>,
    queue: seq<Bytes>
  ): (result: Snapshot)
    requires origins.Keys == initial.Keys == visited.Keys
    ensures result.pending == (set v | v in visited && !visited[v]) && result.queue == queue
  {
    Snapshot((set v | v in visited && !visited[v]),
             (set edge | edge in SortSpec.Edges(initial) && !visited[edge.0] && edge.1 in origins[edge.0]), queue)
  }

  lemma Identity(initial: Graph, visited: map<Bytes, bool>, queue: seq<Bytes>) returns (origins: Origins)
    requires visited.Keys == initial.Keys && forall v | v in visited :: !visited[v]
    ensures Projection(initial, initial, origins)
    ensures SnapshotOf(initial, origins, visited, queue).active == SortSpec.Edges(initial)
  {
    origins := map v | v in initial :: seq(|initial[v]|, i => i);
    reveal SnapshotOf();
    forall edge | edge in SortSpec.Edges(initial)
      ensures edge in SnapshotOf(initial, origins, visited, queue).active
    {
      assert origins[edge.0][edge.1] == edge.1;
    }
  }

  lemma ObserveReady(
    initial: Graph,
    graph: Graph,
    origins: Origins,
    visited: map<Bytes, bool>,
    queue: seq<Bytes>,
    indeg: map<Bytes, nat>
  )
    requires Projection(initial, graph, origins) && Spec.Ready(graph, queue, visited, indeg)
    requires forall v | v in queue :: !visited[v]
    ensures Valid(initial, SnapshotOf(initial, origins, visited, queue))
  {
    reveal SnapshotOf();
    var state := SnapshotOf(initial, origins, visited, queue);
    forall vertex | vertex in graph
      ensures (indeg[vertex] == 0) == (SortSpec.Incoming(initial, state.active, vertex) == {})
    {
      if indeg[vertex] == 0 {
        ZeroPredecessors(graph, visited, indeg, vertex);
        forall edge | edge in SortSpec.Incoming(initial, state.active, vertex)
          ensures false
        {
          var j: nat :| j < |origins[edge.0]| && origins[edge.0][j] == edge.1;
          assert graph[edge.0][j] == vertex;
        }
      } else {
        PositivePredecessor(graph, visited, indeg, vertex);
        var source :| source in graph && !visited[source] && vertex in graph[source];
        var j: nat :| j < |graph[source]| && graph[source][j] == vertex;
        var edge := (source, origins[source][j]);
        assert edge in SortSpec.Incoming(initial, state.active, vertex);
      }
    }
    forall edge | edge in state.active
      ensures initial[edge.0][edge.1] in state.pending
    {
      var target := initial[edge.0][edge.1];
      var j: nat :| j < |origins[edge.0]| && origins[edge.0][j] == edge.1;
      assert target in graph;
      if visited[target] {
        assert SortSpec.Incoming(initial, state.active, target) == {};
        assert edge in SortSpec.Incoming(initial, state.active, target);
      }
    }
  }

  lemma LastAt(initial: Graph, graph: Graph, origins: Origins, source: Bytes, index: nat)
    requires Projection(initial, graph, origins) && source in graph && index < |graph[source]|
    requires graph[source][index] !in graph[source][index + 1..]
    ensures LastPosition(initial,
                         (set edge | edge in SortSpec.Edges(initial) && edge.0 == source && edge.1 in origins[source]),
                         graph[source][index]) == origins[source][index]
  {
    var target := graph[source][index];
    var edges := set edge | edge in SortSpec.Edges(initial) && edge.0 == source && edge.1 in origins[source];
    var incoming := SortSpec.Incoming(initial, edges, target);
    var position := origins[source][index];
    assert (source, position) in incoming;
    forall edge | edge in incoming
      ensures edge.1 <= position
    {
      var j: nat :| j < |origins[source]| && origins[source][j] == edge.1;
      assert graph[source][j] == target;
      if j > index { assert target in graph[source][index + 1..]; }
    }
  }

  lemma AdjacentOrder(values: seq<nat>, first: nat, second: nat)
    requires first < second < |values|
    requires forall i: nat | 0 < i < |values| :: values[i - 1] < values[i]
    ensures values[first] < values[second]
    decreases second - first
  {
    if first + 1 < second { AdjacentOrder(values, first, second - 1); }
  }

  lemma {:isolate_assertions} RecordEmit(
    initial: Graph,
    graph: Graph,
    origins: Origins,
    queue: seq<Bytes>,
    visited: map<Bytes, bool>,
    indeg: map<Bytes, nat>,
    nextQueue: seq<Bytes>,
    nextVisited: map<Bytes, bool>,
    nextIndeg: map<Bytes, nat>
  )
    requires Projection(initial, graph, origins) && Spec.Ready(graph, queue, visited, indeg)
    requires |queue| > 0 && forall v | v in queue :: !visited[v]
    requires Spec.Ready(graph, nextQueue, nextVisited, nextIndeg)
    requires forall v | v in nextQueue :: !nextVisited[v]
    requires Spec.Step(queue, visited, indeg, graph, nextQueue, nextVisited, nextIndeg)
    ensures Transition(initial, SnapshotOf(initial, origins, visited, queue),
                       SnapshotOf(initial, origins, nextVisited, nextQueue), Output.Emit(queue[0]))
  {
    reveal SnapshotOf();
    ObserveReady(initial, graph, origins, visited, queue, indeg);
    ObserveReady(initial, graph, origins, nextVisited, nextQueue, nextIndeg);
    var source := queue[0];
    assert source in graph;
    var before := SnapshotOf(initial, origins, visited, queue);
    var after := SnapshotOf(initial, origins, nextVisited, nextQueue);
    var added: seq<Bytes>, positions: seq<nat> :|
      nextQueue == queue[1..] + added && Spec.Released(graph[source], indeg, added, positions);
    reveal Spec.Released();
    var deleted := set edge | edge in SortSpec.Edges(initial) && edge.0 == source && edge.1 in origins[source];
    assert after.pending == before.pending - {source};
    assert after.active == before.active - deleted;
    assert before.active - after.active == deleted;
    assert deleted == (set edge | edge in before.active && edge.0 == source);
    forall i: nat | i < |added|
      ensures LastPosition(initial, deleted, added[i]) == origins[source][positions[i]]
      ensures added[i] !in queue
    {
      var target := added[i];
      var p: nat := positions[i];
      assert p < |graph[source]|;
      assert nextIndeg[target] == 0;
      assert graph[source] == graph[source][..p + 1] + graph[source][p + 1..] by { hide *; }
      assert multiset(graph[source][p + 1..])[target] == 0;
      assert target !in graph[source][p + 1..];
      LastAt(initial, graph, origins, source, p);
      if target in queue {
        if target == source { assert nextVisited[target]; }
        else {
          var j: nat :| j < |queue[1..]| && queue[j + 1] == target;
          var k: nat :| k < |added| && added[k] == target;
          assert nextQueue[j] == nextQueue[|queue| - 1 + k];
        }
      }
    }
    forall i: nat, j: nat | i < j < |added|
      ensures LastPosition(initial, deleted, added[i]) < LastPosition(initial, deleted, added[j])
    {
      AdjacentOrder(positions, i, j);
      assert origins[source][positions[i]] < origins[source][positions[j]];
    }
    assert Transition(initial, before, after, Output.Emit(source)) by {
      hide *;
      reveal Transition();
    }
  }

  ghost opaque function Maximum(values: set<nat>): (result: nat)
    requires values != {}
    ensures result in values && forall value | value in values :: value <= result
    decreases |values|
  {
    var value :| value in values;
    if values == {value} then value else
    var rest := Maximum(values - {value});
    var maximum := if value > rest then value else rest;
    forall other | other in values
      ensures other <= maximum
    { if other != value { assert other in values - {value}; } }
    maximum
  }

  ghost function LastPosition(graph: Graph, edges: set<Edge>, target: Bytes): (result: nat)
    ensures forall edge | edge in SortSpec.Incoming(graph, edges, target) :: edge.1 <= result
    ensures result == 0 || exists edge :: edge in SortSpec.Incoming(graph, edges, target) && edge.1 == result
  {
    var values := {0} + set edge | edge in SortSpec.Incoming(graph, edges, target) :: edge.1;
    var maximum := Maximum(values);
    forall edge | edge in SortSpec.Incoming(graph, edges, target)
      ensures edge.1 <= maximum
    { assert edge.1 in values; }
    maximum
  }

  ghost predicate Valid(graph: Graph, state: Snapshot) {
    state.pending <= graph.Keys && state.active <= SortSpec.Edges(graph) &&
    (forall edge | edge in state.active :: edge.0 in state.pending && graph[edge.0][edge.1] in state.pending) &&
    (set v | v in state.queue) ==
    (set v | v in state.pending && SortSpec.Incoming(graph, state.active, v) == {}) &&
    (forall i: nat, j: nat | i < j < |state.queue| :: state.queue[i] != state.queue[j])
  }

  lemma QueueFields(graph: Graph, state: Snapshot, vertex: Bytes)
    requires Valid(graph, state)
    ensures (vertex in state.queue) ==
            (vertex in state.pending && SortSpec.Incoming(graph, state.active, vertex) == {})
  {
    var queued := set v | v in state.queue;
    var eligible := set v | v in state.pending && SortSpec.Incoming(graph, state.active, v) == {};
    assert queued == eligible;
    if vertex in state.queue { assert vertex in queued; }
    else if vertex in state.pending && SortSpec.Incoming(graph, state.active, vertex) == {} {
      assert vertex in eligible;
      assert vertex in queued;
    }
  }

  ghost opaque predicate Transition(graph: Graph, before: Snapshot, after: Snapshot, event: Output.Event) {
    Valid(graph, before) && Valid(graph, after) &&
    if event.Emit? then
      |before.queue| > 0 && event.vertex == before.queue[0] &&
      after.pending == before.pending - {event.vertex} &&
      after.active == before.active - (set edge | edge in before.active && edge.0 == event.vertex) &&
      exists added: seq<Bytes> :: after.queue == before.queue[1..] + added &&
                                  (forall v | v in added :: v !in before.queue) &&
                                  (forall i: nat, j: nat | i < j < |added| ::
                                     LastPosition(graph, before.active - after.active, added[i]) <
                                     LastPosition(graph, before.active - after.active, added[j]))
    else
      before.queue == [] && event.edge in before.active &&
      after.pending == before.pending && after.active == before.active - {event.edge} &&
      |after.queue| <= 1 && |event.cycle| > 0 &&
      event.edge.0 == event.cycle[|event.cycle| - 1] && graph[event.edge.0][event.edge.1] == event.cycle[0] &&
      (forall p: nat | p < event.edge.1 && graph[event.edge.0][p] == event.cycle[0] ::
         (event.edge.0, p) !in before.active) && Selection(graph, before.pending, before.active, event.cycle)
  }

  ghost opaque predicate Schedule(graph: Graph, run: Run) {
    |run.states| == |run.events| + 1 &&
    run.states[0].pending == graph.Keys && run.states[0].active == SortSpec.Edges(graph) &&
    SortSpec.Ordered(run.states[0].queue) &&
    (forall i: nat | i < |run.states| :: Valid(graph, run.states[i])) &&
    (forall i: nat | i < |run.events| :: Transition(graph, run.states[i], run.states[i + 1], run.events[i])) &&
    run.ranks.Keys == graph.Keys - run.states[|run.events|].pending &&
    run.removed.Keys == SortSpec.Edges(graph) - run.states[|run.events|].active &&
    (forall v | v in run.ranks :: run.ranks[v] < |run.events| && run.events[run.ranks[v]] == Output.Emit(v)) &&
    (forall i: nat | i < |run.events| && run.events[i].Emit? ::
       run.events[i].vertex in run.ranks && run.ranks[run.events[i].vertex] == i) &&
    (forall edge | edge in run.removed ::
       run.removed[edge] < |run.events| &&
       ((edge.0 in run.ranks && run.removed[edge] == run.ranks[edge.0]) ||
        (run.events[run.removed[edge]].Cut? && run.events[run.removed[edge]].edge == edge))) &&
    (forall i: nat | i < |run.states| ::
       run.states[i].pending == graph.Keys - (set v | v in run.ranks && run.ranks[v] < i) &&
       run.states[i].active == SortSpec.Edges(graph) - (set edge | edge in run.removed && run.removed[edge] < i))
  }

  lemma Start(graph: Graph, state: Snapshot) returns (run: Run)
    requires Valid(graph, state) && SortSpec.Ordered(state.queue)
    requires state.pending == graph.Keys && state.active == SortSpec.Edges(graph)
    ensures Schedule(graph, run) && run.events == [] && run.states == [state]
  {
    reveal Schedule();
    run := Run([], [state], map[], map[]);
  }

  lemma Extend(graph: Graph, run: Run, after: Snapshot, event: Output.Event) returns (next: Run)
    requires Schedule(graph, run) && |run.states| == |run.events| + 1
    requires Transition(graph, run.states[|run.events|], after, event)
    ensures Schedule(graph, next)
    ensures next.events == run.events + [event] && next.states == run.states + [after]
  {
    reveal Schedule();
    reveal Transition();
    var time := |run.events|;
    var before := run.states[time];
    var deleted := before.active - after.active;
    var ranks := if event.Emit? then run.ranks[event.vertex := time] else run.ranks;
    var removed := map edge | edge in run.removed.Keys + deleted ::
      if edge in deleted then time else run.removed[edge];
    next := Run(run.events + [event], run.states + [after], ranks, removed);
    assert deleted * run.removed.Keys == {};
    if event.Emit? {
      assert event.vertex in before.queue;
      QueueFields(graph, before, event.vertex);
      assert event.vertex !in run.ranks;
    }
    forall i: nat | i <= time
      ensures next.states[i].pending == graph.Keys - (set v | v in ranks && ranks[v] < i)
      ensures next.states[i].active == SortSpec.Edges(graph) - (set edge | edge in removed && removed[edge] < i)
    {
      assert (set v | v in ranks && ranks[v] < i) == (set v | v in run.ranks && run.ranks[v] < i);
      assert (set edge | edge in removed && removed[edge] < i) ==
             (set edge | edge in run.removed && run.removed[edge] < i);
    }
    forall edge | edge in removed
      ensures removed[edge] < |next.events|
      ensures (edge.0 in ranks && removed[edge] == ranks[edge.0]) ||
              (next.events[removed[edge]].Cut? && next.events[removed[edge]].edge == edge)
    {
      if edge in deleted {
        if event.Emit? { assert edge.0 == event.vertex; }
        else { assert edge == event.edge; }
      } else { assert removed[edge] == run.removed[edge]; }
    }
    assert after.pending == graph.Keys - (set v | v in ranks && ranks[v] < time + 1);
    assert after.active == SortSpec.Edges(graph) - (set edge | edge in removed && removed[edge] < time + 1);
    forall i: nat | i < |next.states|
      ensures Valid(graph, next.states[i])
    {
      if i <= time { assert next.states[i] == run.states[i]; }
      else { assert next.states[i] == after; }
    }
    forall i: nat | i < |next.events|
      ensures Transition(graph, next.states[i], next.states[i + 1], next.events[i])
    {
      if i < time { assert next.states[i + 1] == run.states[i + 1]; }
      else { assert i == time; }
    }
    forall v | v in ranks
      ensures ranks[v] < |next.events| && next.events[ranks[v]] == Output.Emit(v)
    {
      if event.Emit? && v == event.vertex { assert ranks[v] == time; }
      else { assert ranks[v] == run.ranks[v]; }
    }
    forall i: nat | i < |next.events| && next.events[i].Emit?
      ensures next.events[i].vertex in ranks && ranks[next.events[i].vertex] == i
    {
      if i < time { assert next.events[i] == run.events[i]; }
      else { assert i == time; }
    }
    assert Schedule(graph, next) by { hide *; reveal Schedule(); }
  }

  lemma EventFields(graph: Graph, run: Run, time: nat)
    requires Schedule(graph, run) && time < |run.events|
    ensures |run.states| == |run.events| + 1
    ensures Valid(graph, run.states[time]) && Valid(graph, run.states[time + 1])
    ensures Transition(graph, run.states[time], run.states[time + 1], run.events[time])
  {
    reveal Schedule();
  }

  lemma At(graph: Graph, run: Run, time: nat)
    requires Schedule(graph, run) && time < |run.states|
    ensures forall edge | edge in run.removed ::
              (edge in run.states[time].active) == (run.removed[edge] >= time)
    ensures forall v | v in run.ranks ::
              (v in run.states[time].pending) == (run.ranks[v] >= time)
  {
    reveal Schedule();
  }

  lemma RecordFields(graph: Graph, run: Run)
    requires Schedule(graph, run)
    ensures forall v | v in run.ranks :: run.ranks[v] < |run.events| && run.events[run.ranks[v]] == Output.Emit(v)
    ensures forall i: nat | i < |run.events| && run.events[i].Emit? ::
              run.events[i].vertex in run.ranks && run.ranks[run.events[i].vertex] == i
    ensures forall edge | edge in run.removed ::
              (run.removed[edge] < |run.events| &&
               ((edge.0 in run.ranks && run.removed[edge] == run.ranks[edge.0]) ||
                (run.events[run.removed[edge]].Cut? && run.events[run.removed[edge]].edge == edge)))
  {
    reveal Schedule();
  }

  lemma EmitAt(graph: Graph, run: Run, vertex: Bytes)
    requires Schedule(graph, run) && vertex in run.ranks
    ensures run.ranks[vertex] < |run.events| && |run.states| == |run.events| + 1
    ensures Valid(graph, run.states[run.ranks[vertex]])
    ensures |run.states[run.ranks[vertex]].queue| > 0 && run.states[run.ranks[vertex]].queue[0] == vertex
  {
    reveal Schedule();
    reveal Transition();
    var time := run.ranks[vertex];
    assert run.events[time] == Output.Emit(vertex);
    assert Transition(graph, run.states[time], run.states[time + 1], Output.Emit(vertex));
  }
}
