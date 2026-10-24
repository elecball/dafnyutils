include "TsortSortProof.dfy"
include "TsortCycleSpec.dfy"
include "TsortSpec.dfy"

module TsortCycleProof {
  import BenchWorld
  import Spec = TsortCycleSpec
  import SortProof = TsortSortProof
  import Step = TsortStepSpec
  import SortSpec = TsortSortSpec
  import Output = TsortSpec
  import opened Trace = TsortStepProof

  ghost opaque predicate Reversed(vertices: seq<BenchWorld.Bytes>, indices: seq<nat>, path: seq<BenchWorld.Bytes>) {
    |indices| == |path| && (forall i: nat {:trigger indices[i]} | i < |indices| ::
                              indices[i] < |vertices| && path[|path| - 1 - i] == vertices[indices[i]])
  }

  ghost opaque predicate CursorPath(
    vertices: seq<BenchWorld.Bytes>,
    indices: seq<nat>,
    path: seq<BenchWorld.Bytes>,
    cursor: nat
  ) {
    |indices| == |path| && |indices| > 0 && cursor < |vertices| &&
    cursor == indices[|indices| - 1] && Reversed(vertices, indices, path)
  }

  lemma CursorHead(vertices: seq<BenchWorld.Bytes>, indices: seq<nat>, path: seq<BenchWorld.Bytes>, cursor: nat)
    requires CursorPath(vertices, indices, path, cursor)
    ensures Reversed(vertices, indices, path) && |indices| == |path| && |indices| > 0
    ensures cursor < |vertices| && cursor == indices[|indices| - 1] && path[0] == vertices[cursor]
  {
    reveal CursorPath(), Reversed();
  }

  lemma CursorPrepend(
    vertices: seq<BenchWorld.Bytes>,
    indices: seq<nat>,
    path: seq<BenchWorld.Bytes>,
    cursor: nat,
    next: nat
  )
    requires CursorPath(vertices, indices, path, cursor) && next < |vertices|
    ensures CursorPath(vertices, indices + [next], [vertices[next]] + path, next)
  {
    reveal CursorPath(), Reversed();
    var nextIndices := indices + [next];
    var nextPath := [vertices[next]] + path;
    forall i: nat | i < |nextIndices|
      ensures nextIndices[i] < |vertices| && nextPath[|nextPath| - 1 - i] == vertices[nextIndices[i]]
    {
      if i < |indices| { assert nextIndices[i] == indices[i]; }
      else { assert i == |indices|; }
    }
  }

  lemma Reject(
    vertices: seq<BenchWorld.Bytes>,
    graph: map<BenchWorld.Bytes, seq<BenchWorld.Bytes>>,
    indeg: map<BenchWorld.Bytes, nat>,
    anchor: nat,
    checked: nat
  )
    requires indeg.Keys == graph.Keys && (set v | v in vertices) == graph.Keys
    requires anchor < |vertices| && checked < |vertices|
    requires var next := (anchor + checked + 1) % |vertices|;
             indeg[vertices[next]] == 0 || vertices[anchor] !in graph[vertices[next]]
    ensures Spec.Rejected(vertices, graph, indeg, anchor, checked + 1)
  {
    reveal Spec.Rejected();
  }

  lemma StalledDegrees(
    graph: map<BenchWorld.Bytes, seq<BenchWorld.Bytes>>,
    visited: map<BenchWorld.Bytes, bool>,
    indeg: map<BenchWorld.Bytes, nat>
  )
    requires Step.Ready(graph, [], visited, indeg)
    requires exists v | v in graph :: !visited[v]
    ensures exists v | v in graph :: indeg[v] > 0
    ensures forall target | target in graph && indeg[target] > 0 ::
              exists source | source in graph && indeg[source] > 0 :: target in graph[source]
  {
    assert exists v | v in graph :: indeg[v] > 0 by {
      var v :| v in graph && !visited[v];
      assert indeg[v] > 0;
    }
    forall target | target in graph && indeg[target] > 0
      ensures exists source | source in graph && indeg[source] > 0 :: target in graph[source]
    {
      Trace.PositivePredecessor(graph, visited, indeg, target);
      var source :| source in graph && !visited[source] && target in graph[source];
      assert indeg[source] > 0;
    }
  }

  lemma RecoveryCut(
    before: map<BenchWorld.Bytes, seq<BenchWorld.Bytes>>,
    after: map<BenchWorld.Bytes, seq<BenchWorld.Bytes>>,
    beforeIndeg: map<BenchWorld.Bytes, nat>,
    afterIndeg: map<BenchWorld.Bytes, nat>,
    cycle: seq<BenchWorld.Bytes>,
    position: nat
  )
    requires Spec.Recovery(before, after, beforeIndeg, afterIndeg, cycle, position)
    ensures |cycle| > 0 && cycle[|cycle| - 1] in before
    ensures position < |before[cycle[|cycle| - 1]]|
    ensures after == before[cycle[|cycle| - 1] :=
                     before[cycle[|cycle| - 1]][..position] + before[cycle[|cycle| - 1]][position + 1..]]
  {
    reveal Spec.Recovery();
  }

  lemma DistanceIndex(size: nat, anchor: nat, index: nat)
    requires anchor < size && index < size
    ensures 1 <= Spec.Distance(size, anchor, index) <= size
    ensures (anchor + Spec.Distance(size, anchor, index)) % size == index
  {
    if index > anchor {
      assert anchor + Spec.Distance(size, anchor, index) == index;
    } else {
      assert anchor + Spec.Distance(size, anchor, index) == size + index;
    }
  }

  lemma ScanIndex(size: nat, anchor: nat, checked: nat)
    requires anchor < size && checked < size
    ensures Spec.Distance(size, anchor, (anchor + checked + 1) % size) == checked + 1
  {
    if anchor + checked + 1 < size {
      assert (anchor + checked + 1) % size == anchor + checked + 1;
    } else {
      assert (anchor + checked + 1) % size == anchor + checked + 1 - size;
    }
  }

  lemma Choose(
    vertices: seq<BenchWorld.Bytes>,
    graph: map<BenchWorld.Bytes, seq<BenchWorld.Bytes>>,
    indeg: map<BenchWorld.Bytes, nat>,
    anchor: nat,
    checked: nat
  )
    requires indeg.Keys == graph.Keys && (set v | v in vertices) == graph.Keys
    requires anchor < |vertices| && checked < |vertices|
    requires forall d: nat | 0 < d <= checked ::
               Spec.Rejected(vertices, graph, indeg, anchor, d)
    ensures forall j: nat | j < |vertices| && indeg[vertices[j]] > 0 && vertices[anchor] in graph[vertices[j]] ::
              Spec.Distance(|vertices|, anchor, (anchor + checked + 1) % |vertices|) <= Spec.Distance(|vertices|, anchor, j)
  {
    reveal Spec.Rejected();
    ScanIndex(|vertices|, anchor, checked);
    forall j: nat | j < |vertices| && indeg[vertices[j]] > 0 && vertices[anchor] in graph[vertices[j]]
      ensures Spec.Distance(|vertices|, anchor, (anchor + checked + 1) % |vertices|) <= Spec.Distance(|vertices|, anchor, j)
    {
      DistanceIndex(|vertices|, anchor, j);
      var distance := Spec.Distance(|vertices|, anchor, j);
      if distance <= checked {
        assert Spec.Rejected(vertices, graph, indeg, anchor, distance);
      }
      assert distance > checked;
    }
  }

  lemma NotExhausted(
    vertices: seq<BenchWorld.Bytes>,
    graph: map<BenchWorld.Bytes, seq<BenchWorld.Bytes>>,
    indeg: map<BenchWorld.Bytes, nat>,
    anchor: nat,
    checked: nat
  )
    requires indeg.Keys == graph.Keys && (set v | v in vertices) == graph.Keys
    requires anchor < |vertices| && checked < |vertices|
    requires exists source | source in graph && indeg[source] > 0 :: vertices[anchor] in graph[source]
    requires forall d: nat | 0 < d <= checked + 1 ::
               Spec.Rejected(vertices, graph, indeg, anchor, d)
    ensures checked + 1 < |vertices|
  {
    reveal Spec.Rejected();
    if checked + 1 == |vertices| {
      var source :| source in graph && indeg[source] > 0 && vertices[anchor] in graph[source];
      assert source in vertices;
      var index: nat :| index < |vertices| && vertices[index] == source;
      DistanceIndex(|vertices|, anchor, index);
      assert Spec.Rejected(vertices, graph, indeg, anchor, Spec.Distance(|vertices|, anchor, index));
    }
  }

  lemma AppendWalk(
    graph: map<BenchWorld.Bytes, seq<BenchWorld.Bytes>>,
    indeg: map<BenchWorld.Bytes, nat>,
    vertices: seq<BenchWorld.Bytes>,
    indices: seq<nat>,
    next: nat
  )
    requires indeg.Keys == graph.Keys && (set v | v in vertices) == graph.Keys
    requires Spec.Walk(graph, indeg, vertices, indices)
    requires |indices| > 0 && indices[|indices| - 1] < |vertices|
    requires next < |vertices| && indeg[vertices[next]] > 0
    requires vertices[indices[|indices| - 1]] in graph[vertices[next]]
    requires forall j: nat | j < |vertices| && indeg[vertices[j]] > 0 &&
                             vertices[indices[|indices| - 1]] in graph[vertices[j]] ::
               Spec.Distance(|vertices|, indices[|indices| - 1], next) <= Spec.Distance(|vertices|, indices[|indices| - 1], j)
    ensures Spec.Walk(graph, indeg, vertices, indices + [next])
  {
    reveal Spec.Walk();
  }

  lemma SelectedWalk(
    graph: map<BenchWorld.Bytes, seq<BenchWorld.Bytes>>,
    indeg: map<BenchWorld.Bytes, nat>,
    vertices: seq<BenchWorld.Bytes>,
    indices: seq<nat>,
    path: seq<BenchWorld.Bytes>,
    next: nat,
    index: nat
  )
    requires Spec.Path(graph, indeg, path) && |path| == |indices| && Reversed(vertices, indices, path)
    requires Spec.Walk(graph, indeg, vertices, indices)
    requires forall i: nat, j: nat | i < j < |vertices| :: vertices[i] != vertices[j]
    requires next < |vertices| && index < |path| - 1 && vertices[next] == path[index]
    requires Spec.Walk(graph, indeg, vertices, indices + [next])
    ensures Spec.SelectionFields(graph, indeg, vertices, indices + [next], |indices| - 1 - index, path[..index + 1])
  {
    reveal Reversed();
    reveal Spec.Path();
    reveal Spec.SelectionFields();
    reveal Spec.Walk();
    var begin := |indices| - 1 - index;
    assert vertices[next] == vertices[indices[begin]];
    assert next == indices[begin];
    forall i: nat, j: nat | 1 <= i < j < |indices|
      ensures indices[i] != indices[j]
    {
      assert path[|indices| - 1 - j] != path[|indices| - 1 - i];
    }
    var all := indices + [next];
    forall j: nat | j < |all|
      ensures all[j] < |vertices|
    {
      if j < |indices| {
        assert indices[j] < |vertices|;
      }
    }
    forall j: nat {:trigger path[..index + 1][j]} | j < |path[..index + 1]|
      ensures path[..index + 1][j] == vertices[all[|all| - 2 - j]]
    {
      assert all[|all| - 2 - j] == indices[|indices| - 1 - j];
    }
  }

  lemma Bound(
    graph: map<BenchWorld.Bytes, seq<BenchWorld.Bytes>>,
    indeg: map<BenchWorld.Bytes, nat>,
    path: seq<BenchWorld.Bytes>
  )
    requires Spec.Path(graph, indeg, path)
    ensures |path| <= |graph| + 1
  {
    reveal Spec.Path();
    var prefix := path[..|path| - 1];
    SortProof.DistinctSize(prefix);
    var elements := set v | v in prefix;
    assert elements <= graph.Keys;
    SortProof.SubsetSize(elements, graph.Keys);
    assert |graph.Keys| == |graph|;
  }

  lemma Close(
    graph: map<BenchWorld.Bytes, seq<BenchWorld.Bytes>>,
    indeg: map<BenchWorld.Bytes, nat>,
    path: seq<BenchWorld.Bytes>,
    index: nat
  )
    requires Spec.Path(graph, indeg, path)
    requires index < |path| - 1 && path[index] in graph && path[0] in graph[path[index]]
    ensures Spec.Cycle(graph, path[..index + 1])
    ensures forall v | v in path[..index + 1] :: v in indeg && indeg[v] > 0
  {
    reveal Spec.Path();
  }

  lemma Head(
    graph: map<BenchWorld.Bytes, seq<BenchWorld.Bytes>>,
    indeg: map<BenchWorld.Bytes, nat>,
    path: seq<BenchWorld.Bytes>
  )
    requires Spec.Path(graph, indeg, path)
    ensures |path| > 0 && path[0] in graph && path[0] in indeg && indeg[path[0]] > 0
  {
    reveal Spec.Path();
  }

  lemma Extend(
    graph: map<BenchWorld.Bytes, seq<BenchWorld.Bytes>>,
    indeg: map<BenchWorld.Bytes, nat>,
    path: seq<BenchWorld.Bytes>,
    source: BenchWorld.Bytes
  )
    requires Spec.Path(graph, indeg, path)
    requires |path| > 0 && source in graph && source in indeg && indeg[source] > 0
    requires path[0] in graph[source] && source !in path[..|path| - 1]
    ensures Spec.Path(graph, indeg, [source] + path)
    ensures |path| + 1 <= |graph| + 1
  {
    reveal Spec.Path();
    var next := [source] + path;
    forall i: nat, j: nat | i < j < |next| - 1
      ensures next[i] != next[j]
    {
      if i == 0 { assert path[j - 1] in path[..|path| - 1]; }
    }
    Bound(graph, indeg, next);
  }

  lemma CyclicOrder(vertices: seq<Bytes>, anchor: nat, first: nat, second: nat)
    requires SortSpec.Ordered(vertices) && anchor < |vertices| && first < |vertices| && second < |vertices|
    requires forall i: nat, j: nat | i < j < |vertices| :: vertices[i] != vertices[j]
    ensures Output.CyclicLe(vertices[anchor], vertices[first], vertices[second]) ==
            (Spec.Distance(|vertices|, anchor, first) <= Spec.Distance(|vertices|, anchor, second))
  {
    SortProof.IndexOrder(vertices, first, anchor);
    SortProof.IndexOrder(vertices, second, anchor);
    SortProof.IndexOrder(vertices, first, second);
  }

  lemma ProjectedRelation(
    initial: Graph,
    graph: Graph,
    origins: Origins,
    visited: map<Bytes, bool>,
    source: Bytes,
    target: Bytes
  )
    requires Projection(initial, graph, origins) && visited.Keys == graph.Keys
    requires source in graph && !visited[source]
    ensures (target in graph[source]) == Output.ActiveRelation(
                                           initial,
                                           map edge | edge in SortSpec.Edges(initial) ::
                                             if !visited[edge.0] && edge.1 in origins[edge.0] then 1 else 0, source, target, 1
                                         )
  {
    var removed := map edge | edge in SortSpec.Edges(initial) ::
      if !visited[edge.0] && edge.1 in origins[edge.0] then 1 else 0;
    if target in graph[source] {
      var j: nat :| j < |graph[source]| && graph[source][j] == target;
      assert removed[(source, origins[source][j])] == 1;
    }
    if Output.ActiveRelation(initial, removed, source, target, 1) {
      var p: nat :| p < |initial[source]| && initial[source][p] == target && removed[(source, p)] >= 1;
      var j: nat :| j < |origins[source]| && origins[source][j] == p;
      assert graph[source][j] == target;
    }
  }

  lemma ChooseCycle(
    initial: Graph,
    graph: Graph,
    origins: Origins,
    visited: map<Bytes, bool>,
    indeg: map<Bytes, nat>,
    cycle: seq<Bytes>,
    pending: set<Bytes>,
    active: set<Edge>
  )
    requires Projection(initial, graph, origins) && Step.Ready(graph, [], visited, indeg)
    requires Spec.Selected(graph, indeg, cycle)
    requires pending == (set v | v in visited && !visited[v])
    requires active == (set edge | edge in SortSpec.Edges(initial) && !visited[edge.0] && edge.1 in origins[edge.0])
    ensures Selection(initial, pending, active, cycle)
  {
    reveal Selection(), Spec.Selected(), Spec.SelectionFields(), Spec.Walk();
    var vertices: seq<Bytes>, indices: seq<nat>, begin: nat :|
      SortSpec.Ordered(vertices) &&
      (forall i: nat, j: nat | i < j < |vertices| :: vertices[i] != vertices[j]) &&
      Spec.SelectionFields(graph, indeg, vertices, indices, begin, cycle);
    var walk := seq(|indices|, (i: nat) requires i < |indices| => vertices[indices[i]]);
    var ranks := map v | v in initial :: if v in pending then 2 else 0;
    var removed := map edge | edge in SortSpec.Edges(initial) :: if edge in active then 1 else 0;
    assert forall v | v in graph :: (indeg[v] > 0) == (v in pending);
    forall source, target | source in graph && !visited[source] && target in graph
      ensures (target in graph[source]) == Output.ActiveRelation(initial, removed, source, target, 1)
    {
      ProjectedRelation(initial, graph, origins, visited, source, target);
    }
    forall v | v in pending
      ensures SortSpec.BytesLe(walk[0], v)
    {
      var j: nat :| j < |vertices| && vertices[j] == v;
      assert j >= indices[0];
    }
    forall i: nat | 0 < i < |walk|
      ensures Output.ActiveRelation(initial, removed, walk[i], walk[i - 1], 1)
      ensures forall source | source in initial && ranks[source] > 1 &&
                              Output.ActiveRelation(initial, removed, source, walk[i - 1], 1) ::
                Output.CyclicLe(walk[i - 1], walk[i], source)
    {
      forall source | source in initial && ranks[source] > 1 &&
                      Output.ActiveRelation(initial, removed, source, walk[i - 1], 1)
        ensures Output.CyclicLe(walk[i - 1], walk[i], source)
      {
        var j: nat :| j < |vertices| && vertices[j] == source;
        CyclicOrder(vertices, indices[i - 1], indices[i], j);
      }
    }
    assert Output.SelectedCycleFields(initial, ranks, removed, 1, cycle, walk, begin);
  }

  lemma RecordCut(
    initial: Graph,
    graph: Graph,
    origins: Origins,
    visited: map<Bytes, bool>,
    indeg: map<Bytes, nat>,
    cutIndeg: map<Bytes, nat>,
    remaining: Graph,
    nextQueue: seq<Bytes>,
    nextIndeg: map<Bytes, nat>,
    cycle: seq<Bytes>,
    index: nat
  )
    requires Projection(initial, graph, origins) && Step.Ready(graph, [], visited, indeg)
    requires |cycle| > 0 && cycle[|cycle| - 1] in graph && index < |graph[cycle[|cycle| - 1]]|
    requires Spec.Recovery(graph, remaining, indeg, cutIndeg, cycle, index)
    requires Spec.Selected(graph, indeg, cycle) && forall v | v in cycle :: v in graph && indeg[v] > 0
    requires Step.Ready(remaining, nextQueue, visited, nextIndeg)
    requires forall v | v in nextQueue :: !visited[v]
    ensures var source := cycle[|cycle| - 1];
            var nextOrigins := origins[source := origins[source][..index] + origins[source][index + 1..]];
            Projection(initial, remaining, nextOrigins) &&
            Transition(initial, SnapshotOf(initial, origins, visited, []),
                       SnapshotOf(initial, nextOrigins, visited, nextQueue), Output.Cut(cycle, (source, origins[source][index])))
  {
    reveal SnapshotOf();
    reveal Spec.Recovery();
    var source := cycle[|cycle| - 1];
    var target := cycle[0];
    var edge := (source, origins[source][index]);
    var nextOrigins := origins[source := origins[source][..index] + origins[source][index + 1..]];
    ProjectCut(initial, graph, origins, source, index);
    var before := SnapshotOf(initial, origins, visited, []);
    ChooseCycle(initial, graph, origins, visited, indeg, cycle, before.pending, before.active);
    ObserveReady(initial, graph, origins, visited, [], indeg);
    ObserveReady(initial, remaining, nextOrigins, visited, nextQueue, nextIndeg);
    var after := SnapshotOf(initial, nextOrigins, visited, nextQueue);
    assert !visited[source] && edge in before.active;
    assert after.pending == before.pending;
    assert after.active == before.active - {edge};
    forall v | v in nextQueue
      ensures v == target
    {
      QueueFields(initial, after, v);
      QueueFields(initial, before, v);
      if v != target {
        assert SortSpec.Incoming(initial, before.active, v) == SortSpec.Incoming(initial, after.active, v);
      }
    }
    assert |nextQueue| <= 1 by {
      hide *;
      if |nextQueue| > 1 {
        assert nextQueue[0] in nextQueue && nextQueue[1] in nextQueue;
        assert nextQueue[0] == nextQueue[1];
        assert nextQueue[0] != nextQueue[1];
      }
    }
    forall p: nat | p < edge.1 && initial[source][p] == target
      ensures (source, p) !in before.active
    {
      if (source, p) in before.active {
        var j: nat :| j < |origins[source]| && origins[source][j] == p;
        assert j < index;
        assert graph[source][j] == target;
      }
    }
    assert initial[source][edge.1] == target;
    assert Transition(initial, before, after, Output.Cut(cycle, edge)) by {
      hide *;
      reveal Transition();
    }
  }

  lemma TransportSelection(
    graph: Graph,
    a: map<Bytes, nat>,
    b: map<Edge, nat>,
    time: nat,
    nextA: map<Bytes, nat>,
    nextB: map<Edge, nat>,
    nextTime: nat,
    cycle: seq<Bytes>
  )
    requires a.Keys == graph.Keys == nextA.Keys && b.Keys == SortSpec.Edges(graph) == nextB.Keys
    requires forall v | v in graph :: (a[v] > time) == (nextA[v] > nextTime)
    requires forall edge | edge in b :: (b[edge] >= time) == (nextB[edge] >= nextTime)
    requires Output.SelectedCycle(graph, a, b, time, cycle)
    ensures Output.SelectedCycle(graph, nextA, nextB, nextTime, cycle)
  {
    var walk: seq<Bytes>, begin: nat :| Output.SelectedCycleFields(graph, a, b, time, cycle, walk, begin);
    assert Output.SelectedCycleFields(graph, nextA, nextB, nextTime, cycle, walk, begin);
  }

  lemma SelectionAt(graph: Graph, run: Run, time: nat)
    requires Schedule(graph, run) && run.ranks.Keys == graph.Keys && run.removed.Keys == SortSpec.Edges(graph)
    requires time < |run.events| && run.events[time].Cut?
    ensures Output.SelectedCycle(graph, run.ranks, run.removed, time, run.events[time].cycle)
  {
    EventFields(graph, run, time);
    RecordFields(graph, run);
    At(graph, run, time);
    reveal Transition();
    var state := run.states[time];
    var a: map<Bytes, nat> := map v | v in graph :: if v in state.pending then 2 else 0;
    var b: map<Edge, nat> := map edge | edge in SortSpec.Edges(graph) :: if edge in state.active then 1 else 0;
    forall v | v in graph
      ensures (a[v] > 1) == (run.ranks[v] > time)
    {
      if run.ranks[v] == time { assert run.events[time] == Output.Emit(v); }
    }
    assert forall edge | edge in b :: (b[edge] >= 1) == (run.removed[edge] >= time);
    assert Output.SelectedCycle(graph, a, b, 1, run.events[time].cycle) by {
      reveal Selection();
    }
    TransportSelection(graph, a, b, 1, run.ranks, run.removed, time, run.events[time].cycle);
  }
}
