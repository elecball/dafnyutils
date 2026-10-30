include "../Spec/TsortSortSpec.dfy"
include "TsortStepProof.dfy"

module TsortSortProof {
  import BenchWorld
  import Spec = TsortSortSpec
  import Step = TsortStepSpec
  import Output = TsortSpec
  import opened Trace = TsortStepProof

  lemma SubsetSize<T>(small: set<T>, large: set<T>)
    requires small <= large
    ensures |small| <= |large|
    decreases |small|
  {
    if small != {} {
      var value :| value in small;
      SubsetSize(small - {value}, large - {value});
      assert small == (small - {value}) + {value};
      assert large == (large - {value}) + {value};
    }
  }

  lemma DistinctSize(values: seq<BenchWorld.Bytes>)
    requires forall i: nat, j: nat | i < j < |values| :: values[i] != values[j]
    ensures |set v | v in values| == |values|
    decreases |values|
  {
    if |values| > 0 {
      DistinctSize(values[1..]);
      assert values[0] !in values[1..];
      assert (set v | v in values) == {values[0]} + (set v | v in values[1..]);
    }
  }

  lemma SizeFields(
    vertices: seq<BenchWorld.Bytes>,
    graph: map<BenchWorld.Bytes, seq<BenchWorld.Bytes>>,
    ordered: seq<BenchWorld.Bytes>
  )
    requires (set v | v in vertices) == graph.Keys && Spec.TopologicalPrefix(graph, ordered)
    requires forall i: nat, j: nat | i < j < |vertices| :: vertices[i] != vertices[j]
    ensures |ordered| <= |vertices|
    ensures (|ordered| == |vertices|) == ((set v | v in ordered) == graph.Keys)
  {
    DistinctSize(vertices);
    DistinctSize(ordered);
    var expected := set v | v in vertices;
    var emitted := set v | v in ordered;
    SubsetSize(emitted, expected);
    var remaining := expected - emitted;
    if remaining != {} {
      var missing :| missing in remaining;
      SubsetSize(emitted, expected - {missing});
      assert expected == (expected - {missing}) + {missing};
    } else {
      forall v | v in expected
        ensures v in emitted
      { assert v !in remaining; }
      assert expected <= emitted;
    }
  }

  lemma AppendOrdered(vertices: seq<BenchWorld.Bytes>, queue: seq<BenchWorld.Bytes>, index: nat)
    requires index < |vertices| && Spec.Ordered(vertices) && Spec.Ordered(queue)
    requires forall v | v in queue :: v in vertices[..index]
    ensures Spec.Ordered(queue + [vertices[index]])
  {
    Reflexive(vertices[index]);
    forall j: nat | j < |queue|
      ensures Spec.BytesLe(queue[j], vertices[index])
    {
      assert queue[j] in vertices[..index];
      var k: nat :| k < index && vertices[k] == queue[j];
    }
  }

  lemma ProcessedPredecessors(
    graph: map<BenchWorld.Bytes, seq<BenchWorld.Bytes>>,
    ordered: seq<BenchWorld.Bytes>,
    visited: map<BenchWorld.Bytes, bool>
  )
    requires Spec.TopologicalPrefix(graph, ordered) && visited.Keys == graph.Keys
    requires forall v | v in graph :: visited[v] == (v in ordered)
    ensures forall source | source in graph ::
              forall target | target in graph[source] && target in visited && visited[target] :: visited[source]
  {
    forall source, target | source in graph && target in graph[source] && target in visited && visited[target]
      ensures visited[source]
    {
      var i: nat :| i < |ordered| && ordered[i] == target;
      assert source in ordered[..i];
    }
  }

  lemma WeakenPrefix(
    before: map<BenchWorld.Bytes, seq<BenchWorld.Bytes>>,
    after: map<BenchWorld.Bytes, seq<BenchWorld.Bytes>>,
    ordered: seq<BenchWorld.Bytes>
  )
    requires Spec.TopologicalPrefix(before, ordered) && after.Keys == before.Keys
    requires forall source | source in before ::
               forall target | target in after[source] ::
                 target in before[source]
    ensures Spec.TopologicalPrefix(after, ordered)
  {
    forall i: nat | i < |ordered|
      ensures forall source | source in after && ordered[i] in after[source] :: source in ordered[..i]
    {
      forall source | source in after && ordered[i] in after[source]
        ensures source in ordered[..i]
      {
        assert ordered[i] in before[source];
      }
    }
  }

  lemma AfterCut(
    vertices: seq<BenchWorld.Bytes>,
    before: map<BenchWorld.Bytes, seq<BenchWorld.Bytes>>,
    after: map<BenchWorld.Bytes, seq<BenchWorld.Bytes>>,
    source: BenchWorld.Bytes,
    position: nat,
    ordered: seq<BenchWorld.Bytes>
  )
    requires (set v | v in vertices) == before.Keys && Spec.TopologicalPrefix(before, ordered)
    requires forall i: nat, j: nat | i < j < |vertices| :: vertices[i] != vertices[j]
    requires source in before && position < |before[source]|
    requires after == before[source := before[source][..position] + before[source][position + 1..]]
    ensures Spec.TopologicalPrefix(after, ordered)
    ensures Spec.EdgeCount(vertices, after) + 1 == Spec.EdgeCount(vertices, before)
  {
    CutCount(vertices, before, after, source, position);
    assert forall vertex | vertex in before ::
        forall target | target in after[vertex] :: target in before[vertex];
    WeakenPrefix(before, after, ordered);
  }

  lemma CutCount(
    vertices: seq<BenchWorld.Bytes>,
    before: map<BenchWorld.Bytes, seq<BenchWorld.Bytes>>,
    after: map<BenchWorld.Bytes, seq<BenchWorld.Bytes>>,
    source: BenchWorld.Bytes,
    position: nat
  )
    requires forall v | v in vertices :: v in before
    requires forall i: nat, j: nat | i < j < |vertices| :: vertices[i] != vertices[j]
    requires source in before && position < |before[source]|
    requires after == before[source := before[source][..position] + before[source][position + 1..]]
    ensures Spec.EdgeCount(vertices, after) == Spec.EdgeCount(vertices, before) - (if source in vertices then 1 else 0)
    decreases |vertices|
  {
    if |vertices| > 0 {
      CutCount(vertices[1..], before, after, source, position);
      if vertices[0] == source { assert source !in vertices[1..]; }
    }
  }

  lemma AppendPrefix(
    graph: map<BenchWorld.Bytes, seq<BenchWorld.Bytes>>,
    ordered: seq<BenchWorld.Bytes>,
    visited: map<BenchWorld.Bytes, bool>,
    indeg: map<BenchWorld.Bytes, nat>,
    vertex: BenchWorld.Bytes
  )
    requires Spec.TopologicalPrefix(graph, ordered) && Spec.LiveDegrees(graph, visited, indeg)
    requires forall v | v in graph :: visited[v] == (v in ordered)
    requires vertex in graph && !visited[vertex] && indeg[vertex] == 0
    ensures Spec.TopologicalPrefix(graph, ordered + [vertex])
  {
    ZeroPredecessors(graph, visited, indeg, vertex);
    forall source | source in graph && vertex in graph[source]
      ensures source in ordered
    {
      assert visited[source];
    }
    var next := ordered + [vertex];
    assert vertex !in ordered;
    forall i: nat | i < |next|
      ensures forall source | source in graph && next[i] in graph[source] :: source in next[..i]
    {
      if i < |ordered| {
        assert next[i] == ordered[i] && next[..i] == ordered[..i];
      } else {
        assert next[i] == vertex && next[..i] == ordered;
      }
    }
    assert Spec.TopologicalPrefix(graph, next);
  }

  lemma Reflexive(a: BenchWorld.Bytes)
    ensures Spec.BytesLe(a, a)
    decreases |a|
  {
    if |a| > 0 { Reflexive(a[1..]); }
  }

  lemma Total(a: BenchWorld.Bytes, b: BenchWorld.Bytes)
    ensures Spec.BytesLe(a, b) || Spec.BytesLe(b, a)
    decreases |a| + |b|
  {
    if |a| > 0 && |b| > 0 && a[0] == b[0] { Total(a[1..], b[1..]); }
  }

  lemma CommonPrefix(a: BenchWorld.Bytes, b: BenchWorld.Bytes, count: nat)
    requires count <= |a| && count <= |b|
    requires forall i: nat | i < count :: a[i] == b[i]
    ensures Spec.BytesLe(a, b) == Spec.BytesLe(a[count..], b[count..])
    decreases count
  {
    if count > 0 {
      CommonPrefix(a[1..], b[1..], count - 1);
    }
  }

  lemma Transitive(a: BenchWorld.Bytes, b: BenchWorld.Bytes, c: BenchWorld.Bytes)
    requires Spec.BytesLe(a, b) && Spec.BytesLe(b, c)
    ensures Spec.BytesLe(a, c)
    decreases |a| + |b| + |c|
  {
    if |a| > 0 && |b| > 0 && |c| > 0 && a[0] == b[0] == c[0] {
      Transitive(a[1..], b[1..], c[1..]);
    }
  }

  lemma InsertOrdered(queue: seq<BenchWorld.Bytes>, vertex: BenchWorld.Bytes, index: nat)
    requires index <= |queue| && Spec.Ordered(queue)
    requires forall i: nat | i < index :: Spec.BytesLe(queue[i], vertex)
    requires index < |queue| ==> Spec.BytesLe(vertex, queue[index])
    ensures Spec.Ordered(queue[..index] + [vertex] + queue[index..])
  {
    Reflexive(vertex);
    forall j: nat | index <= j < |queue|
      ensures Spec.BytesLe(vertex, queue[j])
    {
      Transitive(vertex, queue[index], queue[j]);
    }
  }

  lemma FilteredLive(
    graph: map<BenchWorld.Bytes, seq<BenchWorld.Bytes>>,
    visited: map<BenchWorld.Bytes, bool>,
    indeg: map<BenchWorld.Bytes, nat>
  )
    requires visited.Keys == graph.Keys
    requires Spec.Indegrees(map source | source in graph :: if visited[source] then [] else graph[source], indeg)
    requires forall source | source in graph ::
               forall target | target in graph[source] && target in visited && visited[target] :: visited[source]
    ensures Spec.LiveDegrees(graph, visited, indeg)
    ensures forall v | v in graph && visited[v] :: indeg[v] == 0
  {
    reveal Spec.Counts();
    var filtered := map source | source in graph :: if visited[source] then [] else graph[source];
    assert Spec.Edges(filtered) == Spec.ActiveEdges(graph, visited);
    forall target | target in graph
      ensures indeg[target] == |Spec.Incoming(graph, Spec.ActiveEdges(graph, visited), target)|
      ensures visited[target] ==> indeg[target] == 0
    {
      assert Spec.Incoming(filtered, Spec.Edges(filtered), target) ==
             Spec.Incoming(graph, Spec.ActiveEdges(graph, visited), target);
      if visited[target] {
        assert Spec.Incoming(graph, Spec.ActiveEdges(graph, visited), target) == {};
      }
    }
  }

  lemma InitialLive(
    graph: map<BenchWorld.Bytes, seq<BenchWorld.Bytes>>,
    visited: map<BenchWorld.Bytes, bool>,
    indeg: map<BenchWorld.Bytes, nat>
  )
    requires Spec.Indegrees(graph, indeg) && indeg.Keys == graph.Keys
    requires visited.Keys == graph.Keys && forall vertex | vertex in graph :: !visited[vertex]
    ensures Spec.LiveDegrees(graph, visited, indeg)
  {
    assert Spec.ActiveEdges(graph, visited) == Spec.Edges(graph);
  }

  lemma AddEdge(
    graph: map<BenchWorld.Bytes, seq<BenchWorld.Bytes>>,
    edges: set<(BenchWorld.Bytes, nat)>,
    indeg: map<BenchWorld.Bytes, nat>,
    edge: (BenchWorld.Bytes, nat)
  )
    requires Spec.Counts(graph, edges, indeg)
    requires indeg.Keys == graph.Keys
    requires edge in Spec.Edges(graph) && edge !in edges
    requires graph[edge.0][edge.1] in graph
    ensures Spec.Counts(graph, edges + {edge},
                        indeg[graph[edge.0][edge.1] := indeg[graph[edge.0][edge.1]] + 1])
  {
    reveal Spec.Counts();
    forall target | target in graph.Keys
      ensures |Spec.Incoming(graph, edges + {edge}, target)| ==
              indeg[target] + (if graph[edge.0][edge.1] == target then 1 else 0)
    {
      var incoming := Spec.Incoming(graph, edges, target);
      assert edge !in incoming;
      assert Spec.Incoming(graph, edges + {edge}, target) ==
             (if graph[edge.0][edge.1] == target then incoming + {edge} else incoming);
    }
  }

  lemma RemoveEdge(
    graph: map<BenchWorld.Bytes, seq<BenchWorld.Bytes>>,
    edges: set<(BenchWorld.Bytes, nat)>,
    indeg: map<BenchWorld.Bytes, nat>,
    edge: (BenchWorld.Bytes, nat)
  )
    requires Spec.Counts(graph, edges, indeg) && edge in edges
    requires indeg.Keys == graph.Keys && edge in Spec.Edges(graph)
    requires graph[edge.0][edge.1] in graph
    ensures indeg[graph[edge.0][edge.1]] > 0
    ensures Spec.Counts(graph, edges - {edge},
                        indeg[graph[edge.0][edge.1] := indeg[graph[edge.0][edge.1]] - 1])
  {
    reveal Spec.Counts();
    forall target | target in graph.Keys
      ensures |Spec.Incoming(graph, edges - {edge}, target)| +
              (if graph[edge.0][edge.1] == target then 1 else 0) == indeg[target]
    {
      var incoming := Spec.Incoming(graph, edges, target);
      assert (edge in incoming) == (graph[edge.0][edge.1] == target);
      assert Spec.Incoming(graph, edges - {edge}, target) == incoming - {edge};
      if edge in incoming {
        assert incoming == (incoming - {edge}) + {edge};
      }
    }
  }

  lemma Antisymmetric(first: BenchWorld.Bytes, second: BenchWorld.Bytes)
    requires Spec.BytesLe(first, second) && Spec.BytesLe(second, first)
    ensures first == second
    decreases |first| + |second|
  {
    if |first| > 0 && |second| > 0 {
      Antisymmetric(first[1..], second[1..]);
      assert first == [first[0]] + first[1..] && second == [second[0]] + second[1..];
    }
  }

  lemma IndexOrder(vertices: seq<BenchWorld.Bytes>, first: nat, second: nat)
    requires Spec.Ordered(vertices) && first < |vertices| && second < |vertices|
    requires forall i: nat, j: nat | i < j < |vertices| :: vertices[i] != vertices[j]
    ensures Spec.BytesLe(vertices[first], vertices[second]) == (first <= second)
  {
    if second < first && Spec.BytesLe(vertices[first], vertices[second]) {
      Antisymmetric(vertices[first], vertices[second]);
    }
  }

  ghost function Release(graph: Graph, removed: map<Edge, nat>, vertex: Bytes): (result: nat)
    ensures forall edge | edge in Spec.Incoming(graph, removed.Keys, vertex) :: removed[edge] < result
    ensures result == 0 || exists edge ::
              edge in Spec.Incoming(graph, removed.Keys, vertex) && removed[edge] + 1 == result
  {
    var values := {0} + set edge | edge in Spec.Incoming(graph, removed.Keys, vertex) :: removed[edge] + 1;
    var maximum := Maximum(values);
    forall edge | edge in Spec.Incoming(graph, removed.Keys, vertex)
      ensures removed[edge] < maximum
    { assert removed[edge] + 1 in values; }
    maximum
  }

  ghost function Position(graph: Graph, removed: map<Edge, nat>, vertex: Bytes): nat {
    LastPosition(graph, (set edge | edge in removed && removed[edge] + 1 == Release(graph, removed, vertex)), vertex)
  }

  ghost opaque predicate Before(graph: Graph, removed: map<Edge, nat>, first: Bytes, second: Bytes) {
    var a := Release(graph, removed, first);
    var b := Release(graph, removed, second);
    a < b || (a == b && (if a == 0 then Spec.BytesLe(first, second)
                         else Position(graph, removed, first) < Position(graph, removed, second)))
  }

  ghost opaque predicate QueueOrdered(graph: Graph, removed: map<Edge, nat>, queue: seq<Bytes>) {
    forall i: nat, j: nat | i < j < |queue| :: Before(graph, removed, queue[i], queue[j])
  }

  lemma ReleaseAt(graph: Graph, run: Run, vertex: Bytes, time: nat)
    requires Schedule(graph, run) && run.removed.Keys == Spec.Edges(graph)
    requires time < |run.states|
    ensures (Release(graph, run.removed, vertex) <= time) ==
            (Spec.Incoming(graph, run.states[time].active, vertex) == {})
  {
    At(graph, run, time);
    var incoming := Spec.Incoming(graph, run.removed.Keys, vertex);
    var active := Spec.Incoming(graph, run.states[time].active, vertex);
    var release := Release(graph, run.removed, vertex);
    if release <= time {
      forall edge | edge in active
        ensures false
      {
        assert edge in incoming && run.removed[edge] < release;
        assert run.removed[edge] >= time;
      }
    } else if active == {} {
      var edge :| edge in incoming && run.removed[edge] + 1 == release;
      assert edge !in active;
      assert edge !in run.states[time].active;
      assert run.removed[edge] < time;
    }
  }

  lemma PositionAt(graph: Graph, run: Run, vertex: Bytes, time: nat)
    requires Schedule(graph, run) && |run.states| == |run.events| + 1 && run.removed.Keys == Spec.Edges(graph)
    requires time < |run.events| && Release(graph, run.removed, vertex) == time + 1
    ensures Position(graph, run.removed, vertex) ==
            LastPosition(graph, run.states[time].active - run.states[time + 1].active, vertex)
  {
    EventFields(graph, run, time);
    At(graph, run, time);
    At(graph, run, time + 1);
    assert (set edge | edge in run.removed && run.removed[edge] == time) ==
           run.states[time].active - run.states[time + 1].active;
  }

  lemma {:isolate_assertions} QueueOrder(graph: Graph, run: Run, time: nat)
    requires Schedule(graph, run) && run.removed.Keys == Spec.Edges(graph)
    requires time < |run.states|
    ensures QueueOrdered(graph, run.removed, run.states[time].queue)
    decreases time
  {
    reveal Schedule();
    var queue := run.states[time].queue;
    if time == 0 {
      forall i: nat, j: nat | i < j < |queue|
        ensures Before(graph, run.removed, queue[i], queue[j])
      {
        QueueFields(graph, run.states[0], queue[i]);
        QueueFields(graph, run.states[0], queue[j]);
        ReleaseAt(graph, run, queue[i], 0);
        ReleaseAt(graph, run, queue[j], 0);
        assert Spec.BytesLe(queue[i], queue[j]);
        assert Before(graph, run.removed, queue[i], queue[j]) by { hide *; reveal Before(); }
      }
    } else {
      QueueOrder(graph, run, time - 1);
      EventFields(graph, run, time - 1);
      reveal Transition();
      var before := run.states[time - 1];
      var event := run.events[time - 1];
      if event.Emit? {
        assert |before.queue| > 0;
        var added: seq<Bytes>;
        {
          hide *;
          reveal Transition();
          added :| queue == before.queue[1..] + added &&
                   (forall v | v in added :: v !in before.queue) &&
                   (forall i: nat, j: nat | i < j < |added| ::
                      LastPosition(graph, before.active - run.states[time].active, added[i]) <
                      LastPosition(graph, before.active - run.states[time].active, added[j]));
        }
        forall i: nat | i < |added|
          ensures Release(graph, run.removed, added[i]) == time
        {
          QueueFields(graph, run.states[time], added[i]);
          ReleaseAt(graph, run, added[i], time);
          assert added[i] !in before.queue;
          assert added[i] in before.pending;
          QueueFields(graph, before, added[i]);
          ReleaseAt(graph, run, added[i], time - 1);
          PositionAt(graph, run, added[i], time - 1);
        }
        forall i: nat, j: nat | i < j < |queue|
          ensures Before(graph, run.removed, queue[i], queue[j])
        {
          if j < |before.queue| - 1 {
            assert queue[i] == before.queue[i + 1] && queue[j] == before.queue[j + 1];
            assert Before(graph, run.removed, before.queue[i + 1], before.queue[j + 1]) by {
              hide *;
              reveal QueueOrdered();
            }
          } else if i < |before.queue| - 1 {
            var addedIndex := j - |before.queue| + 1;
            assert queue[j] == added[addedIndex] by { hide *; }
            {
              hide *;
              QueueFields(graph, before, queue[i]);
              ReleaseAt(graph, run, queue[i], time - 1);
            }
            assert Release(graph, run.removed, queue[i]) < Release(graph, run.removed, queue[j]) by {
              hide *;
              assert Release(graph, run.removed, queue[i]) <= time - 1;
              assert Release(graph, run.removed, queue[j]) == time;
            }
            assert Before(graph, run.removed, queue[i], queue[j]) by { hide *; reveal Before(); }
          } else {
            var a := i - |before.queue| + 1;
            var b := j - |before.queue| + 1;
            assert queue[i] == added[a] && queue[j] == added[b] by { hide *; }
            PositionAt(graph, run, queue[i], time - 1);
            PositionAt(graph, run, queue[j], time - 1);
            assert LastPosition(graph, before.active - run.states[time].active, added[a]) <
                   LastPosition(graph, before.active - run.states[time].active, added[b]);
            assert Position(graph, run.removed, queue[i]) < Position(graph, run.removed, queue[j]) by {
              hide *;
              assert Position(graph, run.removed, queue[i]) ==
                     LastPosition(graph, before.active - run.states[time].active, added[a]);
              assert Position(graph, run.removed, queue[j]) ==
                     LastPosition(graph, before.active - run.states[time].active, added[b]);
            }
            assert Before(graph, run.removed, queue[i], queue[j]) by { hide *; reveal Before(); }
          }
        }
      } else { assert |queue| <= 1; }
    }
    assert QueueOrdered(graph, run.removed, queue) by { hide *; reveal QueueOrdered(); }
  }
}
