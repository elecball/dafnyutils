include "TsortCycleProof.dfy"

module TsortProof {
  import Spec = TsortSpec
  import SortSpec = TsortSortSpec
  import CycleProof = TsortCycleProof
  import opened Trace = TsortStepProof
  import opened SortProof = TsortSortProof

  lemma {:isolate_assertions} Certificate(graph: Graph, run: Run) returns (release: map<Bytes, nat>, position: map<Bytes, nat>)
    requires Schedule(graph, run) && |run.states| == |run.events| + 1 && run.states[|run.events|].pending == {}
    requires forall source | source in graph ::
               forall target | target in graph[source] ::
                 target in graph
    ensures Spec.SortCertificate(graph, run.events, run.ranks, run.removed, release, position)
  {
    assert run.ranks.Keys == graph.Keys && run.removed.Keys == SortSpec.Edges(graph) by {
      reveal Schedule();
      assert run.states[|run.events|].active == {};
    }
    RecordFields(graph, run);
    assert forall v | v in graph :: run.ranks[v] < |run.events| && run.events[run.ranks[v]] == Spec.Emit(v) by { hide *; }
    assert forall i: nat | i < |run.events| && run.events[i].Emit? ::
        run.events[i].vertex in graph && run.ranks[run.events[i].vertex] == i by { hide *; }
    release := map v | v in graph :: Release(graph, run.removed, v);
    position := map v | v in graph :: Position(graph, run.removed, v);
    forall edge | edge in SortSpec.Edges(graph)
      ensures run.removed[edge] == run.ranks[edge.0] ||
              (run.removed[edge] < run.ranks[edge.0] && run.removed[edge] < |run.events| &&
               run.events[run.removed[edge]].Cut? && run.events[run.removed[edge]].edge == edge)
    {
      var time := run.removed[edge];
      if time != run.ranks[edge.0] {
        EventFields(graph, run, time);
        At(graph, run, time);
        assert edge in run.states[time].active;
        assert edge.0 in run.states[time].pending;
        assert run.ranks[edge.0] >= time;
      }
    }
    forall v | v in graph
      ensures Spec.VertexRelease(graph, run.ranks, run.removed, release, position, v)
    {
      reveal Spec.VertexRelease();
      var time := run.ranks[v];
      EmitAt(graph, run, v);
      QueueFields(graph, run.states[time], v);
      ReleaseAt(graph, run, v, time);
      if release[v] > 0 {
        var edges := set edge | edge in run.removed && run.removed[edge] + 1 == release[v];
        if position[v] == 0 {
          var edge :| edge in SortSpec.Incoming(graph, run.removed.Keys, v) && run.removed[edge] + 1 == release[v];
          assert edge in SortSpec.Incoming(graph, edges, v);
        }
      }
    }
    forall edge | edge in SortSpec.Edges(graph)
      ensures graph[edge.0][edge.1] in graph && run.removed[edge] < run.ranks[graph[edge.0][edge.1]]
    {
      assert Spec.VertexRelease(graph, run.ranks, run.removed, release, position, graph[edge.0][edge.1]);
      reveal Spec.VertexRelease();
      assert edge in SortSpec.Incoming(graph, run.removed.Keys, graph[edge.0][edge.1]);
    }
    forall first: Bytes, second: Bytes {:trigger run.ranks[first], run.ranks[second]} |
      first in graph && second in graph && run.ranks[first] < run.ranks[second]
      ensures release[first] < release[second] ||
              (release[first] == release[second] &&
               (if release[first] == 0 then SortSpec.BytesLe(first, second) else position[first] < position[second]))
    {
      var time := run.ranks[first];
      EmitAt(graph, run, first);
      EmitAt(graph, run, second);
      At(graph, run, time);
      QueueOrder(graph, run, time);
      if release[second] <= time {
        ReleaseAt(graph, run, second, time);
        QueueFields(graph, run.states[time], second);
        var j: nat :| j < |run.states[time].queue| && run.states[time].queue[j] == second;
        assert run.states[time].queue[0] == first && j > 0;
        assert Before(graph, run.removed, first, second) by { hide *; reveal QueueOrdered(); }
      } else {
        assert Release(graph, run.removed, first) < Release(graph, run.removed, second);
        assert Before(graph, run.removed, first, second) by { hide *; reveal Before(); }
      }
      reveal Before();
    }
    forall i: nat | i < |run.events| && run.events[i].Cut?
      ensures run.events[i].edge in SortSpec.Edges(graph) && run.removed[run.events[i].edge] == i
      ensures |run.events[i].cycle| > 0 && run.events[i].edge.0 == run.events[i].cycle[|run.events[i].cycle| - 1] &&
              graph[run.events[i].edge.0][run.events[i].edge.1] == run.events[i].cycle[0]
      ensures forall p: nat | p < run.events[i].edge.1 && graph[run.events[i].edge.0][p] == run.events[i].cycle[0] ::
                run.removed[(run.events[i].edge.0, p)] < i
      ensures forall v | v in graph && run.ranks[v] > i :: release[v] > i
      ensures Spec.SelectedCycle(graph, run.ranks, run.removed, i, run.events[i].cycle)
    {
      var state := run.states[i];
      var event := run.events[i];
      EventFields(graph, run, i);
      reveal Transition();
      At(graph, run, i);
      At(graph, run, i + 1);
      assert forall v | v in graph :: (v in state.pending) == (run.ranks[v] > i);
      forall p: nat | p < event.edge.1 && graph[event.edge.0][p] == event.cycle[0]
        ensures run.removed[(event.edge.0, p)] < i
      {
        assert (event.edge.0, p) in run.removed by { reveal SortSpec.Edges(); }
        assert (event.edge.0, p) !in state.active;
      }
      forall v | v in graph && run.ranks[v] > i
        ensures release[v] > i
      {
        ReleaseAt(graph, run, v, i);
        QueueFields(graph, state, v);
      }
      CycleProof.SelectionAt(graph, run, i);
    }
    assert Spec.SortCertificate(graph, run.events, run.ranks, run.removed, release, position) by {
      hide *;
      reveal Spec.SortCertificate();
    }
  }

  ghost opaque predicate Text(
    events: seq<Spec.Event>,
    quoted: Bytes,
    output: Bytes,
    errors: Bytes,
    exit: int,
    offsets: seq<nat>,
    errOffsets: seq<nat>
  ) {
    |offsets| == |events| + 1 && |errOffsets| == |events| + 1 && offsets[0] == 0 && errOffsets[0] == 0 &&
    offsets[|events|] == |output| && errOffsets[|events|] == |errors| &&
    (forall i: nat | i < |events| ::
       Spec.EventText(
         events[i], quoted, output, errors,
         offsets[i], offsets[i + 1], errOffsets[i], errOffsets[i + 1]
       )) &&
    exit == (if exists i: nat :: i < |events| && events[i].Cut? then 1 else 0)
  }

  lemma EmptyText(quoted: Bytes)
    ensures Text([], quoted, [], [], 0, [0], [0])
  {
    reveal Text();
  }

  lemma AppendText(
    events: seq<Spec.Event>,
    quoted: Bytes,
    output: Bytes,
    errors: Bytes,
    exit: int,
    offsets: seq<nat>,
    errOffsets: seq<nat>,
    event: Spec.Event
  )
    requires Text(events, quoted, output, errors, exit, offsets, errOffsets)
    ensures var nextOut := output + (if event.Emit? then event.vertex + "\n" else []);
            var nextErr := errors + (if event.Cut? then Spec.LoopText(quoted) + Spec.CycleLines(event.cycle) else []);
            Text(events + [event], quoted, nextOut, nextErr, (if event.Cut? then 1 else exit),
                 offsets + [|nextOut|], errOffsets + [|nextErr|])
  {
    reveal Text();
    var nextOut := output + (if event.Emit? then event.vertex + "\n" else []);
    var nextErr := errors + (if event.Cut? then Spec.LoopText(quoted) + Spec.CycleLines(event.cycle) else []);
    forall i: nat | i < |events|
      ensures Spec.EventText(events[i], quoted, nextOut, nextErr, offsets[i], offsets[i + 1], errOffsets[i], errOffsets[i + 1])
    {
      assert Spec.EventText(events[i], quoted, output, errors, offsets[i], offsets[i + 1], errOffsets[i], errOffsets[i + 1]);
      assert nextOut[offsets[i]..offsets[i + 1]] == output[offsets[i]..offsets[i + 1]];
      assert nextErr[errOffsets[i]..errOffsets[i + 1]] == errors[errOffsets[i]..errOffsets[i + 1]];
    }
    var nextEvents := events + [event];
    if event.Cut? { assert nextEvents[|events|].Cut?; }
    else if exists i: nat :: i < |nextEvents| && nextEvents[i].Cut? {
      var i: nat :| i < |nextEvents| && nextEvents[i].Cut?;
      assert i < |events| && events[i].Cut?;
    }
    if exists i: nat :: i < |events| && events[i].Cut? {
      var i: nat :| i < |events| && events[i].Cut?;
      assert nextEvents[i].Cut?;
    }
  }

  lemma Finish(
    graph: Graph,
    run: Run,
    quoted: Bytes,
    output: Bytes,
    errors: Bytes,
    exit: int,
    offsets: seq<nat>,
    errOffsets: seq<nat>
  )
    requires Schedule(graph, run) && |run.states| == |run.events| + 1 && run.states[|run.events|].pending == {}
    requires forall source | source in graph ::
               forall target | target in graph[source] ::
                 target in graph
    requires Text(run.events, quoted, output, errors, exit, offsets, errOffsets)
    ensures Spec.GraphResult(graph, quoted, output, errors, exit)
  {
    reveal Text();
    var release, position := Certificate(graph, run);
    var resultData := Spec.ResultWitness(run.events, run.ranks, run.removed, release, position, offsets, errOffsets);
    assert Spec.ResultFields(graph, quoted, output, errors, exit, resultData);
    reveal Spec.GraphResult();
  }
}
