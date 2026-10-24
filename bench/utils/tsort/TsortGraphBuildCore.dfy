include "../../core/World.dfy"
include "TsortGraphBuildSpec.dfy"
include "TsortGraphBuildProof.dfy"
include "TsortSpec.dfy"

module TsortGraphBuildCore {
  import BenchWorld
  import Spec = TsortGraphBuildSpec
  import Proof = TsortGraphBuildProof
  import TokenSpec = TsortSpec

  method Tokenize(data: BenchWorld.Bytes) returns (tokens: seq<BenchWorld.Bytes>)
    ensures exists starts: seq<nat>, ends: seq<nat> :: TokenSpec.Tokenization(data, tokens, starts, ends)
  {
    tokens := [];
    ghost var starts: seq<nat> := [];
    ghost var ends: seq<nat> := [];
    var i := 0;
    while i < |data|
      invariant 0 <= i <= |data|
      invariant TokenSpec.Tokenization(data[..i], tokens, starts, ends)
      invariant i < |data| && !TokenSpec.IsSpace(data[i]) ==> forall k: nat | k < |ends| :: ends[k] < i
      decreases |data| - i
    {
      if TokenSpec.IsSpace(data[i]) {
        Proof.Space(data, tokens, starts, ends, i);
        i := i + 1;
      } else {
        var begin := i;
        var stop := i;
        while i < |data| && !TokenSpec.IsSpace(data[i])
          invariant TokenSpec.Tokenization(data[..begin], tokens, starts, ends)
          invariant forall k: nat | k < |ends| :: ends[k] < begin
          invariant begin <= stop <= i <= |data|
          invariant forall j: nat | begin <= j < i :: !TokenSpec.IsSpace(data[j])
          invariant forall j: nat | begin <= j < stop :: data[j] != '\0'
          invariant stop == i || data[stop] == '\0'
          decreases |data| - i
        {
          if stop == i && data[i] != '\0' { stop := stop + 1; }
          i := i + 1;
        }
        Proof.AppendToken(data, tokens, starts, ends, begin, stop, i);
        tokens := tokens + [data[begin..stop]];
        starts := starts + [begin];
        ends := ends + [i];
      }
    }
    assert data[..i] == data;
    assert TokenSpec.Tokenization(data, tokens, starts, ends);
  }

  method {:isolate_assertions} BuildGraph(tokens: seq<BenchWorld.Bytes>)
    returns (
      vertices: seq<BenchWorld.Bytes>,
      graph: map<BenchWorld.Bytes, seq<BenchWorld.Bytes>>
    )
    requires |tokens| % 2 == 0
    ensures graph.Keys == (set token | token in tokens)
    ensures (set vertex | vertex in vertices) == graph.Keys
    ensures forall i: nat, j: nat | i < j < |vertices| :: vertices[i] != vertices[j]
    ensures forall source | source in graph.Keys ::
              exists positions: seq<nat> :: Spec.OutgoingEdges(tokens, source, graph[source], positions)
  {
    vertices := [];
    graph := map[];
    var i := 0;
    while i < |tokens|
      invariant 0 <= i <= |tokens|
      invariant graph.Keys == (set token | token in tokens[..i])
      invariant (set vertex | vertex in vertices) == graph.Keys
      invariant forall j: nat, k: nat | j < k < |vertices| :: vertices[j] != vertices[k]
      invariant forall vertex | vertex in graph.Keys :: graph[vertex] == []
      decreases |tokens| - i
    {
      assert tokens[..i + 1] == tokens[..i] + [tokens[i]];
      if tokens[i] !in graph {
        vertices := vertices + [tokens[i]];
        graph := graph[tokens[i] := []];
      }
      i := i + 1;
    }
    ghost var positions: map<BenchWorld.Bytes, seq<nat>> := map v | v in graph.Keys :: [];
    i := 0;
    while i < |tokens|
      invariant 0 <= i <= |tokens| && i % 2 == 0
      invariant graph.Keys == (set token | token in tokens)
      invariant (set vertex | vertex in vertices) == graph.Keys
      invariant forall j: nat, k: nat | j < k < |vertices| :: vertices[j] != vertices[k]
      invariant positions.Keys == graph.Keys
      invariant forall vertex | vertex in graph.Keys ::
                  Spec.OutgoingEdges(tokens[..i], vertex, graph[vertex], positions[vertex])
      decreases |tokens| - i
    {
      assert (i + 2) % 2 == 0 by { hide *; }
      var source, target := tokens[i], tokens[i + 1];
      forall vertex | vertex in graph.Keys
        ensures Spec.OutgoingEdges(
                  tokens[..i + 2], vertex,
                  if source == vertex && target != vertex then [target] + graph[vertex] else graph[vertex],
                  if source == vertex && target != vertex then [i / 2] + positions[vertex] else positions[vertex]
                )
      {
        Proof.ExtendOutgoing(tokens, i, vertex, graph[vertex], positions[vertex]);
      }
      if source != target {
        graph := graph[source := [target] + graph[source]];
        positions := positions[source := [i / 2] + positions[source]];
      }
      i := i + 2;
    }
    Proof.GraphEdgesWitness(tokens, graph, positions);
  }
}
