include "TsortGraphBuildSpec.dfy"
include "TsortSpec.dfy"

module TsortGraphBuildProof {
  import BenchWorld
  import Spec = TsortGraphBuildSpec
  import TokenSpec = TsortSpec

  lemma Fields(tokens: seq<BenchWorld.Bytes>, graph: map<BenchWorld.Bytes, seq<BenchWorld.Bytes>>)
    requires graph.Keys == (set token | token in tokens)
    requires forall source | source in graph ::
               exists positions: seq<nat> :: Spec.OutgoingEdges(tokens, source, graph[source], positions)
    ensures forall source | source in graph ::
              forall target | target in graph[source] ::
                target in graph
    ensures forall source | source in graph :: source !in graph[source]
  {
    forall source | source in graph
      ensures forall target | target in graph[source] :: target in graph && target != source
    {
      var positions: seq<nat> :| Spec.OutgoingEdges(tokens, source, graph[source], positions);
      forall target | target in graph[source]
        ensures target in graph && target != source
      {
        var j: nat :| j < |graph[source]| && graph[source][j] == target;
        assert target == tokens[2 * positions[j] + 1];
        assert target in tokens;
      }
    }
  }

  lemma {:isolate_assertions} ExtendOutgoing(
    tokens: seq<BenchWorld.Bytes>,
    count: nat,
    source: BenchWorld.Bytes,
    successors: seq<BenchWorld.Bytes>,
    positions: seq<nat>
  )
    requires count % 2 == 0 && count + 2 <= |tokens|
    requires Spec.OutgoingEdges(tokens[..count], source, successors, positions)
    ensures Spec.OutgoingEdges(
              tokens[..count + 2], source,
              if tokens[count] == source && tokens[count + 1] != source
              then [tokens[count + 1]] + successors else successors,
              if tokens[count] == source && tokens[count + 1] != source
              then [count / 2] + positions else positions
            )
  {
    var append := tokens[count] == source && tokens[count + 1] != source;
    var next := tokens[..count + 2];
    var nextSuccessors := if append then [tokens[count + 1]] + successors else successors;
    var nextPositions := if append then [count / 2] + positions else positions;
    assert 2 * (count / 2) == count;
    assert (count + 2) / 2 == count / 2 + 1;
    forall j: nat | j < |nextPositions|
      ensures nextPositions[j] < |next| / 2 && next[2 * nextPositions[j]] == source &&
              next[2 * nextPositions[j] + 1] != source &&
              nextSuccessors[j] == next[2 * nextPositions[j] + 1]
    {
      if append && j == 0 {
        assert nextPositions[j] == count / 2;
      } else {
        var previous := if append then j - 1 else j;
        assert 0 <= previous < |positions|;
        assert nextPositions[j] == positions[previous];
        assert nextSuccessors[j] == successors[previous];
        assert positions[previous] < count / 2;
        assert next[2 * positions[previous]] == (tokens[..count])[2 * positions[previous]];
        assert next[2 * positions[previous] + 1] == (tokens[..count])[2 * positions[previous] + 1];
      }
    }
    forall j: nat | 0 < j < |nextPositions|
      ensures nextPositions[j - 1] > nextPositions[j]
    {
      if append && j == 1 {
        assert positions[0] < count / 2;
      }
    }
    forall p: nat | p < |next| / 2 && next[2 * p] == source && next[2 * p + 1] != source
      ensures p in nextPositions
    {
      if p < count / 2 {
        assert (tokens[..count])[2 * p] == next[2 * p];
        assert (tokens[..count])[2 * p + 1] == next[2 * p + 1];
        assert p in positions;
      } else {
        assert p == count / 2 && append;
      }
    }
    assert Spec.OutgoingEdges(next, source, nextSuccessors, nextPositions) by {
      hide *;
      reveal Spec.OutgoingEdges();
    }
  }

  lemma GraphEdgesWitness(
    tokens: seq<BenchWorld.Bytes>,
    graph: map<BenchWorld.Bytes, seq<BenchWorld.Bytes>>,
    positions: map<BenchWorld.Bytes, seq<nat>>
  )
    requires positions.Keys == graph.Keys
    requires forall source | source in graph.Keys ::
               Spec.OutgoingEdges(tokens, source, graph[source], positions[source])
    ensures forall source | source in graph.Keys ::
              exists ps: seq<nat> :: Spec.OutgoingEdges(tokens, source, graph[source], ps)
  {
    forall source | source in graph.Keys
      ensures exists ps: seq<nat> :: Spec.OutgoingEdges(tokens, source, graph[source], ps)
    {
      assert Spec.OutgoingEdges(tokens, source, graph[source], positions[source]);
    }
  }

  lemma Space(data: BenchWorld.Bytes, tokens: seq<BenchWorld.Bytes>, starts: seq<nat>, ends: seq<nat>, i: nat)
    requires i < |data| && TokenSpec.IsSpace(data[i])
    requires TokenSpec.Tokenization(data[..i], tokens, starts, ends)
    ensures TokenSpec.Tokenization(data[..i + 1], tokens, starts, ends)
  {
    forall k: nat | k < |tokens|
      ensures TokenSpec.TokenName(data[..i + 1][starts[k]..ends[k]], tokens[k])
    {
      assert data[..i + 1][starts[k]..ends[k]] == data[..i][starts[k]..ends[k]];
    }
  }

  lemma {:isolate_assertions} AppendToken(
    data: BenchWorld.Bytes,
    tokens: seq<BenchWorld.Bytes>,
    starts: seq<nat>,
    ends: seq<nat>,
    begin: nat,
    stop: nat,
    end: nat
  )
    requires begin < end <= |data| && begin <= stop <= end
    requires TokenSpec.Tokenization(data[..begin], tokens, starts, ends)
    requires forall k: nat | k < |ends| :: ends[k] < begin
    requires forall j: nat | begin <= j < end :: !TokenSpec.IsSpace(data[j])
    requires forall j: nat | begin <= j < stop :: data[j] != '\0'
    requires stop == end || data[stop] == '\0'
    ensures TokenSpec.Tokenization(data[..end], tokens + [data[begin..stop]], starts + [begin], ends + [end])
  {
    var nextTokens := tokens + [data[begin..stop]];
    var nextStarts := starts + [begin];
    var nextEnds := ends + [end];
    var raw := data[begin..end];
    assert raw[..stop - begin] == data[begin..stop];
    assert TokenSpec.TokenName(raw, data[begin..stop]) by { reveal TokenSpec.TokenName(); }
    forall k: nat | k < |nextTokens|
      ensures TokenSpec.TokenName(data[..end][nextStarts[k]..nextEnds[k]], nextTokens[k])
    {
      if k < |tokens| {
        assert data[..end][nextStarts[k]..nextEnds[k]] == data[..begin][starts[k]..ends[k]];
      } else {
        assert k == |tokens|;
        assert data[..end][nextStarts[k]..nextEnds[k]] == raw;
        assert nextTokens[k] == data[begin..stop];
      }
    }
    forall j: nat | j < end
      ensures !TokenSpec.IsSpace(data[j]) <==>
              exists k: nat :: k < |nextTokens| && nextStarts[k] <= j < nextEnds[k]
    {
      if j < begin {
        if !TokenSpec.IsSpace(data[j]) {
          var k: nat :| k < |tokens| && starts[k] <= j < ends[k];
          assert nextStarts[k] <= j < nextEnds[k];
        } else {
          forall k: nat | k < |nextTokens| && nextStarts[k] <= j < nextEnds[k]
            ensures false
          {
            if k < |tokens| { assert !TokenSpec.IsSpace(data[..begin][j]); }
          }
        }
      } else if begin <= j {
        assert nextStarts[|tokens|] <= j < nextEnds[|tokens|];
      }
    }
  }
}
