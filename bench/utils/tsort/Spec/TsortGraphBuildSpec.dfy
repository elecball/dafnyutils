include "../../../core/World.dfy"

module TsortGraphBuildSpec {
  import BenchWorld

  ghost predicate OutgoingEdges(
    tokens: seq<BenchWorld.Bytes>,
    source: BenchWorld.Bytes,
    successors: seq<BenchWorld.Bytes>,
    positions: seq<nat>
  )
  {
    |successors| == |positions| &&
    (forall j: nat | j < |positions| ::
       positions[j] < |tokens| / 2 && tokens[2 * positions[j]] == source &&
       tokens[2 * positions[j] + 1] != source &&
       successors[j] == tokens[2 * positions[j] + 1]) &&
    (forall j: nat | 0 < j < |positions| :: positions[j - 1] > positions[j]) &&
    (forall p: nat | p < |tokens| / 2 &&
                     tokens[2 * p] == source && tokens[2 * p + 1] != source :: p in positions)
  }
}
