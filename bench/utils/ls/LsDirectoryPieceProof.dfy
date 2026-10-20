include "LsSpec.dfy"

module LsDirectoryPieceProof {
  import Spec = LsSpec
  import Native = LsNativeSpec

  lemma Append(
    steps: seq<Spec.DirectoryReadStep>, raw: seq<Spec.EntryObservation>,
    positions: seq<nat>, pieces: seq<seq<Native.Call>>,
    step: Spec.DirectoryReadStep, nextRaw: seq<Spec.EntryObservation>,
    nextPositions: seq<nat>, piece: seq<Native.Call>
  )
    requires |pieces| == |steps|
    requires |positions| == |raw|
    requires forall j: nat | j < |positions| :: positions[j] < |steps|
    requires forall i: nat | i < |steps| ::
      (if exists j: nat :: j < |positions| && positions[j] == i then
         exists j: nat :: j < |positions| && j < |raw| && positions[j] == i &&
           pieces[i] == steps[i].nativeCalls + raw[j].nativeCalls
       else pieces[i] == steps[i].nativeCalls)
    requires (nextRaw == raw && nextPositions == positions && piece == step.nativeCalls) ||
      (|nextRaw| == |raw| + 1 && nextRaw[..|raw|] == raw &&
       nextPositions == positions + [|steps|] &&
       piece == step.nativeCalls + nextRaw[|raw|].nativeCalls)
    ensures forall i: nat | i < |steps + [step]| ::
      (if exists j: nat :: j < |nextPositions| && nextPositions[j] == i then
         exists j: nat :: j < |nextPositions| && j < |nextRaw| && nextPositions[j] == i &&
           (pieces + [piece])[i] == (steps + [step])[i].nativeCalls + nextRaw[j].nativeCalls
       else (pieces + [piece])[i] == (steps + [step])[i].nativeCalls)
  {
    hide *;
    if |nextRaw| == |raw| {
      assert nextRaw == raw && nextPositions == positions && piece == step.nativeCalls;
    } else {
      assert |nextRaw| == |raw| + 1 && nextRaw[..|raw|] == raw &&
        nextPositions == positions + [|steps|] &&
        piece == step.nativeCalls + nextRaw[|raw|].nativeCalls;
    }
    forall j: nat | j < |positions|
      ensures j < |nextPositions| && j < |nextRaw|
      ensures nextPositions[j] == positions[j] && nextRaw[j] == raw[j]
    {
    }
    forall i: nat | i < |steps + [step]|
      ensures
        (if exists j: nat :: j < |nextPositions| && nextPositions[j] == i then
           exists j: nat :: j < |nextPositions| && j < |nextRaw| && nextPositions[j] == i &&
             (pieces + [piece])[i] == (steps + [step])[i].nativeCalls + nextRaw[j].nativeCalls
         else (pieces + [piece])[i] == (steps + [step])[i].nativeCalls)
    {
      if i < |steps| {
        assert (pieces + [piece])[i] == pieces[i] && (steps + [step])[i] == steps[i];
        if exists j: nat :: j < |positions| && positions[j] == i {
          var j: nat :| j < |positions| && j < |raw| && positions[j] == i &&
            pieces[i] == steps[i].nativeCalls + raw[j].nativeCalls;
          assert j < |nextPositions| && j < |nextRaw| && nextPositions[j] == i;
          assert (pieces + [piece])[i] ==
            (steps + [step])[i].nativeCalls + nextRaw[j].nativeCalls;
        } else {
          assert !(exists j: nat :: j < |nextPositions| && nextPositions[j] == i) by {
            forall j: nat | j < |nextPositions|
              ensures nextPositions[j] != i
            {
              if j < |positions| {
                assert positions[j] != i;
              } else {
                assert nextPositions == positions + [|steps|] && j == |positions|;
                assert nextPositions[j] == |steps|;
              }
            }
          }
        }
      } else {
        assert i == |steps|;
        if |nextRaw| == |raw| {
          assert !(exists j: nat :: j < |nextPositions| && nextPositions[j] == i);
        } else {
          var j := |raw|;
          assert j == |positions| && j < |nextPositions| && j < |nextRaw|;
          assert nextPositions[j] == i && (pieces + [piece])[i] == piece &&
            (steps + [step])[i] == step;
          assert (pieces + [piece])[i] ==
            (steps + [step])[i].nativeCalls + nextRaw[j].nativeCalls;
        }
      }
    }
  }
}
