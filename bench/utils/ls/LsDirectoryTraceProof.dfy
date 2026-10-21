include "LsSpec.dfy"

module LsDirectoryTraceProof {
  import W = BenchWorld
  import Spec = LsSpec
  import Schema = LsSchema
  import Native = LsNativeSpec

  lemma NativeCallFragmentsFromFields(pieces: seq<seq<Native.Call>>,
                                      combined: seq<Native.Call>, cuts: seq<nat>)
    requires |cuts| == |pieces|+1 && cuts[0] == 0 && cuts[|pieces|] == |combined|
    requires forall i: nat {:trigger pieces[i]} {:trigger cuts[i]} | i < |pieces| ::
               cuts[i] <= cuts[i+1] <= |combined| && combined[cuts[i]..cuts[i+1]] == pieces[i]
    ensures Spec.NativeCallFragments(pieces,combined,cuts)
  {
    reveal Spec.NativeCallFragments();
  }

  lemma EmptyNativeCallFragments()
    ensures Spec.NativeCallFragments([],[],[0])
  {
    hide *;
    reveal Spec.NativeCallFragments();
  }

  lemma AppendNativeCallFragments(pieces: seq<seq<Native.Call>>,
                                  combined: seq<Native.Call>, cuts: seq<nat>, piece: seq<Native.Call>)
    requires Spec.NativeCallFragments(pieces,combined,cuts)
    ensures Spec.NativeCallFragments(pieces+[piece],combined+piece,cuts+[|combined+piece|])
  {
    reveal Spec.NativeCallFragments();
    var allPieces: seq<seq<Native.Call>> := pieces+[piece];
    var allCalls: seq<Native.Call> := combined+piece;
    var allCuts: seq<nat> := cuts+[|allCalls|];
    forall i: nat {:trigger allPieces[i]} {:trigger allCuts[i]} | i < |allPieces|
      ensures allCuts[i] <= allCuts[i+1] <= |allCalls| &&
              allCalls[allCuts[i]..allCuts[i+1]] == allPieces[i]
    {
      if i < |pieces| {
        assert pieces[i] == allPieces[i];
        assert cuts[i] <= cuts[i+1] <= |combined|;
        assert allCalls[..|combined|] == combined;
      } else {
        assert i == |pieces|;
        assert allCuts[i] == |combined|;
        assert allCalls[|combined|..] == piece;
      }
    }
    assert |allCuts| == |allPieces|+1;
    assert allCuts[0] == 0;
    assert allCuts[|allPieces|] == |allCalls|;
    assert forall i: nat {:trigger allPieces[i]} {:trigger allCuts[i]} | i < |allPieces| ::
        allCuts[i] <= allCuts[i+1] <= |allCalls| &&
        allCalls[allCuts[i]..allCuts[i+1]] == allPieces[i];
    NativeCallFragmentsFromFields(allPieces,allCalls,allCuts);
  }

  lemma AppendReadPrefix(cmd: Schema.LsCmd, fs: W.FileSystem,
                         openedCapabilities: map<int,W.DirectoryCapabilityState>, handle: int,
                         steps: seq<Spec.DirectoryReadStep>, step: Spec.DirectoryReadStep)
    requires Spec.DirectoryReadPrefix(cmd,fs,openedCapabilities,handle,steps,step.before)
    requires step.more && step.err == 0
    requires Spec.DirectoryReadStepFields(cmd,fs,handle,step)
    ensures Spec.DirectoryReadPrefix(cmd,fs,openedCapabilities,handle,steps+[step],step.after)
  {
    hide *;
    reveal Spec.DirectoryReadPrefix();
    forall i: nat | i < |steps+[step]|
      ensures (steps+[step])[i].more && (steps+[step])[i].err == 0 &&
              Spec.DirectoryReadStepFields(cmd,fs,handle,(steps+[step])[i]) &&
              (i > 0 ==> (steps+[step])[i-1].after == (steps+[step])[i].before)
    {
      if i < |steps| {
        assert (steps+[step])[i] == steps[i];
      } else {
        assert i == |steps|;
      }
    }
  }

  lemma AppendReadEvidence(cmd: Schema.LsCmd,
                           steps: seq<Spec.DirectoryReadStep>, step: Spec.DirectoryReadStep,
                           raw: seq<Spec.EntryObservation>, positions: seq<nat>,
                           nextRaw: seq<Spec.EntryObservation>, nextPositions: seq<nat>)
    requires Spec.DirectoryReadEvidence(cmd,steps,raw,positions)
    requires (nextRaw == raw && nextPositions == positions) ||
             (|nextRaw| == |raw|+1 && nextRaw[..|raw|] == raw &&
              nextPositions == positions+[|steps|] &&
              nextRaw[|raw|].displayName == step.name &&
              nextRaw[|raw|].directoryRead == step.nativeCalls &&
              (nextRaw[|raw|].entryKind == step.kind ||
               ((step.name == "." || step.name == "..") &&
                nextRaw[|raw|].entryKind == W.DirectoryDirentKind)))
    requires Spec.VisibleNameSpec(cmd,step.name) ==>
               exists j: nat :: j < |nextRaw| && nextRaw[j].displayName == step.name
    ensures Spec.DirectoryReadEvidence(cmd,steps+[step],nextRaw,nextPositions)
  {
    hide *;
    reveal Spec.DirectoryReadEvidence();
    forall i: nat | i < |nextRaw|
      ensures nextPositions[i] < |steps+[step]| &&
              nextRaw[i].displayName == (steps+[step])[nextPositions[i]].name &&
              nextRaw[i].directoryRead == (steps+[step])[nextPositions[i]].nativeCalls &&
              (nextRaw[i].entryKind == (steps+[step])[nextPositions[i]].kind ||
               ((nextRaw[i].displayName == "." || nextRaw[i].displayName == "..") &&
                nextRaw[i].entryKind == W.DirectoryDirentKind)) &&
              (i > 0 ==> nextPositions[i-1] < nextPositions[i])
    {
      if i < |raw| {
        assert nextRaw[i] == raw[i];
        assert nextPositions[i] == positions[i];
      } else {
        assert i == |raw|;
        assert nextPositions[i] == |steps|;
      }
    }
    forall i: nat | i < |steps+[step]| && Spec.VisibleNameSpec(cmd,(steps+[step])[i].name)
      ensures exists j: nat :: j < |nextRaw| && nextRaw[j].displayName == (steps+[step])[i].name
    {
      if i < |steps| {
        var j: nat :| j < |raw| && raw[j].displayName == steps[i].name;
        assert nextRaw[j] == raw[j];
      } else {
        assert i == |steps|;
      }
    }
  }
}
