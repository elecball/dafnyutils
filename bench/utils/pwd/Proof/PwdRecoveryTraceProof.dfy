include "../Spec/PwdRecoverySpec.dfy"

module PwdRecoveryTraceProof {
  import BenchWorld
  import C = IOContract
  import Spec = PwdRecoverySpec

  lemma SingleObservation(inputs: Spec.RuntimeInputs, call: Spec.RuntimeObservation)
    requires Spec.RuntimeObservationFields(inputs,call)
    ensures Spec.RuntimeTraceFields(inputs,call.before,call.after,[call])
  {
    hide *;
    reveal Spec.RuntimeTraceFields();
  }

  lemma ConcatTraces(inputs: Spec.RuntimeInputs, before: Spec.RuntimeState,
                     middle: Spec.RuntimeState, after: Spec.RuntimeState,
                     left: seq<Spec.RuntimeObservation>, right: seq<Spec.RuntimeObservation>)
    requires Spec.RuntimeTraceFields(inputs,before,middle,left)
    requires Spec.RuntimeTraceFields(inputs,middle,after,right)
    ensures Spec.RuntimeTraceFields(inputs,before,after,left+right)
  {
    hide *;
    reveal Spec.RuntimeTraceFields();
    forall i: nat | i < |left+right|
      ensures Spec.RuntimeObservationFields(inputs,(left+right)[i])
    {
      if i < |left| {
        assert (left+right)[i] == left[i];
      } else {
        assert (left+right)[i] == right[i-|left|];
      }
    }
    forall i: nat | i+1 < |left+right|
      ensures (left+right)[i].after == (left+right)[i+1].before
    {
      if i+1 < |left| {
      } else if i < |left| {
        assert i+1 == |left| && |right| > 0;
      } else {
        assert i-|left|+1 < |right|;
      }
    }
  }

  lemma AppendEntry(inputs: Spec.RuntimeInputs, before: Spec.RuntimeState,
                    middle: Spec.RuntimeState, after: Spec.RuntimeState,
                    child: BenchWorld.FileStatus, parent: BenchWorld.FileStatus, handle: int,
                    prefix: Spec.SearchWitness, entry: Spec.EntryObservation,
                    calls: seq<Spec.RuntimeObservation>)
    requires Spec.EntryWitnessFields(inputs,before,middle,child,parent,handle,prefix)
    requires Spec.RuntimeTraceFields(inputs,middle,after,calls)
    requires Spec.EntryCallBindings(child,parent,handle,entry,calls)
    ensures Spec.EntryWitnessFields(inputs,before,after,child,parent,handle,
                                    Spec.SearchWitness(prefix.entries+[entry],prefix.calls+calls,
                                                       prefix.boundaries+[|prefix.calls+calls|]))
  {
    hide *;
    reveal Spec.EntryWitnessFields(), Spec.EntryPartitionAt();
    ConcatTraces(inputs,before,middle,after,prefix.calls,calls);
    var entries := prefix.entries+[entry];
    var allCalls := prefix.calls+calls;
    var boundaries := prefix.boundaries+[|allCalls|];
    var combined := Spec.SearchWitness(entries,allCalls,boundaries);
    forall i: nat | i < |entries|
      ensures Spec.EntryPartitionAt(child,parent,handle,combined,i)
    {
      if i < |prefix.entries| {
        assert Spec.EntryPartitionAt(child,parent,handle,prefix,i);
        assert boundaries[i+1] <= |prefix.calls|;
        assert allCalls[boundaries[i]..boundaries[i+1]] ==
               prefix.calls[prefix.boundaries[i]..prefix.boundaries[i+1]];
      } else {
        assert i == |prefix.entries|;
        assert boundaries[i] == |prefix.calls|;
        assert boundaries[i+1] == |allCalls|;
        assert allCalls[boundaries[i]..boundaries[i+1]] == calls;
      }
      assert Spec.EntryPartitionAt(child,parent,handle,combined,i);
    }
  }

  lemma FinishEntrySearch(inputs: Spec.RuntimeInputs, before: Spec.RuntimeState,
                          after: Spec.RuntimeState, child: BenchWorld.FileStatus,
                          parent: BenchWorld.FileStatus, handle: int, name: string, readErr: int,
                          evidence: Spec.SearchWitness)
    requires Spec.EntryWitnessFields(inputs,before,after,child,parent,handle,evidence)
    requires |evidence.entries| > 0
    requires forall i: nat | i+1 < |evidence.entries| ::
               evidence.entries[i].read.Ok? && evidence.entries[i].read.v.DirectoryItem? &&
               !Spec.EntryMatchFields(child,parent,evidence.entries[i])
    requires var last := evidence.entries[|evidence.entries|-1];
             if last.read.Err? then name == "" && readErr == C.ResultErrno(last.read)
             else if last.read.v.DirectoryEnd? then name == "" && readErr == 0
             else Spec.EntryMatchFields(child,parent,last) && name == last.read.v.name && readErr == 0
    ensures Spec.SearchWitnessFields(inputs,before,after,child,parent,handle,name,readErr,evidence)
  {
    hide *;
    reveal Spec.SearchWitnessFields(), Spec.EntryWitnessFields(), Spec.EntryPartitionAt(), Spec.EntrySearchFields();
    reveal Spec.EntryCallBindings();
    forall i: nat | i < |evidence.entries|
      ensures Spec.EntryObservationFields(child,parent,evidence.entries[i])
    {
      assert Spec.EntryPartitionAt(child,parent,handle,evidence,i);
    }
  }
}
