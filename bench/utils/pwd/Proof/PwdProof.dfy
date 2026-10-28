include "../Spec/PwdPhysicalSpec.dfy"
include "PwdRecoveryTraceProof.dfy"

module PwdProof {
  import W = BenchWorld
  import Recovery = PwdRecoverySpec
  import Parent = PwdRecoveryParentSpec
  import Spec = PwdPhysicalSpec
  import Trace = PwdRecoveryTraceProof

  lemma EmptySteps(inputs: Recovery.RuntimeInputs, before: Recovery.RuntimeState,
                   root: W.FileStatus, initial: W.FileStatus)
    requires root.kind == initial.kind == W.DirectoryKind
    ensures Spec.StepsWitnessFields(inputs,before,before,root,initial,[],[],[0])
  {
    hide *;
    reveal Spec.StepsWitnessFields(), Recovery.RuntimeTraceFields();
  }

  lemma AppendStep(inputs: Recovery.RuntimeInputs, before: Recovery.RuntimeState,
                   middle: Recovery.RuntimeState, after: Recovery.RuntimeState,
                   root: W.FileStatus, initial: W.FileStatus, steps: seq<Spec.ParentStep>,
                   calls: seq<Recovery.RuntimeObservation>, boundaries: seq<nat>, step: Spec.ParentStep)
    requires Spec.StepsWitnessFields(inputs,before,middle,root,initial,steps,calls,boundaries)
    requires forall i: nat | i < |steps| :: |steps[i].failure| == 0
    requires var child := if |steps| == 0 then initial else steps[|steps|-1].parent;
             child.hostKey != root.hostKey &&
             Parent.ParentAttemptFields(inputs,middle,after,child,|steps|+1,
                                        step.parent,step.name,step.failure,step.evidence)
    ensures Spec.StepsWitnessFields(inputs,before,after,root,initial,steps+[step],
                                    calls+step.evidence.calls,boundaries+[|calls+step.evidence.calls|])
  {
    hide *;
    reveal Spec.StepsWitnessFields(), Spec.StepPartitionAt();
    reveal Parent.ParentAttemptFields();
    Trace.ConcatTraces(inputs,before,middle,after,calls,step.evidence.calls);
    var allSteps := steps+[step];
    var allCalls := calls+step.evidence.calls;
    var cuts := boundaries+[|allCalls|];
    assert |step.evidence.calls| > 0;
    reveal Recovery.RuntimeTraceFields();
    forall i: nat | i < |allSteps|
      ensures Spec.StepPartitionAt(inputs,root,initial,allSteps,allCalls,cuts,i)
    {
      if i < |steps| {
        assert Spec.StepPartitionAt(inputs,root,initial,steps,calls,boundaries,i);
        assert cuts[i+1] <= |calls|;
        assert allCalls[cuts[i]..cuts[i+1]] == calls[boundaries[i]..boundaries[i+1]];
      } else {
        assert i == |steps| && cuts[i] == |calls| && cuts[i+1] == |allCalls|;
        assert allCalls[cuts[i]..cuts[i+1]] == step.evidence.calls;
        assert allCalls[cuts[i]].before == middle;
        assert allCalls[cuts[i+1]-1].after == after;
      }
      assert Spec.StepPartitionAt(inputs,root,initial,allSteps,allCalls,cuts,i);
    }
  }

  lemma PathPartitionSnoc(names: seq<string>, directory: string,
                          boundaries: seq<nat>, name: string)
    requires Spec.PathPartitionFields(names,directory,boundaries)
    requires W.InodeChildNameValid(name)
    ensures Spec.PathPartitionFields(names+[name],"/"+name+directory,
                                     [0]+seq(|boundaries|,i=>if 0 <= i < |boundaries| then |"/"+name|+boundaries[i] else 0))
  {
    hide *;
    reveal Spec.PathPartitionFields(), Spec.PathPartitionAt();
    var prefix := "/"+name;
    var allNames := names+[name];
    var allText := prefix+directory;
    var cuts := [0]+seq(|boundaries|,i=>if 0 <= i < |boundaries| then |prefix|+boundaries[i] else 0);
    forall i: nat | i < |allNames|
      ensures Spec.PathPartitionAt(allNames,allText,cuts,i)
    {
      if i == 0 {
        assert cuts[i] == 0 && cuts[i+1] == |prefix|;
      } else {
        assert i-1 < |names|;
        assert Spec.PathPartitionAt(names,directory,boundaries,i-1);
        assert cuts[i] == |prefix|+boundaries[i-1];
        assert cuts[i+1] == |prefix|+boundaries[i];
        assert allText[cuts[i]..cuts[i+1]] == directory[boundaries[i-1]..boundaries[i]];
      }
    }
  }

  lemma PartitionIsAbsolute(names: seq<string>, directory: string, boundaries: seq<nat>)
    requires |names| > 0
    requires Spec.PathPartitionFields(names,directory,boundaries)
    ensures W.IsAbsolutePath(directory)
  {
    hide *;
    reveal Spec.PathPartitionFields(), Spec.PathPartitionAt(), W.IsAbsolutePath();
    assert Spec.PathPartitionAt(names,directory,boundaries,0);
    assert directory[boundaries[0]..boundaries[1]] == "/"+names[|names|-1];
    assert boundaries[0] == 0 && boundaries[1] > 0;
    assert directory[0] == '/';
  }

  lemma SelectionWitness(inputs: Recovery.RuntimeInputs, before: Recovery.RuntimeState,
                         after: Recovery.RuntimeState, outcome: Recovery.DirectoryOutcome,
                         evidence: Spec.PhysicalEvidence)
    requires Spec.PhysicalSelectionFields(inputs,before,after,outcome,evidence)
    ensures exists observed: Spec.PhysicalEvidence ::
              Spec.PhysicalSelectionFields(inputs,before,after,outcome,observed)
  {
  }
}
