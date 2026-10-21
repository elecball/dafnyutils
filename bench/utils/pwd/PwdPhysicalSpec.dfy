include "PwdRecoverySpec.dfy"
include "PwdRecoveryParentSpec.dfy"

module PwdPhysicalSpec {
  import W = BenchWorld
  import C = IOContract
  import Errno = Errnos
  import Recovery = PwdRecoverySpec
  import Parent = PwdRecoveryParentSpec

  datatype ParentStep = ParentStep(ghost parent: W.FileStatus, ghost name: string,
                                   ghost failure: seq<Recovery.RecoveryFailure>, ghost evidence: Parent.ParentEvidence)

  datatype PhysicalEvidence = PhysicalEvidence(
    ghost direct: W.IOResult<string>, ghost root: seq<W.IOResult<W.FileStatus>>,
    ghost current: seq<W.IOResult<W.FileStatus>>, ghost steps: seq<ParentStep>,
    ghost calls: seq<Recovery.RuntimeObservation>, ghost boundaries: seq<nat>,
    ghost textBoundaries: seq<nat>)

  ghost predicate PathPartitionAt(names: seq<string>, directory: string,
                                  boundaries: seq<nat>, i: nat)
  {
    i < |names| && i+1 < |boundaries| &&
    W.InodeChildNameValid(names[|names|-1-i]) &&
    boundaries[i] <= boundaries[i+1] <= |directory| &&
    directory[boundaries[i]..boundaries[i+1]] == "/"+names[|names|-1-i]
  }

  ghost predicate PathPartitionFields(names: seq<string>, directory: string, boundaries: seq<nat>)
  {
    |boundaries| == |names|+1 && boundaries[0] == 0 &&
    boundaries[|names|] == |directory| &&
    (forall i: nat | i < |names| :: PathPartitionAt(names,directory,boundaries,i))
  }

  ghost predicate StepPartitionAt(inputs: Recovery.RuntimeInputs,
                                  root: W.FileStatus, initial: W.FileStatus, steps: seq<ParentStep>,
                                  calls: seq<Recovery.RuntimeObservation>, boundaries: seq<nat>, i: nat)
  {
    i < |steps| && i+1 < |boundaries| && boundaries[i] < boundaries[i+1] <= |calls| &&
    var child := if i == 0 then initial else steps[i-1].parent;
    child.hostKey != root.hostKey &&
    Parent.ParentAttemptFields(inputs,calls[boundaries[i]].before,
                               calls[boundaries[i+1]-1].after,child,i+1,
                               steps[i].parent,steps[i].name,steps[i].failure,steps[i].evidence) &&
    steps[i].evidence.calls == calls[boundaries[i]..boundaries[i+1]]
  }

  ghost predicate StepsWitnessFields(inputs: Recovery.RuntimeInputs,
                                     before: Recovery.RuntimeState, after: Recovery.RuntimeState,
                                     root: W.FileStatus, initial: W.FileStatus, steps: seq<ParentStep>,
                                     calls: seq<Recovery.RuntimeObservation>, boundaries: seq<nat>)
  {
    root.kind == initial.kind == W.DirectoryKind &&
    Recovery.RuntimeTraceFields(inputs,before,after,calls) &&
    |boundaries| == |steps|+1 && boundaries[0] == 0 &&
    boundaries[|steps|] == |calls| &&
    (forall i: nat | i < |steps| :: StepPartitionAt(inputs,root,initial,steps,calls,boundaries,i)) &&
    (forall i: nat | i+1 < |steps| :: |steps[i].failure| == 0)
  }

  ghost predicate PhysicalSelectionFields(inputs: Recovery.RuntimeInputs,
                                          before: Recovery.RuntimeState, after: Recovery.RuntimeState,
                                          outcome: Recovery.DirectoryOutcome, evidence: PhysicalEvidence)
  {
    Recovery.DirectoryOutcomeFields(outcome) &&
    Recovery.RuntimeTraceFields(inputs,before,after,evidence.calls) && |evidence.calls| >= 1 &&
    Recovery.DirectoryActionFields(evidence.calls[0],W.DirectoryGetCwd,0,0,"") &&
    evidence.direct == C.DirectoryPathResultFields(evidence.calls[0].action.response) &&
    if evidence.direct.Ok? then
      outcome == Recovery.DirectoryRecovered(evidence.direct.v) &&
      |evidence.calls| == 1 && |evidence.root| == |evidence.current| == |evidence.steps| == 0
    else if C.ResultErrno(evidence.direct) == Errno.ENOMEM then
      outcome == Recovery.DirectoryFailed(Recovery.MemoryExhausted) &&
      |evidence.calls| == 1 && |evidence.root| == |evidence.current| == |evidence.steps| == 0
    else
      |evidence.root| == 1 && |evidence.calls| >= 2 &&
      evidence.calls[1].action == Recovery.AbsoluteStatusAction("/",false,evidence.root[0]) &&
      if evidence.root[0].Err? then
        outcome == Recovery.DirectoryFailed(Recovery.RootAttributesFailed(C.ResultErrno(evidence.root[0]))) &&
        |evidence.calls| == 2 && |evidence.current| == |evidence.steps| == 0
      else
        |evidence.current| == 1 && |evidence.calls| >= 3 &&
        Recovery.DirectoryActionFields(evidence.calls[2],W.DirectoryCurrentStatus,0,0,"") &&
        evidence.current[0] == C.DirectoryStatusResultFields(evidence.calls[2].action.response) &&
        if evidence.current[0].Err? then
          outcome == Recovery.DirectoryFailed(Recovery.CurrentDirectoryStatusFailed(C.ResultErrno(evidence.current[0]))) &&
          |evidence.calls| == 3 && |evidence.steps| == 0
        else
          StepsWitnessFields(inputs,evidence.calls[2].after,after,evidence.root[0].v,
                             evidence.current[0].v,evidence.steps,evidence.calls[3..],evidence.boundaries) &&
          if |evidence.steps| > 0 && |evidence.steps[|evidence.steps|-1].failure| != 0 then
            outcome == Recovery.DirectoryFailed(evidence.steps[|evidence.steps|-1].failure[0])
          else
            (if |evidence.steps| == 0 then evidence.current[0].v.hostKey
             else evidence.steps[|evidence.steps|-1].parent.hostKey) == evidence.root[0].v.hostKey &&
            outcome.DirectoryRecovered? &&
            if |evidence.steps| == 0 then outcome.directory == "/"
            else
              var names := seq(|evidence.steps|,i=>if 0 <= i < |evidence.steps| then evidence.steps[i].name else "");
              PathPartitionFields(names,outcome.directory,evidence.textBoundaries)
  }
}
