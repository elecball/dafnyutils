include "PwdRecoverySpec.dfy"

module PwdRecoveryParentSpec {
  import W = BenchWorld
  import C = IOContract
  import Spec = PwdRecoverySpec

  datatype AccessEvidence = AccessEvidence(
    ghost openResult: W.IOResult<int>, ghost descriptor: seq<W.IOResult<int>>,
    ghost movement: seq<W.IOResult<W.Unit>>, ghost status: seq<W.IOResult<W.FileStatus>>,
    ghost calls: seq<Spec.RuntimeObservation>)

  datatype ParentEvidence = ParentEvidence(
    ghost access: AccessEvidence, ghost searches: seq<Spec.SearchWitness>,
    ghost closed: seq<W.IOResult<W.Unit>>, ghost calls: seq<Spec.RuntimeObservation>)

  ghost predicate HandleCallFields(call: Spec.RuntimeObservation,
                                   operation: W.DirectoryOperation, handle: int, fd: int, name: string, result: W.IOResult<int>)
  {
    Spec.DirectoryActionFields(call,operation,handle,fd,name) &&
    result == C.DirectoryHandleResultFields(call.action.response)
  }

  ghost predicate DescriptorCallFields(call: Spec.RuntimeObservation,
                                       handle: int, result: W.IOResult<int>)
  {
    Spec.DirectoryActionFields(call,W.DirectoryGetDescriptor,handle,0,"") &&
    result == C.DirectoryDescriptorResultFields(call.action.response)
  }

  ghost predicate UnitCallFields(call: Spec.RuntimeObservation,
                                 operation: W.DirectoryOperation, handle: int, fd: int, result: W.IOResult<W.Unit>)
  {
    Spec.DirectoryActionFields(call,operation,handle,fd,"") &&
    result == C.DirectoryUnitResultFields(call.action.response)
  }

  ghost predicate StatusCallFields(call: Spec.RuntimeObservation,
                                   operation: W.DirectoryOperation, fd: int, result: W.IOResult<W.FileStatus>)
  {
    Spec.DirectoryActionFields(call,operation,0,fd,"") &&
    result == C.DirectoryStatusResultFields(call.action.response)
  }

  ghost predicate AccessCallBindings(evidence: AccessEvidence)
  {
    |evidence.calls| >= 1 &&
    HandleCallFields(evidence.calls[0],W.DirectoryOpenParent,0,0,"",evidence.openResult) &&
    if evidence.openResult.Err? then
      |evidence.calls| == 1 &&
      |evidence.descriptor| == |evidence.movement| == |evidence.status| == 0
    else
      |evidence.calls| >= 3 && |evidence.descriptor| == |evidence.movement| == 1 &&
      DescriptorCallFields(evidence.calls[1],evidence.openResult.v,evidence.descriptor[0]) &&
      UnitCallFields(evidence.calls[2],
                     if evidence.descriptor[0].Ok? then W.DirectoryFchdir else W.DirectoryChdirParent,
                     0,if evidence.descriptor[0].Ok? then evidence.descriptor[0].v else 0,evidence.movement[0]) &&
      if evidence.movement[0].Err? then |evidence.calls| == 3 && |evidence.status| == 0
      else
        |evidence.calls| == 4 && |evidence.status| == 1 &&
        StatusCallFields(evidence.calls[3],
                         if evidence.descriptor[0].Ok? then W.DirectoryFstat else W.DirectoryCurrentStatus,
                         if evidence.descriptor[0].Ok? then evidence.descriptor[0].v else 0,evidence.status[0])
  }

  ghost predicate AccessOutcomeFields(inputs: Spec.RuntimeInputs, before: Spec.RuntimeState,
                                      after: Spec.RuntimeState, height: nat, parent: W.FileStatus, handle: int,
                                      failure: seq<Spec.RecoveryFailure>, evidence: AccessEvidence)
  {
    height >= 1 && |failure| <= 1 &&
    (|failure| == 1 ==> Spec.ValidRecoveryFailure(failure[0])) &&
    Spec.RuntimeTraceFields(inputs,before,after,evidence.calls) && AccessCallBindings(evidence) &&
    if evidence.openResult.Err? then
      failure == [Spec.ParentOpenFailed(height,C.ResultErrno(evidence.openResult))]
    else
      handle == evidence.openResult.v &&
      if evidence.movement[0].Err? then
        failure == [Spec.ParentChdirFailed(height,C.ResultErrno(evidence.movement[0]))]
      else if evidence.status[0].Err? then
        failure == [Spec.ParentStatusFailed(height,C.ResultErrno(evidence.status[0]))]
      else
        |failure| == 0 && parent == evidence.status[0].v && parent.kind == W.DirectoryKind
  }

  ghost predicate ParentAttemptFields(inputs: Spec.RuntimeInputs, before: Spec.RuntimeState,
                                      after: Spec.RuntimeState, child: W.FileStatus, height: nat,
                                      parent: W.FileStatus, name: string, failure: seq<Spec.RecoveryFailure>,
                                      evidence: ParentEvidence)
  {
    |evidence.access.calls| > 0 &&
    Spec.RuntimeTraceFields(inputs,before,after,evidence.calls) &&
    if |evidence.searches| == 0 then
      |evidence.closed| == 0 && evidence.calls == evidence.access.calls && |failure| == 1 &&
      AccessOutcomeFields(inputs,before,after,height,parent,
                          if evidence.access.openResult.Ok? then evidence.access.openResult.v else 0,failure,evidence.access)
    else
      |evidence.searches| == |evidence.closed| == 1 && evidence.access.openResult.Ok? &&
      |evidence.calls| > |evidence.access.calls| &&
      evidence.calls == evidence.access.calls + evidence.searches[0].calls +
      [evidence.calls[|evidence.calls|-1]] &&
      var middle := evidence.access.calls[|evidence.access.calls|-1].after;
      var close := evidence.calls[|evidence.calls|-1];
      AccessOutcomeFields(inputs,before,middle,height,parent,evidence.access.openResult.v,[],evidence.access) &&
      UnitCallFields(close,W.DirectoryClose,evidence.access.openResult.v,0,evidence.closed[0]) &&
      exists readErr: int ::
        Spec.SearchWitnessFields(inputs,middle,close.before,child,parent,evidence.access.openResult.v,
                                 name,readErr,evidence.searches[0]) &&
        Spec.ParentCompletionFields(height,readErr,C.ResultErrno(evidence.closed[0]),name != "",failure)
  }
}
