include "PwdRecoverySpec.dfy"

module PwdLogicalSpec {
  import W = BenchWorld
  import C = IOContract
  import Recovery = PwdRecoverySpec

  datatype SelectionEvidence = SelectionEvidence(
    ghost statuses: seq<W.IOResult<W.FileStatus>>,
    ghost calls: seq<Recovery.RuntimeObservation>)

  ghost predicate NativeSelectionFields(inputs: Recovery.RuntimeInputs,
    before: Recovery.RuntimeState, after: Recovery.RuntimeState,
    pwd: string, selected: bool, evidence: SelectionEvidence)
  {
    Recovery.LogicalSelectionFields(pwd,evidence.statuses,selected) &&
    Recovery.RuntimeTraceFields(inputs,before,after,evidence.calls) &&
    |evidence.calls| == |evidence.statuses| &&
    if |evidence.statuses| == 0 then true else
      var first := evidence.calls[0];
      first.action.AbsoluteStatusAction? && first.action.path == pwd && first.action.follow &&
      first.action.result == evidence.statuses[0] &&
      (|evidence.statuses| == 2 ==>
        var current := evidence.calls[1];
        current.action.DirectoryAction? &&
        Recovery.DirectoryActionFields(current,W.DirectoryCurrentStatus,0,0,"") &&
        evidence.statuses[1] == C.DirectoryStatusResultFields(current.action.response))
  }
}
