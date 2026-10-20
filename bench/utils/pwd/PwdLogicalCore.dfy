include "PwdLogicalSpec.dfy"
include "PwdRuntimeModel.dfy"
include "PwdRecoveryCore.dfy"
include "PwdRecoveryTraceProof.dfy"

module PwdLogicalCore {
  import BenchIO
  import W = BenchWorld
  import C = IOContract
  import Recovery = PwdRecoverySpec
  import RecoveryCore = PwdRecoveryCore
  import Model = PwdRuntimeModel
  import Trace = PwdRecoveryTraceProof
  import Spec = PwdLogicalSpec

  lemma NoUnsafeComponentIffAllSafe(components: seq<string>, start: nat)
    requires start <= |components|
    ensures !RecoveryCore.ContainsUnsafeComponent(components,start) ==
      (forall i: nat | start <= i < |components| :: components[i] != "." && components[i] != "..")
    decreases |components|-start
  {
    if start < |components| && components[start] != "." && components[start] != ".." {
      NoUnsafeComponentIffAllSafe(components,start+1);
    }
  }

  lemma LogicalTextValidIffSpec(pwd: string)
    ensures RecoveryCore.LogicalTextValid(pwd) <==> Recovery.LogicalTextFields(pwd)
  {
    var components := W.SplitSegments(W.StripLeadingSlash(pwd),0,0);
    NoUnsafeComponentIffAllSafe(components,0);
  }

  lemma LogicalSelectionSummaryImpliesFields(pwd: string,
    observations: seq<W.IOResult<W.FileStatus>>, selected: bool)
    requires RecoveryCore.LogicalSelectionSummary(pwd,observations,selected)
    ensures Recovery.LogicalSelectionFields(pwd,observations,selected)
  {
    LogicalTextValidIffSpec(pwd);
  }

  method {:isolate_assertions} SelectLogical(pwd: string, io: BenchIO.IO)
    returns (selected: bool, ghost evidence: Spec.SelectionEvidence)
    modifies io.directoryStateRegion,io.statusObservationsRegion
    ensures Model.Inputs(io) == old(Model.Inputs(io))
    ensures Spec.NativeSelectionFields(old(Model.Inputs(io)),old(Model.State(io)),
      Model.State(io),pwd,selected,evidence)
  {
    hide *;
    ghost var inputs := Model.Inputs(io);
    ghost var before := Model.State(io);
    Model.InputsMatchModel(io);
    var valid := RecoveryCore.LogicalTextValid(pwd);
    LogicalTextValidIffSpec(pwd);
    if !valid {
      selected := false;
      evidence := Spec.SelectionEvidence([],[]);
      assert Spec.NativeSelectionFields(inputs,before,Model.State(io),pwd,selected,evidence) by {
        reveal Spec.NativeSelectionFields(),Recovery.LogicalSelectionFields(),Recovery.RuntimeTraceFields();
      }
      return;
    }
    var absolute := io.GetFileStatus(pwd,true);
    ghost var middle := Model.State(io);
    ghost var first := Recovery.RuntimeObservation(before,middle,
      Recovery.AbsoluteStatusAction(pwd,true,absolute));
    assert Recovery.RuntimeObservationFields(inputs,first) by {
      reveal Recovery.RuntimeObservationFields(),Recovery.LogicalTextFields();
    }
    Trace.SingleObservation(inputs,first);
    var statuses := [absolute];
    ghost var calls := [first];
    if absolute.Ok? {
      ghost var request := W.DirectoryRequest(W.DirectoryCurrentStatus,middle.ordinal,
        inputs.fs,inputs.topology,middle.position,middle.capabilities,0,0,"",
        middle.statusOrdinal,middle.cwdHint,inputs.occupiedLegacyHandles);
      var current := io.GetCwdDirectoryIdentity();
      Model.InputsMatchModel(io);
      assert Model.Inputs(io) == inputs;
      ghost var after := Model.State(io);
      ghost var response := inputs.observations(request);
      ghost var second := Recovery.RuntimeObservation(middle,after,
        Recovery.DirectoryAction(request,response));
      assert Recovery.RuntimeObservationFields(inputs,second) by {
        reveal Recovery.RuntimeObservationFields();
      }
      assert current == C.DirectoryStatusResultFields(response);
      Trace.SingleObservation(inputs,second);
      Trace.ConcatTraces(inputs,before,middle,after,calls,[second]);
      statuses := [absolute,current];
      calls := calls+[second];
    }
    selected := RecoveryCore.ChooseLogicalFromStatuses(pwd,statuses);
    LogicalSelectionSummaryImpliesFields(pwd,statuses,selected);
    evidence := Spec.SelectionEvidence(statuses,calls);
    assert Spec.NativeSelectionFields(inputs,before,Model.State(io),pwd,selected,evidence) by {
      reveal Spec.NativeSelectionFields(),Recovery.DirectoryActionFields();
    }
  }
}
