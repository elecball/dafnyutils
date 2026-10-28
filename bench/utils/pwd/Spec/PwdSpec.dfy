include "PwdTextSpec.dfy"
include "PwdRuntimeModel.dfy"
include "PwdLogicalSpec.dfy"
include "PwdPhysicalSpec.dfy"
include "PwdEmissionSpec.dfy"

module PwdSpec {
  import BenchIO
  import W = BenchWorld
  import C = IOContract
  import Schema = PwdSchema
  import Text = PwdTextSpec
  import Model = PwdRuntimeModel
  import Recovery = PwdRecoverySpec
  import Logical = PwdLogicalSpec
  import Physical = PwdPhysicalSpec
  import Emission = PwdEmissionSpec

  datatype DirectoryEvidence = DirectoryEvidence(
    ghost logicalSelected: bool, ghost logicalAfter: Recovery.RuntimeState,
    ghost logical: Logical.SelectionEvidence, ghost physical: seq<Physical.PhysicalEvidence>)

  ghost predicate DirectorySelectionFields(raw: Schema.PwdCmdRaw, env: map<string,string>,
                                           inputs: Recovery.RuntimeInputs, before: Recovery.RuntimeState, after: Recovery.RuntimeState,
                                           outcome: Recovery.DirectoryOutcome, evidence: DirectoryEvidence)
  {
    Recovery.DirectoryOutcomeFields(outcome) &&
    (if Text.UseLogicalFields(raw,env) && "PWD" in env then
       Logical.NativeSelectionFields(inputs,before,evidence.logicalAfter,env["PWD"],
                                     evidence.logicalSelected,evidence.logical)
     else !evidence.logicalSelected && evidence.logicalAfter == before &&
          evidence.logical.statuses == [] && evidence.logical.calls == []) &&
    if evidence.logicalSelected then
      "PWD" in env && outcome == Recovery.DirectoryRecovered(env["PWD"]) &&
      after == evidence.logicalAfter && evidence.physical == []
    else
      |evidence.physical| == 1 &&
      Physical.PhysicalSelectionFields(inputs,evidence.logicalAfter,after,outcome,evidence.physical[0])
  }

  ghost predicate WarningFields(raw: Schema.PwdCmdRaw,
                                beforeErr: W.Bytes, afterErr: W.Bytes,
                                streams: (W.TrustedStreamRequest)->W.TrustedStreamResult, warningErr: int)
  {
    if |raw.operands| == 0 then beforeErr == afterErr && warningErr == 0
    else exists committed: nat ::
           C.WriteStderrSpec(beforeErr,streams,afterErr,Text.IgnoredOperandsWarningSpec(),committed,warningErr)
  }

  ghost predicate RunFields(raw: Schema.PwdCmdRaw, env: map<string,string>,
                            inputs: Recovery.RuntimeInputs, before: Recovery.RuntimeState, after: Recovery.RuntimeState,
                            beforeOut: W.Bytes, beforeErr: W.Bytes, afterOut: W.Bytes, afterErr: W.Bytes,
                            streams: (W.TrustedStreamRequest)->W.TrustedStreamResult, exit: int)
  {
    if Text.HelpSelected(raw) then
      before == after &&
      Emission.EmissionFields(beforeOut,beforeErr,afterOut,afterErr,streams,Text.HelpTextSpec(),[],0,exit)
    else if Text.VersionSelected(raw) then
      before == after &&
      Emission.EmissionFields(beforeOut,beforeErr,afterOut,afterErr,streams,Text.VersionTextSpec(),[],0,exit)
    else
      exists middleErr: W.Bytes, warningErr: int, outcome: Recovery.DirectoryOutcome,
        evidence: DirectoryEvidence, emissionExit: int ::
        WarningFields(raw,beforeErr,middleErr,streams,warningErr) &&
        DirectorySelectionFields(raw,env,inputs,before,after,outcome,evidence) &&
        Emission.PhysicalEmissionFields(outcome,beforeOut,middleErr,afterOut,afterErr,streams,emissionExit) &&
        exit == (if warningErr == 0 then emissionExit else 1)
  }

  twostate predicate Spec(raw: Schema.PwdCmdRaw, io: BenchIO.IO, exit: int)
    reads io.fsRegion,io.directoryStateRegion,io.dirHandlesRegion,io.cwdRegion,io.statusObservationsRegion,
          io.envRegion,io.stdoutRegion,io.stderrRegion,io.trustedStreamsRegion,io.trustedNativeFailuresRegion
  {
    Model.Inputs(io) == old(Model.Inputs(io)) &&
    RunFields(raw,old(io.env()),old(Model.Inputs(io)),old(Model.State(io)),Model.State(io),
              old(io.stdout()),old(io.stderr()),io.stdout(),io.stderr(),io.trustedStreams(),exit)
  }
}
