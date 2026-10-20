include "PwdRecoverySpec.dfy"

module PwdRuntimeModel {
  import BenchIO
  import W = BenchWorld
  import Spec = PwdRecoverySpec

  ghost function Inputs(io: BenchIO.IO): (inputs: Spec.RuntimeInputs)
    reads io.fsRegion,io.directoryStateRegion,io.dirHandlesRegion,io.trustedNativeFailuresRegion
    ensures inputs.fs == io.fs()
    ensures inputs.topology == io.directoryTopology()
    ensures inputs.observations == io.directoryObservations()
    ensures inputs.times == io.statusObservations()
    ensures inputs.failures == io.trustedNativeFailures()
    ensures inputs.occupiedLegacyHandles == io.dirHandles().Keys
  {
    Spec.RuntimeInputs(io.fs(),io.directoryTopology(),io.directoryObservations(),
      io.statusObservations(),io.trustedNativeFailures(),io.dirHandles().Keys)
  }

  ghost function State(io: BenchIO.IO): (state: Spec.RuntimeState)
    reads io.directoryStateRegion,io.statusObservationsRegion,io.cwdRegion
    ensures state.position == io.directoryPosition()
    ensures state.capabilities == io.directoryCapabilities()
    ensures state.ordinal == io.directoryOrdinal()
    ensures state.statusOrdinal == io.statusCursor()
    ensures state.cwdHint == io.cwd()
  {
    Spec.RuntimeState(io.directoryPosition(),io.directoryCapabilities(),
      io.directoryOrdinal(),io.statusCursor(),io.cwd())
  }

  lemma InputsMatchModel(io: BenchIO.IO)
    ensures Inputs(io).topology == io.directoryModel().views(io.fs())
    ensures Inputs(io).observations == io.directoryModel().observations
  {
    hide *;
    var state := io.directoryState();
  }
}
