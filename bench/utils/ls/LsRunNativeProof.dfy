include "LsSpec.dfy"

module LsRunNativeProof {
  import W = BenchWorld
  import Schema = LsSchema
  import Spec = LsSpec
  import Native = LsNativeSpec

  lemma RunWitness(cmd: Schema.LsCmd, fs: W.FileSystem,
    firstStatus: nat, afterStatus: nat, observations: seq<Spec.OperandObservation>,
    afterNative: seq<Native.State>, calls: seq<Native.Call>, cuts: seq<nat>)
    requires Spec.NativeCommandFields(cmd,fs)
    requires |cmd.nativeStart| == 1 && |afterNative| == 1
    requires cmd.nativeStart[0].status == firstStatus && afterNative[0].status == afterStatus
    requires Spec.NativeCallFragments(
      seq(|observations|,i requires 0 <= i < |observations| => observations[i].nativeCalls),calls,cuts)
    requires Native.TraceFields(cmd.nativeInputs[0],cmd.nativeStart[0],afterNative[0],calls)
    ensures Spec.RunNativeFields(cmd,fs,firstStatus,afterStatus,observations,afterNative)
  {
    hide *;
    reveal Spec.NativeCommandFields();
    var pieces := seq(|observations|,i requires 0 <= i < |observations| => observations[i].nativeCalls);
    assert exists actualCalls: seq<Native.Call>, actualCuts: seq<nat> ::
      actualCalls == calls && actualCuts == cuts &&
      Spec.NativeCallFragments(pieces,actualCalls,actualCuts) &&
      Native.TraceFields(cmd.nativeInputs[0],cmd.nativeStart[0],afterNative[0],actualCalls);
    reveal Spec.RunNativeFields();
  }
}
