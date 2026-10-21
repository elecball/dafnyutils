include "LsNativeSpec.dfy"

module LsNativeProof {
  import Spec = LsNativeSpec

  lemma Single(inputs: Spec.Inputs, call: Spec.Call)
    requires Spec.CallFields(inputs,call)
    ensures Spec.TraceFields(inputs,call.before,call.after,[call])
  {
    hide *;
    reveal Spec.TraceFields();
  }

  lemma Concat(inputs: Spec.Inputs, before: Spec.State, middle: Spec.State,
               after: Spec.State, left: seq<Spec.Call>, right: seq<Spec.Call>)
    requires Spec.TraceFields(inputs,before,middle,left)
    requires Spec.TraceFields(inputs,middle,after,right)
    ensures Spec.TraceFields(inputs,before,after,left+right)
  {
    hide *;
    reveal Spec.TraceFields();
    forall i: nat | i < |left+right|
      ensures Spec.CallFields(inputs,(left+right)[i])
    {
      if i < |left| { assert (left+right)[i] == left[i]; }
      else { assert (left+right)[i] == right[i-|left|]; }
    }
    forall i: nat | i+1 < |left+right|
      ensures (left+right)[i].after == (left+right)[i+1].before
    {
      if i+1 < |left| { assert (left+right)[i+1] == left[i+1]; }
      else if i < |left| {
        assert i+1 == |left|;
        assert left[i].after == middle == right[0].before;
      } else { assert (left+right)[i+1] == right[i+1-|left|]; }
    }
  }
}
