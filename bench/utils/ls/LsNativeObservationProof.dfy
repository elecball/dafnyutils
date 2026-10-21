include "LsNativeObservationSpec.dfy"

module LsNativeObservationProof {
  import R = Results
  import W = BenchWorld
  import C = IOContract
  import Native = LsNativeSpec
  import Spec = LsNativeObservationSpec

  lemma SelectedResult(inputs: Native.Inputs, before: Native.State, after: Native.State,
                       path: W.Path, implicitDirectoryFollow: bool, explicitFollow: bool,
                       ok: bool, status: W.FileStatus, err: int, calls: seq<Native.Call>)
    requires Spec.OperandFields(inputs,before,after,path,implicitDirectoryFollow,explicitFollow,ok,status,err,calls)
    ensures 1 <= |calls| <= 2
    ensures calls[|calls|-1].action.StatusAction?
    ensures Spec.StatusFields(calls[|calls|-1].action.statusResult,ok,status,err)
    ensures ok ==> calls[|calls|-1].action.statusResult == R.Ok(status)
  {
    hide *;
    reveal Spec.OperandFields(), Spec.StatusFields(), C.ResultValue();
    if implicitDirectoryFollow &&
       (calls[0].action.statusResult.Err? || calls[0].action.statusResult.v.kind != W.DirectoryKind) {
      assert |calls| == 2;
    } else {
      assert |calls| == 1;
    }
  }

  lemma RenderFrame(inputs: Native.Inputs, before: Native.State, after: Native.State,
                    displayName: string, path: W.Path, follow: bool, showTarget: bool,
                    status: W.FileStatus, name: string, linkErr: int, calls: seq<Native.Call>)
    requires Spec.RenderFields(inputs,before,after,displayName,path,follow,showTarget,
                               status,name,linkErr,calls)
    ensures after.status == before.status
    ensures after.context == before.context.(ordinal := before.context.ordinal+|calls|)
  {
    hide *;
    reveal Spec.RenderFields(), Native.TraceFields(), Native.CallFields();
    reveal C.CwdContextReadStepFields();
  }

  lemma PathFrame(inputs: Native.Inputs, before: Native.State, after: Native.State,
                  displayName: string, path: W.Path, follow: bool, showTarget: bool,
                  ok: bool, status: W.FileStatus, err: int, name: string, linkErr: int,
                  calls: seq<Native.Call>)
    requires Spec.PathFields(inputs,before,after,displayName,path,follow,showTarget,
                             ok,status,err,name,linkErr,calls)
    ensures after.status == before.status+1
    ensures after.context == before.context.(ordinal := before.context.ordinal+|calls|)
    ensures |calls| >= 1 && calls[0].before == before
  {
    hide *;
    reveal Spec.PathFields(), Native.TraceFields(), Native.CallFields();
    reveal C.GetFileStatusAtCwdSpec(), C.CwdContextReadStepFields();
    if ok {
      RenderFrame(inputs,calls[0].after,after,displayName,path,follow,showTarget,
                  status,name,linkErr,calls[1..]);
      assert |calls[1..]|+1 == |calls|;
    }
  }

  lemma OperandFrame(inputs: Native.Inputs, before: Native.State, after: Native.State,
                     path: W.Path, implicitDirectoryFollow: bool, explicitFollow: bool,
                     ok: bool, status: W.FileStatus, err: int, calls: seq<Native.Call>)
    requires Spec.OperandFields(inputs,before,after,path,implicitDirectoryFollow,explicitFollow,
                                ok,status,err,calls)
    ensures 1 <= |calls| <= 2 && calls[0].before == before
    ensures after.status == before.status+|calls|
    ensures after.context == before.context.(ordinal := before.context.ordinal+|calls|)
  {
    hide *;
    reveal Spec.OperandFields(), Native.TraceFields(), Native.CallFields();
    reveal C.GetFileStatusAtCwdSpec(), C.CwdContextReadStepFields();
  }
}
