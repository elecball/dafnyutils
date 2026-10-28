include "LsNativeCore.dfy"
include "../Proof/LsNativeProof.dfy"
include "../Spec/LsNativeObservationSpec.dfy"

module LsNativeObservationCore {
  import BenchIO
  import W = BenchWorld
  import C = IOContract
  import Native = LsNativeSpec
  import IO = LsNativeCore
  import Trace = LsNativeProof
  import Spec = LsNativeObservationSpec

  method Render(displayName: string, path: W.Path, follow: bool, showTarget: bool,
                status: W.FileStatus, io: BenchIO.IO)
    returns (name: string, linkErr: int, ghost calls: seq<Native.Call>)
    modifies io.directoryStateRegion
    ensures IO.Inputs(io) == old(IO.Inputs(io))
    ensures Spec.RenderFields(old(IO.Inputs(io)),old(IO.State(io)),IO.State(io),
                              displayName,path,follow,showTarget,status,name,linkErr,calls)
  {
    hide *;
    ghost var inputs := IO.Inputs(io);
    ghost var before := IO.State(io);
    name := displayName;
    linkErr := 0;
    calls := [];
    if status.kind == W.SymlinkKind && !follow && showTarget {
      var target, call := IO.Link(path,io);
      Trace.Single(inputs,call);
      calls := [call];
      match target
      case Ok(value) => name := Spec.LinkNameText(displayName,value);
      case Err(error) => linkErr := C.IOErrorErrno(error);
    }
    assert Spec.RenderFields(inputs,before,IO.State(io),displayName,path,follow,showTarget,
                             status,name,linkErr,calls) by {
      reveal Spec.RenderFields(), Native.TraceFields();
    }
  }

  method Observe(displayName: string, path: W.Path, follow: bool, showTarget: bool, io: BenchIO.IO)
    returns (ok: bool, status: W.FileStatus, err: int, name: string, linkErr: int,
             ghost calls: seq<Native.Call>)
    modifies io.directoryStateRegion,io.statusObservationsRegion
    ensures IO.Inputs(io) == old(IO.Inputs(io))
    ensures Spec.PathFields(old(IO.Inputs(io)),old(IO.State(io)),IO.State(io),
                            displayName,path,follow,showTarget,ok,status,err,name,linkErr,calls)
  {
    hide *;
    ghost var inputs := IO.Inputs(io);
    ghost var before := IO.State(io);
    var result, first := IO.Status(path,follow,io);
    Trace.Single(inputs,first);
    calls := [first];
    ok := result.Ok?;
    status := C.ResultValue(result,W.DEFAULT_FILE_STATUS);
    err := C.ResultErrno(result);
    name := displayName;
    linkErr := 0;
    if ok {
      ghost var middle := IO.State(io);
      ghost var renderCalls: seq<Native.Call>;
      name,linkErr,renderCalls := Render(displayName,path,follow,showTarget,status,io);
      assert Native.TraceFields(inputs,middle,IO.State(io),renderCalls) by {
        reveal Spec.RenderFields();
      }
      Trace.Concat(inputs,before,middle,IO.State(io),calls,renderCalls);
      calls := calls+renderCalls;
    }
    assert Spec.PathFields(inputs,before,IO.State(io),displayName,path,follow,showTarget,
                           ok,status,err,name,linkErr,calls) by {
      reveal Spec.PathFields(), Spec.StatusFields(), Native.TraceFields();
    }
  }

  method Operand(path: W.Path, implicitDirectoryFollow: bool, explicitFollow: bool, io: BenchIO.IO)
    returns (ok: bool, status: W.FileStatus, err: int, ghost calls: seq<Native.Call>)
    modifies io.directoryStateRegion,io.statusObservationsRegion
    ensures IO.Inputs(io) == old(IO.Inputs(io))
    ensures Spec.OperandFields(old(IO.Inputs(io)),old(IO.State(io)),IO.State(io),path,
                               implicitDirectoryFollow,explicitFollow,ok,status,err,calls)
  {
    hide *;
    ghost var inputs := IO.Inputs(io);
    ghost var before := IO.State(io);
    var result, first := IO.Status(path,implicitDirectoryFollow || explicitFollow,io);
    Trace.Single(inputs,first);
    calls := [first];
    ok := result.Ok?;
    status := C.ResultValue(result,W.DEFAULT_FILE_STATUS);
    err := C.ResultErrno(result);
    if implicitDirectoryFollow && (!ok || status.kind != W.DirectoryKind) {
      ghost var middle := IO.State(io);
      var fallback, second := IO.Status(path,false,io);
      Trace.Single(inputs,second);
      Trace.Concat(inputs,before,middle,IO.State(io),calls,[second]);
      calls := calls+[second];
      ok := fallback.Ok?;
      status := C.ResultValue(fallback,W.DEFAULT_FILE_STATUS);
      err := C.ResultErrno(fallback);
    }
    assert Spec.OperandFields(inputs,before,IO.State(io),path,implicitDirectoryFollow,
                              explicitFollow,ok,status,err,calls) by {
      reveal Spec.OperandFields(), Spec.StatusFields();
      reveal C.ResultValue();
    }
  }
}
