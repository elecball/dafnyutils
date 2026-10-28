include "../../../core/IO.dfy"

module LsNativeSpec {
  import W = BenchWorld
  import C = IOContract

  datatype Inputs = Inputs(
    ghost fs: W.FileSystem, ghost times: W.StatusTimeObservations,
    ghost failures: (W.NativeFailureRequest)->int,
    ghost directories: W.DirectoryObservations)
  datatype State = State(ghost context: W.CwdContext, ghost status: nat)
  datatype Action =
    StatusAction(path: W.Path, follow: bool, statusResult: W.IOResult<W.FileStatus>) |
    LinkAction(path: W.Path, linkResult: W.IOResult<W.Path>) |
    OpenAction(path: W.Path, dots: bool, openResult: W.IOResult<int>) |
    ReadAction(handle: int, readResult: W.IOResult<W.DirectoryRead>) |
    CloseAction(handle: int, closeResult: W.IOResult<W.Unit>) |
    HandleStatusAction(handle: int, statusResult: W.IOResult<W.FileStatus>)
  datatype Call = Call(ghost before: State, ghost after: State, ghost action: Action)

  ghost predicate CallFields(inputs: Inputs, call: Call)
  {
    C.CwdContextFields(inputs.fs,call.before.context) &&
    C.CwdContextFields(inputs.fs,call.after.context) &&
    var before := call.before;
    var after := call.after;
    match call.action
    case StatusAction(path,follow,result) =>
      C.CwdContextReadStepFields(before.context,after.context) &&
      C.GetFileStatusAtCwdSpec(inputs.times,inputs.failures,before.status,after.status,
                               inputs.fs,before.context,path,follow,result.Ok?,
                               C.ResultValue(result,W.DEFAULT_FILE_STATUS),C.ResultErrno(result))
    case LinkAction(path,result) =>
      after.status == before.status &&
      C.CwdContextReadStepFields(before.context,after.context) &&
      C.ReadLinkAtCwdSpec(inputs.fs,before.context,inputs.failures,path,result)
    case OpenAction(path,dots,result) =>
      after.status == before.status &&
      C.OpenDirAtCwdSpec(inputs.fs,before.context,inputs.failures,after.context,
                         path,dots,result.Ok?,C.ResultValue(result,0),C.ResultErrno(result))
    case ReadAction(handle,result) =>
      var request := C.DirectoryRequestForContextFields(inputs.fs,before.context,
                                                        W.DirectoryReadNext,handle,0,"",before.status);
      var response := inputs.directories(request);
      C.ContextOperationSpec(inputs.fs,before.context,inputs.directories,
                             W.DirectoryReadNext,handle,0,"",before.status,after.status,response,after.context) &&
      result == C.DirectoryReadResultFields(response)
    case CloseAction(handle,result) =>
      var request := C.DirectoryRequestForContextFields(inputs.fs,before.context,
                                                        W.DirectoryClose,handle,0,"",before.status);
      var response := inputs.directories(request);
      C.ContextOperationSpec(inputs.fs,before.context,inputs.directories,
                             W.DirectoryClose,handle,0,"",before.status,after.status,response,after.context) &&
      result == C.DirectoryUnitResultFields(response)
    case HandleStatusAction(handle,result) =>
      C.CwdContextReadStepFields(before.context,after.context) &&
      C.GetOpenDirectoryCapabilityStatusSpec(inputs.times,inputs.failures,before.status,
                                             after.status,inputs.fs,before.context,handle,result.Ok?,
                                             C.ResultValue(result,W.DEFAULT_FILE_STATUS),C.ResultErrno(result))
  }

  ghost predicate TraceFields(inputs: Inputs, before: State, after: State, calls: seq<Call>)
  {
    (forall i: nat | i < |calls| :: CallFields(inputs,calls[i])) &&
    if |calls| == 0 then before == after
    else calls[0].before == before && calls[|calls|-1].after == after &&
         (forall i: nat | i+1 < |calls| :: calls[i].after == calls[i+1].before)
  }
}
