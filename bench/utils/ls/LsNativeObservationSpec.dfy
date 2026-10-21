include "LsNativeSpec.dfy"

module LsNativeObservationSpec {
  import W = BenchWorld
  import C = IOContract
  import Native = LsNativeSpec

  function LinkNameText(displayName: string, target: string): string
  {
    displayName + " -> " + target
  }

  ghost predicate StatusFields(result: W.IOResult<W.FileStatus>,
                                                  ok: bool, status: W.FileStatus, err: int)
  {
    ok == result.Ok? && status == C.ResultValue(result,W.DEFAULT_FILE_STATUS) &&
    err == C.ResultErrno(result)
  }

  ghost predicate RenderFields(inputs: Native.Inputs, before: Native.State, after: Native.State,
                               displayName: string, path: W.Path, follow: bool, showTarget: bool,
                               status: W.FileStatus, name: string, linkErr: int, calls: seq<Native.Call>)
  {
    Native.TraceFields(inputs,before,after,calls) &&
    if status.kind == W.SymlinkKind && !follow && showTarget then
      |calls| == 1 && calls[0].action.LinkAction? && calls[0].action.path == path &&
      match calls[0].action.linkResult
      case Ok(target) => name == LinkNameText(displayName,target) && linkErr == 0
      case Err(error) => name == displayName && linkErr == C.IOErrorErrno(error)
    else calls == [] && name == displayName && linkErr == 0
  }

  ghost predicate PathFields(inputs: Native.Inputs, before: Native.State, after: Native.State,
                             displayName: string, path: W.Path, follow: bool, showTarget: bool,
                             ok: bool, status: W.FileStatus, err: int, name: string, linkErr: int,
                             calls: seq<Native.Call>)
  {
    Native.TraceFields(inputs,before,after,calls) &&
    |calls| >= 1 && calls[0].action.StatusAction? &&
    calls[0].action.path == path && calls[0].action.follow == follow &&
    StatusFields(calls[0].action.statusResult,ok,status,err) &&
    if ok then
      RenderFields(inputs,calls[0].after,after,displayName,path,follow,showTarget,
                   status,name,linkErr,calls[1..])
    else |calls| == 1 && name == displayName && linkErr == 0
  }

  ghost predicate OperandFields(inputs: Native.Inputs, before: Native.State, after: Native.State,
                                path: W.Path, implicitDirectoryFollow: bool, explicitFollow: bool,
                                ok: bool, status: W.FileStatus, err: int, calls: seq<Native.Call>)
  {
    Native.TraceFields(inputs,before,after,calls) &&
    |calls| >= 1 && calls[0].action.StatusAction? && calls[0].action.path == path &&
    calls[0].action.follow == (implicitDirectoryFollow || explicitFollow) &&
    if implicitDirectoryFollow &&
       (calls[0].action.statusResult.Err? || calls[0].action.statusResult.v.kind != W.DirectoryKind) then
      |calls| == 2 && calls[1].action.StatusAction? &&
      calls[1].action.path == path && !calls[1].action.follow &&
      StatusFields(calls[1].action.statusResult,ok,status,err)
    else |calls| == 1 && StatusFields(calls[0].action.statusResult,ok,status,err)
  }
}
