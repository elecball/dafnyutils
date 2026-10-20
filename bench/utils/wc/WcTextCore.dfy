include "WcSpec.dfy"
include "WcUtf8Core.dfy"
include "WcEscapingCore.dfy"

module WcTextCore {
  import opened Model = WcSpec
  import StreamContract = IOContract
  import StreamUtf8 = WcUtf8Core
  import Result = Results
  import BenchIO
  import BenchWorld
  import IOContract
  import WcSchema
  import Utf8 = WcUtf8Core
  import SE = WcEscapingCore

  function ErrorMessage(path: BenchWorld.Path, err: BenchWorld.IOError): BenchWorld.Bytes
    ensures ErrorMessage(path, err) == Model.ErrorMessage(path, err)
  {
    Model.ErrorMessageText0 + SE.SpecQuoteFBytes(Utf8.Encode(path)) + Model.ErrorMessageText1 + Utf8.Encode(ErrnoText(err)) + Model.ErrorMessageText2
  }

  function StdinReadErrorMessage(name: string, error: BenchWorld.IOError): BenchWorld.Bytes
    ensures StdinReadErrorMessage(name, error) == Model.StdinReadErrorMessage(name, error)
  {
    ErrorMessage(if name == Model.StdinReadErrorMessageText0 then Model.StdinReadErrorMessageText1 else name, error)
  }

  function StreamWriteErrorMessage(message: string): BenchWorld.Bytes
    ensures StreamWriteErrorMessage(message) == Model.StreamWriteErrorMessage(message)
  {
    StreamUtf8.Encode(Model.StreamWriteErrorMessageText0 + message + Model.StreamWriteErrorMessageText1)
  }
}
