include "CutSpec.dfy"
include "CutUtf8Core.dfy"
include "CutEscapingCore.dfy"

module CutTextCore {
  import opened Model = CutSpec
  import StreamContract = IOContract
  import StreamUtf8 = CutUtf8Core
  import Result = Results
  import BenchIO
  import Utf8 = CutUtf8Core
  import BenchWorld
  import IOContract
  import CutSchema
  import SE = CutEscapingCore

  function ErrorMessage(path: BenchWorld.Path, err: BenchWorld.IOError): BenchWorld.Bytes
    ensures ErrorMessage(path, err) == Model.ErrorMessage(path, err)
  {
    Model.ErrorMessageText0 + SE.SpecQuoteFBytes(Utf8.Encode(path)) + Model.ErrorMessageText1 + Utf8.Encode(ErrnoText(err)) + Model.ErrorMessageText2
  }

  function OutputDelimiterBytes(delimiter: CutSchema.OutputDelimiter): BenchWorld.Bytes
    ensures OutputDelimiterBytes(delimiter) == Model.OutputDelimiterBytes(delimiter)
  {
    match delimiter
    case OutputDefault => []
    case OutputCustom(text) => if |text| == 0 then ['\0'] else Utf8.Encode(text)
  }

  function StreamWriteErrorMessage(message: string): BenchWorld.Bytes
    ensures StreamWriteErrorMessage(message) == Model.StreamWriteErrorMessage(message)
  {
    StreamUtf8.Encode(Model.StreamWriteErrorMessageText0 + message + Model.StreamWriteErrorMessageText1)
  }
}
