include "FoldSpec.dfy"
include "FoldUtf8Core.dfy"
include "FoldEscapingCore.dfy"

module FoldTextCore {
  import opened Model = FoldSpec
  import StreamContract = IOContract
  import StreamUtf8 = FoldUtf8Core
  import Result = Results
  import BenchIO
  import BenchWorld
  import IOContract
  import Utf8 = FoldUtf8Core
  import Schema = FoldSchema
  import SE = FoldEscapingCore

  function InvalidWidthMessage(value: string): BenchWorld.Bytes
    ensures InvalidWidthMessage(value) == Model.InvalidWidthMessage(value)
  {
    Model.InvalidWidthMessageText0 + SE.SpecLocaleQuoteBytes(Utf8.Encode(value)) +
    (if AllDigits(value) then Model.InvalidWidthMessageText1 else Model.InvalidWidthMessageText2)
  }

  function ErrorMessage(path: BenchWorld.Path, err: BenchWorld.IOError): BenchWorld.Bytes
    ensures ErrorMessage(path, err) == Model.ErrorMessage(path, err)
  {
    Model.ErrorMessageText0 + SE.SpecQuoteFBytes(Utf8.Encode(path)) +
    Model.ErrorMessageText1 + Utf8.Encode(ErrnoText(err)) + Model.ErrorMessageText2
  }

  function StreamWriteErrorMessage(message: string): BenchWorld.Bytes
    ensures StreamWriteErrorMessage(message) == Model.StreamWriteErrorMessage(message)
  {
    StreamUtf8.Encode(Model.StreamWriteErrorMessageText0 + message + Model.StreamWriteErrorMessageText1)
  }
}
