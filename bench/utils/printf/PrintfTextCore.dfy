include "PrintfSpec.dfy"
include "PrintfUtf8Core.dfy"
include "PrintfEscapingCore.dfy"

module PrintfTextCore {
  import StreamContract = IOContract
  import StreamUtf8 = PrintfUtf8Core
  import BenchIO
  import Utf8 = PrintfUtf8Core
  import BenchWorld
  import Schema = PrintfSchema
  import SE = PrintfEscapingCore
  import opened Model = PrintfSpec

  function ExcessArgumentsWarning(arg: string): BenchWorld.Bytes
    ensures ExcessArgumentsWarning(arg) == Model.ExcessArgumentsWarning(arg)
  {
    ExcessArgumentsWarningPart1() +
    SE.SpecLocaleQuoteBytes(Utf8.Encode(arg)) + ExcessArgumentsWarningPart2()
  }

  function RequestExcessWarning(raw: Schema.PrintfCmdRaw): BenchWorld.Bytes
    ensures RequestExcessWarning(raw) == Model.RequestExcessWarning(raw)
  {
    match raw.excessAfterRequest
    case Some(arg) => ExcessArgumentsWarning(arg)
    case None => []
  }

  function StreamWriteErrorMessage(message: string): BenchWorld.Bytes
    ensures StreamWriteErrorMessage(message) == Model.StreamWriteErrorMessage(message)
  {
    StreamUtf8.Encode(StreamWriteErrorMessagePart1() + message + StreamWriteErrorMessagePart2())
  }
}
