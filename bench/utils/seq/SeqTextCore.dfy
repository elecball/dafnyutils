include "SeqSpec.dfy"
include "SeqUtf8Core.dfy"
include "SeqEscapingCore.dfy"

module SeqTextCore {
  import StreamContract = IOContract
  import StreamUtf8 = SeqUtf8Core
  import Result = Results
  import BenchIO
  import Utf8 = SeqUtf8Core
  import BenchWorld
  import SeqSchema
  import SE = SeqEscapingCore
  import opened Model = SeqSpec

  function ExtraOperandMessage(token: string): BenchWorld.Bytes
    ensures ExtraOperandMessage(token) == Model.ExtraOperandMessage(token)
  {
    ExtraOperandMessagePart1() + SE.SpecLocaleQuoteBytes(Utf8.Encode(token)) + ExtraOperandMessagePart2() + TryHelp()
  }

  function InvalidNumberMessage(token: string): BenchWorld.Bytes
    ensures InvalidNumberMessage(token) == Model.InvalidNumberMessage(token)
  {
    InvalidNumberMessagePart1() + SE.SpecLocaleQuoteBytes(Utf8.Encode(token)) + InvalidNumberMessagePart2() + TryHelp()
  }

  function ZeroIncrementMessage(token: string): BenchWorld.Bytes
    ensures ZeroIncrementMessage(token) == Model.ZeroIncrementMessage(token)
  {
    ZeroIncrementMessagePart1() + SE.SpecLocaleQuoteBytes(Utf8.Encode(token)) + ZeroIncrementMessagePart2() + TryHelp()
  }

  function StreamWriteErrorMessage(message: string): BenchWorld.Bytes
    ensures StreamWriteErrorMessage(message) == Model.StreamWriteErrorMessage(message)
  {
    StreamUtf8.Encode(StreamWriteErrorMessagePart1() + message + StreamWriteErrorMessagePart2())
  }
}
