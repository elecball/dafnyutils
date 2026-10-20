include "ExprSpec.dfy"
include "ExprUtf8Core.dfy"
include "ExprEscapingCore.dfy"

module ExprTextCore {
  import StreamContract = IOContract
  import StreamUtf8 = ExprUtf8Core
  import BenchIO
  import BenchWorld
  import Utf8 = ExprUtf8Core
  import Schema = ExprSchema
  import SE = ExprEscapingCore
  import opened Model = ExprSpec

  function UnexpectedArgumentMessage(token: string): BenchWorld.Bytes
    ensures UnexpectedArgumentMessage(token) == Model.UnexpectedArgumentMessage(token)
  {
    UnexpectedArgumentMessagePart1() +
    SE.SpecLocaleQuoteBytes(Utf8.Encode(token)) + UnexpectedArgumentMessagePart2()
  }

  function MissingAfterMessage(op: string): BenchWorld.Bytes
    ensures MissingAfterMessage(op) == Model.MissingAfterMessage(op)
  {
    MissingAfterMessagePart1() +
    SE.SpecLocaleQuoteBytes(Utf8.Encode(op)) + MissingAfterMessagePart2()
  }

  function MissingCloseAfterMessage(token: string): BenchWorld.Bytes
    ensures MissingCloseAfterMessage(token) == Model.MissingCloseAfterMessage(token)
  {
    MissingCloseAfterMessagePart1() +
    SE.SpecLocaleQuoteBytes(Utf8.Encode(token)) + MissingCloseAfterMessagePart2()
  }

  function MissingCloseInsteadMessage(token: string): BenchWorld.Bytes
    ensures MissingCloseInsteadMessage(token) == Model.MissingCloseInsteadMessage(token)
  {
    MissingCloseInsteadMessagePart1() +
    SE.SpecLocaleQuoteBytes(Utf8.Encode(token)) + MissingCloseInsteadMessagePart2()
  }

  function StreamWriteErrorMessage(message: string): BenchWorld.Bytes
    ensures StreamWriteErrorMessage(message) == Model.StreamWriteErrorMessage(message)
  {
    StreamUtf8.Encode(StreamWriteErrorMessagePart1() + message + StreamWriteErrorMessagePart2())
  }
}
