include "ExpandSpec.dfy"
include "ExpandUtf8Core.dfy"
include "ExpandEscapingCore.dfy"

module ExpandTextCore {
  import StreamContract = IOContract
  import StreamUtf8 = ExpandUtf8Core
  import Result = Results
  import BenchIO
  import BenchWorld
  import IOContract
  import Schema = ExpandSchema
  import Utf8 = ExpandUtf8Core
  import SE = ExpandEscapingCore
  import opened Model = ExpandSpec

  function InvalidTabsMessage(value: BenchWorld.Bytes): BenchWorld.Bytes
    ensures InvalidTabsMessage(value) == Model.InvalidTabsMessage(value)
  {
    "expand: " + value + "\n"
  }

  function ErrorMessage(path: BenchWorld.Path, err: BenchWorld.IOError): BenchWorld.Bytes
    ensures ErrorMessage(path, err) == Model.ErrorMessage(path, err)
  {
    ErrorMessagePart1() + SE.SpecQuoteFBytes(Utf8.Encode(path)) + ErrorMessagePart2() + Utf8.Encode(ErrnoText(err)) + ErrorMessagePart3()
  }

  function InvalidCharacterMessage(suffix: string): BenchWorld.Bytes
    ensures InvalidCharacterMessage(suffix) == Model.InvalidCharacterMessage(suffix)
  {
    InvalidCharacterMessagePart1() + SE.SpecLocaleQuoteBytes(Utf8.Encode(suffix))
  }

  function MarkerNotAtStartMessage(
    marker: Schema.MarkerKind, suffix: string
  ): BenchWorld.Bytes
    ensures MarkerNotAtStartMessage(marker, suffix) == Model.MarkerNotAtStartMessage(marker, suffix)
  {
    SE.SpecLocaleQuoteBytes(Utf8.Encode(MarkerText(marker))) +
    MarkerNotAtStartMessagePart1() + SE.SpecLocaleQuoteBytes(Utf8.Encode(suffix))
  }

  function TooLargeMessage(digits: string): BenchWorld.Bytes
    ensures TooLargeMessage(digits) == Model.TooLargeMessage(digits)
  {
    TooLargeMessagePart1() + SE.SpecLocaleQuoteBytes(Utf8.Encode(digits))
  }

  function RepeatOnlyLastMessage(marker: Schema.MarkerKind): BenchWorld.Bytes
    ensures RepeatOnlyLastMessage(marker) == Model.RepeatOnlyLastMessage(marker)
  {
    SE.SpecLocaleQuoteBytes(Utf8.Encode(MarkerText(marker))) +
    RepeatOnlyLastMessagePart1()
  }

  function StreamWriteErrorMessage(message: string): BenchWorld.Bytes
    ensures StreamWriteErrorMessage(message) == Model.StreamWriteErrorMessage(message)
  {
    StreamUtf8.Encode(StreamWriteErrorMessagePart1() + message + StreamWriteErrorMessagePart2())
  }
}
