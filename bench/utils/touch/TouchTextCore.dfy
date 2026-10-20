include "TouchSpec.dfy"
include "TouchUtf8Core.dfy"
include "TouchEscapingCore.dfy"

module TouchTextCore {
  import StreamWorld = BenchWorld
  import StreamContract = IOContract
  import Errno = Errnos
  import Utf8 = TouchUtf8Core
  import BenchIO
  import CliTypes
  import IOContract
  import BenchWorld
  import Schema = TouchSchema
  import SE = TouchEscapingCore
  import opened Model = TouchSpec

  function MissingShortRequiredArgumentMessageSpec(option: char): BenchWorld.Bytes
    ensures MissingShortRequiredArgumentMessageSpec(option) == Model.MissingShortRequiredArgumentMessageSpec(option)
  {
    var prefix: string := MissingShortRequiredArgumentMessageSpecPart1();
    Utf8.Encode(prefix + [option] + MissingShortRequiredArgumentMessageSpecPart2() +
    MissingShortRequiredArgumentMessageSpecPart3())
  }

  function MissingLongRequiredArgumentMessageSpec(option: string): BenchWorld.Bytes
    ensures MissingLongRequiredArgumentMessageSpec(option) == Model.MissingLongRequiredArgumentMessageSpec(option)
  {
    Utf8.Encode(MissingLongRequiredArgumentMessageSpecPart1() + option + MissingLongRequiredArgumentMessageSpecPart2() +
    MissingLongRequiredArgumentMessageSpecPart3())
  }

  function ParseErrorMessageSpec(e: CliTypes.ParseError): BenchWorld.Bytes
    ensures ParseErrorMessageSpec(e) == Model.ParseErrorMessageSpec(e)
  {
    if Schema.IsMissingShortRequiredArgument(e) then
      MissingShortRequiredArgumentMessageSpec(e.rawToken[|e.rawToken| - 1])
    else if Schema.IsMissingLongRequiredArgument(e) then
      MissingLongRequiredArgumentMessageSpec(Schema.MissingLongRequiredOption(e))
    else
      Utf8.Encode(Schema.ParseErrorText(e))
  }

  function InvalidTimeMessageSpec(value: string): BenchWorld.Bytes
    ensures InvalidTimeMessageSpec(value) == Model.InvalidTimeMessageSpec(value)
  {
    InvalidTimeMessageSpecPart1() + SE.SpecLocaleQuoteBytes(Utf8.Encode(value)) +
    Utf8.Encode(InvalidTimeMessageSpecPart2() +
    InvalidTimeMessageSpecPart3() +
    InvalidTimeMessageSpecPart4() +
    InvalidTimeMessageSpecPart5() +
    InvalidTimeMessageSpecPart6())
  }

  function AmbiguousTimeMessageSpec(value: string): BenchWorld.Bytes
    ensures AmbiguousTimeMessageSpec(value) == Model.AmbiguousTimeMessageSpec(value)
  {
    AmbiguousTimeMessageSpecPart1() + SE.SpecLocaleQuoteBytes(Utf8.Encode(value)) +
    Utf8.Encode(AmbiguousTimeMessageSpecPart2() +
    AmbiguousTimeMessageSpecPart3() +
    AmbiguousTimeMessageSpecPart4() +
    AmbiguousTimeMessageSpecPart5() +
    AmbiguousTimeMessageSpecPart6())
  }

  function InvalidDateMessageSpec(value: string): BenchWorld.Bytes
    ensures InvalidDateMessageSpec(value) == Model.InvalidDateMessageSpec(value)
  {
    InvalidDateMessageSpecPart1() + SE.SpecLocaleQuoteBytes(Utf8.Encode(value)) + InvalidDateMessageSpecPart2()
  }

  function WriteErrorText(reason: string): StreamWorld.Bytes
    ensures WriteErrorText(reason) == Model.WriteErrorText(reason)
  {
    WriteErrorTextPart1() + Utf8.Encode(reason) + WriteErrorTextPart2()
  }
}
