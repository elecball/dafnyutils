include "LognameSpec.dfy"
include "LognameUtf8Core.dfy"
include "LognameEscapingCore.dfy"

module LognameTextCore {
  import BW = BenchWorld
  import Spec = LognameSpec
  import Utf8 = LognameUtf8Core
  import Escape = LognameEscapingCore

  function StreamWriteErrorMessage(message: string): BW.Bytes
    ensures StreamWriteErrorMessage(message) == Spec.StreamWriteErrorMessage(message)
  {
    Utf8.Encode(Spec.StreamWriteErrorText(message))
  }

  function ExtraOperandMessage(op: string): BW.Bytes
    ensures ExtraOperandMessage(op) == Spec.ExtraOperandMessageSpec(op)
  {
    Spec.ExtraOperandPrefix() + Escape.LocaleQuoteBytes(Utf8.Encode(op)) + Spec.ExtraOperandSuffix()
  }

  function LoginNameOutput(name: string): BW.Bytes
    ensures LoginNameOutput(name) == Spec.LoginNameOutput(name)
  {
    Utf8.Encode(name) + Spec.LoginNameTerminator()
  }
}
