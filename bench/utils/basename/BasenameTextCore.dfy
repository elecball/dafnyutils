include "BasenameSpec.dfy"
include "BasenameUtf8Core.dfy"
include "BasenameEscapingCore.dfy"

module BasenameTextCore {
  import BW = BenchWorld
  import Spec = BasenameSpec
  import Utf8 = BasenameUtf8Core
  import Escape = BasenameEscapingCore

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
}
