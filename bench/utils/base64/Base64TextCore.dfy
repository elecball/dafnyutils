include "Base64Spec.dfy"
include "Base64Utf8Core.dfy"
include "Base64EscapingCore.dfy"

module Base64TextCore {
  import BW = BenchWorld
  import C = IOContract
  import Model = Base64Spec
  import Utf8 = Base64Utf8Core
  import SE = Base64EscapingCore

  function InvalidWrapMessage(value: string): BW.Bytes
    ensures InvalidWrapMessage(value) == Model.InvalidWrapMessage(value)
  {
    Model.InvalidWrapPrefix() + SE.SpecLocaleQuoteBytes(Utf8.Encode(value)) + Model.MessageNewline()
  }

  function ExtraOperandMessage(operand: string): BW.Bytes
    ensures ExtraOperandMessage(operand) == Model.ExtraOperandMessage(operand)
  {
    Model.ExtraOperandPrefix() + SE.SpecLocaleQuoteBytes(Utf8.Encode(operand)) + Model.ExtraOperandSuffix()
  }

  function StdinReadErrorMessage(error: BW.IOError): BW.Bytes
    ensures StdinReadErrorMessage(error) == Model.StdinReadErrorMessage(error)
  {
    Model.ReadErrorPrefix() + Utf8.Encode(Model.ErrnoText(error)) + Model.MessageNewline()
  }

  function ErrorMessage(path: BW.Path, err: BW.IOError): BW.Bytes
    ensures ErrorMessage(path, err) == Model.ErrorMessage(path, err)
  {
    if C.IOErrorIsReadFailure(err) && !(err.ReadFailure? && err.readStage == BW.CloseFailed) then
      Model.ReadErrorPrefix() + Utf8.Encode(Model.ErrnoText(err)) + Model.MessageNewline()
    else
      Model.InputPathPrefix() + SE.SpecQuoteFBytes(Utf8.Encode(path)) +
      Model.ErrorSeparator() + Utf8.Encode(Model.ErrnoText(err)) + Model.MessageNewline()
  }

  function StreamWriteErrorMessage(message: string): BW.Bytes
    ensures StreamWriteErrorMessage(message) == Model.StreamWriteErrorMessage(message)
  {
    Utf8.Encode(Model.StreamWriteErrorText(message))
  }
}
