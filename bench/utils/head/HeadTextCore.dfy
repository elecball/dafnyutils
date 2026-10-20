include "HeadSpec.dfy"
include "HeadUtf8Core.dfy"
include "HeadEscapingCore.dfy"

module HeadTextCore {
  import BW = BenchWorld
  import Spec = HeadSpec
  import Schema = HeadSchema
  import Utf8 = HeadUtf8Core
  import Escape = HeadEscapingCore

  function ErrorMessage(path: BW.Path, err: BW.IOError): BW.Bytes
    ensures ErrorMessage(path, err) == Spec.ErrorMessage(path, err)
  {
    Utf8.Encode(Spec.ErrorMessageText(Escape.SpecQuoteAfBytes(Utf8.Encode(path)), err))
  }

  function InvalidCountMessage(unit: Schema.CountUnit, value: string): BW.Bytes
    ensures InvalidCountMessage(unit, value) == Spec.InvalidCountMessage(unit, value)
  {
    var displayValue := if |value| > 0 && value[0] == '-' then value[1..] else value;
    Utf8.Encode(Spec.InvalidCountText(unit, Escape.SpecLocaleQuoteBytes(Utf8.Encode(displayValue))))
  }

  function HeaderText(name: string): BW.Bytes
    ensures HeaderText(name) == Spec.HeaderText(name)
  {
    Spec.HeaderPrefix() + Utf8.Encode(name) + Spec.HeaderSuffix()
  }

  function StdinReadErrorMessage(error: BW.IOError): BW.Bytes
    ensures StdinReadErrorMessage(error) == Spec.StdinReadErrorMessage(error)
  {
    Spec.StdinReadErrorPrefix() + Utf8.Encode(Spec.ErrnoText(error)) + Spec.DiagnosticSuffix()
  }

  function StreamWriteErrorMessage(message: string): BW.Bytes
    ensures StreamWriteErrorMessage(message) == Spec.StreamWriteErrorMessage(message)
  {
    Utf8.Encode(Spec.StreamWriteErrorText(message))
  }
}
