include "TailSpec.dfy"
include "TailUtf8Core.dfy"
include "TailEscapingCore.dfy"

module TailTextCore {
  import BW = BenchWorld
  import Spec = TailSpec
  import Schema = TailSchema
  import Utf8 = TailUtf8Core
  import Escape = TailEscapingCore

  function ErrorMessage(path: BW.Path, err: BW.IOError): BW.Bytes
  {
    Spec.ErrorMessage(path, err)
  } by method {
    reveal Spec.ErrorMessage();
    return Spec.ErrorPrefix(err) + Escape.SpecQuoteAfBytes(Utf8.Encode(path)) + Spec.ErrorInfix(err) +
      Utf8.Encode(Spec.ErrnoText(err)) + Spec.DiagnosticSuffix();
  }

  function InvalidCountMessage(unit: Schema.CountUnit, value: string): BW.Bytes
    ensures InvalidCountMessage(unit, value) == Spec.InvalidCountMessage(unit, value)
  {
    var displayValue := if |value| > 0 && value[0] == '-' then value[1..] else value;
    Utf8.Encode(Spec.InvalidCountPrefix(unit)) + Escape.SpecLocaleQuoteBytes(Utf8.Encode(displayValue)) + Spec.DiagnosticSuffix()
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
