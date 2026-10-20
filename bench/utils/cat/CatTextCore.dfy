include "CatSpec.dfy"
include "CatUtf8Core.dfy"
include "CatQuoteCore.dfy"

module CatTextCore {
  import BW = BenchWorld
  import Spec = CatSpec
  import Utf8 = CatUtf8Core
  import Quote = CatQuoteCore

  function VersionTextSpec(): BW.Bytes
    ensures VersionTextSpec() == Spec.VersionTextSpec()
  {
    Utf8.Encode(Spec.VersionTextValue())
  }

  function ErrorMessageSpec(path: BW.Path, err: BW.IOError): BW.Bytes
    ensures ErrorMessageSpec(path, err) == Spec.ErrorMessageSpec(path, err)
  {
    Spec.ErrorPrefix() + Quote.SpecQuoteFBytes(Utf8.Encode(path)) + Spec.ErrorSeparator() +
      Utf8.Encode(Spec.ErrnoText(err)) + Spec.DiagnosticSuffix()
  }

  function StreamWriteErrorMessage(message: string): BW.Bytes
    ensures StreamWriteErrorMessage(message) == Spec.StreamWriteErrorMessage(message)
  {
    Utf8.Encode(Spec.StreamWriteErrorText(message))
  }
}
