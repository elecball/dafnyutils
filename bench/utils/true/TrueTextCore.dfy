include "TrueSpec.dfy"
include "TrueUtf8Core.dfy"

module TrueTextCore {
  import BW = BenchWorld
  import Spec = TrueSpec
  import Utf8 = TrueUtf8Core

  function StreamWriteErrorMessage(message: string): BW.Bytes
    ensures StreamWriteErrorMessage(message) == Spec.StreamWriteErrorMessage(message)
  {
    Utf8.Encode(Spec.StreamWriteErrorText(message))
  }
}
