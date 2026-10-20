include "PrintenvSpec.dfy"
include "PrintenvUtf8Core.dfy"

module PrintenvTextCore {
  import BW = BenchWorld
  import Spec = PrintenvSpec
  import Utf8 = PrintenvUtf8Core

  function StreamWriteErrorMessage(message: string): BW.Bytes
    ensures StreamWriteErrorMessage(message) == Spec.StreamWriteErrorMessage(message)
  {
    Utf8.Encode(Spec.StreamWriteErrorText(message))
  }
}
