include "EchoSpec.dfy"
include "EchoUtf8Core.dfy"

module EchoTextCore {
  import BW = BenchWorld
  import Spec = EchoSpec
  import Utf8 = EchoUtf8Core

  function StreamWriteErrorMessage(message: string): BW.Bytes
    ensures StreamWriteErrorMessage(message) == Spec.StreamWriteErrorMessage(message)
  {
    Utf8.Encode(Spec.StreamWriteErrorText(message))
  }
}
