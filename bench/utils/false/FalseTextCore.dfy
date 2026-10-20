include "FalseSpec.dfy"
include "FalseUtf8Core.dfy"

module FalseTextCore {
  import BW = BenchWorld
  import Spec = FalseSpec
  import Utf8 = FalseUtf8Core

  function StreamWriteErrorMessage(message: string): BW.Bytes
    ensures StreamWriteErrorMessage(message) == Spec.StreamWriteErrorMessage(message)
  {
    Utf8.Encode(Spec.StreamWriteErrorText(message))
  }
}
