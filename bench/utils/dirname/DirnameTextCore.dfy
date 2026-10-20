include "DirnameSpec.dfy"
include "DirnameUtf8Core.dfy"

module DirnameTextCore {
  import BW = BenchWorld
  import Spec = DirnameSpec
  import Utf8 = DirnameUtf8Core

  function StreamWriteErrorMessage(message: string): BW.Bytes
    ensures StreamWriteErrorMessage(message) == Spec.StreamWriteErrorMessage(message)
  {
    Utf8.Encode(Spec.StreamWriteErrorText(message))
  }
}
