include "Algorithm38Spec.dfy"
include "Algorithm38Utf8Core.dfy"

module Algorithm38TextCore {
  import BenchWorld
  import Spec = Algorithm38Spec
  import Utf8 = Algorithm38Utf8Core

  function OutputText(result: string): BenchWorld.Bytes
    ensures OutputText(result) == Spec.OutputText(result)
  {
    Utf8.Encode(result + "\n")
  }

}
