include "Algorithm3690Spec.dfy"
include "Algorithm3690Utf8Core.dfy"

module Algorithm3690TextCore {
  import BenchWorld
  import Spec = Algorithm3690Spec
  import Utf8 = Algorithm3690Utf8Core

  function OutputText(result: string): BenchWorld.Bytes
    ensures OutputText(result) == Spec.OutputText(result)
  {
    Utf8.Encode(result + "\n")
  }

}
