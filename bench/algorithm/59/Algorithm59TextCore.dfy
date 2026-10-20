include "Algorithm59Spec.dfy"
include "Algorithm59Utf8Core.dfy"

module Algorithm59TextCore {
  import BenchWorld
  import Spec = Algorithm59Spec
  import Utf8 = Algorithm59Utf8Core

  function OutputText(output: string): BenchWorld.Bytes
    ensures OutputText(output) == Spec.OutputText(output)
  {
    Utf8.Encode(output + "\n")
  }

}
