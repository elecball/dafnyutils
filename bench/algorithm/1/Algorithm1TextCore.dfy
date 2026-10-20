include "Algorithm1Spec.dfy"
include "Algorithm1Utf8Core.dfy"

module Algorithm1TextCore {
  import BenchWorld
  import Spec = Algorithm1Spec
  import Utf8 = Algorithm1Utf8Core

  function IntegerText(value: int): string
    ensures IntegerText(value) == Spec.IntegerText(value)
    decreases if value < 0 then 1 else 0, if value < 0 then -value else value
  {
    if value < 0 then "-" + IntegerText(-value)
    else if value < 10 then [(('0' as int) + value) as char]
    else IntegerText(value / 10) + IntegerText(value % 10)
  }

  function OutputText(result: int): BenchWorld.Bytes
    ensures OutputText(result) == Spec.OutputText(result)
  {
    Utf8.Encode(IntegerText(result) + "\n")
  }

}
