include "Algorithm63Spec.dfy"
include "Algorithm63Utf8Core.dfy"

module Algorithm63TextCore {
  import BenchWorld
  import Spec = Algorithm63Spec
  import Utf8 = Algorithm63Utf8Core

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
