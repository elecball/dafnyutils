include "Algorithm4Spec.dfy"
include "Algorithm4Utf8Core.dfy"

module Algorithm4TextCore {
  import BenchWorld
  import Spec = Algorithm4Spec
  import Utf8 = Algorithm4Utf8Core

  function IntegerText(value: int): string
    ensures IntegerText(value) == Spec.IntegerText(value)
    decreases if value < 0 then 1 else 0, if value < 0 then -value else value
  {
    if value < 0 then "-" + IntegerText(-value)
    else if value < 10 then [(('0' as int) + value) as char]
    else IntegerText(value / 10) + IntegerText(value % 10)
  }

  function OutputText(y: int): BenchWorld.Bytes
    ensures OutputText(y) == Spec.OutputText(y)
  {
    Utf8.Encode(IntegerText(y) + "\n")
  }

}
