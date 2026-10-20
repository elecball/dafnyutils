include "Algorithm4004Spec.dfy"
include "Algorithm4004Utf8Core.dfy"

module Algorithm4004TextCore {
  import BenchWorld
  import Spec = Algorithm4004Spec
  import Utf8 = Algorithm4004Utf8Core

  function IntegerText(value: int): string
    ensures IntegerText(value) == Spec.IntegerText(value)
    decreases if value < 0 then 1 else 0, if value < 0 then -value else value
  {
    if value < 0 then "-" + IntegerText(-value)
    else if value < 10 then [(('0' as int) + value) as char]
    else IntegerText(value / 10) + IntegerText(value % 10)
  }

  function OutputText(out: int): BenchWorld.Bytes
    ensures OutputText(out) == Spec.OutputText(out)
  {
    Utf8.Encode(IntegerText(out) + "\n")
  }

}
