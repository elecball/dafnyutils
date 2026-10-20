include "Algorithm20Spec.dfy"
include "Algorithm20Utf8Core.dfy"

module Algorithm20TextCore {
  import BenchWorld
  import Spec = Algorithm20Spec
  import Utf8 = Algorithm20Utf8Core

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
