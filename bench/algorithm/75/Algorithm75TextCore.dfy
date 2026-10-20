include "Algorithm75Spec.dfy"
include "Algorithm75Utf8Core.dfy"

module Algorithm75TextCore {
  import BenchWorld
  import Spec = Algorithm75Spec
  import Utf8 = Algorithm75Utf8Core

  function IntegerText(value: int): string
    ensures IntegerText(value) == Spec.IntegerText(value)
    decreases if value < 0 then 1 else 0, if value < 0 then -value else value
  {
    if value < 0 then "-" + IntegerText(-value)
    else if value < 10 then [(('0' as int) + value) as char]
    else IntegerText(value / 10) + IntegerText(value % 10)
  }

  function OutputText(out_status: string, out_x: int, out_y: int): BenchWorld.Bytes
    ensures OutputText(out_status, out_x, out_y) == Spec.OutputText(out_status, out_x, out_y)
  {
    Utf8.Encode(out_status + "\n" + (if out_status == Spec.PositiveResult() then IntegerText(out_x) + " " + IntegerText(out_y) + "\n" else ""))
  }

}
