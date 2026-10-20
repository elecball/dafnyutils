include "Algorithm100Spec.dfy"
include "Algorithm100Utf8Core.dfy"

module Algorithm100TextCore {
  import BenchWorld
  import Spec = Algorithm100Spec
  import Utf8 = Algorithm100Utf8Core

  function LinesText(lines: seq<string>): string
    ensures LinesText(lines) == Spec.LinesText(lines)
    decreases |lines|
  {
    if |lines| == 0 then "" else lines[0] + "\n" + LinesText(lines[1..])
  }

  function OutputText(output_lines: seq<string>): BenchWorld.Bytes
    ensures OutputText(output_lines) == Spec.OutputText(output_lines)
  {
    Utf8.Encode(LinesText(output_lines))
  }

}
