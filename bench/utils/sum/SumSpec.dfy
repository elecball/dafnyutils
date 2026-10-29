include "SumSchema.dfy"
include "../../core/IO.dfy"

module SumSpec {
  import BenchIO
  import BenchWorld
  import CliTypes
  import Schema = SumSchema

  function ParseErrorText(err: CliTypes.ParseError): BenchWorld.Bytes
  {
    // TODO: define the exact diagnostic bytes here, including fixed text.
    []
  }

  // TODO: define the declarative observable specification.
  // These stream frames are a starting point; use the task's exact IO regions.
  twostate predicate Spec(raw: Schema.SumCmdRaw, io: BenchIO.IO, exit: int)
    reads io.stdinRegion, io.stdoutRegion, io.stderrRegion
  {
    false
  }
}
