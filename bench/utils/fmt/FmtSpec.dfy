include "FmtSchema.dfy"
include "../../core/IO.dfy"

module FmtSpec {
  import BenchIO
  import BenchWorld
  import CliTypes
  import Schema = FmtSchema

  function ParseErrorText(err: CliTypes.ParseError): BenchWorld.Bytes
  {
    // TODO: define the exact diagnostic bytes here, including fixed text.
    []
  }

  // TODO: define the declarative observable specification.
  // These stream frames are a starting point; use the task's exact IO regions.
  twostate predicate Spec(raw: Schema.FmtCmdRaw, io: BenchIO.IO, exit: int)
    reads io.stdinRegion, io.stdoutRegion, io.stderrRegion
  {
    false
  }
}
