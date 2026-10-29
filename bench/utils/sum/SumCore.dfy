include "../../core/IO.dfy"
include "SumSchema.dfy"

module SumCore {
  import BenchIO
  import Schema = SumSchema

  twostate predicate CoreSummary(raw: Schema.SumCmdRaw, io: BenchIO.IO, exit: int)
    reads io.stdinRegion, io.stdoutRegion, io.stderrRegion
  {
    // TODO: state what the implementation establishes.
    false
  }

  method RunCore(raw: Schema.SumCmdRaw, io: BenchIO.IO) returns (exit: int)
    modifies io.stdinRegion, io.stdoutRegion, io.stderrRegion
    ensures CoreSummary(raw, io, exit)
  {
    // TODO: implement the specified behavior and prove CoreSummary.
    assert false;
    exit := 1;
  }
}
