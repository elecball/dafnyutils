include "../../core/IO.dfy"
include "TsortSchema.dfy"

module TsortCore {
  import BenchIO
  import Schema = TsortSchema

  twostate predicate CoreSummary(raw: Schema.TsortCmdRaw, io: BenchIO.IO, exit: int)
    reads io.stdinRegion, io.stdoutRegion, io.stderrRegion
  {
    // TODO: state what the implementation establishes.
    false
  }

  method RunCore(raw: Schema.TsortCmdRaw, io: BenchIO.IO) returns (exit: int)
    modifies io.stdinRegion, io.stdoutRegion, io.stderrRegion
    ensures CoreSummary(raw, io, exit)
  {
    // TODO: implement the specified behavior and prove CoreSummary.
    assert false;
    exit := 1;
  }
}
