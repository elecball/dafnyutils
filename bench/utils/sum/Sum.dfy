include "CliSupport.dfy"
include "SumSpec.dfy"
include "SumCore.dfy"
include "SumProof.dfy"

module Sum {
  import BenchIO
  import BenchWorld
  import BenchItem
  import CliTypes
  import S = SumSchema
  import Core = SumCore
  import Spec = SumSpec
  import Proof = SumProof

  class SumBenchmarkItem extends BenchItem.BenchmarkItemTwostate<S.SumCmdRaw> {
    constructor() {}

    method Name() returns (name: string) {
      name := "sum";
    }

    method Schema() returns (schema: CliTypes.CliSchema) {
      schema := S.Schema();
    }

    method ParseConfig() returns (cfg: CliTypes.ParseConfig) {
      cfg := S.ParserConfig();
    }

    method Decode(parsed: CliTypes.ParsedArgs) returns (raw: S.SumCmdRaw) {
      raw := S.Decode(parsed);
    }

    method FormatParseError(err: CliTypes.ParseError) returns (msg: BenchWorld.Bytes) {
      // TODO: implement and test command-line parse errors, including early exits.
      assert false;
      msg := Spec.ParseErrorText(err);
    }

    method RunCore(raw: S.SumCmdRaw, io: BenchIO.IO) returns (exit: int)
      modifies io.stdinRegion, io.stdoutRegion, io.stderrRegion
      ensures Spec.Spec(raw, io, exit)
    {
      exit := Core.RunCore(raw, io);
      Proof.CoreSummaryImpliesSpec(raw, io, exit);
    }
  }
}
