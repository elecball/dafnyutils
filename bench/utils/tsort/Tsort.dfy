include "CliSupport.dfy"
include "TsortSpec.dfy"
include "TsortCore.dfy"
include "TsortProof.dfy"

module Tsort {
  import BenchIO
  import BenchWorld
  import BenchItem
  import CliTypes
  import S = TsortSchema
  import Core = TsortCore
  import Spec = TsortSpec
  import Proof = TsortProof

  class TsortBenchmarkItem extends BenchItem.BenchmarkItemTwostate<S.TsortCmdRaw> {
    constructor() {}

    method Name() returns (name: string) {
      name := "tsort";
    }

    method Schema() returns (schema: CliTypes.CliSchema) {
      schema := S.Schema();
    }

    method ParseConfig() returns (cfg: CliTypes.ParseConfig) {
      cfg := S.ParserConfig();
    }

    method Decode(parsed: CliTypes.ParsedArgs) returns (raw: S.TsortCmdRaw) {
      raw := S.Decode(parsed);
    }

    method FormatParseError(err: CliTypes.ParseError) returns (msg: BenchWorld.Bytes) {
      // TODO: implement and test command-line parse errors, including early exits.
      assert false;
      msg := Spec.ParseErrorText(err);
    }

    method RunCore(raw: S.TsortCmdRaw, io: BenchIO.IO) returns (exit: int)
      modifies io.stdinRegion, io.stdoutRegion, io.stderrRegion
      ensures Spec.Spec(raw, io, exit)
    {
      exit := Core.RunCore(raw, io);
      Proof.CoreSummaryImpliesSpec(raw, io, exit);
    }
  }
}
