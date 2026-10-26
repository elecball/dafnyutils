include "CliSupport.dfy"
include "FmtSpec.dfy"
include "FmtCore.dfy"
include "FmtProof.dfy"

module Fmt {
  import BenchIO
  import BenchWorld
  import BenchItem
  import CliTypes
  import S = FmtSchema
  import Core = FmtCore
  import Spec = FmtSpec
  import Proof = FmtProof

  class FmtBenchmarkItem extends BenchItem.BenchmarkItemTwostate<S.FmtCmdRaw> {
    constructor() {}

    method Name() returns (name: string) {
      name := "fmt";
    }

    method Schema() returns (schema: CliTypes.CliSchema) {
      schema := S.Schema();
    }

    method ParseConfig() returns (cfg: CliTypes.ParseConfig) {
      cfg := S.ParserConfig();
    }

    method Decode(parsed: CliTypes.ParsedArgs) returns (raw: S.FmtCmdRaw) {
      raw := S.Decode(parsed);
    }

    method FormatParseError(err: CliTypes.ParseError) returns (msg: BenchWorld.Bytes) {
      // TODO: implement and test command-line parse errors, including early exits.
      assert false;
      msg := Spec.ParseErrorText(err);
    }

    method RunCore(raw: S.FmtCmdRaw, io: BenchIO.IO) returns (exit: int)
      modifies io.stdinRegion, io.stdoutRegion, io.stderrRegion
      ensures Spec.Spec(raw, io, exit)
    {
      exit := Core.RunCore(raw, io);
      Proof.CoreSummaryImpliesSpec(raw, io, exit);
    }
  }
}
