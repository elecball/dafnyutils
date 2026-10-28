include "CliSupport.dfy"
include "../Spec/DdSpec.dfy"
include "DdCore.dfy"
include "../Proof/DdProof.dfy"

module Dd {
  import BenchIO
  import BenchWorld
  import BenchItem
  import CliTypes
  import S = DdSchema
  import Core = DdCore
  import Spec = DdSpec
  import Proof = DdProof

  class DdBenchmarkItem extends BenchItem.BenchmarkItemTwostate<S.DdCmdRaw> {
    constructor() {}

    method Name() returns (name: string) {
      name := "dd";
    }

    method Schema() returns (schema: CliTypes.CliSchema) {
      schema := S.Schema();
    }

    method ParseConfig() returns (cfg: CliTypes.ParseConfig) {
      cfg := S.ParserConfig();
    }

    method Decode(parsed: CliTypes.ParsedArgs) returns (raw: S.DdCmdRaw) {
      raw := S.Decode(parsed);
    }

    method FormatParseError(err: CliTypes.ParseError) returns (msg: BenchWorld.Bytes) {
      msg := Spec.ParseErrorText(err);
    }

    method PlanParseFailure(err: CliTypes.ParseError, argv: seq<string>) returns (plan: CliTypes.CliPlan<S.DdCmdRaw>)
      decreases |argv|
    {
      var i := 1;
      while i < |argv| && i < err.tokenIndex
        decreases |argv| - i
      {
        if argv[i] == "--" { break; }
        if |argv[i]| > 2 && argv[i][..2] == "--" {
          var name := argv[i][2..];
          if S.Starts("help", name) || S.Starts("version", name) {
            var raw := S.DecodeOperands([], if S.Starts("help", name) then S.Help else S.Version);
            return CliTypes.CliRun(raw);
          }
        }
        i := i + 1;
      }
      plan := CliTypes.CliEarlyExit(1, [], Spec.ParseErrorText(err));
    }

    method RunCore(raw: S.DdCmdRaw, io: BenchIO.IO) returns (exit: int)
      modifies if raw.mode == S.Copy && raw.error == S.None
               then {io.stdinRegion as object, io.stdoutRegion, io.stderrRegion}
               else {io.stdoutRegion as object, io.stderrRegion}
      ensures Spec.Spec(raw, io, exit)
    {
      exit := Core.RunCore(raw, io);
      Proof.CoreSummaryImpliesSpec(raw, io, exit);
    }
  }
}
