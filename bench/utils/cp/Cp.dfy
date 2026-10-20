include "../../core/BenchmarkItem.dfy"
include "CpSpec.dfy"
include "CpCore.dfy"
include "CpProof.dfy"

module Cp {
  import BenchIO
  import BenchWorld
  import BenchItem
  import CliTypes
  import S = CpSchema
  import Core = CpCore
  import Spec = CpSpec
  import Proof = CpProof
  import opened CliExtern

  class CpBenchmarkItem extends BenchItem.BenchmarkItemTwostate<S.CpCmdRaw> {
    constructor() {}

    method Name() returns (name: string) {
      name := "cp";
    }

    method Schema() returns (schema: CliTypes.CliSchema) {
      schema := S.Schema();
    }

    method ParseConfig() returns (cfg: CliTypes.ParseConfig) {
      cfg := S.ParserConfig();
    }

    method Decode(parsed: CliTypes.ParsedArgs) returns (raw: S.CpCmdRaw) {
      raw := S.Decode(parsed);
    }

    method FormatParseError(err: CliTypes.ParseError) returns (msg: BenchWorld.Bytes) {
      msg := Spec.ParseErrorText(err);
    }

    method PlanArgv(argv: seq<string>) returns (plan: CliTypes.CliPlan<S.CpCmdRaw>) {
      var result := S.ParseArgs(argv);
      match result {
        case ParseSuccess(parsed) =>
          var raw := S.Decode(parsed);
          plan := CliTypes.CliRun(raw);
        case ParseFailure(error) =>
          plan := PlanParseFailure(error,argv);
      }
    }

    method PlanParseFailure(e: CliTypes.ParseError, argv: seq<string>)
        returns (plan: CliTypes.CliPlan<S.CpCmdRaw>)
    {
      if 0 < e.tokenIndex && e.tokenIndex < |argv| {
        var result := S.ParseArgs(argv[..e.tokenIndex]);
        match result {
          case ParseSuccess(parsed) =>
            var raw := S.Decode(parsed);
            if raw.mode == S.Help || raw.mode == S.Version {
              return CliTypes.CliRun(raw);
            }
          case ParseFailure(_) =>
        }
      }
      return CliTypes.CliEarlyExit(1,[],Spec.ParseErrorText(e));
    }

    method RunCore(raw: S.CpCmdRaw, io: BenchIO.IO) returns (exit: int)
      modifies io.fsRegion, io.dirHandlesRegion, io.stdoutRegion, io.stderrRegion
      ensures Spec.Spec(raw, io, exit)
    {
      exit := Core.RunCore(raw, io);
      Proof.CoreSummaryImpliesSpec(raw, io, exit);
    }
  }
}
