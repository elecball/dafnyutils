include "CliSupport.dfy"
include "TsortSpec.dfy"
include "TsortCore.dfy"
include "TsortProof.dfy"

module Tsort {
  import BenchIO
  import BenchWorld
  import BenchItem
  import CliTypes
  import opened CliExtern
  import S = TsortSchema
  import Core = TsortCore
  import Spec = TsortSpec

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
      msg := Spec.ParseErrorText(err);
    }

    method PlanParseFailure(err: CliTypes.ParseError, argv: seq<string>)
      returns (plan: CliTypes.CliPlan<S.TsortCmdRaw>)
      decreases *
    {
      if 0 < err.tokenIndex < |argv| {
        var schema := S.Schema();
        var cfg := S.ParserConfig();
        var result := Cli.Parse(argv[..err.tokenIndex], schema, cfg);
        if result.ParseSuccess? {
          var raw := S.Decode(result.parsed);
          if raw.mode == S.ModeHelp || raw.mode == S.ModeVersion {
            plan := CliTypes.CliRun(raw);
            return;
          }
        }
      }
      plan := CliTypes.CliEarlyExit(1, [], Spec.ParseErrorText(err));
    }

    method RunCore(raw: S.TsortCmdRaw, io: BenchIO.IO) returns (exit: int)
      modifies (if raw.mode == S.ModeRun && Spec.InputPath(raw) == "-" then {io.stdinRegion} else {}),
               io.stdoutRegion, io.stderrRegion
      ensures Spec.Spec(raw, io, exit)
    {
      exit := Core.RunCore(raw, io);
    }
  }
}
