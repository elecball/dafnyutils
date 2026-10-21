include "RmSpec.dfy"
include "CliSupport.dfy"
include "RmCore.dfy"
include "RmProof.dfy"

module Rm {
  // CLI codecs are fixed protocol details, outside the candidate API.
  export
    provides BenchIO, BenchWorld, BenchItem, CliTypes, CliExtern, S, Core, Spec, RmBenchmarkItem._ctor, RmBenchmarkItem.Name, RmBenchmarkItem.Schema, RmBenchmarkItem.ParseConfig, RmBenchmarkItem.Decode, RmBenchmarkItem.FormatParseError, RmBenchmarkItem.PlanArgv, RmBenchmarkItem.PlanParseFailure, RmBenchmarkItem.RunCore
    reveals RmBenchmarkItem

  import BenchIO
  import opened BenchWorld
  import BenchItem
  import CliTypes
  import opened CliExtern
  import S = RmSchema
  import Core = RmCore
  import Spec = RmSpec

  class RmBenchmarkItem extends BenchItem.BenchmarkItemTwostate<S.RmCmdRaw> {
    constructor() {}

    method Name() returns (name: string) {
      name := "rm";
    }

    method Schema() returns (schema: CliTypes.CliSchema) {
      schema := S.Schema();
    }

    method ParseConfig() returns (cfg: CliTypes.ParseConfig) {
      cfg := S.ParserConfig();
    }

    method Decode(parsed: CliTypes.ParsedArgs) returns (raw: S.RmCmdRaw) {
      raw := S.Decode(parsed);
    }

    method FormatParseError(err: CliTypes.ParseError) returns (msg: BenchWorld.Bytes) {
      var invalidShort := S.InvalidShortCharacter(err.rawToken);
      msg := Spec.ParseErrorText(err,invalidShort);
    }

    method PlanArgv(argv: seq<string>) returns (plan: CliTypes.CliPlan<S.RmCmdRaw>)
    {
      var result := S.ParseArgs(argv);
      if result.ParseFailure? { plan := PlanParseFailure(result.error,argv); }
      else {
        var raw := S.Decode(result.parsed);
        plan := CliTypes.CliRun(raw);
      }
    }

    method PlanParseFailure(e: CliTypes.ParseError, argv: seq<string>)
      returns (plan: CliTypes.CliPlan<S.RmCmdRaw>)
    {
      if 0 < e.tokenIndex && e.tokenIndex < |argv| {
        var result := S.ParseArgs(argv[..e.tokenIndex]);
        if result.ParseSuccess? {
          var raw := S.Decode(result.parsed);
          if raw.mode != S.ModeRun && raw.mode != S.ModeInteractive {
            plan := CliTypes.CliRun(raw);
            return;
          }
        }
      }
      var invalidShort := S.InvalidShortCharacter(e.rawToken);
      var message := Spec.ParseDiagnostic(e,invalidShort);
      var io := BenchIO.Process();
      var i := 1;
      while i < |argv|
        invariant 0 <= i <= |argv|+1
        decreases |argv|-i
      {
        var arg := argv[i];
        if |arg| > 1 && arg[0] == '-' {
          var existsResult := io.PathExists(arg,false);
          if existsResult.Ok? {
            message := message + Spec.HyphenSuggestion(arg);
            break;
          }
        }
        i := i+1;
      }
      plan := CliTypes.CliEarlyExit(1,[],message + Spec.UsageText());
    }

    method RunCore(raw: S.RmCmdRaw, io: BenchIO.IO) returns (exit: int)
      modifies io.fsRegion, io.stdoutRegion, io.stderrRegion, io.dirHandlesRegion
      ensures Spec.Spec(raw, io, exit)
    {
      exit := Core.RunCore(raw, io);
    }
  }

}
