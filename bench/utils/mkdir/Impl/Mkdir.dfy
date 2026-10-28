include "../Spec/MkdirSpec.dfy"
include "CliSupport.dfy"
include "MkdirCore.dfy"
include "../Proof/MkdirProof.dfy"

module Mkdir {
  // CLI codecs are fixed protocol details, outside the candidate API.
  export
    provides BenchIO, BenchWorld, BenchItem, CliTypes, CliExtern, S, Core, Spec, Proof, MkdirBenchmarkItem._ctor, MkdirBenchmarkItem.Name, MkdirBenchmarkItem.Schema, MkdirBenchmarkItem.ParseConfig, MkdirBenchmarkItem.Decode, MkdirBenchmarkItem.FormatParseError, MkdirBenchmarkItem.PlanParsed, MkdirBenchmarkItem.PlanParseFailure, MkdirBenchmarkItem.RunCore
    reveals MkdirBenchmarkItem

  import BenchIO
  import BenchWorld
  import BenchItem
  import CliTypes
  import opened CliExtern
  import S = MkdirSchema
  import Core = MkdirCore
  import Spec = MkdirSpec
  import Proof = MkdirProof

  class MkdirBenchmarkItem extends BenchItem.BenchmarkItemTwostate<S.MkdirCmdRaw> {
    constructor() {}

    method Name() returns (name: string) {
      name := "mkdir";
    }

    method Schema() returns (schema: CliTypes.CliSchema) {
      schema := S.Schema();
    }

    method ParseConfig() returns (cfg: CliTypes.ParseConfig) {
      cfg := S.ParserConfig();
    }

    method Decode(parsed: CliTypes.ParsedArgs) returns (raw: S.MkdirCmdRaw) {
      raw := S.Decode(parsed);
    }

    method FormatParseError(err: CliTypes.ParseError) returns (msg: BenchWorld.Bytes) {
      var normalized := err;
      if err.kind == CliTypes.UnknownOption && |err.rawToken| > 1 &&
         err.rawToken[0] == '-' && err.rawToken[1] != '-' {
        var j := 1;
        while j < |err.rawToken| && err.rawToken[j] == 'v'
          invariant 1 <= j <= |err.rawToken|
          decreases |err.rawToken| - j
        {
          j := j + 1;
        }
        if j < |err.rawToken| {
          normalized := CliTypes.ParseError(err.kind, err.tokenIndex,
                                            "-" + err.rawToken[j..]);
        }
      }
      msg := Spec.ParseErrorText(normalized);
    }

    method PlanParsed(parsed: CliTypes.ParsedArgs)
      returns (plan: CliTypes.CliPlan<S.MkdirCmdRaw>)
    {
      var request := S.InformationRequest(parsed);
      if request == CliTypes.RequestHelp {
        plan := CliTypes.CliEarlyExit(0, Spec.HelpTextSpec(), []);
      } else if request == CliTypes.RequestVersion {
        plan := CliTypes.CliEarlyExit(0, Spec.VersionTextSpec(), []);
      } else if |parsed.positionals| == 0 {
        plan := CliTypes.CliEarlyExit(1, [], Spec.MissingOperandText());
      } else {
        var raw := S.Decode(parsed);
        plan := CliTypes.CliRun(raw);
      }
    }

    method PlanParseFailure(e: CliTypes.ParseError, argv: seq<string>)
      returns (plan: CliTypes.CliPlan<S.MkdirCmdRaw>)
    {
      if 0 < e.tokenIndex < |argv| {
        var schema := S.Schema();
        var cfg := S.ParserConfig();
        var result := Cli.Parse(argv[..e.tokenIndex], schema, cfg);
        match result {
          case ParseSuccess(parsed) =>
            var request := S.InformationRequest(parsed);
            if request != CliTypes.RequestNone {
              plan := PlanParsed(parsed);
              return;
            }
          case ParseFailure(_) =>
        }
      }
      var msg := FormatParseError(e);
      plan := CliTypes.CliEarlyExit(1, [], msg);
    }

    method RunCore(raw: S.MkdirCmdRaw, io: BenchIO.IO) returns (exit: int)
      modifies io.fsRegion, io.stdoutRegion, io.stderrRegion
      ensures Spec.Spec(raw, io, exit)
    {
      exit := Core.RunCore(raw, io);
    }
  }

}
