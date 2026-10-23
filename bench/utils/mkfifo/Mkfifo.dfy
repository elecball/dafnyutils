include "MkfifoSpec.dfy"
include "CliSupport.dfy"
include "MkfifoCore.dfy"
include "MkfifoProof.dfy"

module Mkfifo {
  // CLI codecs are fixed protocol details, outside the candidate API.
  export
    provides BenchIO, BenchWorld, BenchItem, CliTypes, CliExtern, S, Core, Spec, Proof, MkfifoBenchmarkItem._ctor, MkfifoBenchmarkItem.Name, MkfifoBenchmarkItem.Schema, MkfifoBenchmarkItem.ParseConfig, MkfifoBenchmarkItem.Decode, MkfifoBenchmarkItem.FormatParseError, MkfifoBenchmarkItem.PlanParsed, MkfifoBenchmarkItem.PlanParseFailure, MkfifoBenchmarkItem.RunCore
    reveals MkfifoBenchmarkItem

  import BenchIO
  import BenchWorld
  import BenchItem
  import CliTypes
  import opened CliExtern
  import S = MkfifoSchema
  import Core = MkfifoCore
  import Spec = MkfifoSpec
  import Proof = MkfifoProof

  class MkfifoBenchmarkItem extends BenchItem.BenchmarkItemTwostate<S.MkfifoCmdRaw> {
    constructor() {}

    method Name() returns (name: string) {
      name := "mkfifo";
    }

    method Schema() returns (schema: CliTypes.CliSchema) {
      schema := S.Schema();
    }

    method ParseConfig() returns (cfg: CliTypes.ParseConfig) {
      cfg := S.ParserConfig();
    }

    method Decode(parsed: CliTypes.ParsedArgs) returns (raw: S.MkfifoCmdRaw) {
      raw := S.Decode(parsed);
    }

    method FormatParseError(err: CliTypes.ParseError) returns (msg: BenchWorld.Bytes) {
      msg := Spec.ParseErrorText(err);
    }

    // GNU handles --help/--version as soon as getopt reaches them, then reports
    // a missing operand; MODE is checked only after that.
    method PlanParsed(parsed: CliTypes.ParsedArgs)
      returns (plan: CliTypes.CliPlan<S.MkfifoCmdRaw>)
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

    // An earlier --help/--version wins over a later parse error, as in getopt.
    method PlanParseFailure(e: CliTypes.ParseError, argv: seq<string>)
      returns (plan: CliTypes.CliPlan<S.MkfifoCmdRaw>)
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

    method RunCore(raw: S.MkfifoCmdRaw, io: BenchIO.IO) returns (exit: int)
      modifies io.fsRegion, io.stderrRegion
      ensures Spec.Spec(raw, io, exit)
    {
      exit := Core.RunCore(raw, io);
    }
  }
}
