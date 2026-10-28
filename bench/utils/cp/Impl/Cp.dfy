include "../Spec/CpSpec.dfy"
include "../../../core/StringEscaping.dfy"
include "../../../core/Utf8.dfy"
include "CliSupport.dfy"
include "CpCore.dfy"
include "../Proof/CpProof.dfy"

module Cp {
  // CLI codecs are fixed protocol details, outside the candidate API.
  export
    provides BenchIO, BenchWorld, BenchItem, CliTypes, S, Core, Spec, Proof, CliExtern, CpBenchmarkItem._ctor, CpBenchmarkItem.Name, CpBenchmarkItem.Schema, CpBenchmarkItem.ParseConfig, CpBenchmarkItem.Decode, CpBenchmarkItem.FormatParseError, CpBenchmarkItem.PlanArgv, CpBenchmarkItem.PlanParseFailure, CpBenchmarkItem.RunCore
    reveals CpBenchmarkItem

  import opened ProtocolModel = CpSpec

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
      msg := ProtocolModel.ParseErrorText(err);
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
      return CliTypes.CliEarlyExit(1,[],ProtocolModel.ParseErrorText(e));
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
