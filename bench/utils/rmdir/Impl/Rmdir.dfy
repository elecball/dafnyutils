include "../../../core/Utf8.dfy"
include "../Spec/RmdirSpec.dfy"
include "CliSupport.dfy"
include "RmdirCore.dfy"
include "../Proof/RmdirProof.dfy"

module Rmdir {
  // CLI codecs are fixed protocol details, outside the candidate API.
  export
    provides BenchIO, BenchWorld, BenchItem, CliTypes, CliModel, Utf8, S, Core, Spec, CliExtern, RmdirBenchmarkItem._ctor, RmdirBenchmarkItem.Name, RmdirBenchmarkItem.Schema, RmdirBenchmarkItem.ParseConfig, RmdirBenchmarkItem.Decode, RmdirBenchmarkItem.FormatParseError, RmdirBenchmarkItem.NormalizeArgv, RmdirBenchmarkItem.PlanArgv, RmdirBenchmarkItem.PlanParseFailure, RmdirBenchmarkItem.RunCore
    reveals RmdirBenchmarkItem

  import BenchIO
  import opened BenchWorld
  import BenchItem
  import CliTypes
  import CliModel
  import Utf8 = Utf8Semantics
  import S = RmdirSchema
  import Core = RmdirCore
  import Spec = RmdirSpec
  import opened CliExtern

  class RmdirBenchmarkItem extends BenchItem.BenchmarkItemTwostate<S.RmdirCmdRaw> {
    constructor() {}

    method Name() returns (name: string) {
      name := "rmdir";
    }

    method Schema() returns (schema: CliTypes.CliSchema) {
      schema := S.Schema();
    }

    method ParseConfig() returns (cfg: CliTypes.ParseConfig) {
      cfg := S.ParserConfig();
    }

    method Decode(parsed: CliTypes.ParsedArgs) returns (raw: S.RmdirCmdRaw) {
      raw := S.Decode(parsed);
    }

    method FormatParseError(e: CliTypes.ParseError) returns (msg: BenchWorld.Bytes) {
      if e.kind == CliTypes.UnknownOption && |e.rawToken| > 1 &&
         e.rawToken[0] == '-' && e.rawToken[1] != '-' {
        var i := 1;
        while i < |e.rawToken| && e.rawToken[i] in {'p', 'v'}
          invariant 1 <= i <= |e.rawToken|
          decreases |e.rawToken| - i
        { i := i + 1; }
        var ch := if i < |e.rawToken| then e.rawToken[i] else e.rawToken[1];
        msg := Spec.ShortOptionText([Utf8.EncodeChar(ch)[0]]);
      } else {
        msg := Spec.ParseErrorText(e);
      }
    }
    method NormalizeArgv(argv: seq<string>) returns (normalized: seq<string>)
    {
      normalized := argv;
      var i := 1;
      var options := true;
      while i < |argv|
        invariant |normalized| == |argv|
        decreases |argv| - i
      {
        var token := argv[i];
        if options && token == "--" { options := false; }
        if options {
          var eq := CliModel.FindChar(token, '=');
          var name := if eq < 0 then token else token[..eq];
          if name in {"--p", "--pa", "--pat", "--path"} {
            normalized := normalized[i := "--parents" + (if eq < 0 then "" else token[eq..])];
          }
        }
        i := i + 1;
      }
    }

    method PlanArgv(argv: seq<string>) returns (plan: CliTypes.CliPlan<S.RmdirCmdRaw>)
      decreases *
    {
      var schema := S.Schema();
      var cfg := S.ParserConfig();
      var normalized := NormalizeArgv(argv);
      var parsed := Cli.Parse(normalized, schema, cfg);
      match parsed {
        case ParseSuccess(value) =>
          var raw := S.Decode(value);
          plan := CliTypes.CliRun(raw);
        case ParseFailure(error) =>
          var e := error;
          if 0 <= e.tokenIndex < |argv| {
            e := e.(rawToken := argv[e.tokenIndex]);
          }
          plan := PlanParseFailure(e, argv);
      }
    }

    method PlanParseFailure(e: CliTypes.ParseError, argv: seq<string>)
      returns (plan: CliTypes.CliPlan<S.RmdirCmdRaw>)
      decreases *
    {
      if 0 < e.tokenIndex < |argv| {
        var schema := S.Schema();
        var cfg := S.ParserConfig();
        var prefix := NormalizeArgv(argv[..e.tokenIndex]);
        var parsed := Cli.Parse(prefix, schema, cfg);
        match parsed {
          case ParseSuccess(value) =>
            var raw := S.Decode(value);
            if raw.mode != S.ModeRun {
              return CliTypes.CliRun(raw);
            }
          case ParseFailure(_) =>
        }
      }
      var msg := FormatParseError(e);
      plan := CliTypes.CliEarlyExit(1, [], msg);
    }

    method RunCore(raw: S.RmdirCmdRaw, io: BenchIO.IO) returns (exit: int)
      modifies if raw.mode != S.ModeRun || |raw.operands| == 0
               then {io.stdoutRegion as object, io.stderrRegion}
               else {io.fsRegion, io.stdoutRegion, io.stderrRegion, io.dirHandlesRegion}
      ensures Spec.Spec(raw, io, exit)
    {
      exit := Core.RunCore(raw, io);
    }
  }

}
