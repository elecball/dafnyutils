include "../../core/StringEscaping.dfy"
include "../../core/Utf8.dfy"
include "CliSupport.dfy"
include "CpSpec.dfy"
include "CpCore.dfy"
include "CpProof.dfy"

module Cp {
  // CLI codecs are fixed protocol details, outside the candidate API.
  export
    provides BenchIO, BenchWorld, BenchItem, CliTypes, S, Core, Spec, Proof, CliExtern, CpBenchmarkItem._ctor, CpBenchmarkItem.Name, CpBenchmarkItem.Schema, CpBenchmarkItem.ParseConfig, CpBenchmarkItem.Decode, CpBenchmarkItem.FormatParseError, CpBenchmarkItem.PlanArgv, CpBenchmarkItem.PlanParseFailure, CpBenchmarkItem.RunCore
    reveals CpBenchmarkItem

  import ProtocolUtf8Model = Utf8Semantics
  import ProtocolEscapingModel = StringEscaping
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
      msg := ProtocolParseErrorText(err);
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
      return CliTypes.CliEarlyExit(1,[],ProtocolParseErrorText(e));
    }

    method RunCore(raw: S.CpCmdRaw, io: BenchIO.IO) returns (exit: int)
      modifies io.fsRegion, io.dirHandlesRegion, io.stdoutRegion, io.stderrRegion
      ensures Spec.Spec(raw, io, exit)
    {
      exit := Core.RunCore(raw, io);
      Proof.CoreSummaryImpliesSpec(raw, io, exit);
    }
  }
  function ProtocolEncodeChar(ch: char): BenchWorld.Bytes
    ensures ProtocolEncodeChar(ch) == ProtocolUtf8Model.EncodeChar(ch)
    ensures |ProtocolEncodeChar(ch)| == BenchWorld.Utf8ByteWidth(ch)
    ensures 1 <= |ProtocolEncodeChar(ch)| <= 4
  {
    var code := ch as int;
    if code <= 0x7f then
      [code as char]
    else if code <= 0x7ff then
      [
        (0xc0 + code / 0x40) as char,
        (0x80 + code % 0x40) as char
      ]
    else if code <= 0xffff then
      [
        (0xe0 + code / 0x1000) as char,
        (0x80 + (code / 0x40) % 0x40) as char,
        (0x80 + code % 0x40) as char
      ]
    else
      [
        (0xf0 + code / 0x40000) as char,
        (0x80 + (code / 0x1000) % 0x40) as char,
        (0x80 + (code / 0x40) % 0x40) as char,
        (0x80 + code % 0x40) as char
      ]
  }

  function ProtocolEncode(text: string): BenchWorld.Bytes
    ensures ProtocolEncode(text) == ProtocolUtf8Model.Encode(text)
    ensures |ProtocolEncode(text)| >= |text|
    decreases |text|
  {
    if text == [] then [] else ProtocolEncodeChar(text[0]) + ProtocolEncode(text[1..])
  }

  function ProtocolParseErrorText(error: CliTypes.ParseError): BW.Bytes
    ensures ProtocolParseErrorText(error) == ProtocolModel.ParseErrorText(error)
  {
    if error.kind == CliTypes.UnknownOption then
      if |error.rawToken| > 2 && error.rawToken[..2] == ParseErrorTextPart1() then
        ParseErrorTextPart2() + ProtocolEncode(error.rawToken) + ParseErrorTextPart3() + Hint()
      else if |error.rawToken| > 1 then
        ParseErrorTextPart4() + [ProtocolEncodeChar(error.rawToken[1])[0]] + ParseErrorTextPart3() + Hint()
      else ParseErrorTextPart5() + Hint()
    else if error.kind == CliTypes.MissingValue then
      if |error.rawToken| > 2 && error.rawToken[..2] == ParseErrorTextPart1() then
        ParseErrorTextPart6() + ProtocolEncode(error.rawToken) + ParseErrorTextPart7() + Hint()
      else if |error.rawToken| > 1 then
        ParseErrorTextPart8() + [ProtocolEncodeChar(error.rawToken[|error.rawToken|-1])[0]] + ParseErrorTextPart3() + Hint()
      else ParseErrorTextPart9() + Hint()
    else if error.kind == CliTypes.UnexpectedValue then
      ParseErrorTextPart6() + ProtocolEncode(LongOption(error.rawToken)) + ParseErrorTextPart10() + Hint()
    else ParseErrorTextPart6() + ProtocolEncode(error.rawToken) + ParseErrorTextPart11() + Hint()
  }

}
