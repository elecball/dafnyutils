include "../../core/StringEscaping.dfy"
include "../../core/Utf8.dfy"
include "CliSupport.dfy"
include "MkdirSpec.dfy"
include "MkdirCore.dfy"
include "MkdirProof.dfy"

module Mkdir {
  // CLI codecs are fixed protocol details, outside the candidate API.
  export
    provides BenchIO, BenchWorld, BenchItem, CliTypes, CliExtern, S, Core, Spec, Proof, MkdirBenchmarkItem._ctor, MkdirBenchmarkItem.Name, MkdirBenchmarkItem.Schema, MkdirBenchmarkItem.ParseConfig, MkdirBenchmarkItem.Decode, MkdirBenchmarkItem.FormatParseError, MkdirBenchmarkItem.PlanParsed, MkdirBenchmarkItem.PlanParseFailure, MkdirBenchmarkItem.RunCore
    reveals MkdirBenchmarkItem

  import ProtocolUtf8Model = Utf8Semantics
  import ProtocolEscapingModel = StringEscaping
  import opened ProtocolModel = MkdirSpec

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
      msg := ProtocolParseErrorText(normalized);
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

  function ProtocolParseErrorText(err: CliTypes.ParseError): BenchWorld.Bytes
    ensures ProtocolParseErrorText(err) == ProtocolModel.ParseErrorText(err)
  {
    if err.kind == CliTypes.UnknownOption then
      if |err.rawToken| > 2 && err.rawToken[0] == '-' && err.rawToken[1] == '-' then
        ParseErrorTextPart1() + ProtocolEncode(err.rawToken) + ParseErrorTextPart2() +
        ParseErrorTextPart3()
      else if |err.rawToken| > 1 && err.rawToken[0] == '-' then
        UnknownShortText(ProtocolEncodeChar(err.rawToken[1])[0])
      else
        ParseErrorTextPart4()
    else if err.kind == CliTypes.UnexpectedValue then
      ParseErrorTextPart5() + ProtocolEncode(LongOptionName(err.rawToken)) +
      ParseErrorTextPart6() +
      ParseErrorTextPart3()
    else if err.kind == CliTypes.Ambiguous then
      ParseErrorTextPart5() + ProtocolEncode(err.rawToken) +
      ParseErrorTextPart7() +
      (if |err.rawToken| > 2 && err.rawToken[2] == '=' then
         ParseErrorTextPart8()
       else ParseErrorTextPart9()) +
      ParseErrorTextPart3()
    else
      ParseErrorTextPart10() + ProtocolEncode(
        (if err.kind == CliTypes.MissingValue
         then ParseErrorTextPart11()
         else ParseErrorTextPart12())) +
      ParseErrorTextPart13() + ProtocolEncode(err.rawToken) + ParseErrorTextPart2()
  }

}
