include "../../core/StringEscaping.dfy"
include "../../core/Utf8.dfy"
include "CliSupport.dfy"
include "RmdirSpec.dfy"
include "RmdirCore.dfy"
include "RmdirProof.dfy"

module Rmdir {
  // CLI codecs are fixed protocol details, outside the candidate API.
  export
    provides BenchIO, BenchWorld, BenchItem, CliTypes, CliModel, Utf8, S, Core, Spec, CliExtern, RmdirBenchmarkItem._ctor, RmdirBenchmarkItem.Name, RmdirBenchmarkItem.Schema, RmdirBenchmarkItem.ParseConfig, RmdirBenchmarkItem.Decode, RmdirBenchmarkItem.FormatParseError, RmdirBenchmarkItem.NormalizeArgv, RmdirBenchmarkItem.PlanArgv, RmdirBenchmarkItem.PlanParseFailure, RmdirBenchmarkItem.RunCore
    reveals RmdirBenchmarkItem

  import ProtocolUtf8Model = Utf8Semantics
  import ProtocolEscapingModel = StringEscaping
  import opened ProtocolModel = RmdirSpec

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
        msg := Spec.ShortOptionText([ProtocolEncodeChar(ch)[0]]);
      } else {
        msg := ProtocolParseErrorText(e);
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

  function ProtocolParseErrorText(e: CliTypes.ParseError): Bytes
    ensures ProtocolParseErrorText(e) == ProtocolModel.ParseErrorText(e)
  {
    var end := CliModel.FindChar(e.rawToken, '=');
    var name := if end < 0 then e.rawToken else e.rawToken[..end];
    var full := if name in {ParseErrorTextPart1(), ParseErrorTextPart2(), ParseErrorTextPart3(), ParseErrorTextPart4()} then ParseErrorTextPart4()
                else if CliModel.HasPrefix(ParseErrorTextPart5(), name) then ParseErrorTextPart5()
                else if CliModel.HasPrefix(ParseErrorTextPart6(), name) then ParseErrorTextPart6()
                else if CliModel.HasPrefix(ParseErrorTextPart7(), name) then ParseErrorTextPart7()
                else if CliModel.HasPrefix(ParseErrorTextPart8(), name) then ParseErrorTextPart8()
                else if CliModel.HasPrefix(ParseErrorTextPart9(), name) then ParseErrorTextPart9()
                else name;
    if e.kind == CliTypes.UnexpectedValue then
      ParseErrorTextPart10() + ProtocolEncode(full) + ParseErrorTextPart11() +
      ParseErrorTextPart12()
    else if e.kind == CliTypes.Ambiguous then
      ParseErrorTextPart10() + ProtocolEncode(e.rawToken) +
      ParseErrorTextPart13() +
      (if name == ParseErrorTextPart14() then
         ParseErrorTextPart15()
       else ParseErrorTextPart16()) +
      ParseErrorTextPart12()
    else
      ParseErrorTextPart17() + ProtocolEncode(e.rawToken) +
      ParseErrorTextPart18()
  }

}
