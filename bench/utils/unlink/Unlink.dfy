include "../../core/StringEscaping.dfy"
include "CliSupport.dfy"
include "../../core/Utf8.dfy"
include "UnlinkSchema.dfy"
include "UnlinkSpec.dfy"
include "UnlinkCore.dfy"
include "UnlinkProof.dfy"

module Unlink {
  // CLI codecs are fixed protocol details, outside the candidate API.
  export
    provides BenchIO, BenchWorld, BenchItem, CliTypes, Utf8, S, Core, Spec, Proof, CliExtern, UnlinkBenchmarkItem._ctor, UnlinkBenchmarkItem.Name, UnlinkBenchmarkItem.Schema, UnlinkBenchmarkItem.ParseConfig, UnlinkBenchmarkItem.Decode, UnlinkBenchmarkItem.FormatParseError, UnlinkBenchmarkItem.PlanParseFailure, UnlinkBenchmarkItem.RunCore
    reveals UnlinkBenchmarkItem

  import ProtocolUtf8Model = Utf8Semantics
  import ProtocolEscapingModel = StringEscaping
  import opened ProtocolModel = UnlinkSpec

  import BenchIO
  import BenchWorld
  import BenchItem
  import CliTypes
  import Utf8 = Utf8Semantics
  import S = UnlinkSchema
  import Core = UnlinkCore
  import Spec = UnlinkSpec
  import Proof = UnlinkProof
  import opened CliExtern

  class UnlinkBenchmarkItem extends BenchItem.BenchmarkItemTwostate<S.UnlinkCmdRaw> {
    constructor() {}

    method Name() returns (name: string) {
      name := "unlink";
    }

    method Schema() returns (schema: CliTypes.CliSchema) {
      schema := S.Schema();
    }

    method ParseConfig() returns (cfg: CliTypes.ParseConfig) {
      cfg := S.ParserConfig();
    }

    method Decode(parsed: CliTypes.ParsedArgs) returns (raw: S.UnlinkCmdRaw) {
      raw := S.Decode(parsed);
    }

    method FormatParseError(err: CliTypes.ParseError) returns (msg: BenchWorld.Bytes) {
      msg := ProtocolParseErrorText(err);
    }

    method PlanParseFailure(
      e: CliTypes.ParseError,
      argv: seq<string>
    ) returns (plan: CliTypes.CliPlan<S.UnlinkCmdRaw>)
      decreases *
    {
      if 0 < e.tokenIndex && e.tokenIndex < |argv| {
        var s := S.Schema();
        var cfg := S.ParserConfig();
        var result := Cli.Parse(argv[..e.tokenIndex], s, cfg);
        match result {
          case ParseSuccess(parsed) =>
            var raw := S.Decode(parsed);
            if raw.mode == S.ModeHelp || raw.mode == S.ModeVersion {
              plan := CliTypes.CliRun(raw);
              return;
            }
          case ParseFailure(_) =>
        }
      }
      var msg := ProtocolParseErrorText(e);
      plan := CliTypes.CliEarlyExit(1, [], msg);
    }

    method RunCore(raw: S.UnlinkCmdRaw, io: BenchIO.IO) returns (exit: int)
      modifies io.fsRegion, io.stdoutRegion, io.stderrRegion
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

  function ProtocolParseErrorText(err: CliTypes.ParseError): BenchWorld.Bytes
    ensures ProtocolParseErrorText(err) == ProtocolModel.ParseErrorText(err)
  {
    var shortOptionPrefix: string := ParseErrorTextPart4();
    var text: string := if err.kind == CliTypes.UnknownOption then
                          if |err.rawToken| > 2 && err.rawToken[0] == '-' && err.rawToken[1] == '-' then
                            ParseErrorTextPart1() + err.rawToken + ParseErrorTextPart2() +
                            ParseErrorTextPart3()
                          else if |err.rawToken| > 1 && err.rawToken[0] == '-' then
                            shortOptionPrefix + [err.rawToken[1]] + ParseErrorTextPart2() +
                            ParseErrorTextPart3()
                          else
                            ParseErrorTextPart5()
                        else if err.kind == CliTypes.UnexpectedValue then
                          ParseErrorTextPart6() + LongOptionName(err.rawToken) +
                          ParseErrorTextPart7() +
                          ParseErrorTextPart3()
                        else if err.kind == CliTypes.Ambiguous then
                          ParseErrorTextPart6() + err.rawToken + ParseErrorTextPart8() +
                          ParseErrorTextPart3()
                        else
                          ParseErrorTextPart9() +
                          (if err.kind == CliTypes.MissingValue
                           then ParseErrorTextPart10()
                           else ParseErrorTextPart11()) +
                          ParseErrorTextPart12() + err.rawToken + ParseErrorTextPart2();
    ProtocolEncode(text)
  }

}
