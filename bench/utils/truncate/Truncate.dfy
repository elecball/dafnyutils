include "../../core/StringEscaping.dfy"
include "../../core/Utf8.dfy"
include "CliSupport.dfy"
include "TruncateCore.dfy"

module Truncate {
  // CLI codecs are fixed protocol details, outside the candidate API.
  export
    provides BenchItem, BenchIO, BenchWorld, CliTypes, CliExtern, S, Spec, Core, InvalidShortCharacter, TruncateBenchmarkItem._ctor, TruncateBenchmarkItem.Name, TruncateBenchmarkItem.Schema, TruncateBenchmarkItem.ParseConfig, TruncateBenchmarkItem.Decode, TruncateBenchmarkItem.FormatParseError, TruncateBenchmarkItem.PlanParseFailure, TruncateBenchmarkItem.RunCore
    reveals TruncateBenchmarkItem

  import ProtocolUtf8Model = Utf8Semantics
  import ProtocolEscapingModel = StringEscaping
  import opened ProtocolModel = TruncateSpec

  import BenchItem
  import BenchIO
  import BenchWorld
  import CliTypes
  import opened CliExtern
  import S = TruncateSchema
  import Spec = TruncateSpec
  import Core = TruncateCore

  method InvalidShortCharacter(text: string) returns (character: char)
    ensures Spec.UnknownShortRelation(text, character)
  {
    var index := 0;
    while index < |text| && text[index] in {'c', 'o'}
      invariant 0 <= index <= |text|
      invariant forall i :: 0 <= i < index ==> text[i] in {'c', 'o'}
      decreases |text| - index
    {
      index := index + 1;
    }
    character := if index == |text| then '?' else text[index];
  }

  class TruncateBenchmarkItem extends BenchItem.BenchmarkItemTwostate<S.TruncateCmdRaw> {
    constructor() {}
    method Name() returns (name: string) { name := "truncate"; }
    method Schema() returns (schema: CliTypes.CliSchema) { schema := S.Schema(); }
    method ParseConfig() returns (cfg: CliTypes.ParseConfig) { cfg := S.ParserConfig(); }
    method Decode(parsed: CliTypes.ParsedArgs) returns (raw: S.TruncateCmdRaw) { raw := S.Decode(parsed); }
    method FormatParseError(error: CliTypes.ParseError) returns (message: BenchWorld.Bytes) {
      var invalidShort := '?';
      if |error.rawToken| > 1 {
        invalidShort := InvalidShortCharacter(error.rawToken[1..]);
      }
      message := ProtocolParseErrorText(error, invalidShort);
    }
    method PlanParseFailure(error: CliTypes.ParseError, argv: seq<string>)
      returns (plan: CliTypes.CliPlan<S.TruncateCmdRaw>)
    {
      var message := FormatParseError(error);
      if 0 < error.tokenIndex < |argv| {
        var schema := S.Schema();
        var config := S.ParserConfig();
        var result := Cli.Parse(argv[..error.tokenIndex], schema, config);
        if result.ParseSuccess? {
          var raw := S.Decode(result.parsed);
          plan := CliTypes.CliRun(raw.(parseError := message));
          return;
        }
      }
      plan := CliTypes.CliEarlyExit(1, [], message);
    }
    method RunCore(raw: S.TruncateCmdRaw, io: BenchIO.IO) returns (exit: int)
      modifies io.fsRegion, io.statusObservationsRegion, io.stdoutRegion, io.stderrRegion
      ensures Spec.Spec(raw, io, exit)
    { exit := Core.RunCore(raw, io); }
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

  function ProtocolParseErrorText(err: CliTypes.ParseError, invalidShort: char): W.Bytes
    requires |err.rawToken| > 1 ==> UnknownShortRelation(err.rawToken[1..], invalidShort)
    ensures ProtocolParseErrorText(err, invalidShort) == ProtocolModel.ParseErrorText(err, invalidShort)
  {
    var long := |err.rawToken| > 2 && err.rawToken[0] == '-' && err.rawToken[1] == '-';
    var detail :=
      if err.kind == CliTypes.MissingValue then
        (if long then
           ParseErrorTextPart1() + ProtocolEncode(LongOption(err.rawToken)) + ParseErrorTextPart2()
         else
           ParseErrorTextPart3() +
           (if |err.rawToken| > 1 then ProtocolEncode([err.rawToken[|err.rawToken| - 1]]) else []) + ParseErrorTextPart4())
      else if err.kind == CliTypes.Ambiguous then
        ParseErrorTextPart1() + ProtocolEncode(err.rawToken) +
        ParseErrorTextPart5()
      else if err.kind == CliTypes.UnexpectedValue then
        ParseErrorTextPart1() + ProtocolEncode(LongOption(err.rawToken)) + ParseErrorTextPart6()
      else if long then
        ParseErrorTextPart7() + ProtocolEncode(err.rawToken) + ParseErrorTextPart4()
      else
        ParseErrorTextPart8() +
        (if |err.rawToken| > 1 then ProtocolEncodeChar(invalidShort)[..1] else []) + ParseErrorTextPart4();
    detail + UsageHint()
  }

}
