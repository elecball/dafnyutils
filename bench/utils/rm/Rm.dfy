include "../../core/StringEscaping.dfy"
include "../../core/Utf8.dfy"
include "CliSupport.dfy"
include "RmSpec.dfy"
include "RmCore.dfy"
include "RmProof.dfy"

module Rm {
  // CLI codecs are fixed protocol details, outside the candidate API.
  export
    provides BenchIO, BenchWorld, BenchItem, CliTypes, CliExtern, S, Core, Spec, RmBenchmarkItem._ctor, RmBenchmarkItem.Name, RmBenchmarkItem.Schema, RmBenchmarkItem.ParseConfig, RmBenchmarkItem.Decode, RmBenchmarkItem.FormatParseError, RmBenchmarkItem.PlanArgv, RmBenchmarkItem.PlanParseFailure, RmBenchmarkItem.RunCore
    reveals RmBenchmarkItem

  import ProtocolUtf8Model = Utf8Semantics
  import ProtocolEscapingModel = StringEscaping
  import opened ProtocolModel = RmSpec

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
      msg := ProtocolParseErrorText(err,invalidShort);
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
      var message := ProtocolParseDiagnostic(e,invalidShort);
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
            message := message + ProtocolHyphenSuggestion(arg);
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

  function ProtocolSpecCPrintableByte(byte: char): bool
    ensures ProtocolSpecCPrintableByte(byte) == ProtocolEscapingModel.SpecCPrintableByte(byte)
  {
    0x20 <= byte as int <= 0x7e
  }

  function ProtocolSpecOctDigit(value: int): char
    ensures ProtocolSpecOctDigit(value) == ProtocolEscapingModel.SpecOctDigit(value)
  {
    if value == 0 then '0'
    else if value == 1 then '1'
    else if value == 2 then '2'
    else if value == 3 then '3'
    else if value == 4 then '4'
    else if value == 5 then '5'
    else if value == 6 then '6'
    else '7'
  }

  function ProtocolSpecOctalEscape(byte: char): BenchWorld.Bytes
    ensures ProtocolSpecOctalEscape(byte) == ProtocolEscapingModel.SpecOctalEscape(byte)
  {
    var value := byte as int;
    ['\\', ProtocolSpecOctDigit((value / 64) % 8), ProtocolSpecOctDigit((value / 8) % 8), ProtocolSpecOctDigit(value % 8)]
  }

  function ProtocolSpecNamedEscape(byte: char): BenchWorld.Bytes
    ensures ProtocolSpecNamedEscape(byte) == ProtocolEscapingModel.SpecNamedEscape(byte)
  {
    if byte == 7 as char then "\\a"
    else if byte == 8 as char then "\\b"
    else if byte == 12 as char then "\\f"
    else if byte == '\n' then "\\n"
    else if byte == '\r' then "\\r"
    else if byte == '\t' then "\\t"
    else if byte == 11 as char then "\\v"
    else []
  }

  function ProtocolSpecAnsiEscape(byte: char): BenchWorld.Bytes
    ensures ProtocolSpecAnsiEscape(byte) == ProtocolEscapingModel.SpecAnsiEscape(byte)
  {
    var named := ProtocolSpecNamedEscape(byte);
    if named != [] then named else ProtocolSpecOctalEscape(byte)
  }

  function ProtocolSpecNeedsAnsiEscape(byte: char): bool
    ensures ProtocolSpecNeedsAnsiEscape(byte) == ProtocolEscapingModel.SpecNeedsAnsiEscape(byte)
  {
    !ProtocolSpecCPrintableByte(byte)
  }

  function ProtocolSpecCQuoteByte(byte: char): BenchWorld.Bytes
    ensures ProtocolSpecCQuoteByte(byte) == ProtocolEscapingModel.SpecCQuoteByte(byte)
  {
    var named := ProtocolSpecNamedEscape(byte);
    if named != [] then named
    else if byte == '\\' then "\\\\"
    else if byte == '"' then "\\\""
    else if ProtocolSpecCPrintableByte(byte) then [byte]
    else ProtocolSpecOctalEscape(byte)
  }

  function ProtocolSpecCQuoteBytes(bytes: BenchWorld.Bytes): BenchWorld.Bytes
    ensures ProtocolSpecCQuoteBytes(bytes) == ProtocolEscapingModel.SpecCQuoteBytes(bytes)
    decreases |bytes|
  {
    if |bytes| == 0 then
      []
    else
      ProtocolSpecCQuoteByte(bytes[0]) + ProtocolSpecCQuoteBytes(bytes[1..])
  }

  function ProtocolSpecDoubleQuote(bytes: BenchWorld.Bytes): BenchWorld.Bytes
    ensures ProtocolSpecDoubleQuote(bytes) == ProtocolEscapingModel.SpecDoubleQuote(bytes)
  {
    "\"" + ProtocolSpecCQuoteBytes(bytes) + "\""
  }

  function ProtocolSpecShellCompatibleByte(byte: char, atStart: bool, singleton: bool): bool
    ensures ProtocolSpecShellCompatibleByte(byte, atStart, singleton) == ProtocolEscapingModel.SpecShellCompatibleByte(byte, atStart, singleton)
  {
    if byte == '?' || byte == '\\' then
      false
    else if byte == '{' || byte == '}' then
      singleton
    else if byte == '#' || byte == '~' then
      atStart
    else if byte == ' ' || byte == '\'' then
      true
    else if byte == '!' || byte == '"' || byte == '$' || byte == '&' ||
            byte == '(' || byte == ')' || byte == '*' || byte == ';' ||
            byte == '<' || byte == '=' || byte == '>' || byte == '[' ||
            byte == '^' || byte == '`' || byte == '|' then
      false
    else
      ProtocolSpecCPrintableByte(byte)
  }

  function ProtocolSpecShellCompatibleTail(bytes: BenchWorld.Bytes): bool
    ensures ProtocolSpecShellCompatibleTail(bytes) == ProtocolEscapingModel.SpecShellCompatibleTail(bytes)
    decreases |bytes|
  {
    |bytes| == 0 ||
    (ProtocolSpecShellCompatibleByte(bytes[0], false, false) &&
     ProtocolSpecShellCompatibleTail(bytes[1..]))
  }

  function ProtocolSpecAllShellCompatible(bytes: BenchWorld.Bytes): bool
    ensures ProtocolSpecAllShellCompatible(bytes) == ProtocolEscapingModel.SpecAllShellCompatible(bytes)
  {
    |bytes| == 0 ||
    (ProtocolSpecShellCompatibleByte(bytes[0], true, |bytes| == 1) &&
     ProtocolSpecShellCompatibleTail(bytes[1..]))
  }

  function ProtocolSpecContainsApostrophe(bytes: BenchWorld.Bytes): bool
    ensures ProtocolSpecContainsApostrophe(bytes) == ProtocolEscapingModel.SpecContainsApostrophe(bytes)
  {
    '\'' in bytes
  }

  function ProtocolSpecShellEscapeTail(bytes: BenchWorld.Bytes, ansi: bool): BenchWorld.Bytes
    ensures ProtocolSpecShellEscapeTail(bytes, ansi) == ProtocolEscapingModel.SpecShellEscapeTail(bytes, ansi)
    decreases |bytes|
  {
    if |bytes| == 0 then
      "'"
    else
      var byte := bytes[0];
      if byte == '\'' then
        "'\\''" + ProtocolSpecShellEscapeTail(bytes[1..], false)
      else if ProtocolSpecNeedsAnsiEscape(byte) then
        (if ansi then [] else "'$'") + ProtocolSpecAnsiEscape(byte) +
        ProtocolSpecShellEscapeTail(bytes[1..], true)
      else
        (if ansi then "''" else []) + [byte] +
        ProtocolSpecShellEscapeTail(bytes[1..], false)
  }

  function ProtocolSpecQuoteAfBytes(bytes: BenchWorld.Bytes): BenchWorld.Bytes
    ensures ProtocolSpecQuoteAfBytes(bytes) == ProtocolEscapingModel.SpecQuoteAfBytes(bytes)
  {
    if ProtocolSpecContainsApostrophe(bytes) && ProtocolSpecAllShellCompatible(bytes) then
      ProtocolSpecDoubleQuote(bytes)
    else
      "'" + ProtocolSpecShellEscapeTail(bytes, false)
  }

  function ProtocolSpecShellQuoteTriggerByte(byte: char, atStart: bool, singleton: bool): bool
    ensures ProtocolSpecShellQuoteTriggerByte(byte, atStart, singleton) == ProtocolEscapingModel.SpecShellQuoteTriggerByte(byte, atStart, singleton)
  {
    !ProtocolSpecCPrintableByte(byte) ||
    byte == '\\' || byte == '\'' || byte == '?' || byte == ':' ||
    byte == ' ' || byte == '!' || byte == '"' || byte == '$' ||
    byte == '&' || byte == '(' || byte == ')' || byte == '*' ||
    byte == ';' || byte == '<' || byte == '=' || byte == '>' ||
    byte == '[' || byte == '^' || byte == '`' || byte == '|' ||
    ((byte == '#' || byte == '~') && atStart) ||
    ((byte == '{' || byte == '}') && singleton)
  }

  function ProtocolParseDiagnostic(err: CliTypes.ParseError, invalidShort: char): Bytes
    ensures ProtocolParseDiagnostic(err, invalidShort) == ProtocolModel.ParseDiagnostic(err, invalidShort)
  {
    if err.kind == CliTypes.UnknownOption && !CliModel.HasPrefix(err.rawToken,ParseDiagnosticPart1()) && |err.rawToken| > 1 then
      ParseDiagnosticPart2() + [ProtocolEncodeChar(invalidShort)[0]] + ParseDiagnosticPart3()
    else ProtocolEncode(
      if err.kind == CliTypes.UnknownOption then
        if CliModel.HasPrefix(err.rawToken, ParseDiagnosticPart1()) then
          ParseDiagnosticPart4() + err.rawToken + ParseDiagnosticPart3()
        else ParseDiagnosticPart5()
      else if err.kind == CliTypes.UnexpectedValue then
        ParseDiagnosticPart6() + LongOptionName(err.rawToken) + ParseDiagnosticPart7()
      else if err.kind == CliTypes.Ambiguous then
        ParseDiagnosticPart6() + err.rawToken + ParseDiagnosticPart8() +
        (if CliModel.HasPrefix(err.rawToken,ParseDiagnosticPart9()) then
          ParseDiagnosticPart10() +
          ParseDiagnosticPart11() +
          ParseDiagnosticPart12()
         else ParseDiagnosticPart13())
      else ParseDiagnosticPart6() + err.rawToken + ParseDiagnosticPart14())
  }

  function ProtocolParseErrorText(err: CliTypes.ParseError, invalidShort: char): Bytes
    ensures ProtocolParseErrorText(err, invalidShort) == ProtocolModel.ParseErrorText(err, invalidShort)
  {
    ProtocolParseDiagnostic(err,invalidShort) + UsageText()
  }

  function ProtocolHyphenSuggestion(path: Path): Bytes
    ensures ProtocolHyphenSuggestion(path) == ProtocolModel.HyphenSuggestion(path)
  {
    var encoded := ProtocolEncode(path);
    var trigger := exists i: int ::
      0 <= i < |encoded| && encoded[i] != ':' &&
      ProtocolSpecShellQuoteTriggerByte(encoded[i],i == 0,|encoded| == 1);
    var quoted := if trigger then ProtocolSpecQuoteAfBytes(encoded) else encoded;
    HyphenSuggestionPart1() + quoted + HyphenSuggestionPart2() + ProtocolSpecQuoteAfBytes(encoded) + HyphenSuggestionPart3()
  }

}
