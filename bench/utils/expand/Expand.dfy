include "../../core/StringEscaping.dfy"
include "../../core/Utf8.dfy"
include "../../core/World.dfy"
include "../../core/CliTypes.dfy"
include "CliSupport.dfy"
include "ExpandSchema.dfy"
include "ExpandCore.dfy"
include "ExpandSpec.dfy"
include "ExpandProof.dfy"

module Expand {
  // CLI codecs are fixed protocol details, outside the candidate API.
  export
    provides BenchIO, BenchWorld, CliTypes, CliExtern, BenchItem, S, Core, Proof, ES, ExpandBenchmarkItem._ctor, ExpandBenchmarkItem.Name, ExpandBenchmarkItem.Schema, ExpandBenchmarkItem.ParseConfig, ExpandBenchmarkItem.Decode, ExpandBenchmarkItem.FormatParseError, ExpandBenchmarkItem.PlanParseFailure, ExpandBenchmarkItem.RunCore
    reveals FixedIsDigit, FixedMaxColumn, FixedDigitValue, FixedParseNatFrom, FixedParsePositiveNat, FixedIsSeparator, FixedIsMarker, FixedMarkerOf, FixedFindTokenEnd, FixedFindDigitsEnd, FixedCombineDiagnostics, FixedSyntaxDiagnosticsFrom, FixedSyntaxDiagnostics, FixedScanMarkers, FixedCommitTabValue, FixedParseTabPart, FixedParseTabTextFrom, FixedParseTabArgsFrom, FixedHelpBeforeOther, FixedVersionBeforeInvalid, FixedRequestTokenIndex, FixedScanCommandOptions, ExpandBenchmarkItem

  import ProtocolUtf8Model = Utf8Semantics
  import ProtocolEscapingModel = StringEscaping
  import opened ProtocolModel = ExpandSpec

  import BenchIO
  import BenchWorld
  import CliTypes
  import CliExtern
  import BenchItem
  import S = ExpandSchema
  import Core = ExpandCore
  import Proof = ExpandProof
  import ES = ExpandSpec

  function FixedIsDigit(ch: char): bool
  {
    '0' <= ch <= '9'
  }

  function FixedMaxColumn(): nat
  {
    9223372036854775807
  }

  function FixedDigitValue(ch: char): nat
    requires FixedIsDigit(ch)
  {
    ((ch as int) - ('0' as int)) as nat
  }

  function FixedParseNatFrom(text: string, i: nat, acc: nat): S.NatParse
    requires i <= |text|
    decreases |text| - i
  {
    if i == |text| then
      S.NatOk(acc)
    else if !FixedIsDigit(text[i]) then
      S.NatErr
    else if acc > (FixedMaxColumn() - FixedDigitValue(text[i])) / 10 then
      S.NatErr
    else
      FixedParseNatFrom(text, i + 1, acc * 10 + FixedDigitValue(text[i]))
  }

  function FixedParsePositiveNat(text: string): S.NatParse
  {
    if |text| == 0 then S.NatErr else FixedParseNatFrom(text, 0, 0)
  }

  function FixedIsSeparator(ch: char): bool
  {
    ch == ',' || ch == ' ' || ch == '\t'
  }

  function FixedIsMarker(ch: char): bool
  {
    ch == '+' || ch == '/'
  }

  function FixedMarkerOf(ch: char): S.MarkerKind
    requires FixedIsMarker(ch)
  {
    if ch == '+' then S.MarkerPlus else S.MarkerSlash
  }

  function FixedFindTokenEnd(text: string, start: nat): nat
    requires start <= |text|
    ensures start <= FixedFindTokenEnd(text, start) <= |text|
    decreases |text| - start
  {
    if start == |text| || FixedIsSeparator(text[start]) then
      start
    else
      FixedFindTokenEnd(text, start + 1)
  }

  function FixedFindDigitsEnd(text: string, start: nat): nat
    requires start <= |text|
    ensures start <= FixedFindDigitsEnd(text, start) <= |text|
    decreases |text| - start
  {
    if start == |text| || !FixedIsDigit(text[start]) then
      start
    else
      FixedFindDigitsEnd(text, start + 1)
  }

  function FixedCombineDiagnostics(first: BenchWorld.Bytes, rest: BenchWorld.Bytes): BenchWorld.Bytes
  {
    if rest == "" then first else first + "\nexpand: " + rest
  }

  function FixedSyntaxDiagnosticsFrom(
    text: string,
    i: nat,
    haveValue: bool,
    numberStart: nat,
    value: nat
  ): BenchWorld.Bytes
    requires i <= |text|
    requires !haveValue || numberStart <= i
    decreases |text| - i
  {
    if i == |text| then
      ""
    else if FixedIsSeparator(text[i]) then
      FixedSyntaxDiagnosticsFrom(text, i + 1, false, 0, 0)
    else if FixedIsMarker(text[i]) then
      var rest := FixedSyntaxDiagnosticsFrom(
                    text, i + 1, haveValue, numberStart, value
                  );
      if haveValue then
        FixedCombineDiagnostics(
          ES.MarkerNotAtStartMessage(FixedMarkerOf(text[i]), text[i..]),
          rest
        )
      else
        rest
    else if FixedIsDigit(text[i]) then
      var start := if haveValue then numberStart else i;
      var accumulated := if haveValue then value else 0;
      var digit := FixedDigitValue(text[i]);
      if accumulated > (FixedMaxColumn() - digit) / 10 then
        var end := FixedFindDigitsEnd(text, i);
        FixedCombineDiagnostics(
          ES.TooLargeMessage(text[start..end]),
          FixedSyntaxDiagnosticsFrom(text, end, true, start, accumulated)
        )
      else
        FixedSyntaxDiagnosticsFrom(
          text, i + 1, true, start, accumulated * 10 + digit
        )
    else
      ES.InvalidCharacterMessage(text[i..])
  } by method {
    return
      if i == |text| then
      ""
    else if FixedIsSeparator(text[i]) then
      FixedSyntaxDiagnosticsFrom(text, i + 1, false, 0, 0)
    else if FixedIsMarker(text[i]) then
      var rest := FixedSyntaxDiagnosticsFrom(
                    text, i + 1, haveValue, numberStart, value
                  );
      if haveValue then
        FixedCombineDiagnostics(
          ProtocolMarkerNotAtStartMessage(FixedMarkerOf(text[i]), text[i..]),
          rest
        )
      else
        rest
    else if FixedIsDigit(text[i]) then
      var start := if haveValue then numberStart else i;
      var accumulated := if haveValue then value else 0;
      var digit := FixedDigitValue(text[i]);
      if accumulated > (FixedMaxColumn() - digit) / 10 then
        var end := FixedFindDigitsEnd(text, i);
        FixedCombineDiagnostics(
          ProtocolTooLargeMessage(text[start..end]),
          FixedSyntaxDiagnosticsFrom(text, end, true, start, accumulated)
        )
      else
        FixedSyntaxDiagnosticsFrom(
          text, i + 1, true, start, accumulated * 10 + digit
        )
    else
      ProtocolInvalidCharacterMessage(text[i..]);
  }

  function FixedSyntaxDiagnostics(text: string): BenchWorld.Bytes
  {
    FixedSyntaxDiagnosticsFrom(text, 0, false, 0, 0)
  }

  function FixedScanMarkers(
    part: string,
    i: nat,
    marker: S.MarkerKind,
    hasMarker: bool
  ): S.MarkerScan
    requires i <= |part|
    ensures i <= FixedScanMarkers(part, i, marker, hasMarker).index <= |part|
    decreases |part| - i
  {
    if i == |part| || !FixedIsMarker(part[i]) then
      S.MarkerScan(i, marker, hasMarker)
    else
      FixedScanMarkers(part, i + 1, FixedMarkerOf(part[i]), true)
  }

  function FixedCommitTabValue(
    acc: S.TabAccum,
    marker: S.MarkerKind,
    value: nat
  ): S.TabAccumParse
  {
    if marker == S.MarkerSlash then
      if acc.extendSize != 0 then
        S.TabAccumErr(ES.RepeatOnlyLastMessage(S.MarkerSlash))
      else
        S.TabAccumOk(S.TabAccum(acc.stops, value, acc.incrementSize, marker))
    else if marker == S.MarkerPlus then
      if acc.incrementSize != 0 then
        S.TabAccumErr(ES.RepeatOnlyLastMessage(S.MarkerPlus))
      else
        S.TabAccumOk(S.TabAccum(acc.stops, acc.extendSize, value, marker))
    else
      S.TabAccumOk(S.TabAccum(
        acc.stops + [value], acc.extendSize, acc.incrementSize, marker
      ))
  } by method {
    return
      if marker == S.MarkerSlash then
      if acc.extendSize != 0 then
        S.TabAccumErr(ProtocolRepeatOnlyLastMessage(S.MarkerSlash))
      else
        S.TabAccumOk(S.TabAccum(acc.stops, value, acc.incrementSize, marker))
    else if marker == S.MarkerPlus then
      if acc.incrementSize != 0 then
        S.TabAccumErr(ProtocolRepeatOnlyLastMessage(S.MarkerPlus))
      else
        S.TabAccumOk(S.TabAccum(acc.stops, acc.extendSize, value, marker))
    else
      S.TabAccumOk(S.TabAccum(
        acc.stops + [value], acc.extendSize, acc.incrementSize, marker
      ));
  }

  function FixedParseTabPart(part: string, acc: S.TabAccum): S.TabAccumParse
  {
    if |part| == 0 then
      S.TabAccumOk(acc)
    else
      var scan := FixedScanMarkers(part, 0, S.MarkerNone, false);
      var marker := if scan.hasMarker then scan.marker else acc.activeMarker;
      if scan.index == |part| then
        S.TabAccumOk(S.TabAccum(
          acc.stops, acc.extendSize, acc.incrementSize, marker
        ))
      else
        var end := FixedFindDigitsEnd(part, scan.index);
        if end < |part| then
          if FixedIsMarker(part[end]) then
            S.TabAccumErr(ES.MarkerNotAtStartMessage(
              FixedMarkerOf(part[end]), part[end..]
            ))
          else
            S.TabAccumErr(ES.InvalidCharacterMessage(part[end..]))
        else
          var digits := part[scan.index..end];
          match FixedParsePositiveNat(digits)
          case NatErr => S.TabAccumErr(ES.TooLargeMessage(digits))
          case NatOk(value) => FixedCommitTabValue(acc, marker, value)
  } by method {
    return
      if |part| == 0 then
      S.TabAccumOk(acc)
    else
      var scan := FixedScanMarkers(part, 0, S.MarkerNone, false);
      var marker := if scan.hasMarker then scan.marker else acc.activeMarker;
      if scan.index == |part| then
        S.TabAccumOk(S.TabAccum(
          acc.stops, acc.extendSize, acc.incrementSize, marker
        ))
      else
        var end := FixedFindDigitsEnd(part, scan.index);
        if end < |part| then
          if FixedIsMarker(part[end]) then
            S.TabAccumErr(ProtocolMarkerNotAtStartMessage(
              FixedMarkerOf(part[end]), part[end..]
            ))
          else
            S.TabAccumErr(ProtocolInvalidCharacterMessage(part[end..]))
        else
          var digits := part[scan.index..end];
          match FixedParsePositiveNat(digits)
          case NatErr => S.TabAccumErr(ProtocolTooLargeMessage(digits))
          case NatOk(value) => FixedCommitTabValue(acc, marker, value);
  }

  function FixedParseTabTextFrom(
    text: string,
    start: nat,
    acc: S.TabAccum
  ): S.TabAccumParse
    requires start <= |text|
    decreases |text| - start
  {
    if start == |text| then
      S.TabAccumOk(acc)
    else if FixedIsSeparator(text[start]) then
      FixedParseTabTextFrom(text, start + 1, acc)
    else
      var end := FixedFindTokenEnd(text, start);
      match FixedParseTabPart(text[start..end], acc)
      case TabAccumErr(value) => S.TabAccumErr(value)
      case TabAccumOk(next) => FixedParseTabTextFrom(text, end, next)
  }

  function FixedParseTabArgsFrom(
    args: seq<S.TabArg>,
    i: nat,
    limit: int,
    acc: S.TabAccum
  ): S.TabAccumParse
    requires i <= |args|
    decreases |args| - i
  {
    if i == |args| || (limit >= 0 && args[i].tokenIndex >= limit) then
      S.TabAccumOk(acc)
    else
      var arg := args[i];
      var argAcc := S.TabAccum(
        acc.stops, acc.extendSize, acc.incrementSize, S.MarkerNone
      );
      var diagnostics := FixedSyntaxDiagnostics(arg.text);
      if diagnostics != "" then
        S.TabAccumErr(diagnostics)
      else
        match FixedParseTabTextFrom(arg.text, 0, argAcc)
        case TabAccumErr(value) => S.TabAccumErr(value)
        case TabAccumOk(next) => FixedParseTabArgsFrom(args, i + 1, limit, next)
  }

  function FixedHelpBeforeOther(raw: S.ExpandCmdRaw): bool
  {
    raw.seenHelp &&
    (!raw.seenVersion || raw.helpTokenIndex <= raw.versionTokenIndex)
  }

  function FixedVersionBeforeInvalid(raw: S.ExpandCmdRaw): bool
  {
    raw.seenVersion &&
    (!raw.seenHelp || raw.versionTokenIndex < raw.helpTokenIndex)
  }

  function FixedRequestTokenIndex(raw: S.ExpandCmdRaw): int
  {
    if FixedHelpBeforeOther(raw) then raw.helpTokenIndex
    else if FixedVersionBeforeInvalid(raw) then raw.versionTokenIndex
    else -1
  }

  function FixedScanCommandOptions(raw: S.ExpandCmdRaw): S.OptionScan
  {
    match FixedParseTabArgsFrom(
        raw.tabArgs,
        0,
        FixedRequestTokenIndex(raw),
        S.TabAccum([], 0, 0, S.MarkerNone)
      )
    case TabAccumErr(value) => S.ScanInvalidTabs(value)
    case TabAccumOk(acc) =>
      if FixedHelpBeforeOther(raw) then S.ScanHelp
      else if FixedVersionBeforeInvalid(raw) then S.ScanVersion
      else S.ScanContinue(acc)
  }

  class {:termination false} ExpandBenchmarkItem extends BenchItem.BenchmarkItemTwostate<S.ExpandCmdRaw> {
    constructor()
    {
    }

    method Name() returns (name: string)
    {
      name := "expand";
    }

    method Schema() returns (schema: CliTypes.CliSchema)
    {
      schema := S.Schema();
    }

    method ParseConfig() returns (cfg: CliTypes.ParseConfig)
    {
      cfg := S.ParserConfig();
    }

    method Decode(parsed: CliTypes.ParsedArgs) returns (raw: S.ExpandCmdRaw)
    {
      raw := S.Decode(parsed);
    }

    method FormatParseError(err: CliTypes.ParseError) returns (msg: BenchWorld.Bytes)
    {
      msg := S.ExpandFormatParseError(err);
    }

    method PlanParseFailure(err: CliTypes.ParseError, argv: seq<string>) returns (plan: CliTypes.CliPlan<S.ExpandCmdRaw>)
      decreases *
    {
      if 0 <= err.tokenIndex <= |argv| {
        var schema := S.Schema();
        var cfg := S.ParserConfig();
        var prefix := argv[..err.tokenIndex as nat];
        var prefixResult := CliExtern.Cli.Parse(prefix, schema, cfg);
        match prefixResult {
          case ParseSuccess(parsed) =>
            var raw := S.Decode(parsed);
            match FixedScanCommandOptions(raw) {
              case ScanInvalidTabs(value) =>
                plan := CliTypes.CliEarlyExit(
                  1, [], ES.InvalidTabsMessage(value)
                );
                return;
              case ScanHelp =>
                plan := CliTypes.CliEarlyExit(0, ES.HelpText(), []);
                return;
              case ScanVersion =>
                plan := CliTypes.CliEarlyExit(0, ES.VersionText(), []);
                return;
              case ScanContinue(_) =>
            }
          case ParseFailure(_) =>
        }
      }
      var msg := S.ExpandFormatParseError(err);
      plan := CliTypes.CliEarlyExit(1, [], msg);
    }

    method RunCore(raw: S.ExpandCmdRaw, io: BenchIO.IO) returns (exit: int)
      modifies io.stdinRegion, io.stdoutRegion, io.stderrRegion
      ensures ES.Spec(raw, io, exit)
      decreases *
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

  function ProtocolSpecLocaleQuoteByte(byte: char): BenchWorld.Bytes
    ensures ProtocolSpecLocaleQuoteByte(byte) == ProtocolEscapingModel.SpecLocaleQuoteByte(byte)
  {
    var named := ProtocolSpecNamedEscape(byte);
    if named != [] then named
    else if byte == '\'' then "\\'"
    else if byte == '\\' then "\\\\"
    else if ProtocolSpecCPrintableByte(byte) then [byte]
    else ProtocolSpecOctalEscape(byte)
  }

  function ProtocolSpecLocaleQuoteBody(bytes: BenchWorld.Bytes): BenchWorld.Bytes
    ensures ProtocolSpecLocaleQuoteBody(bytes) == ProtocolEscapingModel.SpecLocaleQuoteBody(bytes)
    decreases |bytes|
  {
    if |bytes| == 0 then
      []
    else
      ProtocolSpecLocaleQuoteByte(bytes[0]) + ProtocolSpecLocaleQuoteBody(bytes[1..])
  }

  function ProtocolSpecLocaleQuoteBytes(bytes: BenchWorld.Bytes): BenchWorld.Bytes
    ensures ProtocolSpecLocaleQuoteBytes(bytes) == ProtocolEscapingModel.SpecLocaleQuoteBytes(bytes)
  {
    "'" + ProtocolSpecLocaleQuoteBody(bytes) + "'"
  }

  function ProtocolInvalidCharacterMessage(suffix: string): BenchWorld.Bytes
    ensures ProtocolInvalidCharacterMessage(suffix) == ES.InvalidCharacterMessage(suffix)
  {
    InvalidCharacterMessagePart1() + ProtocolSpecLocaleQuoteBytes(ProtocolEncode(suffix))
  }

  function ProtocolMarkerNotAtStartMessage(
    marker: Schema.MarkerKind, suffix: string
  ): BenchWorld.Bytes
    ensures ProtocolMarkerNotAtStartMessage(marker, suffix) == ES.MarkerNotAtStartMessage(marker, suffix)
  {
    ProtocolSpecLocaleQuoteBytes(ProtocolEncode(MarkerText(marker))) +
    MarkerNotAtStartMessagePart1() + ProtocolSpecLocaleQuoteBytes(ProtocolEncode(suffix))
  }

  function ProtocolTooLargeMessage(digits: string): BenchWorld.Bytes
    ensures ProtocolTooLargeMessage(digits) == ES.TooLargeMessage(digits)
  {
    TooLargeMessagePart1() + ProtocolSpecLocaleQuoteBytes(ProtocolEncode(digits))
  }

  function ProtocolRepeatOnlyLastMessage(marker: Schema.MarkerKind): BenchWorld.Bytes
    ensures ProtocolRepeatOnlyLastMessage(marker) == ES.RepeatOnlyLastMessage(marker)
  {
    ProtocolSpecLocaleQuoteBytes(ProtocolEncode(MarkerText(marker))) +
    RepeatOnlyLastMessagePart1()
  }

}
