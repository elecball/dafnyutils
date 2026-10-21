include "ExpandSpec.dfy"
include "../../core/World.dfy"
include "../../core/CliTypes.dfy"
include "CliSupport.dfy"
include "ExpandSchema.dfy"
include "ExpandCore.dfy"
include "ExpandProof.dfy"

module Expand {
  // CLI codecs are fixed protocol details, outside the candidate API.
  export
    provides BenchIO, BenchWorld, CliTypes, CliExtern, BenchItem, S, Core, Proof, ES, ExpandBenchmarkItem._ctor, ExpandBenchmarkItem.Name, ExpandBenchmarkItem.Schema, ExpandBenchmarkItem.ParseConfig, ExpandBenchmarkItem.Decode, ExpandBenchmarkItem.FormatParseError, ExpandBenchmarkItem.PlanParseFailure, ExpandBenchmarkItem.RunCore
    reveals FixedParseNatFrom, FixedParsePositiveNat, FixedFindTokenEnd, FixedScanMarkers, FixedCommitTabValue, FixedParseTabPart, FixedParseTabTextFrom, FixedParseTabArgsFrom, FixedScanCommandOptions, ExpandBenchmarkItem

  import BenchIO
  import BenchWorld
  import CliTypes
  import CliExtern
  import BenchItem
  import S = ExpandSchema
  import Core = ExpandCore
  import Proof = ExpandProof
  import ES = ExpandSpec

  function FixedParseNatFrom(text: string, i: nat, acc: nat): S.NatParse
    requires i <= |text|
    decreases |text| - i
  {
    if i == |text| then
      S.NatOk(acc)
    else if !ES.IsDigit(text[i]) then
      S.NatErr
    else if acc > (ES.MaxColumn() - ES.DigitValue(text[i])) / 10 then
      S.NatErr
    else
      FixedParseNatFrom(text, i + 1, acc * 10 + ES.DigitValue(text[i]))
  }

  function FixedParsePositiveNat(text: string): S.NatParse
  {
    if |text| == 0 then S.NatErr else FixedParseNatFrom(text, 0, 0)
  }

  function FixedFindTokenEnd(text: string, start: nat): nat
    requires start <= |text|
    ensures start <= FixedFindTokenEnd(text, start) <= |text|
    decreases |text| - start
  {
    if start == |text| || ES.IsSeparator(text[start]) then
      start
    else
      FixedFindTokenEnd(text, start + 1)
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
    if i == |part| || !ES.IsMarker(part[i]) then
      S.MarkerScan(i, marker, hasMarker)
    else
      FixedScanMarkers(part, i + 1, ES.MarkerOf(part[i]), true)
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
        var end := ES.FindDigitsEnd(part, scan.index);
        if end < |part| then
          if ES.IsMarker(part[end]) then
            S.TabAccumErr(ES.MarkerNotAtStartMessage(
                            ES.MarkerOf(part[end]), part[end..]
                          ))
          else
            S.TabAccumErr(ES.InvalidCharacterMessage(part[end..]))
        else
          var digits := part[scan.index..end];
          match FixedParsePositiveNat(digits)
          case NatErr => S.TabAccumErr(ES.TooLargeMessage(digits))
          case NatOk(value) => FixedCommitTabValue(acc, marker, value)
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
    else if ES.IsSeparator(text[start]) then
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
      var diagnostics := ES.SyntaxDiagnostics(arg.text);
      if diagnostics != "" then
        S.TabAccumErr(diagnostics)
      else
        match FixedParseTabTextFrom(arg.text, 0, argAcc)
        case TabAccumErr(value) => S.TabAccumErr(value)
        case TabAccumOk(next) => FixedParseTabArgsFrom(args, i + 1, limit, next)
  }

  function FixedScanCommandOptions(raw: S.ExpandCmdRaw): S.OptionScan
  {
    match FixedParseTabArgsFrom(
        raw.tabArgs,
        0,
        ES.RequestTokenIndex(raw),
        S.TabAccum([], 0, 0, S.MarkerNone)
      )
    case TabAccumErr(value) => S.ScanInvalidTabs(value)
    case TabAccumOk(acc) =>
      if ES.HelpBeforeOther(raw) then S.ScanHelp
      else if ES.VersionBeforeInvalid(raw) then S.ScanVersion
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

}
