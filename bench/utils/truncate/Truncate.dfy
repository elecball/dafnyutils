include "TruncateSpec.dfy"
include "CliSupport.dfy"
include "TruncateCore.dfy"

module Truncate {
  // CLI codecs are fixed protocol details, outside the candidate API.
  export
    provides BenchItem, BenchIO, BenchWorld, CliTypes, CliExtern, S, Spec, Core, InvalidShortCharacter, TruncateBenchmarkItem._ctor, TruncateBenchmarkItem.Name, TruncateBenchmarkItem.Schema, TruncateBenchmarkItem.ParseConfig, TruncateBenchmarkItem.Decode, TruncateBenchmarkItem.FormatParseError, TruncateBenchmarkItem.PlanParseFailure, TruncateBenchmarkItem.RunCore
    reveals TruncateBenchmarkItem

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
      message := Spec.ParseErrorText(error, invalidShort);
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

}
