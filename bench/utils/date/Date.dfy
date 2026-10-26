include "CliSupport.dfy"
include "DateSpec.dfy"
include "DateCore.dfy"
include "DateProof.dfy"

module Date {
  import BenchIO
  import W = BenchWorld
  import BenchItem
  import CliTypes
  import CliModel
  import S = DateSchema
  import Core = DateCore
  import Spec = DateSpec
  import Proof = DateProof

  class DateBenchmarkItem extends BenchItem.BenchmarkItemTwostate<S.DateCmdRaw> {
    constructor() {}
    method Name() returns (name: string) { name := "date"; }
    method Schema() returns (schema: CliTypes.CliSchema) { schema := S.Schema(); }
    method ParseConfig() returns (cfg: CliTypes.ParseConfig) { cfg := S.ParserConfig(); }
    method Decode(parsed: CliTypes.ParsedArgs) returns (raw: S.DateCmdRaw) { raw := S.Decode(parsed); }

    method FormatParseError(error: CliTypes.ParseError) returns (message: W.Bytes)
    {
      var token := error.rawToken;
      var name := token;
      var short := '?';
      if |token| > 1 {
        var index := 1;
        while index + 1 < |token| && token[index] in {'u', 'R'}
          invariant 1 <= index < |token|
          decreases |token| - index
        { index := index + 1; }
        short := token[index];
      }
      var equals := CliModel.FindChar(token, '=');
      if equals >= 0 { name := token[..equals]; }
      var possibilities := "";
      if error.kind == CliTypes.Ambiguous && |name| > 2 {
        var options := Spec.LongOptions();
        var index := 0;
        while index < |options|
          invariant 0 <= index <= |options|
          decreases |options| - index
        {
          if S.Prefix(name[2..], options[index]) { possibilities := possibilities + Spec.Possibility(options[index]); }
          index := index + 1;
        }
      }
      message := Spec.ParseMessage(error.kind, token, short, name, possibilities);
    }

    method PlanParseFailure(error: CliTypes.ParseError, argv: seq<string>) returns (plan: CliTypes.CliPlan<S.DateCmdRaw>)
      decreases *
    {
      if 1 <= error.tokenIndex <= |argv| {
        var schema := S.Schema();
        var cfg := S.ParserConfig();
        var prior := CliModel.ParseValue(argv[..error.tokenIndex], schema, cfg);
        if prior.ParseSuccess? {
          var raw := S.Decode(prior.parsed);
          if raw.mode != S.Run { plan := CliTypes.CliRun(raw); return; }
        }
      }
      var message := FormatParseError(error);
      plan := CliTypes.CliEarlyExit(1, [], message);
    }

    method RunCore(raw: S.DateCmdRaw, io: BenchIO.IO) returns (exit: int)
      modifies io.stdoutRegion, io.stderrRegion
      ensures Spec.Spec(raw, io, exit)
    {
      exit := Core.RunCore(raw, io);
      Proof.CoreSummaryImpliesSpec(raw, io, exit);
    }
  }
}
