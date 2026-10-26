include "CliSupport.dfy"
include "RealpathSpec.dfy"
include "RealpathCore.dfy"
include "RealpathProof.dfy"

module Realpath {
  import BenchIO
  import BenchWorld
  import BenchItem
  import CliTypes
  import CliExtern
  import Utf8 = Utf8Semantics
  import S = RealpathSchema
  import Core = RealpathCore
  import Spec = RealpathSpec
  import Proof = RealpathProof

  class RealpathBenchmarkItem extends BenchItem.BenchmarkItemTwostate<S.RealpathCmdRaw> {
    constructor() {}

    method Name() returns (name: string) {
      name := "realpath";
    }

    method Schema() returns (schema: CliTypes.CliSchema) {
      schema := S.Schema();
    }

    method ParseConfig() returns (cfg: CliTypes.ParseConfig) {
      cfg := S.ParserConfig();
    }

    method Decode(parsed: CliTypes.ParsedArgs) returns (raw: S.RealpathCmdRaw) {
      raw := S.Decode(parsed);
    }

    method FormatParseError(err: CliTypes.ParseError) returns (msg: BenchWorld.Bytes) {
      var token := err.rawToken;
      var cut := 0;
      while cut < |token| && token[cut] != '='
        invariant 0 <= cut <= |token|
        decreases |token| - cut
      { cut := cut + 1; }
      var name := token[..cut];
      var fullName := name;
      if err.kind == CliTypes.UnexpectedValue && |name| > 2 {
        var schema := S.Schema();
        var i := 0;
        while i < |schema.options|
          invariant 0 <= i <= |schema.options|
          decreases |schema.options| - i
        {
          var j := 0;
          while j < |schema.options[i].longs|
            invariant 0 <= j <= |schema.options[i].longs|
            decreases |schema.options[i].longs| - j
          {
            var option := schema.options[i].longs[j];
            if |name| - 2 <= |option| && option[..|name| - 2] == name[2..] {
              fullName := "--" + option;
            }
            j := j + 1;
          }
          i := i + 1;
        }
      }
      var invalid: BenchWorld.Bytes := [];
      if |token| > 1 && token[0] == '-' && token[1] != '-' {
        var i := 1;
        while i < |token| && token[i] in "EeLmPqsz"
          invariant 1 <= i <= |token|
          decreases |token| - i
        { i := i + 1; }
        if i < |token| {
          var encoded := Utf8.Encode([token[i]]);
          if encoded != [] { invalid := encoded[..1]; }
        }
      }
      msg := Spec.ParseErrorText(err, name, invalid, fullName);
    }

    method PlanParseFailure(err: CliTypes.ParseError, argv: seq<string>)
      returns (plan: CliTypes.CliPlan<S.RealpathCmdRaw>)
    {
      if 0 <= err.tokenIndex <= |argv| {
        var schema := S.Schema();
        var config := S.ParserConfig();
        var prefix := CliExtern.Cli.Parse(argv[..err.tokenIndex], schema, config);
        if prefix.ParseSuccess? {
          var raw := S.Decode(prefix.parsed);
          if raw.mode != S.Run { return CliTypes.CliRun(raw); }
        }
      }
      var msg := FormatParseError(err);
      plan := CliTypes.CliEarlyExit(1, [], msg);
    }

    method RunCore(raw: S.RealpathCmdRaw, io: BenchIO.IO) returns (exit: int)
      modifies io.directoryStateRegion, io.statusObservationsRegion, io.stdoutRegion, io.stderrRegion
      ensures Spec.Spec(raw, io, exit)
    {
      exit := Core.RunCore(raw, io);
      Proof.CoreSummaryImpliesSpec(raw, io, exit);
    }
  }
}
