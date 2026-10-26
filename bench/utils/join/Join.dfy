include "CliSupport.dfy"
include "JoinSpec.dfy"
include "JoinCore.dfy"
include "JoinProof.dfy"

module Join {
  import BenchIO
  import BenchWorld
  import BenchItem
  import Cli = CliExtern
  import CliModel
  import CliTypes
  import S = JoinSchema
  import Core = JoinCore
  import Spec = JoinSpec
  import Proof = JoinProof

  class JoinBenchmarkItem extends BenchItem.BenchmarkItemTwostate<S.JoinCmdRaw> {
    constructor() {}

    method Name() returns (name: string) {
      name := "join";
    }

    method Schema() returns (schema: CliTypes.CliSchema) {
      schema := S.Schema();
    }

    method ParseConfig() returns (cfg: CliTypes.ParseConfig) {
      cfg := S.ParserConfig();
    }

    method Decode(parsed: CliTypes.ParsedArgs) returns (raw: S.JoinCmdRaw) {
      raw := S.Decode(parsed);
    }

    method FormatParseError(err: CliTypes.ParseError) returns (msg: BenchWorld.Bytes) {
      msg := Spec.ParseErrorText(err);
    }

    method PlanArgv(argv: seq<string>) returns (plan: CliTypes.CliPlan<S.JoinCmdRaw>)
      decreases *
    {
      var schema := S.Schema();
      var cfg := S.ParserConfig();
      var parsed := Cli.Cli.Parse(argv,schema,cfg);
      match parsed
      case ParseSuccess(p) =>
        var raw := S.DecodeArgv(p,argv);
        plan := CliTypes.CliRun(raw);
      case ParseFailure(error) =>
        var before := if 0 <= error.tokenIndex <= |argv| then argv[..error.tokenIndex] else ["join"];
        var prefix := Cli.Cli.Parse(before,schema,cfg);
        var raw := S.DefaultCommand();
        if prefix.ParseSuccess? {
          raw := S.DecodeArgv(prefix.parsed,before);
          // Operand count is finalized only after getopt has completed.
          if raw.mode.Error? && (raw.mode.error.Missing? || raw.mode.error.MissingAfter?) {
            raw := raw.(mode := S.Run);
          }
        }
        var normalized := S.NormalizeParseError(error);
        if S.IsRunning(raw) { raw := raw.(mode := S.Error(S.Parse(normalized))); }
        plan := CliTypes.CliRun(raw);
    }

    method RunCore(raw: S.JoinCmdRaw, io: BenchIO.IO) returns (exit: int)
      modifies io.stdinRegion, io.stdoutRegion, io.stderrRegion
      ensures Spec.Spec(raw, io, exit)
    {
      exit := Core.RunCore(raw, io);
      Proof.CoreSummaryImpliesSpec(raw, io, exit);
    }
  }
}
