include "../../core/BenchmarkItem.dfy"
include "Algorithm20Schema.dfy"
include "Algorithm20Core.dfy"
include "Algorithm20Proof.dfy"

module Algorithm20 {
  import BenchIO
  import BenchItem
  import CliTypes
  import SchemaMod = Algorithm20Schema
  import Spec = Algorithm20Spec
  import Core = Algorithm20Core
  import Proof = Algorithm20Proof

  class {:termination false} Algorithm20BenchmarkItem extends BenchItem.BenchmarkItemTwostate<SchemaMod.Algorithm20CmdRaw> {
    var input: string

    constructor(input: string) { this.input := input; }

    method Name() returns (name: string) { name := "algorithm-20"; }
    method Schema() returns (schema: CliTypes.CliSchema) { schema := SchemaMod.Schema(); }
    method ParseConfig() returns (cfg: CliTypes.ParseConfig) { cfg := SchemaMod.ParserConfig(); }
    method Decode(parsed: CliTypes.ParsedArgs) returns (raw: SchemaMod.Algorithm20CmdRaw) {
      raw := SchemaMod.FromInput(input);
    }
    method FormatParseError(err: CliTypes.ParseError) returns (msg: BenchIO.BenchWorld.Bytes) {
      msg := Spec.InvalidInputText();
    }
    method PlanArgv(argv: seq<string>) returns (plan: CliTypes.CliPlan<SchemaMod.Algorithm20CmdRaw>)
      decreases *
    {
      if |argv| != 1 {
        plan := CliTypes.CliEarlyExit(2, [], Spec.InvalidInputText());
      } else {
        var raw := SchemaMod.FromInput(input);
        plan := CliTypes.CliRun(raw);
      }
    }

    method RunCore(raw: SchemaMod.Algorithm20CmdRaw, io: BenchIO.IO) returns (exit: int)
      modifies io.stdoutRegion, io.stderrRegion
      ensures Spec.Spec(raw, io, exit)
      decreases *
    {
      exit := Core.RunCore(raw, io);
      Proof.CoreSummaryImpliesSpec(raw, io, exit);
    }
  }
}
