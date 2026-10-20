include "../../core/BenchmarkItem.dfy"
include "Algorithm63Schema.dfy"
include "Algorithm63Core.dfy"
include "Algorithm63Proof.dfy"

module Algorithm63 {
  import BenchIO
  import BenchItem
  import CliTypes
  import SchemaMod = Algorithm63Schema
  import Spec = Algorithm63Spec
  import Core = Algorithm63Core
  import Proof = Algorithm63Proof

  class {:termination false} Algorithm63BenchmarkItem extends BenchItem.BenchmarkItemTwostate<SchemaMod.Algorithm63CmdRaw> {
    var input: string

    constructor(input: string) { this.input := input; }

    method Name() returns (name: string) { name := "algorithm-63"; }
    method Schema() returns (schema: CliTypes.CliSchema) { schema := SchemaMod.Schema(); }
    method ParseConfig() returns (cfg: CliTypes.ParseConfig) { cfg := SchemaMod.ParserConfig(); }
    method Decode(parsed: CliTypes.ParsedArgs) returns (raw: SchemaMod.Algorithm63CmdRaw) {
      raw := SchemaMod.FromInput(input);
    }
    method FormatParseError(err: CliTypes.ParseError) returns (msg: BenchIO.BenchWorld.Bytes) {
      msg := Spec.InvalidInputText();
    }
    method PlanArgv(argv: seq<string>) returns (plan: CliTypes.CliPlan<SchemaMod.Algorithm63CmdRaw>)
      decreases *
    {
      if |argv| != 1 {
        plan := CliTypes.CliEarlyExit(2, [], Spec.InvalidInputText());
      } else {
        var raw := SchemaMod.FromInput(input);
        plan := CliTypes.CliRun(raw);
      }
    }

    method RunCore(raw: SchemaMod.Algorithm63CmdRaw, io: BenchIO.IO) returns (exit: int)
      modifies io.stdoutRegion, io.stderrRegion
      ensures Spec.Spec(raw, io, exit)
      decreases *
    {
      exit := Core.RunCore(raw, io);
      Proof.CoreSummaryImpliesSpec(raw, io, exit);
    }
  }
}
