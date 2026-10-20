include "../../core/BenchmarkItem.dfy"
include "Algorithm4004Schema.dfy"
include "Algorithm4004Core.dfy"
include "Algorithm4004Proof.dfy"

module Algorithm4004 {
  import BenchIO
  import BenchItem
  import CliTypes
  import SchemaMod = Algorithm4004Schema
  import Spec = Algorithm4004Spec
  import Core = Algorithm4004Core
  import Proof = Algorithm4004Proof

  class {:termination false} Algorithm4004BenchmarkItem extends BenchItem.BenchmarkItemTwostate<SchemaMod.Algorithm4004CmdRaw> {
    var input: string

    constructor(input: string) { this.input := input; }

    method Name() returns (name: string) { name := "algorithm-4004"; }
    method Schema() returns (schema: CliTypes.CliSchema) { schema := SchemaMod.Schema(); }
    method ParseConfig() returns (cfg: CliTypes.ParseConfig) { cfg := SchemaMod.ParserConfig(); }
    method Decode(parsed: CliTypes.ParsedArgs) returns (raw: SchemaMod.Algorithm4004CmdRaw) {
      raw := SchemaMod.FromInput(input);
    }
    method FormatParseError(err: CliTypes.ParseError) returns (msg: BenchIO.BenchWorld.Bytes) {
      msg := Spec.InvalidInputText();
    }
    method PlanArgv(argv: seq<string>) returns (plan: CliTypes.CliPlan<SchemaMod.Algorithm4004CmdRaw>)
      decreases *
    {
      if |argv| != 1 {
        plan := CliTypes.CliEarlyExit(2, [], Spec.InvalidInputText());
      } else {
        var raw := SchemaMod.FromInput(input);
        plan := CliTypes.CliRun(raw);
      }
    }

    method RunCore(raw: SchemaMod.Algorithm4004CmdRaw, io: BenchIO.IO) returns (exit: int)
      modifies io.stdoutRegion, io.stderrRegion
      ensures Spec.Spec(raw, io, exit)
      decreases *
    {
      exit := Core.RunCore(raw, io);
      Proof.CoreSummaryImpliesSpec(raw, io, exit);
    }
  }
}
