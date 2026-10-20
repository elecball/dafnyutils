include "CliSupport.dfy"
include "Algorithm59Schema.dfy"
include "Algorithm59Core.dfy"
include "Algorithm59Proof.dfy"

module Algorithm59 {
  import BenchIO
  import BenchItem
  import CliTypes
  import SchemaMod = Algorithm59Schema
  import Spec = Algorithm59Spec
  import Core = Algorithm59Core
  import Proof = Algorithm59Proof

  class {:termination false} Algorithm59BenchmarkItem extends BenchItem.BenchmarkItemTwostate<SchemaMod.Algorithm59CmdRaw> {
    var input: string

    constructor(input: string) { this.input := input; }

    method Name() returns (name: string) { name := "algorithm-59"; }
    method Schema() returns (schema: CliTypes.CliSchema) { schema := SchemaMod.Schema(); }
    method ParseConfig() returns (cfg: CliTypes.ParseConfig) { cfg := SchemaMod.ParserConfig(); }
    method Decode(parsed: CliTypes.ParsedArgs) returns (raw: SchemaMod.Algorithm59CmdRaw) {
      raw := SchemaMod.FromInput(input);
    }
    method FormatParseError(err: CliTypes.ParseError) returns (msg: BenchIO.BenchWorld.Bytes) {
      msg := Spec.InvalidInputText();
    }
    method PlanArgv(argv: seq<string>) returns (plan: CliTypes.CliPlan<SchemaMod.Algorithm59CmdRaw>)
      decreases *
    {
      if |argv| != 1 {
        plan := CliTypes.CliEarlyExit(2, [], Spec.InvalidInputText());
      } else {
        var raw := SchemaMod.FromInput(input);
        plan := CliTypes.CliRun(raw);
      }
    }

    method RunCore(raw: SchemaMod.Algorithm59CmdRaw, io: BenchIO.IO) returns (exit: int)
      modifies io.stdoutRegion, io.stderrRegion
      ensures Spec.Spec(raw, io, exit)
      decreases *
    {
      if Spec.Valid(raw) { Proof.ValidInputSpecToCore(raw.n, raw.a, raw.s); }
      exit := Core.RunCore(raw, io);
      Proof.CoreSummaryImpliesSpec(raw, io, exit);
    }
  }
}
