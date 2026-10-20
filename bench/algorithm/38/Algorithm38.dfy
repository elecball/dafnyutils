include "CliSupport.dfy"
include "Algorithm38Schema.dfy"
include "Algorithm38Core.dfy"
include "Algorithm38Proof.dfy"

module Algorithm38 {
  import BenchIO
  import BenchItem
  import CliTypes
  import SchemaMod = Algorithm38Schema
  import Spec = Algorithm38Spec
  import Core = Algorithm38Core
  import Proof = Algorithm38Proof

  class {:termination false} Algorithm38BenchmarkItem extends BenchItem.BenchmarkItemTwostate<SchemaMod.Algorithm38CmdRaw> {
    var input: string

    constructor(input: string) { this.input := input; }

    method Name() returns (name: string) { name := "algorithm-38"; }
    method Schema() returns (schema: CliTypes.CliSchema) { schema := SchemaMod.Schema(); }
    method ParseConfig() returns (cfg: CliTypes.ParseConfig) { cfg := SchemaMod.ParserConfig(); }
    method Decode(parsed: CliTypes.ParsedArgs) returns (raw: SchemaMod.Algorithm38CmdRaw) {
      raw := SchemaMod.FromInput(input);
    }
    method FormatParseError(err: CliTypes.ParseError) returns (msg: BenchIO.BenchWorld.Bytes) {
      msg := Spec.InvalidInputText();
    }
    method PlanArgv(argv: seq<string>) returns (plan: CliTypes.CliPlan<SchemaMod.Algorithm38CmdRaw>)
      decreases *
    {
      if |argv| != 1 {
        plan := CliTypes.CliEarlyExit(2, [], Spec.InvalidInputText());
      } else {
        var raw := SchemaMod.FromInput(input);
        plan := CliTypes.CliRun(raw);
      }
    }

    method RunCore(raw: SchemaMod.Algorithm38CmdRaw, io: BenchIO.IO) returns (exit: int)
      modifies io.stdoutRegion, io.stderrRegion
      ensures Spec.Spec(raw, io, exit)
      decreases *
    {
      if Spec.Valid(raw) { Proof.ValidInputSpecToCore(raw.n, raw.L, raw.kefa, raw.sasha); }
      exit := Core.RunCore(raw, io);
      Proof.CoreSummaryImpliesSpec(raw, io, exit);
    }
  }
}
