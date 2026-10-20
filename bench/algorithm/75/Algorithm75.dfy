include "CliSupport.dfy"
include "Algorithm75Schema.dfy"
include "Algorithm75Core.dfy"
include "Algorithm75Proof.dfy"

module Algorithm75 {
  import BenchIO
  import BenchItem
  import CliTypes
  import SchemaMod = Algorithm75Schema
  import Spec = Algorithm75Spec
  import Core = Algorithm75Core
  import Proof = Algorithm75Proof

  class {:termination false} Algorithm75BenchmarkItem extends BenchItem.BenchmarkItemTwostate<SchemaMod.Algorithm75CmdRaw> {
    var input: string

    constructor(input: string) { this.input := input; }

    method Name() returns (name: string) { name := "algorithm-75"; }
    method Schema() returns (schema: CliTypes.CliSchema) { schema := SchemaMod.Schema(); }
    method ParseConfig() returns (cfg: CliTypes.ParseConfig) { cfg := SchemaMod.ParserConfig(); }
    method Decode(parsed: CliTypes.ParsedArgs) returns (raw: SchemaMod.Algorithm75CmdRaw) {
      raw := SchemaMod.FromInput(input);
    }
    method FormatParseError(err: CliTypes.ParseError) returns (msg: BenchIO.BenchWorld.Bytes) {
      msg := Spec.InvalidInputText();
    }
    method PlanArgv(argv: seq<string>) returns (plan: CliTypes.CliPlan<SchemaMod.Algorithm75CmdRaw>)
      decreases *
    {
      if |argv| != 1 {
        plan := CliTypes.CliEarlyExit(2, [], Spec.InvalidInputText());
      } else {
        var raw := SchemaMod.FromInput(input);
        plan := CliTypes.CliRun(raw);
      }
    }

    method RunCore(raw: SchemaMod.Algorithm75CmdRaw, io: BenchIO.IO) returns (exit: int)
      modifies io.stdoutRegion, io.stderrRegion
      ensures Spec.Spec(raw, io, exit)
      decreases *
    {
      if Spec.Valid(raw) { Proof.ValidGridSpecToCore(raw.n, raw.m, raw.grid); }
      exit := Core.RunCore(raw, io);
      Proof.CoreSummaryImpliesSpec(raw, io, exit);
    }
  }
}
