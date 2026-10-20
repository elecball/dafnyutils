include "../../core/BenchmarkItem.dfy"
include "Algorithm3690Schema.dfy"
include "Algorithm3690Core.dfy"
include "Algorithm3690Proof.dfy"

module Algorithm3690 {
  import BenchIO
  import BenchItem
  import CliTypes
  import SchemaMod = Algorithm3690Schema
  import Spec = Algorithm3690Spec
  import Core = Algorithm3690Core
  import Proof = Algorithm3690Proof

  class {:termination false} Algorithm3690BenchmarkItem extends BenchItem.BenchmarkItemTwostate<SchemaMod.Algorithm3690CmdRaw> {
    var input: string

    constructor(input: string) { this.input := input; }

    method Name() returns (name: string) { name := "algorithm-3690"; }
    method Schema() returns (schema: CliTypes.CliSchema) { schema := SchemaMod.Schema(); }
    method ParseConfig() returns (cfg: CliTypes.ParseConfig) { cfg := SchemaMod.ParserConfig(); }
    method Decode(parsed: CliTypes.ParsedArgs) returns (raw: SchemaMod.Algorithm3690CmdRaw) {
      raw := SchemaMod.FromInput(input);
    }
    method FormatParseError(err: CliTypes.ParseError) returns (msg: BenchIO.BenchWorld.Bytes) {
      msg := Spec.InvalidInputText();
    }
    method PlanArgv(argv: seq<string>) returns (plan: CliTypes.CliPlan<SchemaMod.Algorithm3690CmdRaw>)
      decreases *
    {
      if |argv| != 1 {
        plan := CliTypes.CliEarlyExit(2, [], Spec.InvalidInputText());
      } else {
        var raw := SchemaMod.FromInput(input);
        plan := CliTypes.CliRun(raw);
      }
    }

    method RunCore(raw: SchemaMod.Algorithm3690CmdRaw, io: BenchIO.IO) returns (exit: int)
      modifies io.stdoutRegion, io.stderrRegion
      ensures Spec.Spec(raw, io, exit)
      decreases *
    {
      if Spec.Valid(raw) { Proof.ValidInputSpecToCore(raw.h, raw.m, raw.s, raw.t1, raw.t2); }
      exit := Core.RunCore(raw, io);
      Proof.CoreSummaryImpliesSpec(raw, io, exit);
    }
  }
}
