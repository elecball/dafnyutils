include "../../../core/World.dfy"
include "../../../core/IO.dfy"
include "../../../core/CliTypes.dfy"
include "CliSupport.dfy"
include "../Spec/PwdSchema.dfy"
include "PwdCore.dfy"
include "../Spec/PwdSpec.dfy"

module Pwd {
  import BenchIO
  import BenchWorld
  import CliTypes
  import BenchItem
  import PwdSchema
  import Core = PwdCore
  import PS = PwdSpec

  class {:termination false} PwdBenchmarkItem extends BenchItem.BenchmarkItemTwostate<PwdSchema.PwdCmdRaw> {
    constructor()
    {
    }

    method Name() returns (name: string)
    {
      name := "pwd";
    }

    method Schema() returns (schema: CliTypes.CliSchema)
    {
      schema := PwdSchema.Schema();
    }

    method ParseConfig() returns (cfg: CliTypes.ParseConfig)
    {
      cfg := PwdSchema.ParserConfig();
    }

    method Decode(parsed: CliTypes.ParsedArgs) returns (raw: PwdSchema.PwdCmdRaw)
    {
      raw := PwdSchema.Decode(parsed);
    }

    method FormatParseError(err: CliTypes.ParseError) returns (msg: BenchWorld.Bytes)
    {
      msg := PwdSchema.FormatParseError(err);
    }

    method PlanParseFailure(err: CliTypes.ParseError, argv: seq<string>) returns (plan: CliTypes.CliPlan<PwdSchema.PwdCmdRaw>)
      decreases *
    {
      plan := PwdSchema.PlanParseFailure(err, argv);
    }

    method RunCore(raw: PwdSchema.PwdCmdRaw, io: BenchIO.IO) returns (exit: int)
      modifies io.stdoutRegion, io.stderrRegion, io.directoryStateRegion, io.cwdRegion, io.statusObservationsRegion
      ensures PS.Spec(raw, io, exit)
      decreases *
    {
      exit := Core.RunCore(raw, io);
    }
  }
}
