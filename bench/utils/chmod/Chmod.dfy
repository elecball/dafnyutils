include "../../core/World.dfy"
include "../../core/CliTypes.dfy"
include "../../core/BenchmarkItem.dfy"
include "ChmodSchema.dfy"
include "ChmodSpec.dfy"
include "ChmodDescriptorCore.dfy"
include "ChmodDescriptorPrincipalSpec.dfy"

module Chmod {
  import BenchIO
  import BenchWorld
  import CliTypes
  import BenchItem
  import ChmodSchema
  import Core = ChmodDescriptorCore
  import CS = ChmodSpec
  import Spec = ChmodDescriptorPrincipalSpec

  class {:termination false} ChmodBenchmarkItem extends BenchItem.BenchmarkItemTwostate<ChmodSchema.ChmodCmdRaw> {
    constructor()
    {
    }

    method Name() returns (name: string)
    {
      name := "chmod";
    }

    method Schema() returns (schema: CliTypes.CliSchema)
    {
      schema := ChmodSchema.Schema();
    }

    method ParseConfig() returns (cfg: CliTypes.ParseConfig)
    {
      cfg := ChmodSchema.ParserConfig();
    }

    method Decode(parsed: CliTypes.ParsedArgs) returns (raw: ChmodSchema.ChmodCmdRaw)
    {
      raw := ChmodSchema.Decode(parsed);
    }

    method FormatParseError(err: CliTypes.ParseError) returns (msg: BenchWorld.Bytes)
    {
      msg := ChmodSchema.ChmodFormatParseError(err);
    }

    method PlanParseFailure(err: CliTypes.ParseError, argv: seq<string>) returns (plan: CliTypes.CliPlan<ChmodSchema.ChmodCmdRaw>)
      decreases *
    {
      plan := ChmodSchema.PlanParseFailure(err, argv);
    }

    predicate ExternalDomain(raw: ChmodSchema.ChmodCmdRaw)
    {
      CS.SpecExternalDomain(raw)
    }

    method RunCore(raw: ChmodSchema.ChmodCmdRaw, io: BenchIO.IO) returns (exit: int)
      modifies io.fsRegion, io.stdoutRegion, io.stderrRegion, io.directoryStateRegion, io.statusObservationsRegion
      ensures Spec.Spec(raw, io, exit)
      decreases *
    {
      exit := Core.RunCore(raw, io);
    }
  }

  method RunCli(argv: seq<string>, io: BenchIO.IO) returns (exit: int)
    modifies io.Footprint()
    decreases *
  {
    var item := new ChmodBenchmarkItem();
    exit := BenchItem.RunMain(item, argv, io);
  }
}
