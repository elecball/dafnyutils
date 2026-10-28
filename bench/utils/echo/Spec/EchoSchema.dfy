include "../../../core/World.dfy"
include "../../../core/CliTypes.dfy"

module EchoSchema {
  import BenchWorld
  import CliTypes

  datatype EchoCmdRaw = EchoCmdRaw(args: seq<string>)

  method Schema() returns (s: CliTypes.CliSchema)
  {
    s := CliTypes.CliSchema([], false);
  }

  method ParserConfig() returns (cfg: CliTypes.ParseConfig)
  {
    cfg := CliTypes.ParseConfig(CliTypes.POSIX_StopAtFirst, false, false, true);
  }

  method Decode(p: CliTypes.ParsedArgs) returns (raw: EchoCmdRaw)
  {
    raw := EchoCmdRaw(p.positionals);
  }

  function ParseErrorText(e: CliTypes.ParseError): string
  {
    "echo: parse error\n"
  }

  method EchoFormatParseError(e: CliTypes.ParseError) returns (b: BenchWorld.Bytes)
  {
    b := ParseErrorText(e);
  }
}
