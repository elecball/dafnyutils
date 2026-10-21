include "../../core/CliTypes.dfy"

module TsortSchema {
  import CliTypes

  // TODO: replace this wrapper with the task's decoded command fields.
  datatype TsortCmdRaw = TsortCmdRaw(parsed: CliTypes.ParsedArgs)

  method Schema() returns (schema: CliTypes.CliSchema)
  {
    // TODO: declare the accepted options and their argument requirements.
    assert false;
    schema := CliTypes.CliSchema([], true);
  }

  method ParserConfig() returns (cfg: CliTypes.ParseConfig)
  {
    // TODO: choose parsing rules from the task's pinned source contract.
    assert false;
    cfg := CliTypes.ParseConfig(CliTypes.GNU_Permute, true, true, true);
  }

  method Decode(parsed: CliTypes.ParsedArgs) returns (raw: TsortCmdRaw)
  {
    raw := TsortCmdRaw(parsed);
  }
}
