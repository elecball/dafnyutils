include "../../../core/CliTypes.dfy"
include "../../../core/World.dfy"

module TruncateSchema {
  import CliTypes
  import BenchWorld

  datatype Modifier = Absolute | Relative | AtMost | AtLeast | RoundDown | RoundUp
  datatype Mode = Run | Help | Version
  datatype TruncateCmdRaw = TruncateCmdRaw(
    noCreate: bool, blocks: bool, hasReference: bool, reference: string,
    sizes: seq<string>, mode: Mode, files: seq<string>, parseError: BenchWorld.Bytes
  )
  datatype ParsedSize = ParsedSize(
    modifier: Modifier, signed: bool, value: int, error: BenchWorld.Bytes
  )

  method Schema() returns (schema: CliTypes.CliSchema)
  {
    schema := CliTypes.CliSchema([
                                   CliTypes.OptionDecl("truncate.no-create", ['c'], ["no-create"], CliTypes.NoArg),
                                   CliTypes.OptionDecl("truncate.io-blocks", ['o'], ["io-blocks"], CliTypes.NoArg),
                                   CliTypes.OptionDecl("truncate.reference", ['r'], ["reference"], CliTypes.ReqArg),
                                   CliTypes.OptionDecl("truncate.size", ['s'], ["size"], CliTypes.ReqArg),
                                   CliTypes.OptionDecl("truncate.help", [], ["help"], CliTypes.NoArg),
                                   CliTypes.OptionDecl("truncate.version", [], ["version"], CliTypes.NoArg)
                                 ], true);
  }

  method ParserConfig() returns (config: CliTypes.ParseConfig)
  {
    config := CliTypes.ParseConfig(CliTypes.GNU_Permute, true, true, true);
  }

  method Decode(parsed: CliTypes.ParsedArgs) returns (raw: TruncateCmdRaw)
  {
    var noCreate, blocks, hasReference := false, false, false;
    var reference := "";
    var sizes: seq<string> := [];
    var mode := Run;
    var i := 0;
    while i < |parsed.options| && mode == Run
      decreases |parsed.options| - i
    {
      var option := parsed.options[i];
      if option.key == "truncate.no-create" { noCreate := true; }
      if option.key == "truncate.io-blocks" { blocks := true; }
      if option.key == "truncate.reference" && option.value.Some? {
        hasReference := true;
        reference := option.value.value;
      }
      if option.key == "truncate.size" && option.value.Some? {
        sizes := sizes + [option.value.value];
      }
      if option.key == "truncate.help" { mode := Help; }
      if option.key == "truncate.version" { mode := Version; }
      i := i + 1;
    }
    raw := TruncateCmdRaw(noCreate, blocks, hasReference, reference, sizes, mode, parsed.positionals, []);
  }
}
