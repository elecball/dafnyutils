include "../../core/CliTypes.dfy"

module RmdirSchema {
  import CliTypes

  datatype RmdirMode = ModeRun | ModeHelp | ModeVersion
  datatype RmdirCmdRaw = RmdirCmdRaw(
    mode: RmdirMode, parents: bool, ignoreNonempty: bool,
    verbose: bool, operands: seq<string>)

  method Schema() returns (schema: CliTypes.CliSchema) {
    schema := CliTypes.CliSchema([
                                   CliTypes.OptionDecl("rmdir.parents", ['p'], ["parents"], CliTypes.NoArg),
                                   CliTypes.OptionDecl("rmdir.ignore", [], ["ignore-fail-on-non-empty"], CliTypes.NoArg),
                                   CliTypes.OptionDecl("rmdir.verbose", ['v'], ["verbose"], CliTypes.NoArg),
                                   CliTypes.OptionDecl("rmdir.help", [], ["help"], CliTypes.NoArg),
                                   CliTypes.OptionDecl("rmdir.version", [], ["version"], CliTypes.NoArg)
                                 ], true);
  }

  method ParserConfig() returns (cfg: CliTypes.ParseConfig) {
    cfg := CliTypes.ParseConfig(CliTypes.GNU_Permute, true, true, true);
  }

  method Decode(parsed: CliTypes.ParsedArgs) returns (raw: RmdirCmdRaw) {
    var parents, ignoreNonempty, verbose := false, false, false;
    var help, version := -1, -1;
    var i := 0;
    while i < |parsed.options|
      decreases |parsed.options| - i
    {
      var opt := parsed.options[i];
      parents := parents || opt.key == "rmdir.parents";
      ignoreNonempty := ignoreNonempty || opt.key == "rmdir.ignore";
      verbose := verbose || opt.key == "rmdir.verbose";
      if opt.key == "rmdir.help" && (help < 0 || opt.tokenIndex < help) {
        help := opt.tokenIndex;
      }
      if opt.key == "rmdir.version" && (version < 0 || opt.tokenIndex < version) {
        version := opt.tokenIndex;
      }
      i := i + 1;
    }
    raw := RmdirCmdRaw(
      if help >= 0 && (version < 0 || help <= version) then ModeHelp
      else if version >= 0 then ModeVersion else ModeRun,
      parents, ignoreNonempty, verbose, parsed.positionals);
  }
}
