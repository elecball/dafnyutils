include "../../../core/CliTypes.dfy"

module RealpathSchema {
  import CliTypes

  datatype Existence = AllButLast | Existing | Missing
  datatype Links = Physical | Logical | Strip
  datatype Mode = Run | Help | Version
  datatype RealpathCmdRaw = RealpathCmdRaw(
    existence: Existence, links: Links, quiet: bool, zero: bool,
    relativeTo: CliTypes.OptionalString, relativeBase: CliTypes.OptionalString,
    mode: Mode, operands: seq<string>)

  // A path expression is a directory anchor followed by filename components.
  datatype PathExpr = Anchor(directory: string) | Child(parent: PathExpr, name: string)

  method Schema() returns (schema: CliTypes.CliSchema) {
    schema := CliTypes.CliSchema([
                                   CliTypes.OptionDecl("existing", ['e'], ["canonicalize-existing"], CliTypes.NoArg),
                                   CliTypes.OptionDecl("all", ['E'], ["canonicalize"], CliTypes.NoArg),
                                   CliTypes.OptionDecl("missing", ['m'], ["canonicalize-missing"], CliTypes.NoArg),
                                   CliTypes.OptionDecl("logical", ['L'], ["logical"], CliTypes.NoArg),
                                   CliTypes.OptionDecl("physical", ['P'], ["physical"], CliTypes.NoArg),
                                   CliTypes.OptionDecl("strip", ['s'], ["strip", "no-symlinks"], CliTypes.NoArg),
                                   CliTypes.OptionDecl("quiet", ['q'], ["quiet"], CliTypes.NoArg),
                                   CliTypes.OptionDecl("zero", ['z'], ["zero"], CliTypes.NoArg),
                                   CliTypes.OptionDecl("relativeTo", [], ["relative-to"], CliTypes.ReqArg),
                                   CliTypes.OptionDecl("relativeBase", [], ["relative-base"], CliTypes.ReqArg),
                                   CliTypes.OptionDecl("help", [], ["help"], CliTypes.NoArg),
                                   CliTypes.OptionDecl("version", [], ["version"], CliTypes.NoArg)
                                 ], true);
  }

  method ParserConfig() returns (cfg: CliTypes.ParseConfig) {
    cfg := CliTypes.ParseConfig(CliTypes.GNU_Permute, true, true, true);
  }

  method Decode(parsed: CliTypes.ParsedArgs) returns (raw: RealpathCmdRaw) {
    var existence := AllButLast;
    var links := Physical;
    var quiet, zero := false, false;
    var relativeTo, relativeBase := CliTypes.None, CliTypes.None;
    var mode := Run;
    var i := 0;
    while i < |parsed.options|
      invariant 0 <= i <= |parsed.options|
      decreases |parsed.options| - i
    {
      var option := parsed.options[i];
      if option.key == "all" { existence := AllButLast; }
      else if option.key == "existing" { existence := Existing; }
      else if option.key == "missing" { existence := Missing; }
      else if option.key == "logical" { links := Logical; }
      else if option.key == "physical" { links := Physical; }
      else if option.key == "strip" { links := Strip; }
      else if option.key == "quiet" { quiet := true; }
      else if option.key == "zero" { zero := true; }
      else if option.key == "relativeTo" { relativeTo := option.value; }
      else if option.key == "relativeBase" { relativeBase := option.value; }
      else if option.key == "help" && mode == Run { mode := Help; }
      else if option.key == "version" && mode == Run { mode := Version; }
      i := i + 1;
    }
    raw := RealpathCmdRaw(existence, links, quiet, zero, relativeTo, relativeBase,
                          mode, parsed.positionals);
  }
}
