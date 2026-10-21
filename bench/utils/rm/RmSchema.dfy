include "../../core/CliTypes.dfy"
include "CliSupport.dfy"

module RmSchema {
  import CliTypes
  import CliModel
  import opened CliExtern

  datatype RmMode = ModeRun | ModeHelp | ModeVersion | ModeInteractive |
                    ModeInvalidInteractive(value: string) | ModeInvalidPreserve(value: string) |
                    ModeAbbreviatedNoPreserve
  datatype RmCmdRaw = RmCmdRaw(mode: RmMode, operands: seq<string>,
                               force: bool, verbose: bool, recursive: bool, directory: bool,
                               oneFileSystem: bool, preserveRoot: bool, preserveAll: bool)

  method Schema() returns (schema: CliTypes.CliSchema) {
    schema := CliTypes.CliSchema([
                                   CliTypes.OptionDecl("rm.force", ['f'], ["force"], CliTypes.NoArg),
                                   CliTypes.OptionDecl("rm.interactive", ['i'], [], CliTypes.NoArg),
                                   CliTypes.OptionDecl("rm.once", ['I'], [], CliTypes.NoArg),
                                   CliTypes.OptionDecl("rm.interactive_long", [], ["interactive"], CliTypes.OptArg),
                                   CliTypes.OptionDecl("rm.recursive", ['r', 'R'], ["recursive"], CliTypes.NoArg),
                                   CliTypes.OptionDecl("rm.directory", ['d'], ["dir"], CliTypes.NoArg),
                                   CliTypes.OptionDecl("rm.verbose", ['v'], ["verbose"], CliTypes.NoArg),
                                   CliTypes.OptionDecl("rm.one_file_system", [], ["one-file-system"], CliTypes.NoArg),
                                   CliTypes.OptionDecl("rm.no_preserve_root", [], ["no-preserve-root"], CliTypes.NoArg),
                                   CliTypes.OptionDecl("rm.preserve_root", [], ["preserve-root"], CliTypes.OptArg),
                                   CliTypes.OptionDecl("rm.tty", [], ["-presume-input-tty"], CliTypes.NoArg),
                                   CliTypes.OptionDecl("rm.help", [], ["help"], CliTypes.NoArg),
                                   CliTypes.OptionDecl("rm.version", [], ["version"], CliTypes.NoArg)
                                 ], true);
  }

  method ParserConfig() returns (cfg: CliTypes.ParseConfig) {
    cfg := CliTypes.ParseConfig(CliTypes.GNU_Permute, true, true, true);
  }

  // GNU optional long-option values require '='. Restore original bare
  // occurrences after making them explicit to the existing shared parser.
  method ParseArgs(argv: seq<string>) returns (result: CliTypes.ParseResult) {
    var normalized := argv;
    var bare: set<int> := {};
    var i := 1;
    var options := true;
    while i < |argv|
      invariant 0 <= i <= |argv| + 1
      invariant |normalized| == |argv|
      decreases |argv| - i
    {
      var token := argv[i];
      if token == "--" { options := false; }
      else if options && |token| > 2 && CliModel.HasPrefix(token,"--") &&
              CliModel.FindChar(token,'=') < 0 &&
              (CliModel.HasPrefix("interactive",token[2..]) || CliModel.HasPrefix("preserve-root",token[2..]))
      {
        normalized := normalized[i := token + "="];
        bare := bare + {i};
      }
      i := i+1;
    }
    var schema := Schema();
    var config := ParserConfig();
    result := Cli.Parse(normalized,schema,config);
    if result.ParseSuccess? {
      var parsed := result.parsed;
      var occurrences := parsed.options;
      i := 0;
      while i < |occurrences|
        invariant 0 <= i <= |occurrences|
        invariant |occurrences| == |parsed.options|
        decreases |occurrences|-i
      {
        var occurrence := occurrences[i];
        if occurrence.tokenIndex in bare && 0 <= occurrence.tokenIndex < |argv| {
          occurrences := occurrences[i := occurrence.(value := CliTypes.None, rawToken := argv[occurrence.tokenIndex])];
        }
        i := i+1;
      }
      result := CliTypes.ParseSuccess(parsed.(options := occurrences));
    }
  }

  method InvalidShortCharacter(token: string) returns (character: char) {
    var schema := Schema();
    var i := 1;
    while i < |token|
      invariant 1 <= i <= |token|+1
      decreases |token|-i
    {
      if CliModel.FindShortInDecls(schema.options,token[i]).OptionMissing? {
        character := token[i];
        return;
      }
      i := i+1;
    }
    character := if |token| > 1 then token[1] else '?';
  }

  method Decode(parsed: CliTypes.ParsedArgs) returns (raw: RmCmdRaw) {
    raw := RmCmdRaw(ModeRun, parsed.positionals, false, false, false, false,
                    false, true, false);
    var interactive := -1;
    var presumedTty := false;
    var i := 0;
    while i < |parsed.options|
      invariant 0 <= i <= |parsed.options|
      decreases |parsed.options| - i
    {
      var option := parsed.options[i];
      if option.key == "rm.help" { raw := raw.(mode := ModeHelp); return; }
      if option.key == "rm.version" { raw := raw.(mode := ModeVersion); return; }
      if option.key == "rm.force" { raw := raw.(force := true); interactive := 0; }
      if option.key == "rm.interactive" { raw := raw.(force := false); interactive := 2; }
      if option.key == "rm.once" { raw := raw.(force := false); interactive := 1; }
      if option.key == "rm.tty" { presumedTty := true; }
      if option.key == "rm.interactive_long" {
        var value := if option.value.Some? then option.value.value else "always";
        if value != "" && (CliModel.HasPrefix("never", value) ||
                           CliModel.HasPrefix("no", value) || CliModel.HasPrefix("none", value)) {
          interactive := 0;
        } else if value != "" && (CliModel.HasPrefix("once", value) ||
                                  CliModel.HasPrefix("always", value) || CliModel.HasPrefix("yes", value)) {
          raw := raw.(force := false);
          interactive := if CliModel.HasPrefix("once",value) then 1 else 2;
        } else {
          raw := raw.(mode := ModeInvalidInteractive(value)); return;
        }
      }
      if option.key == "rm.recursive" { raw := raw.(recursive := true); }
      if option.key == "rm.directory" { raw := raw.(directory := true); }
      if option.key == "rm.verbose" { raw := raw.(verbose := true); }
      if option.key == "rm.one_file_system" { raw := raw.(oneFileSystem := true); }
      if option.key == "rm.preserve_root" {
        raw := raw.(preserveRoot := true);
        if option.value.Some? {
          if option.value.value != "all" {
            raw := raw.(mode := ModeInvalidPreserve(option.value.value)); return;
          }
          raw := raw.(preserveAll := true);
        }
      }
      if option.key == "rm.no_preserve_root" {
        if option.rawToken != "--no-preserve-root" {
          raw := raw.(mode := ModeAbbreviatedNoPreserve); return;
        }
        raw := raw.(preserveRoot := false);
      }
      i := i + 1;
    }
    if |raw.operands| > 0 &&
       (interactive == 2 || (interactive == 1 && (raw.recursive || |raw.operands| > 3)) ||
        (presumedTty && interactive != 0)) {
      raw := raw.(mode := ModeInteractive);
    }
  }
}
