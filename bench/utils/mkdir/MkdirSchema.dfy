include "../../core/CliTypes.dfy"

module MkdirSchema {
  import CliTypes

  datatype MkdirCmdRaw = MkdirCmdRaw(verbose: bool, first: string, rest: seq<string>)

  function Operands(raw: MkdirCmdRaw): seq<string> {
    [raw.first] + raw.rest
  }

  method Schema() returns (schema: CliTypes.CliSchema) {
    schema := CliTypes.CliSchema([
                                   CliTypes.OptionDecl("mkdir.verbose", ['v'], ["verbose"], CliTypes.NoArg),
                                   CliTypes.OptionDecl("mkdir.help", [], ["help"], CliTypes.NoArg),
                                   CliTypes.OptionDecl("mkdir.version", [], ["version"], CliTypes.NoArg)
                                 ], true);
  }

  method ParserConfig() returns (cfg: CliTypes.ParseConfig) {
    cfg := CliTypes.ParseConfig(CliTypes.GNU_Permute, true, true, true);
  }

  method InformationRequest(parsed: CliTypes.ParsedArgs)
    returns (request: CliTypes.PriorRequest)
  {
    request := CliTypes.RequestNone;
    var firstIndex := -1;
    var i := 0;
    while i < |parsed.options|
      decreases |parsed.options| - i
    {
      var option := parsed.options[i];
      if (option.key == "mkdir.help" || option.key == "mkdir.version") &&
         (firstIndex < 0 || option.tokenIndex < firstIndex) {
        firstIndex := option.tokenIndex;
        request := if option.key == "mkdir.help" then CliTypes.RequestHelp
        else CliTypes.RequestVersion;
      }
      i := i + 1;
    }
  }

  method Decode(parsed: CliTypes.ParsedArgs) returns (raw: MkdirCmdRaw) {
    var verbose := false;
    var i := 0;
    while i < |parsed.options|
      decreases |parsed.options| - i
    {
      verbose := verbose || parsed.options[i].key == "mkdir.verbose";
      i := i + 1;
    }
    raw := MkdirCmdRaw(verbose,
                       if |parsed.positionals| == 0 then "" else parsed.positionals[0],
                       if |parsed.positionals| == 0 then [] else parsed.positionals[1..]);
  }
}
