include "../../../core/CliTypes.dfy"

module MkfifoSchema {
  import CliTypes

  // `mode` holds the value of the last -m/--mode occurrence (GNU keeps the last
  // one), or None when no -m is given. -Z/--context are not declared: they are
  // outside this contribution's accepted command domain (see mkfifo.md).
  datatype MkfifoCmdRaw = MkfifoCmdRaw(mode: CliTypes.OptionalString, first: string, rest: seq<string>)

  function Operands(raw: MkfifoCmdRaw): seq<string> {
    [raw.first] + raw.rest
  }

  method Schema() returns (schema: CliTypes.CliSchema) {
    schema := CliTypes.CliSchema([
                                   CliTypes.OptionDecl("mkfifo.mode", ['m'], ["mode"], CliTypes.ReqArg),
                                   CliTypes.OptionDecl("mkfifo.help", [], ["help"], CliTypes.NoArg),
                                   CliTypes.OptionDecl("mkfifo.version", [], ["version"], CliTypes.NoArg)
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
      if (option.key == "mkfifo.help" || option.key == "mkfifo.version") &&
         (firstIndex < 0 || option.tokenIndex < firstIndex) {
        firstIndex := option.tokenIndex;
        request := if option.key == "mkfifo.help" then CliTypes.RequestHelp
        else CliTypes.RequestVersion;
      }
      i := i + 1;
    }
  }

  method Decode(parsed: CliTypes.ParsedArgs) returns (raw: MkfifoCmdRaw) {
    var mode := CliTypes.None;
    var i := 0;
    while i < |parsed.options|
      decreases |parsed.options| - i
    {
      if parsed.options[i].key == "mkfifo.mode" {
        mode := parsed.options[i].value;
      }
      i := i + 1;
    }
    raw := MkfifoCmdRaw(mode,
                        if |parsed.positionals| == 0 then "" else parsed.positionals[0],
                        if |parsed.positionals| == 0 then [] else parsed.positionals[1..]);
  }
}
