include "../../core/CliTypes.dfy"

module DateSchema {
  import C = CliTypes

  datatype Mode = Run | Help | Version | InvalidIso | InvalidRfc
  datatype Format = Default | IsoDate | IsoHours | IsoMinutes | IsoSeconds | IsoNs | RfcEmail | RfcDate | RfcSeconds | RfcNs
  datatype DateCmdRaw = DateCmdRaw(mode: Mode, date: C.OptionalString,
                                   reference: C.OptionalString, format: Format, optionFormat: bool,
                                   invalidValue: string, operands: seq<string>)

  method Schema() returns (schema: C.CliSchema)
  {
    schema := C.CliSchema([
                            C.OptionDecl("date.date", ['d'], ["date"], C.ReqArg),
                            C.OptionDecl("date.reference", ['r'], ["reference"], C.ReqArg),
                            C.OptionDecl("date.utc", ['u'], ["uct", "utc", "universal"], C.NoArg),
                            C.OptionDecl("date.iso", ['I'], ["iso-8601"], C.OptArg),
                            C.OptionDecl("date.email", ['R'], ["rfc-email", "rfc-822", "rfc-2822"], C.NoArg),
                            C.OptionDecl("date.rfc", [], ["rfc-3339"], C.ReqArg),
                            C.OptionDecl("date.help", [], ["help"], C.NoArg),
                            C.OptionDecl("date.version", [], ["version"], C.NoArg)
                          ], true);
  }

  method ParserConfig() returns (cfg: C.ParseConfig)
  {
    cfg := C.ParseConfig(C.GNU_Permute, true, true, true);
  }

  function Prefix(value: string, candidate: string): bool
  {
    |value| > 0 && |value| <= |candidate| && candidate[..|value|] == value
  }

  method Decode(parsed: C.ParsedArgs) returns (raw: DateCmdRaw)
  {
    var mode := Run;
    var date := C.None;
    var reference := C.None;
    var format := Default;
    var optionFormat := false;
    var invalidValue := "";
    var i := 0;
    while i < |parsed.options| && mode == Run
      invariant 0 <= i <= |parsed.options|
      decreases |parsed.options| - i
    {
      var option := parsed.options[i];
      if option.key == "date.date" { date := option.value; }
      else if option.key == "date.reference" { reference := option.value; }
      else if option.key == "date.help" { mode := Help; }
      else if option.key == "date.version" { mode := Version; }
      else if option.key == "date.email" { format := RfcEmail; optionFormat := true; }
      else if option.key == "date.iso" || option.key == "date.rfc" {
        var value := if option.value.Some? then option.value.value else "date";
        optionFormat := true;
        if Prefix(value, "date") { format := if option.key == "date.iso" then IsoDate else RfcDate; }
        else if Prefix(value, "seconds") { format := if option.key == "date.iso" then IsoSeconds else RfcSeconds; }
        else if Prefix(value, "ns") { format := if option.key == "date.iso" then IsoNs else RfcNs; }
        else if option.key == "date.iso" && Prefix(value, "hours") { format := IsoHours; }
        else if option.key == "date.iso" && Prefix(value, "minutes") { format := IsoMinutes; }
        else { mode := if option.key == "date.iso" then InvalidIso else InvalidRfc; invalidValue := value; }
      }
      i := i + 1;
    }
    raw := DateCmdRaw(mode, date, reference, format, optionFormat, invalidValue, parsed.positionals);
  }
}
