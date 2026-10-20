include "../../core/Utf8.dfy"
include "../../core/World.dfy"
include "../../core/CliTypes.dfy"

module ExprSchema {
  import Utf8 = Utf8Semantics
  import BenchWorld
  import CliTypes

  datatype ExprCmdRaw = ExprCmdRaw(args: seq<string>)

  method Schema() returns (s: CliTypes.CliSchema)
  {
    s := CliTypes.CliSchema([], false);
  }

  method ParserConfig() returns (cfg: CliTypes.ParseConfig)
  {
    cfg := CliTypes.ParseConfig(CliTypes.POSIX_StopAtFirst, false, false, true);
  }

  method Decode(p: CliTypes.ParsedArgs) returns (raw: ExprCmdRaw)
  {
    raw := ExprCmdRaw(p.positionals);
  }

  function ParseErrorText(e: CliTypes.ParseError): string
  {
    "expr: parse error\n"
  }

  method ExprFormatParseError(e: CliTypes.ParseError) returns (b: BenchWorld.Bytes)
  {
    var text := ParseErrorText(e);
    b := [];
    var i := |text|;
    while 0 < i
      invariant 0 <= i <= |text|
      invariant b == Utf8.Encode(text[i..])
      decreases i
    {
      i := i - 1;
      var code := text[i] as int;
      var piece: BenchWorld.Bytes :=
        if code <= 0x7f then
          [code as char]
        else if code <= 0x7ff then
          [
            (0xc0 + code / 0x40) as char,
            (0x80 + code % 0x40) as char
          ]
        else if code <= 0xffff then
          [
            (0xe0 + code / 0x1000) as char,
            (0x80 + (code / 0x40) % 0x40) as char,
            (0x80 + code % 0x40) as char
          ]
        else
          [
            (0xf0 + code / 0x40000) as char,
            (0x80 + (code / 0x1000) % 0x40) as char,
            (0x80 + (code / 0x40) % 0x40) as char,
            (0x80 + code % 0x40) as char
          ];
      b := piece + b;
    }
    assert b == Utf8.Encode(ParseErrorText(e));
  }
}
