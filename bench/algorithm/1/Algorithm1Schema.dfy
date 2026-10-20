include "../../core/CliTypes.dfy"

module Algorithm1Schema {
  import CliTypes

  datatype Algorithm1CmdRaw = Algorithm1CmdRaw(parsed: bool, x: int)

  method Schema() returns (schema: CliTypes.CliSchema)
  {
    schema := CliTypes.CliSchema([], true);
  }

  method ParserConfig() returns (cfg: CliTypes.ParseConfig)
  {
    cfg := CliTypes.ParseConfig(CliTypes.POSIX_StopAtFirst, false, false, true);
  }

  predicate Whitespace(ch: char)
  {
    ch in {' ', '\t', '\r', '\n'} || ch as int == 11 || ch as int == 12
  }

  method Tokens(input: string) returns (tokens: seq<string>)
  {
    tokens := [];
    var i := 0;
    while i < |input|
      invariant 0 <= i <= |input|
      decreases |input| - i
    {
      if Whitespace(input[i]) {
        i := i + 1;
      } else {
        var start := i;
        i := i + 1;
        while i < |input| && !Whitespace(input[i])
          invariant 0 <= start < i <= |input|
          decreases |input| - i
        {
          i := i + 1;
        }
        tokens := tokens + [input[start..i]];
      }
    }
  }

  method Integer(token: string) returns (value: int, ok: bool)
  {
    value := 0;
    ok := false;
    var negative := |token| > 0 && token[0] == '-';
    var start := if |token| > 0 && token[0] in {'-', '+'} then 1 else 0;
    if start == |token| { return; }
    var i := start;
    while i < |token|
      invariant 0 <= i <= |token|
      decreases |token| - i
    {
      if token[i] < '0' || token[i] > '9' { return; }
      value := value * 10 + (token[i] as int) - ('0' as int);
      i := i + 1;
    }
    if negative { value := -value; }
    ok := true;
  }

  method Integers(tokens: seq<string>) returns (values: seq<int>, ok: bool)
  {
    values := [];
    ok := true;
    var i := 0;
    while i < |tokens|
      invariant 0 <= i <= |tokens|
      decreases |tokens| - i
    {
      var value, valid := Integer(tokens[i]);
      values := values + [value];
      ok := ok && valid;
      i := i + 1;
    }
  }

  method FromInput(input: string) returns (raw: Algorithm1CmdRaw)
  {
    raw := Algorithm1CmdRaw(false, 0);
    var tokens := Tokens(input);
    if |tokens| != 1 { return; }
    var x, ok0 := Integer(tokens[0]);
    raw := Algorithm1CmdRaw(ok0, x);
  }
}
