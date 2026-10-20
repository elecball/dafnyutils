include "../../core/CliTypes.dfy"

module Algorithm38Schema {
  import CliTypes

  datatype Algorithm38CmdRaw = Algorithm38CmdRaw(parsed: bool, n: int, L: int, kefa: seq<int>, sasha: seq<int>)

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

  method FromInput(input: string) returns (raw: Algorithm38CmdRaw)
  {
    raw := Algorithm38CmdRaw(false, 0, 0, [], []);
    var tokens := Tokens(input);
    if |tokens| < 2 { return; }
    var n, ok0 := Integer(tokens[0]);
    var L, ok1 := Integer(tokens[1]);
    if n < 0 || |tokens| != 2 + 2 * n { return; }
    var kefa, ok2 := Integers(tokens[2..2+n]);
    var sasha, ok3 := Integers(tokens[2+n..]);
    raw := Algorithm38CmdRaw(ok0 && ok1 && ok2 && ok3, n, L, kefa, sasha);
  }
}
