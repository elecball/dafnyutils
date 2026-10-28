include "../../../core/CliTypes.dfy"

module DdSchema {
  import CliTypes

  type BlockSize = n: int | 0 < n <= 9223372036854775806 witness 512
  datatype Mode = Copy | Help | Version
  datatype Error = None | Operand(text: string) | Conversion(text: string) |
                   InputFlag(text: string) | OutputFlag(text: string) | Status(text: string) |
                   Number(text: string, overflow: bool) | CaseConflict | OutsideScope
  datatype DdCmdRaw = DdCmdRaw(
    mode: Mode, error: Error, ibs: BlockSize, obs: BlockSize,
    fullblock: bool, lower: bool, upper: bool, swab: bool, sync: bool,
    direct: bool, count: int, countBytes: bool, warnings: nat
  )

  method Schema() returns (schema: CliTypes.CliSchema) {
    schema := CliTypes.CliSchema([
                                   CliTypes.OptionDecl("dd.help", [], ["help"], CliTypes.NoArg),
                                   CliTypes.OptionDecl("dd.version", [], ["version"], CliTypes.NoArg)
                                 ], true);
  }

  method ParserConfig() returns (cfg: CliTypes.ParseConfig) {
    cfg := CliTypes.ParseConfig(CliTypes.GNU_Permute, true, true, true);
  }

  function Starts(text: string, prefix: string): bool {
    |prefix| <= |text| && text[..|prefix|] == prefix
  }

  function Find(text: string, target: char): nat
    ensures Find(text, target) <= |text|
    decreases |text|
  {
    if |text| == 0 || text[0] == target then 0
    else 1 + Find(text[1..], target)
  }

  function Power(base: nat, exponent: nat): nat
    decreases exponent
  {
    if exponent == 0 then 1 else base * Power(base, exponent - 1)
  }

  // strtoumax's bounded magnitude and recognized suffix prefix, before dd's
  // optional B and recursive x processing. A bad trailing suffix does not erase
  // an overflow already caused by a recognized unit.
  method Magnitude(text: string) returns (good: bool, value: nat, saturated: bool, at: nat)
    ensures at <= |text|
    ensures value <= 18446744073709551615
    ensures saturated ==> value == 18446744073709551615
  {
    var i: nat := 0;
    while i < |text| && text[i] in [' ', '\t', '\n', '\r', 11 as char, 12 as char]
      invariant i <= |text|
      decreases |text| - i
    { i := i + 1; }
    if i < |text| && text[i] == '+' { i := i + 1; }
    var start := i;
    value := 0;
    while i < |text| && '0' <= text[i] <= '9'
      invariant start <= i <= |text|
      decreases |text| - i
    {
      value := value * 10 + (text[i] as int - '0' as int) as nat;
      i := i + 1;
    }
    if i == start {
      if |text| == 0 || !(text[0] in "bcEGkKMPQRTwYZ") { return false, 0, false, 0; }
      i := 0;
      value := 1;
    }
    saturated := value > 18446744073709551615;
    if saturated { value := 18446744073709551615; }
    at := i;
    good := true;
    if at == |text| { return; }
    var unit := text[at];
    var factor: nat := 1;
    var consumed: nat := 1;
    if unit == 'b' { factor := 512; }
    else if unit == 'w' { factor := 2; }
    else if unit != 'c' {
      var powers := "kKMGTPEZYRQ";
      var p := Find(powers, unit);
      if p == |powers| { return; }
      var base: nat := 1024;
      if at + 1 < |text| && (text[at + 1] == 'B' || text[at + 1] == 'D') {
        base := 1000;
        consumed := 2;
      } else if at + 2 < |text| && text[at + 1] == 'i' && text[at + 2] == 'B' {
        consumed := 3;
      }
      factor := Power(base, if p < 2 then 1 else p);
    }
    var scaled := value * factor;
    saturated := saturated || scaled > 18446744073709551615;
    value := if saturated then 18446744073709551615 else scaled;
    at := at + consumed;
  }

  method Numeric(text: string) returns (valid: bool, value: nat, warnings: nat, overflow: bool)
    decreases |text|
  {
    var good, magnitude, saturated, at := Magnitude(text);
    if !good { return false, 0, 0, false; }
    if at < |text| && text[at] == 'B' && at > 0 && text[at - 1] != 'B' {
      at := at + 1;
    }
    if at < |text| && text[at] == 'x' {
      var childValid, child, childWarnings, childOverflow := Numeric(text[at + 1..]);
      if !childValid && !childOverflow { return false, 0, childWarnings, false; }
      var product := magnitude * child;
      if product > 9223372036854775807 || (product != 0 && (saturated || childOverflow)) {
        return false, 9223372036854775807, childWarnings, true;
      }
      return true, product,
          childWarnings + (if product == 0 && Starts(text, "0x") then 1 else 0), false;
    }
    if magnitude > 9223372036854775807 {
      return false, 9223372036854775807, 0, true;
    }
    return at == |text|, magnitude, 0, false;
  }

  method Decode(p: CliTypes.ParsedArgs) returns (raw: DdCmdRaw) {
    var mode := Copy;
    var earliest := -1;
    var k := 0;
    while k < |p.options|
      decreases |p.options| - k
    {
      var o := p.options[k];
      if earliest < 0 || o.tokenIndex < earliest {
        earliest := o.tokenIndex;
        mode := if o.key == "dd.help" then Help else Version;
      }
      k := k + 1;
    }
    raw := DecodeOperands(p.positionals, mode);
  }

  method DecodeOperands(args: seq<string>, mode: Mode) returns (raw: DdCmdRaw) {
    var ibs: BlockSize := 512;
    var obs: BlockSize := 512;
    var bs := 0;
    var fullblock, lower, upper, swab, sync := false, false, false, false, false;
    var count := -1;
    var countBytes := false;
    var countSuffixBytes := false;
    var status := 2;
    var outputFullblock := false;
    var error := None;
    var warnings: nat := 0;
    var i := 0;
    while i < |args| && error == None && mode == Copy
      invariant 0 <= bs <= 9223372036854775806
      decreases |args| - i
    {
      var token := args[i];
      var eq := Find(token, '=');
      if eq == |token| { error := Operand(token); }
      else {
        var name := token[..eq];
        var value := token[eq + 1..];
        if name == "conv" || name == "iflag" || name == "oflag" || name == "status" {
          var at: nat := 0;
          while at <= |value| && error == None
            invariant at <= |value| + 1
            decreases |value| + 1 - at
          {
            var len := Find(value[at..], ',');
            var symbol := value[at..at + len];
            if name == "conv" {
              if symbol == "lcase" { lower := true; }
              else if symbol == "ucase" { upper := true; }
              else if symbol == "swab" { swab := true; }
              else if symbol == "sync" { sync := true; }
              else if symbol in ["ascii", "ebcdic", "ibm", "block", "unblock", "sparse", "excl", "nocreat", "notrunc", "noerror", "fdatasync", "fsync"] { error := OutsideScope; }
              else { error := Conversion(symbol); }
            } else if name == "iflag" {
              if symbol == "fullblock" { fullblock := true; }
              else if symbol == "count_bytes" { countBytes := true; }
              else if symbol in ["skip_bytes", "append", "direct", "directory", "dsync", "sync", "nonblock", "noatime", "nocache", "noctty", "nofollow", "nolinks"] { error := OutsideScope; }
              else { error := InputFlag(symbol); }
            } else if name == "oflag" {
              if symbol == "fullblock" { outputFullblock := true; }
              else if symbol in ["append", "direct", "directory", "dsync", "sync", "nonblock", "noatime", "nocache", "noctty", "nofollow", "nolinks", "seek_bytes"] { error := OutsideScope; }
              else { error := OutputFlag(symbol); }
            } else {
              if symbol == "none" { status := 0; }
              else if symbol == "noxfer" { status := 1; }
              else if symbol == "progress" { status := 2; }
              else { error := Status(symbol); }
            }
            at := at + len + 1;
          }
        } else if name in ["ibs", "obs", "bs", "cbs", "count"] {
          var valid, number, warns, overflow := Numeric(value);
          warnings := warnings + warns;
          if name != "count" && number == 0 {
            error := Number(value, false);
          } else if number > (if name == "count" || name == "cbs" then 9223372036854775807 else 9223372036854775806) {
            error := Number(value, true);
          } else if !valid {
            error := Number(value, overflow);
          } else if name == "count" {
            count := if number == 9223372036854775807 then -1 else number;
            countSuffixBytes := Find(value, 'B') < |value|;
          } else if name == "ibs" { ibs := number; }
          else if name == "obs" { obs := number; }
          else if name == "bs" { bs := number; }
        } else if name in ["if", "of", "skip", "iseek", "seek", "oseek"] { error := OutsideScope; }
        else { error := Operand(token); }
      }
      i := i + 1;
    }
    if bs > 0 { ibs := bs; obs := bs; }
    if error == None && outputFullblock { error := OutputFlag("fullblock"); }
    if error == None && lower && upper { error := CaseConflict; }
    if error == None && status != 0 && mode == Copy { error := OutsideScope; }
    raw := DdCmdRaw(mode, error, ibs, obs, fullblock, lower, upper, swab, sync,
                    bs > 0 && !(lower || upper || swab), count, countBytes || countSuffixBytes, warnings);
  }
}
