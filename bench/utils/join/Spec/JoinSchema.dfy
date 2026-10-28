include "../../../core/CliTypes.dfy"
include "../../../core/Utf8.dfy"

module JoinSchema {
  import CliTypes
  import BW = BenchWorld
  import Utf8 = Utf8Semantics

  // xstrtol resets errno for each conversion; overflow can remain observable
  // in GNU's invalid repeated-stdin diagnostic before any file is opened.
  datatype Mode = Run | RunWithRangeError | Help | Version | Error(error: ArgumentError)
  datatype ArgumentError = Missing | MissingAfter(text: string) | Extra(text: string)
                         | BadField(text: string) | BadFile(text: string) | BadFormat(text: string, kind: nat)
                         | IncompatibleFields(previous: nat, current: nat) | ConflictingFiller
                         | MultiTab(text: string) | IncompatibleTabs | Parse(error: CliTypes.ParseError)
  datatype Order = DefaultOrder | CheckOrder | NoCheckOrder
  datatype Field = Field(file: nat, index: nat)
  datatype JoinCmdRaw = JoinCmdRaw(mode: Mode, field1: nat, field2: nat,
                                   separator: int, outputSeparator: BW.Bytes, filler: BW.Bytes,
                                   unpaired1: bool, unpaired2: bool, paired: bool, ignoreCase: bool,
                                   zero: bool, header: bool, autoformat: bool, format: seq<Field>, order: Order,
                                   operands: seq<string>)
  datatype Number = Number(ok: bool, value: nat, rangeError: bool)

  function IsRunning(cmd: JoinCmdRaw): bool { cmd.mode == Run || cmd.mode == RunWithRangeError }

  function DefaultCommand(): JoinCmdRaw {
    JoinCmdRaw(Run, 0, 0, -1, " ", [], false, false, true, false,
               false, false, false, [], DefaultOrder, [])
  }

  method Schema() returns (s: CliTypes.CliSchema) {
    s := CliTypes.CliSchema([
                              CliTypes.OptionDecl("a", ['a'], [], CliTypes.ReqArg),
                              CliTypes.OptionDecl("e", ['e'], [], CliTypes.ReqArg),
                              CliTypes.OptionDecl("i", ['i'], ["ignore-case"], CliTypes.NoArg),
                              CliTypes.OptionDecl("1", ['1'], [], CliTypes.ReqArg),
                              CliTypes.OptionDecl("2", ['2'], [], CliTypes.ReqArg),
                              CliTypes.OptionDecl("j", ['j'], [], CliTypes.ReqArg),
                              CliTypes.OptionDecl("o", ['o'], [], CliTypes.ReqArg),
                              CliTypes.OptionDecl("t", ['t'], [], CliTypes.ReqArg),
                              CliTypes.OptionDecl("v", ['v'], [], CliTypes.ReqArg),
                              CliTypes.OptionDecl("z", ['z'], ["zero-terminated"], CliTypes.NoArg),
                              CliTypes.OptionDecl("check", [], ["check-order"], CliTypes.NoArg),
                              CliTypes.OptionDecl("nocheck", [], ["nocheck-order"], CliTypes.NoArg),
                              CliTypes.OptionDecl("header", [], ["header"], CliTypes.NoArg),
                              CliTypes.OptionDecl("help", [], ["help"], CliTypes.NoArg),
                              CliTypes.OptionDecl("version", [], ["version"], CliTypes.NoArg)
                            ], true);
  }
  method ParserConfig() returns (cfg: CliTypes.ParseConfig) {
    cfg := CliTypes.ParseConfig(CliTypes.GNU_Permute, true, true, true);
  }

  method ParseNumber(text: string, saturate: bool) returns (n: Number) {
    var i := 0;
    while i < |text| && text[i] as int in {9,10,11,12,13,32}
      invariant 0 <= i <= |text|
      decreases |text| - i
    { i := i + 1; }
    var negative := i < |text| && text[i] == '-';
    if i < |text| && (text[i] == '+' || text[i] == '-') { i := i + 1; }
    var begin := i;
    var value: nat := 0;
    while i < |text| && '0' <= text[i] <= '9'
      invariant begin <= i <= |text|
      decreases |text| - i
    { value := value * 10 + (text[i] as int - '0' as int); i := i + 1; }
    // xstrtoimax reports overflow before sign/range validation.
    if saturate && ((!negative && value > 9223372036854775807) || (negative && value > 9223372036854775808)) {
      n := Number(i == |text|, 9223372036854775806, true);
    } else {
      n := Number(i == |text| && i > begin && !negative && value > 0,
                  if saturate && value > 0 then value - 1 else value, false);
    }
  }

  method SetField(cmd: JoinCmdRaw, side: nat, text: string,
                  seen1: bool, seen2: bool)
    returns (result: JoinCmdRaw, next1: bool, next2: bool) {
    result := cmd; next1 := seen1; next2 := seen2;
    var n := ParseNumber(text, true);
    if !n.ok { result := cmd.(mode := Error(BadField(text))); return; }
    result := result.(mode := if n.rangeError then RunWithRangeError else Run);
    if (side == 0 || side == 1) && seen1 && cmd.field1 != n.value {
      result := cmd.(mode := Error(IncompatibleFields(cmd.field1, n.value))); return;
    }
    if side == 0 || side == 1 { result := result.(field1 := n.value); next1 := true; }
    // GNU -j reuses the first field when setting the second.
    if (side == 0 || side == 2) && seen2 && cmd.field2 != n.value {
      result := result.(mode := Error(IncompatibleFields(cmd.field2, n.value))); return;
    }
    if side == 0 || side == 2 { result := result.(field2 := n.value); next2 := true; }
  }

  method AddFormat(cmd: JoinCmdRaw, text: string) returns (result: JoinCmdRaw) {
    result := cmd;
    var p := 0;
    var done := false;
    while !done
      invariant 0 <= p <= |text|
      decreases |text| + 1 - p
    {
      var q := p;
      while q < |text| && text[q] !in ", \t"
        invariant p <= q <= |text|
        decreases |text| - q
      { q := q + 1; }
      var part := text[p..q];
      if part == "0" { result := result.(format := result.format + [Field(0, 0)]); }
      else if |part| > 0 && (part[0] == '1' || part[0] == '2') {
        if |part| < 2 || part[1] != '.' {
          result := result.(mode := Error(BadFormat(part, 1))); return;
        }
        var n := ParseNumber(part[2..], true);
        if !n.ok { result := result.(mode := Error(BadField(part[2..]))); return; }
        result := result.(mode := if n.rangeError then RunWithRangeError else Run,
        format := result.format + [Field(part[0] as int - '0' as int, n.value)]);
      } else {
        result := result.(mode := Error(BadFormat(part, if |part| > 0 && part[0] == '0' then 1 else 0)));
        return;
      }
      if q == |text| || q + 1 == |text| { done := true; }
      else { p := q + 1; }
    }
  }

  method Apply(cmd: JoinCmdRaw, occ: CliTypes.OptOccurrence, seen1: bool,
               seen2: bool, seenFiller: bool) returns (result: JoinCmdRaw,
                                                       next1: bool, next2: bool, nextFiller: bool, status: nat) {
    result := cmd; next1 := seen1; next2 := seen2; nextFiller := seenFiller; status := 0;
    var value := if occ.value.Some? then occ.value.value else "";
    if occ.key == "help" { result := cmd.(mode := Help); }
    else if occ.key == "version" { result := cmd.(mode := Version); }
    else if occ.key == "i" { result := cmd.(ignoreCase := true); }
    else if occ.key == "z" { result := cmd.(zero := true); }
    else if occ.key == "header" { result := cmd.(header := true); }
    else if occ.key == "check" { result := cmd.(order := CheckOrder); }
    else if occ.key == "nocheck" { result := cmd.(order := NoCheckOrder); }
    else if occ.key == "a" || occ.key == "v" {
      var n := ParseNumber(value, false);
      if !n.ok || (n.value != 1 && n.value != 2) { result := cmd.(mode := Error(BadFile(value))); }
      else {
        result := cmd.(mode := Run, unpaired1 := cmd.unpaired1 || n.value == 1,
                                                 unpaired2 := cmd.unpaired2 || n.value == 2, paired := cmd.paired && occ.key != "v");
      }
    } else if occ.key == "e" {
      var bytes := Utf8.Encode(value);
      if seenFiller && cmd.filler != bytes { result := cmd.(mode := Error(ConflictingFiller)); }
      else { result := cmd.(filler := bytes); nextFiller := true; }
    } else if occ.key == "t" {
      var bytes := Utf8.Encode(value);
      if |bytes| > 1 && value != "\\0" { result := cmd.(mode := Error(MultiTab(value))); }
      else {
        var sep := if value == "" then 10 else if value == "\\0" then 0 else bytes[0] as int;
        if cmd.separator != -1 && cmd.separator != sep { result := cmd.(mode := Error(IncompatibleTabs)); }
        else { result := cmd.(separator := sep, outputSeparator := if value == "" then cmd.outputSeparator else [sep as char]); }
      }
    } else if occ.key == "o" {
      if value == "auto" { result := cmd.(autoformat := true); }
      else { result := AddFormat(cmd, value); status := 3; }
    } else if occ.key == "j" && (occ.rawToken == "-j1" || occ.rawToken == "-j2") {
      status := if occ.rawToken == "-j1" then 1 else 2;
    } else if occ.key == "1" || occ.key == "2" || occ.key == "j" {
      result, next1, next2 := SetField(cmd, if occ.key == "1" then 1 else if occ.key == "2" then 2 else 0,
                                       value, seen1, seen2);
    }
  }

  method AddOperand(cmd: JoinCmdRaw, tags: seq<nat>, text: string, status: nat,
                    seen1: bool, seen2: bool, j1: nat, j2: nat)
    returns (result: JoinCmdRaw, newtags: seq<nat>, nextStatus: nat,
             next1: bool, next2: bool, nextj1: nat, nextj2: nat)
    requires |tags| == |cmd.operands| <= 2
    ensures |newtags| == |result.operands| <= 2
  {
    result := cmd; newtags := tags; nextStatus := if status == 3 then 3 else 0;
    next1 := seen1; next2 := seen2; nextj1 := j1; nextj2 := j2;
    if |tags| == 2 {
      var idx := if tags[0] == 0 then 1 else 0;
      var tag := tags[idx];
      var arg := cmd.operands[idx];
      if tag == 0 { result := cmd.(mode := Error(Extra(text))); return; }
      else if tag == 3 { result := AddFormat(cmd, arg); }
      else {
        result, next1, next2 := SetField(cmd, tag, arg, seen1, seen2);
        if tag == 1 && nextj1 > 0 { nextj1 := nextj1 - 1; }
        if tag == 2 && nextj2 > 0 { nextj2 := nextj2 - 1; }
      }
      if idx == 0 { result := result.(operands := [cmd.operands[1]]); newtags := [tags[1]]; }
      else { result := result.(operands := [cmd.operands[0]]); newtags := [tags[0]]; }
    }
    if IsRunning(result) {
      result := result.(operands := result.operands + [text]); newtags := newtags + [status];
    }
  }

  method DecodeArgv(p: CliTypes.ParsedArgs, argv: seq<string>) returns (cmd: JoinCmdRaw) {
    cmd := DefaultCommand();
    var seen1 := false; var seen2 := false; var seenFiller := false;
    var j1: nat := 0; var j2: nat := 0; var tags: seq<nat> := [];
    var status: nat := 0; var i := 1; var o := 0;
    var endOptions := false;
    while i < |argv| && IsRunning(cmd)
      invariant 1 <= i
      invariant 0 <= o <= |p.options|
      invariant |tags| == |cmd.operands| <= 2
      decreases |argv| - i
    {
      if o < |p.options| && p.options[o].tokenIndex == i {
        var consumed := false;
        while o < |p.options| && p.options[o].tokenIndex == i && IsRunning(cmd)
          invariant 0 <= o <= |p.options|
          decreases |p.options| - o
        {
          var occ := p.options[o];
          cmd, seen1, seen2, seenFiller, status := Apply(cmd, occ, seen1, seen2, seenFiller);
          if status == 1 { j1 := j1 + 1; }
          if status == 2 { j2 := j2 + 1; }
          if occ.value.Some? {
            var at := 1;
            while at < |occ.rawToken| && occ.rawToken[at] in "iz"
              invariant 1 <= at
              decreases |occ.rawToken| - at
            { at := at + 1; }
            consumed := at + 1 == |occ.rawToken|;
          }
          o := o + 1;
        }
        i := i + (if consumed then 2 else 1);
      } else if !endOptions && argv[i] == "--" {
        endOptions := true; status := 0; i := i + 1;
      } else {
        cmd, tags, status, seen1, seen2, j1, j2 := AddOperand(cmd, tags, argv[i], status, seen1, seen2, j1, j2);
        i := i + 1;
      }
    }
    if !IsRunning(cmd) { return; }
    if |cmd.operands| == 0 { cmd := cmd.(mode := Error(Missing)); }
    else if |cmd.operands| == 1 {
      cmd := cmd.(mode := Error(MissingAfter(if |argv| > 1 then argv[|argv|-1] else cmd.operands[0])));
    } else {
      var numericMode := cmd.mode;
      if j1 > 0 { cmd, seen1, seen2 := SetField(cmd, 0, "1", seen1, seen2); }
      if IsRunning(cmd) && j2 > 0 { cmd, seen1, seen2 := SetField(cmd, 0, "2", seen1, seen2); }
      if IsRunning(cmd) { cmd := cmd.(mode := numericMode); }
    }
  }

  method NormalizeParseError(error: CliTypes.ParseError) returns (result: CliTypes.ParseError) {
    result := error;
    var token := error.rawToken;
    if error.kind == CliTypes.UnknownOption && |token|>1 && token[1] != '-' {
      var at := 1;
      while at < |token| && token[at] in "iz"
        invariant 1 <= at <= |token|
        decreases |token|-at
      { at := at+1; }
      if at < |token| { result := error.(rawToken := "-"+[token[at]]); }
    } else if error.kind == CliTypes.UnexpectedValue {
      var at := 0;
      while at < |token| && token[at] != '='
        invariant 0 <= at <= |token|
        decreases |token|-at
      { at := at+1; }
      result := error.(rawToken := token[..at]);
    }
  }

  method Decode(p: CliTypes.ParsedArgs) returns (cmd: JoinCmdRaw) {
    // The process entry supplies original argv to preserve legacy GNU operand status.
    cmd := DefaultCommand();
    var seen1 := false; var seen2 := false; var seenFiller := false;
    var i := 0;
    while i < |p.options| && IsRunning(cmd)
      decreases |p.options| - i
    {
      var status: nat;
      cmd, seen1, seen2, seenFiller, status := Apply(cmd, p.options[i], seen1, seen2, seenFiller);
      if IsRunning(cmd) && (status == 1 || status == 2) {
        var previousMode := cmd.mode;
        cmd, seen1, seen2 := SetField(cmd,0,if status == 1 then "1" else "2",seen1,seen2);
        if IsRunning(cmd) { cmd := cmd.(mode := previousMode); }
      }
      i := i + 1;
    }
    cmd := cmd.(operands := p.positionals);
  }
}
