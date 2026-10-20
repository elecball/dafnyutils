include "ChmodSchema.dfy"
include "../../core/World.dfy"

module ChmodModeCore {
  import BenchWorld
  import opened Schema = ChmodSchema

  function AllOctalDigits(text: string, i: nat): bool
    ensures AllOctalDigits(text, i) == BenchWorld.AllOctalDigits(text, i)
    decreases |text| - i
  {
    if i >= |text| then
      true
    else if !BenchWorld.IsOctalDigit(text[i]) then
      false
    else
      AllOctalDigits(text, i + 1)
  }

  function OctalValue(text: string, i: nat, acc: int): int
    requires i <= |text|
    requires AllOctalDigits(text, i)
    ensures OctalValue(text, i, acc) == BenchWorld.OctalValue(text, i, acc)
    decreases |text| - i
  {
    if i >= |text| then
      acc
    else
      OctalValue(text, i + 1, acc * 8 + BenchWorld.CharToDigit(text[i]))
  }

  function ParseWhoFrom(expr: string, i: nat, acc: bv32): ParseResult<bv32>
    ensures ParseWhoFrom(expr, i, acc) == Schema.ParseWhoFrom(expr, i, acc)
    decreases |expr| - i
  {
    if i >= |expr| then
      Parsed(acc, i)
    else if ModeIsOp(expr[i]) then
      Parsed(acc, i)
    else if ModeIsWhoChar(expr[i]) then
      ParseWhoFrom(expr, i + 1, acc | WhoMask(expr[i]))
    else
      Invalid
  }

  function ParseWho(expr: string, i: nat): ParseResult<bv32>
    ensures ParseWho(expr, i) == Schema.ParseWho(expr, i)
  {
    ParseWhoFrom(expr, i, 0 as bv32)
  }

  function ParseOctalRun(expr: string, i: nat, acc: int): OctalParse
    ensures ParseOctalRun(expr, i, acc) == Schema.ParseOctalRun(expr, i, acc)
    decreases |expr| - i
  {
    if i >= |expr| || !BenchWorld.IsOctalDigit(expr[i]) then
      OctalParse(acc, i)
    else
      ParseOctalRun(expr, i + 1, acc * 8 + BenchWorld.CharToDigit(expr[i]))
  }

  function ParsePerms(expr: string, i: nat, value: bv32, flag: ModeFlag): PermParse
    ensures ParsePerms(expr, i, value, flag) == Schema.ParsePerms(expr, i, value, flag)
    decreases |expr| - i
  {
    if i >= |expr| then
      PermParse(value, flag, i)
    else if expr[i] == 'r' then
      ParsePerms(expr, i + 1, value | READ_MASK, flag)
    else if expr[i] == 'w' then
      ParsePerms(expr, i + 1, value | WRITE_MASK, flag)
    else if expr[i] == 'x' then
      ParsePerms(expr, i + 1, value | EXEC_MASK, flag)
    else if expr[i] == 'X' then
      ParsePerms(expr, i + 1, value, FlagWithX(flag))
    else if expr[i] == 's' then
      ParsePerms(expr, i + 1, value | (S_ISUID | S_ISGID), flag)
    else if expr[i] == 't' then
      ParsePerms(expr, i + 1, value | S_ISVTX, flag)
    else
      PermParse(value, flag, i)
  }

  function ParseOneChange(expr: string, i: nat, affected: bv32): ParseResult<ModeChange>
    ensures ParseOneChange(expr, i, affected) == Schema.ParseOneChange(expr, i, affected)
    decreases |expr| - i
  {
    if i >= |expr| || !ModeIsOp(expr[i]) then
      Invalid
    else
      var op := expr[i];
      var j := i + 1;
      if j >= |expr| then
        var value := 0 as bv32;
        var mentioned := DefaultMentioned(affected, value);
        Parsed(ModeChange(op, ModeOrdinary, affected, value, mentioned), j)
      else if BenchWorld.IsOctalDigit(expr[j]) then
        if affected != 0 as bv32 then
          Invalid
        else
          var octal := ParseOctalRun(expr, j, 0);
          if octal.value > 4095 then
            Invalid
          else if octal.next < |expr| && expr[octal.next] != ',' then
            Invalid
          else
            var value := BenchWorld.NormalizeMode(BenchWorld.ToBv32(octal.value));
            Parsed(
              ModeChange(op, ModeOrdinary, CHMOD_MODE_BITS, value, CHMOD_MODE_BITS),
              octal.next
            )
      else if expr[j] == 'u' || expr[j] == 'g' || expr[j] == 'o' then
        var value := CopySourceMask(expr[j]);
        var mentioned := DefaultMentioned(affected, value);
        Parsed(ModeChange(op, ModeCopyExisting, affected, value, mentioned), j + 1)
      else
        var perms := ParsePerms(expr, j, 0 as bv32, ModeOrdinary);
        var mentioned := DefaultMentioned(affected, perms.value);
        Parsed(ModeChange(op, perms.flag, affected, perms.value, mentioned), perms.next)
  }

  function ParseOpSeq(expr: string, i: nat, affected: bv32): ParseResult<seq<ModeChange>>
    ensures ParseOpSeq(expr, i, affected) == Schema.ParseOpSeq(expr, i, affected)
    decreases |expr| - i
  {
    if i >= |expr| || !ModeIsOp(expr[i]) then
      Invalid
    else
      match ParseOneChange(expr, i, affected)
      case Invalid => Invalid
      case Parsed(change, next) =>
        if next <= i then
          Invalid
        else if next < |expr| && ModeIsOp(expr[next]) then
          match ParseOpSeq(expr, next, affected)
          case Invalid => Invalid
          case Parsed(rest, finalNext) => Parsed([change] + rest, finalNext)
        else
          Parsed([change], next)
  }

  function ParseSymbolic(expr: string, i: nat): ParseResult<seq<ModeChange>>
    ensures ParseSymbolic(expr, i) == Schema.ParseSymbolic(expr, i)
    decreases |expr| - i
  {
    if i >= |expr| then
      Invalid
    else
      match ParseWho(expr, i)
      case Invalid => Invalid
      case Parsed(affected, next) =>
        match ParseOpSeq(expr, next, affected)
        case Invalid => Invalid
        case Parsed(changes, endIdx) =>
          if endIdx < i then
            Invalid
          else if endIdx < |expr| && expr[endIdx] == ',' then
            match ParseSymbolic(expr, endIdx + 1)
            case Invalid => Invalid
            case Parsed(rest, finalNext) => Parsed(changes + rest, finalNext)
          else if endIdx == |expr| then
            Parsed(changes, endIdx)
          else
            Invalid
  }

  function IsValidModeExpr(expr: string): bool
    ensures IsValidModeExpr(expr) == Schema.IsValidModeExpr(expr)
  {
    if |expr| == 0 then
      false
    else if BenchWorld.IsOctalDigit(expr[0]) then
      AllOctalDigits(expr, 0) && OctalValue(expr, 0, 0) <= 4095
    else
      match ParseSymbolic(expr, 0)
      case Invalid => false
      case Parsed(_, endIdx) => endIdx == |expr|
  }
}
