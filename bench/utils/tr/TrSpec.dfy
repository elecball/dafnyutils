include "../../core/World.dfy"
include "../../core/IO.dfy"
include "../../core/IOContract.dfy"
include "../../core/StringEscaping.dfy"
include "TrSchema.dfy"

module TrSpec {

  const MissingSet2MessageSpecText0: BenchWorld.Bytes := "tr: missing operand after "

  const MissingSet2MessageSpecText1: BenchWorld.Bytes := "\nTwo strings must be given when both deleting and squeezing repeats.\n"

  const MissingSet2MessageSpecText2: BenchWorld.Bytes := "\nTwo strings must be given when translating.\n"

  const MissingSet2MessageSpecText3: BenchWorld.Bytes := "Try 'tr --help' for more information.\n"

  const ExtraOperandMessageSpecText0: BenchWorld.Bytes := "tr: extra operand "

  const ExtraOperandMessageSpecText1: BenchWorld.Bytes := "\nOnly one string may be given when deleting without squeezing repeats.\n"

  const ExtraOperandMessageSpecText2: BenchWorld.Bytes := "\n"

  const ExtraOperandMessageSpecText3: BenchWorld.Bytes := "Try 'tr --help' for more information.\n"

  const UnsupportedSetMessageSpecText0: BenchWorld.Bytes := "tr: range-endpoints of '"

  const UnsupportedSetMessageSpecText1: BenchWorld.Bytes := "-"

  const UnsupportedSetMessageSpecText2: BenchWorld.Bytes := "' are in reverse collating sequence order\n"

  const UnsupportedSetMessageSpecText3: BenchWorld.Bytes := "tr: unsupported set syntax '"

  const UnsupportedSetMessageSpecText4: BenchWorld.Bytes := "' in this benchmark\n"

  const AmbiguousOctalWarningSpecText0: BenchWorld.Bytes := "tr: warning: the ambiguous octal escape \\"

  const AmbiguousOctalWarningSpecText1: BenchWorld.Bytes := " is being\n\tinterpreted as the 2-byte sequence \\0"

  const AmbiguousOctalWarningSpecText2: BenchWorld.Bytes := ", "

  const AmbiguousOctalWarningSpecText3: BenchWorld.Bytes := "\n"

  const ReadErrorTextText0: BenchWorld.Bytes := "tr: read error: "

  const ReadErrorTextText1: BenchWorld.Bytes := "\n"

  const WriteErrorTextText0: BenchWorld.Bytes := "tr: write error: "

  const WriteErrorTextText1: BenchWorld.Bytes := "\n"

  import StreamWorld = BenchWorld
  import StreamContract = IOContract

  import Result = Results
  import BenchIO
  import BenchWorld
  import IOContract
  import TrSchema
  import Schema = TrSchema
  import Utf8 = Utf8Semantics
  import SE = StringEscaping




  datatype TrMode =
    | ModeRun
    | ModeHelp
    | ModeVersion
    | ModeMissingOperand(message: BenchWorld.Bytes)
    | ModeExtraOperand(operand: string)
    | ModeUnsupportedSet(operand: string)
    | ModeEmptySet2

  datatype TrCmd = TrCmd(
    mode: TrMode,
    deleteSet: bool,
    squeeze: bool,
    set1: BenchWorld.Bytes,
    set2: BenchWorld.Bytes,
    squeezeSet: BenchWorld.Bytes,
    warnings: BenchWorld.Bytes
  )

  type SetDecode = Result.Result<BenchWorld.Bytes, string>
  datatype ReverseRange = NoReverseRange |
    FoundReverseRange(first: BenchWorld.RawByte, last: BenchWorld.RawByte)

  function HelpTextSpec(): BenchWorld.Bytes
  {
    "Usage: tr [OPTION]... STRING1 [STRING2]\n"
    + "Translate, squeeze, and/or delete characters from standard input,\n"
    + "writing to standard output.  STRING1 and STRING2 specify arrays of\n"
    + "characters ARRAY1 and ARRAY2 that control the action.\n"
    + "\n"
    + "  -c, -C, --complement\n"
    + "         use the complement of ARRAY1\n"
    + "  -d, --delete\n"
    + "         delete characters in ARRAY1, do not translate\n"
    + "  -s, --squeeze-repeats\n"
    + "         replace each sequence of a repeated character\n"
    + "         that is listed in the last specified ARRAY,\n"
    + "         with a single occurrence of that character\n"
    + "  -t, --truncate-set1\n"
    + "         first truncate ARRAY1 to length of ARRAY2\n"
    + "      --help\n"
    + "         display this help and exit\n"
    + "      --version\n"
    + "         output version information and exit\n"
    + "\n"
    + "ARRAYs are specified as strings of characters.  Most represent themselves.\n"
    + "Interpreted sequences are:\n"
    + "\n"
    + "  \\NNN            character with octal value NNN (1 to 3 octal digits)\n"
    + "  \\\\              backslash\n"
    + "  \\a              audible BEL\n"
    + "  \\b              backspace\n"
    + "  \\f              form feed\n"
    + "  \\n              new line\n"
    + "  \\r              return\n"
    + "  \\t              horizontal tab\n"
    + "  \\v              vertical tab\n"
    + "  CHAR1-CHAR2     all characters from CHAR1 to CHAR2 in ascending order\n"
    + "  [CHAR*]         in ARRAY2, copies of CHAR until length of ARRAY1\n"
    + "  [CHAR*REPEAT]   REPEAT copies of CHAR, REPEAT octal if starting with 0\n"
    + "  [:alnum:]       all letters and digits\n"
    + "  [:alpha:]       all letters\n"
    + "  [:blank:]       all horizontal whitespace\n"
    + "  [:cntrl:]       all control characters\n"
    + "  [:digit:]       all digits\n"
    + "  [:graph:]       all printable characters, not including space\n"
    + "  [:lower:]       all lower case letters\n"
    + "  [:print:]       all printable characters, including space\n"
    + "  [:punct:]       all punctuation characters\n"
    + "  [:space:]       all horizontal or vertical whitespace\n"
    + "  [:upper:]       all upper case letters\n"
    + "  [:xdigit:]      all hexadecimal digits\n"
    + "  [=CHAR=]        all characters which are equivalent to CHAR\n"
    + "\n"
    + "Translation occurs if -d is not given and both STRING1 and STRING2 appear.\n"
    + "-t is only significant when translating.  ARRAY2 is extended to length of\n"
    + "ARRAY1 by repeating its last character as necessary.  Excess characters\n"
    + "of ARRAY2 are ignored.  Character classes expand in unspecified order;\n"
    + "while translating, '[:lower:]' and '[:upper:]' may be used in pairs to\n"
    + "specify case conversion.  Squeezing occurs after translation or deletion.\n"
    + "Arguments like '[...]' should be quoted, to avoid potential shell globbing.\n"
    + "\n"
    + "Report bugs to: bug-coreutils@gnu.org\n"
    + "GNU coreutils home page: <https://www.gnu.org/software/coreutils/>\n"
    + "General help using GNU software: <https://www.gnu.org/gethelp/>\n"
    + "Report any translation bugs to <https://translationproject.org/team/>\n"
    + "Full documentation <https://www.gnu.org/software/coreutils/tr>\n"
    + "or available locally via: info '(coreutils) tr invocation'\n"
  }

  function VersionTextSpec(): BenchWorld.Bytes
  {
    "tr (GNU coreutils) 9.10.13-2cf49\n"
    + "Copyright (C) 2026 Free Software Foundation, Inc.\n"
    + "License GPLv3+: GNU GPL version 3 or later <https://gnu.org/licenses/gpl.html>.\n"
    + "This is free software: you are free to change and redistribute it.\n"
    + "There is NO WARRANTY, to the extent permitted by law.\n"
    + "\n"
    + "Written by Jim Meyering.\n"
  }

  function MissingOperandMessageSpec(): BenchWorld.Bytes
  {
    "tr: missing operand\nTry 'tr --help' for more information.\n"
  }

  ghost function MissingSet2MessageSpec(operand: string, deleteAndSqueeze: bool): BenchWorld.Bytes
  {
    MissingSet2MessageSpecText0 + SE.SpecLocaleQuoteBytes(Utf8.Encode(operand)) +
      (if deleteAndSqueeze then
         MissingSet2MessageSpecText1
       else
         MissingSet2MessageSpecText2) +
      MissingSet2MessageSpecText3
  }

  ghost function ExtraOperandMessageSpec(operand: string, explainDeleteLimit: bool): BenchWorld.Bytes
  {
    ExtraOperandMessageSpecText0 + SE.SpecLocaleQuoteBytes(Utf8.Encode(operand)) +
      (if explainDeleteLimit then
         ExtraOperandMessageSpecText1
       else
         ExtraOperandMessageSpecText2) +
      ExtraOperandMessageSpecText3
  }

  ghost function UnsupportedSetMessageSpec(operand: string): BenchWorld.Bytes
  {
    match FirstReverseRangeFrom(operand, 0)
    case FoundReverseRange(first, last) =>
      UnsupportedSetMessageSpecText0 + DisplayRangeByte(first) + UnsupportedSetMessageSpecText1 +
      DisplayRangeByte(last) +
      UnsupportedSetMessageSpecText2
    case NoReverseRange =>
      UnsupportedSetMessageSpecText3 + Utf8.Encode(operand) +
      UnsupportedSetMessageSpecText4
  }

  function EmptySet2MessageSpec(): BenchWorld.Bytes
  {
    "tr: when not deleting, string2 must be non-empty in this benchmark\n"
  }

  ghost function FirstReverseRangeFrom(text: string, i: nat): ReverseRange
    requires i <= |text|
    decreases |text| - i
  {
    if i == |text| then
      NoReverseRange
    else
      var first := AtomBytes(text, i);
      var next := AtomNext(text, i);
      if next + 1 < |text| && text[next] == '-' && |first| == 1 then
        var last := AtomBytes(text, next + 1);
        if |last| == 1 && first[0] as int > last[0] as int then
          FoundReverseRange(first[0], last[0])
        else
          FirstReverseRangeFrom(text, next)
      else
        FirstReverseRangeFrom(text, next)
  }

  function DisplayRangeByte(ch: BenchWorld.RawByte): BenchWorld.Bytes
  {
    if ch as int < 32 || ch as int >= 127 then
      ['\\',
       ((('0' as int) + (ch as int / 64)) as char),
       ((('0' as int) + (ch as int / 8) % 8) as char),
       ((('0' as int) + (ch as int % 8)) as char)]
    else [ch]
  }

  function IsOctal(ch: char): bool
  {
    '0' <= ch <= '7'
  }

  function OctalValue(ch: char): int
    requires IsOctal(ch)
  {
    ch as int - '0' as int
  }

  function SimpleEscape(ch: char): char
  {
    if ch == 'a' then 7 as char
    else if ch == 'b' then 8 as char
    else if ch == 'f' then 12 as char
    else if ch == 'n' then '\n'
    else if ch == 'r' then '\r'
    else if ch == 't' then '\t'
    else if ch == 'v' then 11 as char
    else ch
  }

  function AtomNext(text: string, i: nat): nat
    requires i < |text|
    ensures i < AtomNext(text, i) <= |text|
  {
    if text[i] != '\\' || i + 1 == |text| then i + 1
    else if IsOctal(text[i + 1]) then
      if i + 2 < |text| && IsOctal(text[i + 2]) then
        if i + 3 < |text| && IsOctal(text[i + 3]) &&
           OctalValue(text[i + 1]) < 4 then i + 4
        else i + 3
      else i + 2
    else i + 2
  }

  ghost function AtomBytes(text: string, i: nat): BenchWorld.Bytes
    requires i < |text|
  {
    if text[i] != '\\' then Utf8.EncodeChar(text[i])
    else if i + 1 == |text| then ['\\']
    else if IsOctal(text[i + 1]) then
      if i + 2 < |text| && IsOctal(text[i + 2]) then
        if i + 3 < |text| && IsOctal(text[i + 3]) &&
           OctalValue(text[i + 1]) < 4 then
          [((OctalValue(text[i + 1]) * 64 +
             OctalValue(text[i + 2]) * 8 +
             OctalValue(text[i + 3])) as char)]
        else
          [((OctalValue(text[i + 1]) * 8 +
             OctalValue(text[i + 2])) as char)]
      else [(OctalValue(text[i + 1]) as char)]
    else EscapeBytes(text[i + 1])
  }

  ghost function AmbiguousOctalWarningSpec(text: string, i: nat): BenchWorld.Bytes
    requires i + 3 < |text|
  {
    AmbiguousOctalWarningSpecText0 +
    Utf8.Encode(text[i + 1..i + 4]) +
    AmbiguousOctalWarningSpecText1 +
    Utf8.Encode(text[i + 1..i + 3]) + AmbiguousOctalWarningSpecText2 +
    Utf8.EncodeChar(text[i + 3]) + AmbiguousOctalWarningSpecText3
  }

  function TrailingBackslashWarningSpec(): BenchWorld.Bytes
  {
    "tr: warning: an unescaped backslash at end of string is not portable\n"
  }

  ghost function WarningAtSpec(text: string, i: nat): BenchWorld.Bytes
    requires i < |text|
  {
    if text[i] != '\\' then []
    else if i + 1 == |text| then TrailingBackslashWarningSpec()
    else if i + 3 < |text| && IsOctal(text[i + 1]) &&
            IsOctal(text[i + 2]) && IsOctal(text[i + 3]) &&
            OctalValue(text[i + 1]) >= 4 then
      AmbiguousOctalWarningSpec(text, i)
    else []
  }

  ghost function EscapeBytes(ch: char): BenchWorld.Bytes
  {
    if ch == 'a' || ch == 'b' || ch == 'f' || ch == 'n' ||
       ch == 'r' || ch == 't' || ch == 'v' then
      [SimpleEscape(ch)]
    else
      Utf8.EncodeChar(ch)
  }

  // Ghost, so the adjacent-pair test can be the existential it actually is and
  // the single-character test can be plain membership. `ContainsCharFrom` is
  // gone entirely: it was sequence membership written as index recursion.
  ghost predicate ContainsPair(text: string, first: char, second: char)
  {
    exists k :: 0 <= k < |text| - 1 && text[k] == first && text[k + 1] == second
  }

  ghost predicate StartsUnsupportedConstruct(text: string)
  {
    |text| > 0 && text[0] == '[' && (
      (1 < |text| && text[1] == ':' && ContainsPair(text[2..], ':', ']')) ||
      (1 < |text| && text[1] == '=' && ContainsPair(text[2..], '=', ']')) ||
      (2 < |text| && text[2] == '*' && ']' in text[3..])
    )
  }

  // Formal specification gap: GNU bracket classes, repeats,
  // complement/truncate modes and locale-dependent collation are intentionally
  // rejected by this relation until modeled explicitly.
  ghost predicate RangeExpansion(lo: char, hi: char, bytes: BenchWorld.Bytes)
  {
    0 <= lo as int < 256 &&
    0 <= hi as int < 256 &&
    lo as int <= hi as int &&
    |bytes| == (hi as int) - (lo as int) + 1 &&
    forall i :: 0 <= i < |bytes| ==>
                  bytes[i] as int == lo as int + i
  }

  ghost predicate SetAtomRelation(
    text: string, lo: nat, hi: nat, bytes: BenchWorld.Bytes
  )
  {
    lo < |text| &&
    if text[lo] != '\\' then
      hi == lo + 1 && bytes == Utf8.EncodeChar(text[lo])
    else if lo + 1 == |text| then
      hi == lo + 1 && bytes == ['\\']
    else if IsOctal(text[lo + 1]) then
      if lo + 2 < |text| && IsOctal(text[lo + 2]) then
        if lo + 3 < |text| && IsOctal(text[lo + 3]) &&
           OctalValue(text[lo + 1]) < 4 then
          hi == lo + 4 &&
          bytes == [((OctalValue(text[lo + 1]) * 64 +
                      OctalValue(text[lo + 2]) * 8 +
                      OctalValue(text[lo + 3])) as char)]
        else
          hi == lo + 3 &&
          bytes == [((OctalValue(text[lo + 1]) * 8 +
                      OctalValue(text[lo + 2])) as char)]
      else
        hi == lo + 2 &&
        bytes == [(OctalValue(text[lo + 1]) as char)]
    else
      hi == lo + 2 && bytes == EscapeBytes(text[lo + 1])
  }

  opaque ghost predicate SetUnitRelation(
    text: string,
    lo: nat,
    hi: nat,
    bytes: BenchWorld.Bytes
  )
  {
    lo < |text| &&
    !StartsUnsupportedConstruct(text[lo..]) &&
    exists atomEnd: nat, atomBytes: BenchWorld.Bytes ::
      SetAtomRelation(text, lo, atomEnd, atomBytes) &&
      if atomEnd < |text| && text[atomEnd] == '-' &&
         atomEnd + 1 < |text| then
        exists endEnd: nat, endBytes: BenchWorld.Bytes
          {:trigger SetAtomRelation(text, atomEnd + 1, endEnd, endBytes)} ::
          SetAtomRelation(text, atomEnd + 1, endEnd, endBytes) &&
          |atomBytes| == 1 && |endBytes| == 1 &&
          hi == endEnd &&
          RangeExpansion(atomBytes[0], endBytes[0], bytes)
      else
        hi == atomEnd && bytes == atomBytes
  }

  ghost predicate SetPartitionFrom(
    text: string,
    start: nat,
    bytes: BenchWorld.Bytes,
    inputCuts: seq<nat>,
    outputCuts: seq<nat>
  )
  {
    |inputCuts| == |outputCuts| &&
    0 < |inputCuts| &&
    start <= |text| &&
    inputCuts[0] == start &&
    outputCuts[0] == 0 &&
    inputCuts[|inputCuts| - 1] == |text| &&
    outputCuts[|outputCuts| - 1] == |bytes| &&
    forall i
      {:trigger inputCuts[i], inputCuts[i + 1]}
      {:trigger bytes[outputCuts[i]..outputCuts[i + 1]]} ::
      0 <= i && i + 1 < |inputCuts| ==>
        inputCuts[i] < inputCuts[i + 1] <= |text| &&
        outputCuts[i] <= outputCuts[i + 1] <= |bytes| &&
        SetUnitRelation(
          text,
          inputCuts[i],
          inputCuts[i + 1],
          bytes[outputCuts[i]..outputCuts[i + 1]]
        )
  }

  ghost predicate SetPartition(
    text: string,
    bytes: BenchWorld.Bytes,
    inputCuts: seq<nat>,
    outputCuts: seq<nat>
  )
  {
    SetPartitionFrom(text, 0, bytes, inputCuts, outputCuts)
  }

  ghost predicate SetBytesRelation(text: string, bytes: BenchWorld.Bytes)
  {
    exists inputCuts: seq<nat>, outputCuts: seq<nat> ::
      SetPartition(text, bytes, inputCuts, outputCuts)
  }

  ghost predicate WarningPartitionFrom(
    text: string,
    start: nat,
    warnings: BenchWorld.Bytes,
    inputCuts: seq<nat>,
    outputCuts: seq<nat>
  )
  {
    |inputCuts| == |outputCuts| &&
    0 < |inputCuts| &&
    start <= |text| &&
    inputCuts[0] == start &&
    outputCuts[0] == 0 &&
    inputCuts[|inputCuts| - 1] == |text| &&
    outputCuts[|outputCuts| - 1] == |warnings| &&
    forall i
      {:trigger inputCuts[i], inputCuts[i + 1]}
      {:trigger warnings[outputCuts[i]..outputCuts[i + 1]]} ::
      0 <= i && i + 1 < |inputCuts| ==>
        inputCuts[i] < inputCuts[i + 1] <= |text| &&
        inputCuts[i + 1] == AtomNext(text, inputCuts[i]) &&
        outputCuts[i] <= outputCuts[i + 1] <= |warnings| &&
        warnings[outputCuts[i]..outputCuts[i + 1]] ==
          WarningAtSpec(text, inputCuts[i])
  }

  ghost predicate WarningBytesRelation(
    text: string, warnings: BenchWorld.Bytes
  )
  {
    exists inputCuts: seq<nat>, outputCuts: seq<nat> ::
      WarningPartitionFrom(text, 0, warnings, inputCuts, outputCuts)
  }

  ghost predicate CommandWarningsRelation(
    raw: TrSchema.TrCmdRaw,
    decoded: seq<SetDecode>,
    warnings: BenchWorld.Bytes
  )
    requires |decoded| == |raw.operands|
  {
    if |raw.operands| == 0 then
      warnings == []
    else
      exists first: BenchWorld.Bytes ::
        WarningBytesRelation(raw.operands[0], first) &&
        (if |raw.operands| > 1 && decoded[0].Ok? then
           exists second: BenchWorld.Bytes ::
             WarningBytesRelation(raw.operands[1], second) &&
             warnings == first + second
         else warnings == first)
  }

  ghost predicate SetDecodeRelation(text: string, decoded: SetDecode)
  {
    (exists bytes: BenchWorld.Bytes ::
       SetBytesRelation(text, bytes) &&
       decoded == Result.Ok(bytes)) ||
    ((forall bytes: BenchWorld.Bytes :: !SetBytesRelation(text, bytes)) &&
     decoded == Result.Err(text))
  }

  ghost predicate DecodedOperandsRelation(
    operands: seq<string>,
    decoded: seq<SetDecode>
  )
  {
    |decoded| == |operands| &&
    forall i :: 0 <= i < |operands| ==>
                  SetDecodeRelation(operands[i], decoded[i])
  }

  function DecodedBytes(decoded: SetDecode): BenchWorld.Bytes
  {
    match decoded
    case Ok(bytes) => bytes
    case Err(_) => []
  }

  ghost predicate FirstUnsupportedOperandRelation(
    operands: seq<string>,
    decoded: seq<SetDecode>,
    operand: string
  )
  {
    |decoded| == |operands| &&
    exists i ::
      0 <= i < |operands| &&
      decoded[i] == Result.Err(operands[i]) &&
      operand == operands[i] &&
      forall j :: 0 <= j < i ==> decoded[j].Ok?
  }

  ghost predicate CommandDecodedRelation(
    raw: TrSchema.TrCmdRaw,
    decoded: seq<SetDecode>,
    cmd: TrCmd
  )
  {
    DecodedOperandsRelation(raw.operands, decoded) &&
    cmd.deleteSet == raw.seenDelete &&
    cmd.squeeze == raw.seenSqueeze &&
    cmd.set1 ==
    (if |raw.operands| > 0 then DecodedBytes(decoded[0]) else []) &&
    cmd.set2 ==
    (if |raw.operands| > 1 then DecodedBytes(decoded[1]) else []) &&
    cmd.squeezeSet ==
    (if raw.seenSqueeze && |raw.operands| > 1 then
       DecodedBytes(decoded[1])
     else if |raw.operands| > 0 then
       DecodedBytes(decoded[0])
     else
       []) &&
    CommandWarningsRelation(raw, decoded, cmd.warnings) &&
    if raw.seenHelp &&
       (!raw.seenVersion || raw.helpTokenIndex <= raw.versionTokenIndex) then
      cmd.mode == ModeHelp
    else if raw.seenVersion then
      cmd.mode == ModeVersion
    else if |raw.operands| == 0 then
      cmd.mode == ModeMissingOperand(MissingOperandMessageSpec())
    else if !raw.seenDelete && !raw.seenSqueeze &&
            |raw.operands| == 1 then
      cmd.mode == ModeMissingOperand(MissingSet2MessageSpec(raw.operands[0], false))
    else if raw.seenDelete && raw.seenSqueeze &&
            |raw.operands| == 1 then
      cmd.mode == ModeMissingOperand(MissingSet2MessageSpec(raw.operands[0], true))
    else if raw.seenDelete && !raw.seenSqueeze &&
            |raw.operands| > 1 then
      cmd.mode == ModeExtraOperand(raw.operands[1])
    else if |raw.operands| > 2 then
      cmd.mode == ModeExtraOperand(raw.operands[2])
    else if exists operand ::
              FirstUnsupportedOperandRelation(raw.operands, decoded, operand) then
      exists operand ::
        FirstUnsupportedOperandRelation(raw.operands, decoded, operand) &&
        cmd.mode == ModeUnsupportedSet(operand)
    else if !raw.seenDelete && |raw.operands| == 2 &&
            |DecodedBytes(decoded[1])| == 0 then
      cmd.mode == ModeEmptySet2
    else
      cmd.mode == ModeRun
  }

  ghost predicate CommandRelation(raw: TrSchema.TrCmdRaw, cmd: TrCmd)
  {
    exists decoded: seq<SetDecode> ::
      CommandDecodedRelation(raw, decoded, cmd)
  }

  ghost predicate StrictlyIncreasing(indices: seq<nat>)
  {
    forall i, j :: 0 <= i < j < |indices| ==>
                     indices[i] < indices[j]
  }

  ghost predicate TranslationRelation(
    set1: BenchWorld.Bytes,
    set2: BenchWorld.Bytes,
    inputByte: char,
    outputByte: char
  )
  {
    if inputByte !in set1 then
      outputByte == inputByte
    else
      |set2| > 0 &&
      exists i ::
        0 <= i < |set1| &&
        set1[i] == inputByte &&
        (forall j :: i < j < |set1| ==> set1[j] != inputByte) &&
        outputByte == set2[if i < |set2| then i else |set2| - 1]
  }

  ghost predicate DeleteTranslateRelation(
    cmd: TrCmd,
    input: BenchWorld.Bytes,
    transformed: BenchWorld.Bytes
  )
  {
    exists kept: seq<nat> ::
      StrictlyIncreasing(kept) &&
      (forall k :: 0 <= k < |kept| ==> kept[k] < |input|) &&
      (forall i :: 0 <= i < |input| ==>
                     (i in kept) ==
                     (!cmd.deleteSet || input[i] !in cmd.set1)) &&
      |transformed| == |kept| &&
      (forall k :: 0 <= k < |kept| ==>
                     (if cmd.deleteSet || |cmd.set2| == 0 then
                        transformed[k] == input[kept[k]]
                      else
                        TranslationRelation(
                          cmd.set1,
                          cmd.set2,
                          input[kept[k]],
                          transformed[k]
                        )))
  }

  ghost predicate SqueezeStateRelation(
    input: BenchWorld.Bytes,
    squeezeSet: BenchWorld.Bytes,
    hasPrevious: bool,
    previous: char,
    output: BenchWorld.Bytes
  )
  {
    exists emitted: seq<nat> ::
      StrictlyIncreasing(emitted) &&
      (forall k :: 0 <= k < |emitted| ==> emitted[k] < |input|) &&
      (forall i :: 0 <= i < |input| ==>
                     (i in emitted) ==
                     SqueezeEmittedAt(
                       input, squeezeSet, hasPrevious, previous, i
                     )) &&
      |output| == |emitted| &&
      (forall k :: 0 <= k < |emitted| ==>
                     output[k] == input[emitted[k]])
  }

  ghost predicate SqueezeEmittedAt(
    input: BenchWorld.Bytes,
    squeezeSet: BenchWorld.Bytes,
    hasPrevious: bool,
    previous: char,
    i: nat
  )
    requires i < |input|
  {
    input[i] !in squeezeSet ||
    (if i == 0 then
       !hasPrevious || input[i] != previous
     else
       input[i] != input[i - 1])
  }

  ghost predicate SqueezeRelation(
    input: BenchWorld.Bytes,
    squeezeSet: BenchWorld.Bytes,
    output: BenchWorld.Bytes
  )
  {
    SqueezeStateRelation(input, squeezeSet, false, '\0', output)
  }

  ghost predicate OutputRelation(
    cmd: TrCmd,
    input: BenchWorld.Bytes,
    output: BenchWorld.Bytes
  )
  {
    exists transformed: BenchWorld.Bytes ::
      DeleteTranslateRelation(cmd, input, transformed) &&
      if cmd.squeeze then
        SqueezeRelation(transformed, cmd.squeezeSet, output)
      else
        output == transformed
  }

  ghost function ReadErrorText(reason: string): BenchWorld.Bytes
  {
    ReadErrorTextText0 + Utf8.Encode(reason) + ReadErrorTextText1
  }

  ghost function ReadError(err: int): BenchWorld.Bytes
  {
    ReadErrorText(IOContract.CLocaleErrnoTextResult(err))
  }


  ghost function WriteErrorText(reason: string): StreamWorld.Bytes
  {
    WriteErrorTextText0 + Utf8.Encode(reason) + WriteErrorTextText1
  }

  function WriteErrorAfterReadFailure(): StreamWorld.Bytes
  {
    "tr: write error\n"
  }

  ghost predicate EmissionOutcomeFields(
    beforeOut: StreamWorld.Bytes, beforeErr: StreamWorld.Bytes,
    afterOut: StreamWorld.Bytes, afterErr: StreamWorld.Bytes,
    observations: (StreamWorld.TrustedStreamRequest) -> StreamWorld.TrustedStreamResult,
    output: StreamWorld.Bytes, diagnostics: StreamWorld.Bytes,
    normalExit: int, exit: int,
    committed: nat, outErr: int, errCommitted: nat, errErr: int
  )
  {
    (if |output| == 0 then afterOut == beforeOut && committed == 0 && outErr == 0
     else StreamContract.WriteStdoutSpec(beforeOut, observations, afterOut, output, committed, outErr)) &&
    var finalDiagnostics := diagnostics +
      (if outErr == 0 then []
       else if normalExit != 0 then WriteErrorAfterReadFailure()
       else WriteErrorText(StreamContract.CLocaleErrnoTextResult(outErr)));
    (if |finalDiagnostics| == 0 then afterErr == beforeErr && errCommitted == 0 && errErr == 0
     else StreamContract.WriteStderrSpec(beforeErr, observations, afterErr, finalDiagnostics, errCommitted, errErr)) &&
    exit == (if outErr != 0 || errErr != 0 then 1 else normalExit)
  }

  ghost predicate EmissionFields(
    beforeOut: StreamWorld.Bytes, beforeErr: StreamWorld.Bytes,
    afterOut: StreamWorld.Bytes, afterErr: StreamWorld.Bytes,
    observations: (StreamWorld.TrustedStreamRequest) -> StreamWorld.TrustedStreamResult,
    output: StreamWorld.Bytes, diagnostics: StreamWorld.Bytes,
    normalExit: int, exit: int
  )
  {
    exists committed: nat, outErr: int, errCommitted: nat, errErr: int ::
      EmissionOutcomeFields(beforeOut, beforeErr, afterOut, afterErr, observations,
                            output, diagnostics, normalExit, exit,
                            committed, outErr, errCommitted, errErr)
  }
  twostate predicate PreparedSpec(raw: TrSchema.TrCmdRaw, io: BenchIO.IO, exit: int, plannedStdout: StreamWorld.Bytes, plannedStderr: StreamWorld.Bytes)
    reads io.Footprint()
  {
    exists cmd: TrCmd ::
      CommandRelation(raw, cmd) &&
      match cmd.mode
      case ModeHelp =>
        io.stdin() == old(io.stdin()) &&
        plannedStdout == old(io.stdout()) + HelpTextSpec() &&
        plannedStderr == old(io.stderr()) &&
        exit == 0
      case ModeVersion =>
        io.stdin() == old(io.stdin()) &&
        plannedStdout == old(io.stdout()) + VersionTextSpec() &&
        plannedStderr == old(io.stderr()) &&
        exit == 0
      case ModeMissingOperand(message) =>
        io.stdin() == old(io.stdin()) &&
        plannedStdout == old(io.stdout()) &&
        plannedStderr == old(io.stderr()) + message &&
        exit == 1
      case ModeExtraOperand(operand) =>
        io.stdin() == old(io.stdin()) &&
        plannedStdout == old(io.stdout()) &&
        plannedStderr == old(io.stderr()) +
          ExtraOperandMessageSpec(operand, |raw.operands| == 2) &&
        exit == 1
      case ModeUnsupportedSet(operand) =>
        io.stdin() == old(io.stdin()) &&
        plannedStdout == old(io.stdout()) &&
        plannedStderr == old(io.stderr()) + cmd.warnings +
          UnsupportedSetMessageSpec(operand) &&
        exit == 1
      case ModeEmptySet2 =>
        io.stdin() == old(io.stdin()) &&
        plannedStdout == old(io.stdout()) &&
        plannedStderr == old(io.stderr()) + EmptySet2MessageSpec() &&
        exit == 1
      case ModeRun =>
        var read := IOContract.ObservedReadStdinResultFields(old(io.stdin()), old(io.trustedStreams()));
        var input := IOContract.ReadResultData(read);
        io.stdin() == IOContract.ObservedReadStdinRemainingFields(old(io.stdin()), old(io.trustedStreams())) &&
        (exists output: BenchWorld.Bytes ::
           OutputRelation(cmd, input, output) &&
           plannedStdout == old(io.stdout()) + output) &&
        plannedStderr == old(io.stderr()) + cmd.warnings +
          (if read.Ok? then [] else ReadError(IOContract.ResultErrno(read))) &&
        exit == (if read.Ok? then 0 else 1)
  }

  twostate predicate Spec(raw: Schema.TrCmdRaw, io: BenchIO.IO, exit: int)
    reads io.Footprint()
  {
    exists output: StreamWorld.Bytes, diagnostics: StreamWorld.Bytes, normalExit: int ::
      PreparedSpec(raw, io, normalExit, old(io.stdout()) + output, old(io.stderr()) + diagnostics) &&
      EmissionFields(old(io.stdout()), old(io.stderr()), io.stdout(), io.stderr(),
                     io.trustedStreams(), output, diagnostics, normalExit, exit)
  }
}
