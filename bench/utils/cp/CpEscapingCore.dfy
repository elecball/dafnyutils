include "../../core/StringEscaping.dfy"

module CpEscapingCore {
  import BW = BenchWorld
  import Model = StringEscaping

  function SpecCPrintableByte(byte: char): bool
    ensures SpecCPrintableByte(byte) == Model.SpecCPrintableByte(byte)
  {
    0x20 <= byte as int <= 0x7e
  }

  function SpecOctDigit(value: int): char
    ensures SpecOctDigit(value) == Model.SpecOctDigit(value)
  {
    if value == 0 then '0'
    else if value == 1 then '1'
    else if value == 2 then '2'
    else if value == 3 then '3'
    else if value == 4 then '4'
    else if value == 5 then '5'
    else if value == 6 then '6'
    else '7'
  }

  function SpecOctalEscape(byte: char): BW.Bytes
    ensures SpecOctalEscape(byte) == Model.SpecOctalEscape(byte)
  {
    var value := byte as int;
    ['\\', SpecOctDigit((value / 64) % 8), SpecOctDigit((value / 8) % 8), SpecOctDigit(value % 8)]
  }

  function SpecNamedEscape(byte: char): BW.Bytes
    ensures SpecNamedEscape(byte) == Model.SpecNamedEscape(byte)
  {
    if byte == 7 as char then "\\a"
    else if byte == 8 as char then "\\b"
    else if byte == 12 as char then "\\f"
    else if byte == '\n' then "\\n"
    else if byte == '\r' then "\\r"
    else if byte == '\t' then "\\t"
    else if byte == 11 as char then "\\v"
    else []
  }

  function SpecAnsiEscape(byte: char): BW.Bytes
    ensures SpecAnsiEscape(byte) == Model.SpecAnsiEscape(byte)
  {
    var named := SpecNamedEscape(byte);
    if named != [] then named else SpecOctalEscape(byte)
  }

  function SpecNeedsAnsiEscape(byte: char): bool
    ensures SpecNeedsAnsiEscape(byte) == Model.SpecNeedsAnsiEscape(byte)
  {
    !SpecCPrintableByte(byte)
  }

  function SpecCQuoteByte(byte: char): BW.Bytes
    ensures SpecCQuoteByte(byte) == Model.SpecCQuoteByte(byte)
  {
    var named := SpecNamedEscape(byte);
    if named != [] then named
    else if byte == '\\' then "\\\\"
    else if byte == '"' then "\\\""
    else if SpecCPrintableByte(byte) then [byte]
    else SpecOctalEscape(byte)
  }

  function SpecCQuoteBytes(bytes: BW.Bytes): BW.Bytes
    ensures SpecCQuoteBytes(bytes) == Model.SpecCQuoteBytes(bytes)
    decreases |bytes|
  {
    if |bytes| == 0 then
      []
    else
      SpecCQuoteByte(bytes[0]) + SpecCQuoteBytes(bytes[1..])
  }

  function SpecDoubleQuote(bytes: BW.Bytes): BW.Bytes
    ensures SpecDoubleQuote(bytes) == Model.SpecDoubleQuote(bytes)
  {
    "\"" + SpecCQuoteBytes(bytes) + "\""
  }

  function SpecShellCompatibleByte(byte: char, atStart: bool, singleton: bool): bool
    ensures SpecShellCompatibleByte(byte, atStart, singleton) == Model.SpecShellCompatibleByte(byte, atStart, singleton)
  {
    if byte == '?' || byte == '\\' then
      false
    else if byte == '{' || byte == '}' then
      singleton
    else if byte == '#' || byte == '~' then
      atStart
    else if byte == ' ' || byte == '\'' then
      true
    else if byte == '!' || byte == '"' || byte == '$' || byte == '&' ||
            byte == '(' || byte == ')' || byte == '*' || byte == ';' ||
            byte == '<' || byte == '=' || byte == '>' || byte == '[' ||
            byte == '^' || byte == '`' || byte == '|' then
      false
    else
      SpecCPrintableByte(byte)
  }

  function SpecShellCompatibleTail(bytes: BW.Bytes): bool
    ensures SpecShellCompatibleTail(bytes) == Model.SpecShellCompatibleTail(bytes)
    decreases |bytes|
  {
    |bytes| == 0 ||
    (SpecShellCompatibleByte(bytes[0], false, false) &&
     SpecShellCompatibleTail(bytes[1..]))
  }

  function SpecAllShellCompatible(bytes: BW.Bytes): bool
    ensures SpecAllShellCompatible(bytes) == Model.SpecAllShellCompatible(bytes)
  {
    |bytes| == 0 ||
    (SpecShellCompatibleByte(bytes[0], true, |bytes| == 1) &&
     SpecShellCompatibleTail(bytes[1..]))
  }

  function SpecContainsApostrophe(bytes: BW.Bytes): bool
    ensures SpecContainsApostrophe(bytes) == Model.SpecContainsApostrophe(bytes)
  {
    '\'' in bytes
  }

  function SpecShellEscapeTail(bytes: BW.Bytes, ansi: bool): BW.Bytes
    ensures SpecShellEscapeTail(bytes, ansi) == Model.SpecShellEscapeTail(bytes, ansi)
    decreases |bytes|
  {
    if |bytes| == 0 then
      "'"
    else
      var byte := bytes[0];
      if byte == '\'' then
        "'\\''" + SpecShellEscapeTail(bytes[1..], false)
      else if SpecNeedsAnsiEscape(byte) then
        (if ansi then [] else "'$'") + SpecAnsiEscape(byte) +
        SpecShellEscapeTail(bytes[1..], true)
      else
        (if ansi then "''" else []) + [byte] +
        SpecShellEscapeTail(bytes[1..], false)
  }

  function SpecQuoteAfBytes(bytes: BW.Bytes): BW.Bytes
    ensures SpecQuoteAfBytes(bytes) == Model.SpecQuoteAfBytes(bytes)
  {
    if SpecContainsApostrophe(bytes) && SpecAllShellCompatible(bytes) then
      SpecDoubleQuote(bytes)
    else
      "'" + SpecShellEscapeTail(bytes, false)
  }

  function SpecShellQuoteTriggerByte(byte: char, atStart: bool, singleton: bool): bool
    ensures SpecShellQuoteTriggerByte(byte, atStart, singleton) == Model.SpecShellQuoteTriggerByte(byte, atStart, singleton)
  {
    !SpecCPrintableByte(byte) ||
    byte == '\\' || byte == '\'' || byte == '?' || byte == ':' ||
    byte == ' ' || byte == '!' || byte == '"' || byte == '$' ||
    byte == '&' || byte == '(' || byte == ')' || byte == '*' ||
    byte == ';' || byte == '<' || byte == '=' || byte == '>' ||
    byte == '[' || byte == '^' || byte == '`' || byte == '|' ||
    ((byte == '#' || byte == '~') && atStart) ||
    ((byte == '{' || byte == '}') && singleton)
  }

  function SpecHasShellQuoteTriggerTail(bytes: BW.Bytes): bool
    ensures SpecHasShellQuoteTriggerTail(bytes) == Model.SpecHasShellQuoteTriggerTail(bytes)
    decreases |bytes|
  {
    |bytes| != 0 &&
    (SpecShellQuoteTriggerByte(bytes[0], false, false) ||
     SpecHasShellQuoteTriggerTail(bytes[1..]))
  }

  function SpecHasShellQuoteTrigger(bytes: BW.Bytes): bool
    ensures SpecHasShellQuoteTrigger(bytes) == Model.SpecHasShellQuoteTrigger(bytes)
  {
    |bytes| != 0 &&
    (SpecShellQuoteTriggerByte(bytes[0], true, |bytes| == 1) ||
     SpecHasShellQuoteTriggerTail(bytes[1..]))
  }

  function SpecQuoteFBytes(bytes: BW.Bytes): BW.Bytes
    ensures SpecQuoteFBytes(bytes) == Model.SpecQuoteFBytes(bytes)
  {
    if |bytes| == 0 || SpecHasShellQuoteTrigger(bytes) then
      SpecQuoteAfBytes(bytes)
    else
      bytes
  }

  function SpecLocaleQuoteByte(byte: char): BW.Bytes
    ensures SpecLocaleQuoteByte(byte) == Model.SpecLocaleQuoteByte(byte)
  {
    var named := SpecNamedEscape(byte);
    if named != [] then named
    else if byte == '\'' then "\\'"
    else if byte == '\\' then "\\\\"
    else if SpecCPrintableByte(byte) then [byte]
    else SpecOctalEscape(byte)
  }

  function SpecLocaleQuoteBody(bytes: BW.Bytes): BW.Bytes
    ensures SpecLocaleQuoteBody(bytes) == Model.SpecLocaleQuoteBody(bytes)
    decreases |bytes|
  {
    if |bytes| == 0 then
      []
    else
      SpecLocaleQuoteByte(bytes[0]) + SpecLocaleQuoteBody(bytes[1..])
  }

  function SpecLocaleQuoteBytes(bytes: BW.Bytes): BW.Bytes
    ensures SpecLocaleQuoteBytes(bytes) == Model.SpecLocaleQuoteBytes(bytes)
  {
    "'" + SpecLocaleQuoteBody(bytes) + "'"
  }
}
