include "../../core/StringEscaping.dfy"

module TouchEscapingCore {
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
