include "../../core/StringEscaping.dfy"

module LognameEscapingCore {
  import BW = BenchWorld
  import Spec = StringEscaping

  function CPrintableByte(byte: char): bool
    ensures CPrintableByte(byte) == Spec.SpecCPrintableByte(byte)
  {
    0x20 <= byte as int <= 0x7e
  }

  function OctDigit(value: int): char
    ensures OctDigit(value) == Spec.SpecOctDigit(value)
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

  function OctalEscape(byte: char): BW.Bytes
    ensures OctalEscape(byte) == Spec.SpecOctalEscape(byte)
  {
    var value := byte as int;
    ['\\', OctDigit((value / 64) % 8), OctDigit((value / 8) % 8), OctDigit(value % 8)]
  }

  function NamedEscape(byte: char): BW.Bytes
    ensures NamedEscape(byte) == Spec.SpecNamedEscape(byte)
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

  function LocaleQuoteByte(byte: char): BW.Bytes
    ensures LocaleQuoteByte(byte) == Spec.SpecLocaleQuoteByte(byte)
  {
    var named := NamedEscape(byte);
    if named != [] then named
    else if byte == '\'' then "\\'"
    else if byte == '\\' then "\\\\"
    else if CPrintableByte(byte) then [byte]
    else OctalEscape(byte)
  }

  function LocaleQuoteBody(bytes: BW.Bytes): BW.Bytes
    ensures LocaleQuoteBody(bytes) == Spec.SpecLocaleQuoteBody(bytes)
    decreases |bytes|
  {
    if |bytes| == 0 then
      []
    else
      LocaleQuoteByte(bytes[0]) + LocaleQuoteBody(bytes[1..])
  }

  function LocaleQuoteBytes(bytes: BW.Bytes): BW.Bytes
    ensures LocaleQuoteBytes(bytes) == Spec.SpecLocaleQuoteBytes(bytes)
  {
    "'" + LocaleQuoteBody(bytes) + "'"
  }
}
