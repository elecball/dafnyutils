include "../../core/Utf8.dfy"

module PasteUtf8Core {
  import BW = BenchWorld
  import Spec = Utf8Semantics

  function EncodeChar(ch: char): BW.Bytes
    ensures EncodeChar(ch) == Spec.EncodeChar(ch)
    ensures |EncodeChar(ch)| == BW.Utf8ByteWidth(ch)
    ensures 1 <= |EncodeChar(ch)| <= 4
  {
    var code := ch as int;
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
      ]
  }

  function Encode(text: string): BW.Bytes
    ensures Encode(text) == Spec.Encode(text)
    ensures |Encode(text)| >= |text|
    decreases |text|
  {
    if text == [] then [] else EncodeChar(text[0]) + Encode(text[1..])
  }

}
