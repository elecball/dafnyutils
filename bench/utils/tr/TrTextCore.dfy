include "TrSpec.dfy"
include "TrUtf8Core.dfy"
include "TrEscapingCore.dfy"

module TrTextCore {
  import opened Model = TrSpec
  import StreamWorld = BenchWorld
  import StreamContract = IOContract
  import Result = Results
  import BenchIO
  import BenchWorld
  import IOContract
  import TrSchema
  import Schema = TrSchema
  import Utf8 = TrUtf8Core
  import SE = TrEscapingCore

  function MissingSet2MessageSpec(operand: string, deleteAndSqueeze: bool): BenchWorld.Bytes
    ensures MissingSet2MessageSpec(operand, deleteAndSqueeze) == Model.MissingSet2MessageSpec(operand, deleteAndSqueeze)
  {
    Model.MissingSet2MessageSpecText0 + SE.SpecLocaleQuoteBytes(Utf8.Encode(operand)) +
      (if deleteAndSqueeze then
         Model.MissingSet2MessageSpecText1
       else
         Model.MissingSet2MessageSpecText2) +
      Model.MissingSet2MessageSpecText3
  }

  function ExtraOperandMessageSpec(operand: string, explainDeleteLimit: bool): BenchWorld.Bytes
    ensures ExtraOperandMessageSpec(operand, explainDeleteLimit) == Model.ExtraOperandMessageSpec(operand, explainDeleteLimit)
  {
    Model.ExtraOperandMessageSpecText0 + SE.SpecLocaleQuoteBytes(Utf8.Encode(operand)) +
      (if explainDeleteLimit then
         Model.ExtraOperandMessageSpecText1
       else
         Model.ExtraOperandMessageSpecText2) +
      Model.ExtraOperandMessageSpecText3
  }

  function UnsupportedSetMessageSpec(operand: string): BenchWorld.Bytes
    ensures UnsupportedSetMessageSpec(operand) == Model.UnsupportedSetMessageSpec(operand)
  {
    match FirstReverseRangeFrom(operand, 0)
    case FoundReverseRange(first, last) =>
      Model.UnsupportedSetMessageSpecText0 + DisplayRangeByte(first) + Model.UnsupportedSetMessageSpecText1 +
      DisplayRangeByte(last) +
      Model.UnsupportedSetMessageSpecText2
    case NoReverseRange =>
      Model.UnsupportedSetMessageSpecText3 + Utf8.Encode(operand) +
      Model.UnsupportedSetMessageSpecText4
  }

  function FirstReverseRangeFrom(text: string, i: nat): ReverseRange
    requires i <= |text|
    ensures FirstReverseRangeFrom(text, i) == Model.FirstReverseRangeFrom(text, i)
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

  function AtomBytes(text: string, i: nat): BenchWorld.Bytes
    requires i < |text|
    ensures AtomBytes(text, i) == Model.AtomBytes(text, i)
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

  function AmbiguousOctalWarningSpec(text: string, i: nat): BenchWorld.Bytes
    requires i + 3 < |text|
    ensures AmbiguousOctalWarningSpec(text, i) == Model.AmbiguousOctalWarningSpec(text, i)
  {
    Model.AmbiguousOctalWarningSpecText0 +
    Utf8.Encode(text[i + 1..i + 4]) +
    Model.AmbiguousOctalWarningSpecText1 +
    Utf8.Encode(text[i + 1..i + 3]) + Model.AmbiguousOctalWarningSpecText2 +
    Utf8.EncodeChar(text[i + 3]) + Model.AmbiguousOctalWarningSpecText3
  }

  function WarningAtSpec(text: string, i: nat): BenchWorld.Bytes
    requires i < |text|
    ensures WarningAtSpec(text, i) == Model.WarningAtSpec(text, i)
  {
    if text[i] != '\\' then []
    else if i + 1 == |text| then TrailingBackslashWarningSpec()
    else if i + 3 < |text| && IsOctal(text[i + 1]) &&
            IsOctal(text[i + 2]) && IsOctal(text[i + 3]) &&
            OctalValue(text[i + 1]) >= 4 then
      AmbiguousOctalWarningSpec(text, i)
    else []
  }

  function EscapeBytes(ch: char): BenchWorld.Bytes
    ensures EscapeBytes(ch) == Model.EscapeBytes(ch)
  {
    if ch == 'a' || ch == 'b' || ch == 'f' || ch == 'n' ||
       ch == 'r' || ch == 't' || ch == 'v' then
      [SimpleEscape(ch)]
    else
      Utf8.EncodeChar(ch)
  }

  function ReadErrorText(reason: string): BenchWorld.Bytes
    ensures ReadErrorText(reason) == Model.ReadErrorText(reason)
  {
    Model.ReadErrorTextText0 + Utf8.Encode(reason) + Model.ReadErrorTextText1
  }

  function WriteErrorText(reason: string): StreamWorld.Bytes
    ensures WriteErrorText(reason) == Model.WriteErrorText(reason)
  {
    Model.WriteErrorTextText0 + Utf8.Encode(reason) + Model.WriteErrorTextText1
  }
}
