include "RmSpec.dfy"
include "RmUtf8Core.dfy"
include "RmEscapingCore.dfy"

module RmTextCore {
  import BenchIO
  import R = Results
  import opened BenchWorld
  import CliTypes
  import CliModel
  import Schema = RmSchema
  import Utf8 = RmUtf8Core
  import C = IOContract
  import Errno = Errnos
  import Escaping = RmEscapingCore
  import Paths = RmPathSpec
  import opened Model = RmSpec

  function HyphenSuggestion(path: Path): Bytes
    ensures HyphenSuggestion(path) == Model.HyphenSuggestion(path)
  {
    var encoded := Utf8.Encode(path);
    var trigger := exists i: int ::
      0 <= i < |encoded| && encoded[i] != ':' &&
      Escaping.SpecShellQuoteTriggerByte(encoded[i],i == 0,|encoded| == 1);
    var quoted := if trigger then Escaping.SpecQuoteAfBytes(encoded) else encoded;
    HyphenSuggestionPart1() + quoted + HyphenSuggestionPart2() + Escaping.SpecQuoteAfBytes(encoded) + HyphenSuggestionPart3()
  }

  function CannotRemoveMessage(quoted: Bytes, reason: string): Bytes
    ensures CannotRemoveMessage(quoted, reason) == Model.CannotRemoveMessage(quoted, reason)
  {
    CannotRemoveMessagePart1() + quoted + CannotRemoveMessagePart2() + Utf8.Encode(reason) + CannotRemoveMessagePart3()
  }

  function TraversalMessage(path: Path, reason: string): Bytes
    ensures TraversalMessage(path, reason) == Model.TraversalMessage(path, reason)
  {
    TraversalMessagePart1() + Escaping.SpecQuoteFBytes(Utf8.Encode(path)) + TraversalMessagePart2() + Utf8.Encode(reason) + TraversalMessagePart3()
  }

  function RootAttributesMessage(reason: string): Bytes
    ensures RootAttributesMessage(reason) == Model.RootAttributesMessage(reason)
  {
    RootAttributesMessagePart1() + Utf8.Encode(reason) + RootAttributesMessagePart2()
  }

  function RefusalMessage(path: Path, why: Refusal, quoted: Bytes, quotedParent: Bytes): Bytes
    ensures RefusalMessage(path, why, quoted, quotedParent) == Model.RefusalMessage(path, why, quoted, quotedParent)
  {
    match why
    case DirectoryRefusal => CannotRemoveMessage(quoted, RefusalMessagePart1())
    case DotRefusal =>
      RefusalMessagePart2() + quoted + RefusalMessagePart3()
    case RootRefusal =>
      (if path == RefusalMessagePart4() then RefusalMessagePart5()
       else RefusalMessagePart6() + quoted + RefusalMessagePart7()) +
      RefusalMessagePart8()
    case CycleRefusal =>
      RefusalMessagePart9() + Escaping.SpecQuoteFBytes(Utf8.Encode(path)) + RefusalMessagePart10()
    case DeviceRefusal =>
      RefusalMessagePart11() + quoted + RefusalMessagePart12()
    case PreserveDeviceRefusal =>
      RefusalMessagePart11() + quoted + RefusalMessagePart12() +
      RefusalMessagePart13()
    case ParentRefusal =>
      RefusalMessagePart14() + quotedParent + RefusalMessagePart15() +
        quoted + RefusalMessagePart3()
    case NoRefusal => []
  }

  function WriteErrorText(reason: string): Bytes
    ensures WriteErrorText(reason) == Model.WriteErrorText(reason)
  {
    WriteErrorTextPart1() + Utf8.Encode(reason) + WriteErrorTextPart2()
  }
}
