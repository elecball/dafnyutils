include "TruncateSpec.dfy"
include "TruncateUtf8Core.dfy"

module TruncateTextCore {
  import S = TruncateSchema
  import BenchIO
  import W = BenchWorld
  import C = IOContract
  import Utf8 = TruncateUtf8Core
  import CliTypes
  import CliModel
  import opened Model = TruncateSpec

  function WriteErrorText(reason: string): W.Bytes
    ensures WriteErrorText(reason) == Model.WriteErrorText(reason)
  {
    WriteErrorTextPart1() + Utf8.Encode(reason) + WriteErrorTextPart2()
  }

  opaque function NatText(n: nat): string
    ensures NatText(n) == Model.NatText(n)
    decreases n
  {
    reveal Model.NatText();
    if n < 10 then [('0' as int + n) as char]
    else NatText(n / 10) + [('0' as int + n % 10) as char]
  }

  function IntText(n: int): string
    ensures IntText(n) == Model.IntText(n)
  { if n < 0 then IntTextPart1() + NatText(-n) else NatText(n) }

  function OpenText(quoted: W.Bytes, reason: string): W.Bytes
    ensures OpenText(quoted, reason) == Model.OpenText(quoted, reason)
  {
    OpenTextPart1() + quoted + OpenTextPart2() + Utf8.Encode(reason) + OpenTextPart3()
  }

  function StatText(quoted: W.Bytes, reason: string, reference: bool): W.Bytes
    ensures StatText(quoted, reason, reference) == Model.StatText(quoted, reason, reference)
  {
    StatTextPart1() + (if reference then StatTextPart2() else StatTextPart3()) + quoted + StatTextPart4() +
      Utf8.Encode(reason) + StatTextPart5()
  }

  function ResizeText(quoted: W.Bytes, size: nat, reason: string): W.Bytes
    ensures ResizeText(quoted, size, reason) == Model.ResizeText(quoted, size, reason)
  {
    ResizeTextPart1() + quoted + ResizeTextPart2() + Utf8.Encode(NatText(size)) +
      ResizeTextPart3() + Utf8.Encode(reason) + ResizeTextPart4()
  }

  function BlockOverflowText(quoted: W.Bytes, delta: int, block: nat): W.Bytes
    ensures BlockOverflowText(quoted, delta, block) == Model.BlockOverflowText(quoted, delta, block)
  {
    BlockOverflowTextPart1() + Utf8.Encode(IntText(delta)) + BlockOverflowTextPart2() + Utf8.Encode(NatText(block)) +
      BlockOverflowTextPart3() + quoted + BlockOverflowTextPart4()
  }
}
