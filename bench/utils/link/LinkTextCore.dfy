include "LinkSpec.dfy"
include "LinkUtf8Core.dfy"

module LinkTextCore {
  import StreamWorld = BenchWorld
  import StreamContract = IOContract
  import BenchIO
  import BenchWorld
  import CliTypes
  import Schema = LinkSchema
  import Utf8 = LinkUtf8Core
  import CliModel
  import C = IOContract
  import opened Model = LinkSpec

  function CannotCreateLinkText(
    quotedTarget: BenchWorld.Bytes,
    quotedSource: BenchWorld.Bytes,
    reason: string
  ): BenchWorld.Bytes
    ensures CannotCreateLinkText(quotedTarget, quotedSource, reason) == Model.CannotCreateLinkText(quotedTarget, quotedSource, reason)
  {
    CannotCreateLinkTextPart1() + quotedTarget + CannotCreateLinkTextPart2() + quotedSource + CannotCreateLinkTextPart3()
    + Utf8.Encode(reason) + CannotCreateLinkTextPart4()
  }

  function WriteErrorText(reason: string): StreamWorld.Bytes
    ensures WriteErrorText(reason) == Model.WriteErrorText(reason)
  {
    WriteErrorTextPart1() + Utf8.Encode(reason) + WriteErrorTextPart2()
  }
}
