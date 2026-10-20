include "UnlinkSpec.dfy"
include "UnlinkUtf8Core.dfy"

module UnlinkTextCore {
  import StreamWorld = BenchWorld
  import StreamContract = IOContract
  import BenchIO
  import BenchWorld
  import CliTypes
  import Schema = UnlinkSchema
  import Utf8 = UnlinkUtf8Core
  import CliModel
  import C = IOContract
  import opened Model = UnlinkSpec

  function CannotUnlinkText(
    quotedPath: BenchWorld.Bytes,
    reason: string
  ): BenchWorld.Bytes
    ensures CannotUnlinkText(quotedPath, reason) == Model.CannotUnlinkText(quotedPath, reason)
  {
    CannotUnlinkTextPart1() + quotedPath + CannotUnlinkTextPart2()
    + Utf8.Encode(reason) + CannotUnlinkTextPart3()
  }

  function WriteErrorText(reason: string): StreamWorld.Bytes
    ensures WriteErrorText(reason) == Model.WriteErrorText(reason)
  {
    WriteErrorTextPart1() + Utf8.Encode(reason) + WriteErrorTextPart2()
  }
}
