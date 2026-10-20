include "FactorSpec.dfy"
include "FactorUtf8Core.dfy"
include "FactorEscapingCore.dfy"

module FactorTextCore {
  import StreamWorld = BenchWorld
  import StreamContract = IOContract
  import BenchIO
  import BenchWorld
  import IOContract
  import Schema = FactorSchema
  import Utf8 = FactorUtf8Core
  import SE = FactorEscapingCore
  import opened Model = FactorSpec

  function InvalidTokenMessage(token: string): BenchWorld.Bytes
    requires token is BenchWorld.Bytes
    ensures InvalidTokenMessage(token) == Model.InvalidTokenMessage(token)
  {
    InvalidTokenMessagePart1() + SE.SpecLocaleQuoteBytes(token) + InvalidTokenMessagePart2()
  }

  function InvalidArgvTokenMessage(token: string): BenchWorld.Bytes
    ensures InvalidArgvTokenMessage(token) == Model.InvalidArgvTokenMessage(token)
  {
    InvalidArgvTokenMessagePart1() + SE.SpecLocaleQuoteBytes(Utf8.Encode(token)) +
    InvalidArgvTokenMessagePart2()
  }

  function ReadErrorText(reason: string): BenchWorld.Bytes
    ensures ReadErrorText(reason) == Model.ReadErrorText(reason)
  {
    ReadErrorTextPart1() + Utf8.Encode(reason) + ReadErrorTextPart2()
  }

  function WriteErrorText(reason: string): StreamWorld.Bytes
    ensures WriteErrorText(reason) == Model.WriteErrorText(reason)
  {
    WriteErrorTextPart1() + Utf8.Encode(reason) + WriteErrorTextPart2()
  }
}
