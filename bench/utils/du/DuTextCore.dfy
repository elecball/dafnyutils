include "DuSpec.dfy"
include "DuUtf8Core.dfy"
include "DuEscapingCore.dfy"

module DuTextCore {
  import StreamWorld = BenchWorld
  import StreamContract = IOContract
  import Result = Results
  import BenchIO
  import BenchWorld
  import IOContract
  import Schema = DuSchema
  import Utf8 = DuUtf8Core
  import SE = DuEscapingCore
  import opened Model = DuSpec

  function ErrorMessageSpec(path: BenchWorld.Path, err: BenchWorld.IOError): BenchWorld.Bytes
    ensures ErrorMessageSpec(path, err) == Model.ErrorMessageSpec(path, err)
  {
    ErrorMessageSpecPart1() + SE.SpecQuoteAfBytes(Utf8.Encode(path)) +
    ErrorMessageSpecPart2() + Utf8.Encode(ErrnoText(err)) + ErrorMessageSpecPart3()
  }

  function WriteErrorText(reason: string): StreamWorld.Bytes
    ensures WriteErrorText(reason) == Model.WriteErrorText(reason)
  {
    WriteErrorTextPart1() + Utf8.Encode(reason) + WriteErrorTextPart2()
  }
}
