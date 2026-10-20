include "ReadlinkSpec.dfy"
include "ReadlinkUtf8Core.dfy"
include "ReadlinkEscapingCore.dfy"

module ReadlinkTextCore {
  import StreamWorld = BenchWorld
  import StreamContract = IOContract
  import Errno = Errnos
  import Result = Results
  import BenchIO
  import Utf8 = ReadlinkUtf8Core
  import IOContract
  import BenchWorld
  import Schema = ReadlinkSchema
  import SE = ReadlinkEscapingCore
  import opened Model = ReadlinkSpec

  function ErrorMessageSpec(path: BenchWorld.Path, err: BenchWorld.IOError): BenchWorld.Bytes
    ensures ErrorMessageSpec(path, err) == Model.ErrorMessageSpec(path, err)
  {
    ErrorMessageSpecPart1() + SE.SpecQuoteFBytes(Utf8.Encode(path)) + ErrorMessageSpecPart2() + ErrnoTextSpec(err) + ErrorMessageSpecPart3()
  }

  function WriteErrorText(reason: string): StreamWorld.Bytes
    ensures WriteErrorText(reason) == Model.WriteErrorText(reason)
  {
    WriteErrorTextPart1() + Utf8.Encode(reason) + WriteErrorTextPart2()
  }
}
