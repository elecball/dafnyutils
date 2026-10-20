include "CsplitSpec.dfy"
include "CsplitUtf8Core.dfy"
include "CsplitEscapingCore.dfy"

module CsplitTextCore {
  import StreamContract = IOContract
  import StreamUtf8 = CsplitUtf8Core
  import Errno = Errnos
  import Result = Results
  import BenchIO
  import Utf8 = CsplitUtf8Core
  import BenchWorld
  import IOContract
  import Schema = CsplitSchema
  import SE = CsplitEscapingCore
  import opened Model = CsplitSpec

  function ReadErrorMessage(input: Schema.Input, err: BenchWorld.IOError): BenchWorld.Bytes
    ensures ReadErrorMessage(input, err) == Model.ReadErrorMessage(input, err)
  {
    match input
    case Stdin => ReadErrorMessagePart1() + Utf8.Encode(ReadErrnoText(err)) + ReadErrorMessagePart2()
    case File(path) =>
      ReadErrorMessagePart3() + SE.SpecQuoteAfBytes(Utf8.Encode(path)) +
      ReadErrorMessagePart4() + Utf8.Encode(ReadErrnoText(err)) + ReadErrorMessagePart2()
  }

  function WriteErrorMessage(path: BenchWorld.Path, err: int): BenchWorld.Bytes
    ensures WriteErrorMessage(path, err) == Model.WriteErrorMessage(path, err)
  {
    WriteErrorMessagePart1() + SE.SpecQuoteFBytes(Utf8.Encode(path)) +
    WriteErrorMessagePart2() + Utf8.Encode(WriteErrnoText(err)) + WriteErrorMessagePart3()
  }

  function StreamWriteErrorMessage(message: string): BenchWorld.Bytes
    ensures StreamWriteErrorMessage(message) == Model.StreamWriteErrorMessage(message)
  {
    StreamUtf8.Encode(StreamWriteErrorMessagePart1() + message + StreamWriteErrorMessagePart2())
  }
}
