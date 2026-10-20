include "TeeSpec.dfy"
include "TeeUtf8Core.dfy"
include "TeeEscapingCore.dfy"

module TeeTextCore {
  import opened Model = TeeSpec
  import StreamWorld = BenchWorld
  import StreamContract = IOContract
  import Errno = Errnos
  import BenchIO
  import BenchWorld
  import IOContract
  import Schema = TeeSchema
  import Utf8 = TeeUtf8Core
  import SE = TeeEscapingCore

  function ReadErrorMessageSpec(path: BenchWorld.Path, err: BenchWorld.IOError): BenchWorld.Bytes
    ensures ReadErrorMessageSpec(path, err) == Model.ReadErrorMessageSpec(path, err)
  {
    Model.ReadErrorMessageSpecText0 + SE.SpecQuoteFBytes(Utf8.Encode(path)) +
      Model.ReadErrorMessageSpecText1 + Utf8.Encode(ReadErrnoTextSpec(err)) + Model.ReadErrorMessageSpecText2
  }

  function WriteErrorMessageText(path: BenchWorld.Path, reason: string): BenchWorld.Bytes
    ensures WriteErrorMessageText(path, reason) == Model.WriteErrorMessageText(path, reason)
  {
    Model.WriteErrorMessageTextText0 + SE.SpecQuoteFBytes(Utf8.Encode(path)) +
      Model.WriteErrorMessageTextText1 + Utf8.Encode(reason) + Model.WriteErrorMessageTextText2
  }

  function StdinReadErrorText(reason: string): BenchWorld.Bytes
    ensures StdinReadErrorText(reason) == Model.StdinReadErrorText(reason)
  {
    Model.StdinReadErrorTextText0 + Utf8.Encode(reason) + Model.StdinReadErrorTextText1
  }

  function WriteErrorText(raw: Schema.TeeCmdRaw, reason: string): StreamWorld.Bytes
    ensures WriteErrorText(raw, reason) == Model.WriteErrorText(raw, reason)
  {
    (if CommandSpec(raw).mode == Schema.ModeRun then Model.WriteErrorTextText0
     else Model.WriteErrorTextText1) + Utf8.Encode(reason) + Model.WriteErrorTextText2
  }
}
