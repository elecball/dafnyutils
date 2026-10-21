include "CommSpec.dfy"
include "CommUtf8Core.dfy"
include "CommEscapingCore.dfy"

module CommTextCore {
  import opened Model = CommSpec
  import StreamContract = IOContract
  import StreamUtf8 = CommUtf8Core
  import Result = Results
  import BenchIO
  import Utf8 = CommUtf8Core
  import BenchWorld
  import IOContract
  import Schema = CommSchema
  import Render = CommRenderSpec
  import SE = CommEscapingCore

  function FileErrorMessageSpec(path: BenchWorld.Path, err: BenchWorld.IOError): BenchWorld.Bytes
    ensures FileErrorMessageSpec(path, err) == Model.FileErrorMessageSpec(path, err)
  {
    Model.FileErrorMessageSpecText0 + SE.SpecQuoteFBytes(Utf8.Encode(path)) + Model.FileErrorMessageSpecText1 + Utf8.Encode(ErrnoText(err)) + Model.FileErrorMessageSpecText2
  }

  function InputErrorMessageSpec(input: Schema.CommInput, err: BenchWorld.IOError): BenchWorld.Bytes
    ensures InputErrorMessageSpec(input, err) == Model.InputErrorMessageSpec(input, err)
  {
    match input
    case Stdin => Model.InputErrorMessageSpecText0 + Utf8.Encode(ErrnoText(err)) + Model.InputErrorMessageSpecText1
    case File(path) => FileErrorMessageSpec(path, err)
  }

  function MissingOperandAfterMessageSpec(operand: string): BenchWorld.Bytes
    ensures MissingOperandAfterMessageSpec(operand) == Model.MissingOperandAfterMessageSpec(operand)
  {
    Model.MissingOperandAfterMessageSpecText0 + SE.SpecLocaleQuoteBytes(Utf8.Encode(operand)) + Model.MissingOperandAfterMessageSpecText1 +
    Model.MissingOperandAfterMessageSpecText2
  }

  function ExtraOperandMessageSpec(operand: string): BenchWorld.Bytes
    ensures ExtraOperandMessageSpec(operand) == Model.ExtraOperandMessageSpec(operand)
  {
    Model.ExtraOperandMessageSpecText0 + SE.SpecLocaleQuoteBytes(Utf8.Encode(operand)) + Model.ExtraOperandMessageSpecText1 +
    Model.ExtraOperandMessageSpecText2
  }

  function StreamWriteErrorMessage(message: string): BenchWorld.Bytes
    ensures StreamWriteErrorMessage(message) == Model.StreamWriteErrorMessage(message)
  {
    StreamUtf8.Encode(Model.StreamWriteErrorMessageText0 + message + Model.StreamWriteErrorMessageText1)
  }

  function FailedReadMessage(cmd: Schema.CommCmd, first: BenchWorld.IOResult<BenchWorld.Bytes>,
                                                                             second: BenchWorld.IOResult<BenchWorld.Bytes>, leftFault: bool): BenchWorld.Bytes
    ensures FailedReadMessage(cmd, first, second, leftFault) == Model.FailedReadMessage(cmd, first, second, leftFault)
  {
    var result := if leftFault then first else second;
    match result
    case Err(error) => InputErrorMessageSpec(if leftFault then cmd.input1 else cmd.input2, error)
    case Ok(_) => []
  }
}
