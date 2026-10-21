include "PasteSpec.dfy"
include "PasteUtf8Core.dfy"
include "PasteEscapingCore.dfy"

module PasteTextCore {
  import opened Model = PasteSpec
  import StreamContract = IOContract
  import StreamUtf8 = PasteUtf8Core
  import Result = Results
  import BenchIO
  import Utf8 = PasteUtf8Core
  import BenchWorld
  import IOContract
  import PasteSchema
  import SE = PasteEscapingCore

  function NeedsErrorQuoting(path: string): bool
    ensures NeedsErrorQuoting(path) == Model.NeedsErrorQuoting(path)
  {
    var bytes := Utf8.Encode(path);
    |bytes| == 0 || SE.SpecHasShellQuoteTrigger(bytes)
  }

  function ErrorMessage(path: BenchWorld.Path, err: BenchWorld.IOError): BenchWorld.Bytes
    ensures ErrorMessage(path, err) == Model.ErrorMessage(path, err)
  {
    Model.ErrorMessageText0 + SE.SpecQuoteFBytes(Utf8.Encode(path)) +
    Model.ErrorMessageText1 + Utf8.Encode(ErrnoText(err)) + Model.ErrorMessageText2
  }

  function DelimiterBackslashError(text: BenchWorld.Bytes): BenchWorld.Bytes
    ensures DelimiterBackslashError(text) == Model.DelimiterBackslashError(text)
  {
    var rendered :=
      if exists i: nat :: i < |text| &&
                          (text[i] == ':' || text[i] == '"' || !SE.SpecCPrintableByte(text[i]))
      then SE.SpecDoubleQuote(text)
      else text;
    Model.DelimiterBackslashErrorText0 + rendered + Model.DelimiterBackslashErrorText1
  }

  function StreamWriteErrorMessage(message: string): BenchWorld.Bytes
    ensures StreamWriteErrorMessage(message) == Model.StreamWriteErrorMessage(message)
  {
    StreamUtf8.Encode(Model.StreamWriteErrorMessageText0 + message + Model.StreamWriteErrorMessageText1)
  }
}
