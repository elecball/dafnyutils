include "MkdirSpec.dfy"
include "MkdirUtf8Core.dfy"

module MkdirTextCore {
  import BenchIO
  import BenchWorld
  import CliTypes
  import Schema = MkdirSchema
  import Utf8 = MkdirUtf8Core
  import CliModel
  import C = IOContract
  import opened Model = MkdirSpec

  function DiagnosticText(quoted: BenchWorld.Bytes, reason: string): BenchWorld.Bytes
    ensures DiagnosticText(quoted, reason) == Model.DiagnosticText(quoted, reason)
  {
    DiagnosticTextPart1() + quoted + DiagnosticTextPart2() + Utf8.Encode(reason) + DiagnosticTextPart3()
  }

  function WriteErrorText(reason: string): BenchWorld.Bytes
    ensures WriteErrorText(reason) == Model.WriteErrorText(reason)
  {
    WriteErrorTextPart1() + Utf8.Encode(reason) + WriteErrorTextPart2()
  }
}
