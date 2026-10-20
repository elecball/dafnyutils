include "RmdirSpec.dfy"
include "RmdirUtf8Core.dfy"

module RmdirTextCore {
  import BenchIO
  import opened BenchWorld
  import C = IOContract
  import Errno = Errnos
  import S = RmdirSchema
  import Path = RmdirPathSpec
  import Utf8 = RmdirUtf8Core
  import CliTypes
  import CliModel
  import opened Model = RmdirSpec

  function FailureText(parent: bool, err: int, custom: bool,
                       quoted: Bytes, reason: string): Bytes
    ensures FailureText(parent, err, custom, quoted, reason) == Model.FailureText(parent, err, custom, quoted, reason)
  {
    FailureTextPart1() +
    (if parent && err != Errno.ENOTDIR then FailureTextPart2() else FailureTextPart3()) + quoted +
    FailureTextPart4() + (if custom then FailureTextPart5() else Utf8.Encode(reason)) + FailureTextPart6()
  }

  function WriteErrorText(reason: string): Bytes
    ensures WriteErrorText(reason) == Model.WriteErrorText(reason)
  {
    WriteErrorTextPart1() + Utf8.Encode(reason) + WriteErrorTextPart2()
  }
}
