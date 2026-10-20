include "LnSpec.dfy"
include "LnUtf8Core.dfy"
include "LnEscapingCore.dfy"

module LnTextCore {
  import StreamWorld = BenchWorld
  import StreamContract = IOContract
  import Errno = Errnos
  import BenchIO
  import IOContract
  import BenchWorld
  import Schema = LnSchema
  import SE = LnEscapingCore
  import Utf8 = LnUtf8Core
  import opened Model = LnSpec

  function FailedAccessMessageText(source: BenchWorld.Path, err: int, reason: string): BenchWorld.Bytes
    ensures FailedAccessMessageText(source, err, reason) == Model.FailedAccessMessageText(source, err, reason)
  {
    FailedAccessMessageTextPart1() + SE.SpecQuoteAfBytes(Utf8.Encode(source)) +
    FailedAccessMessageTextPart2() + Utf8.Encode(reason) + FailedAccessMessageTextPart3()
  }

  function HardDirectoryMessageSpec(source: BenchWorld.Path): BenchWorld.Bytes
    ensures HardDirectoryMessageSpec(source) == Model.HardDirectoryMessageSpec(source)
  {
    HardDirectoryMessageSpecPart1() + SE.SpecQuoteFBytes(Utf8.Encode(source)) +
    HardDirectoryMessageSpecPart2()
  }

  function CreateHardLinkErrorMessageText(source: BenchWorld.Path, linkName: BenchWorld.Path, err: int, reason: string): BenchWorld.Bytes
    ensures CreateHardLinkErrorMessageText(source, linkName, err, reason) == Model.CreateHardLinkErrorMessageText(source, linkName, err, reason)
  {
    CreateHardLinkErrorMessageTextPart1() +
    (if err == Errno.EMLINK then
       CreateHardLinkErrorMessageTextPart2() + SE.SpecQuoteAfBytes(Utf8.Encode(source))
     else if err == Errno.EEXIST || err == Errno.ENOSPC || err == Errno.EDQUOT || err == Errno.EROFS then
       CreateHardLinkErrorMessageTextPart3() + SE.SpecQuoteAfBytes(Utf8.Encode(linkName))
     else
       CreateHardLinkErrorMessageTextPart3() + SE.SpecQuoteAfBytes(Utf8.Encode(linkName)) +
       CreateHardLinkErrorMessageTextPart4() + SE.SpecQuoteAfBytes(Utf8.Encode(source))) +
    CreateHardLinkErrorMessageTextPart5() + Utf8.Encode(reason) + CreateHardLinkErrorMessageTextPart6()
  }

  function CreateSymlinkErrorMessageText(linkName: BenchWorld.Path, source: BenchWorld.Path, err: int, reason: string): BenchWorld.Bytes
    ensures CreateSymlinkErrorMessageText(linkName, source, err, reason) == Model.CreateSymlinkErrorMessageText(linkName, source, err, reason)
  {
    CreateSymlinkErrorMessageTextPart1() + SE.SpecQuoteAfBytes(Utf8.Encode(linkName)) +
    (if source == CreateSymlinkErrorMessageTextPart2() then CreateSymlinkErrorMessageTextPart3() + SE.SpecQuoteAfBytes(Utf8.Encode(source)) else CreateSymlinkErrorMessageTextPart2()) +
    CreateSymlinkErrorMessageTextPart4() + Utf8.Encode(reason) + CreateSymlinkErrorMessageTextPart5()
  }

  function TargetDirectoryErrorMessageText(target: BenchWorld.Path, err: int, reason: string): BenchWorld.Bytes
    ensures TargetDirectoryErrorMessageText(target, err, reason) == Model.TargetDirectoryErrorMessageText(target, err, reason)
  {
    TargetDirectoryErrorMessageTextPart1() + SE.SpecQuoteAfBytes(Utf8.Encode(target)) +
    TargetDirectoryErrorMessageTextPart2() + Utf8.Encode(reason) + TargetDirectoryErrorMessageTextPart3()
  }

  function WriteErrorText(reason: string): StreamWorld.Bytes
    ensures WriteErrorText(reason) == Model.WriteErrorText(reason)
  {
    WriteErrorTextPart1() + Utf8.Encode(reason) + WriteErrorTextPart2()
  }
}
