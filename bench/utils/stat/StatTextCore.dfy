include "StatSpec.dfy"
include "StatUtf8Core.dfy"
include "StatEscapingCore.dfy"

module StatTextCore {
  import StreamWorld = BenchWorld
  import StreamContract = IOContract
  import Errno = Errnos
  import Result = Results
  import BenchWorld
  import BenchIO
  import Utf8 = StatUtf8Core
  import IOContract
  import Schema = StatSchema
  import SE = StatEscapingCore
  import opened Model = StatSpec

  function ErrorMessageWithReasonSpec(path: BenchWorld.Path, reason: string): BenchWorld.Bytes
    ensures ErrorMessageWithReasonSpec(path, reason) == Model.ErrorMessageWithReasonSpec(path, reason)
  {
    ErrorMessageWithReasonSpecPart1() + SE.SpecQuoteAfBytes(Utf8.Encode(path)) +
      ErrorMessageWithReasonSpecPart2() + Utf8.Encode(reason) + ErrorMessageWithReasonSpecPart3()
  }

  function BaseNatTextSpec(value: nat, base: nat): string
    requires 2 <= base <= 16
    ensures BaseNatTextSpec(value, base) == Model.BaseNatTextSpec(value, base)
    decreases value
  {
    if value < base then
      [DigitForBaseSpec(value)]
    else
      BaseNatTextSpec(value / base, base) + [DigitForBaseSpec(value % base)]
  }

  function IntTextSpec(value: int): string
    ensures IntTextSpec(value) == Model.IntTextSpec(value)
  {
    if value < 0 then IntTextSpecPart1() + BaseNatTextSpec((-value) as nat, 10)
    else BaseNatTextSpec(value as nat, 10)
  }

  function IntHexTextSpec(value: int): string
    ensures IntHexTextSpec(value) == Model.IntHexTextSpec(value)
  {
    if value < 0 then IntHexTextSpecPart1() + BaseNatTextSpec((-value) as nat, 16)
    else BaseNatTextSpec(value as nat, 16)
  }

  function DirectiveTextSpec(
    directive: char,
    status: BenchWorld.FileStatus
  ): BenchWorld.Bytes
    ensures DirectiveTextSpec(directive, status) == Model.DirectiveTextSpec(directive, status)
  {
    Utf8.Encode(if directive == '%' then DirectiveTextSpecPart1()
    else if directive == 'a' then BaseNatTextSpec((status.mode as int) as nat, 8)
    else if directive == 'b' then BaseNatTextSpec(status.storage.allocatedBlocks, 10)
    else if directive == 'B' then BaseNatTextSpec(BenchWorld.STAT_BLOCK_BYTES, 10)
    else if directive == 'd' then IntTextSpec(status.hostKey.device)
    else if directive == 'D' then IntHexTextSpec(status.hostKey.device)
    else if directive == 'f' then BaseNatTextSpec(RawModeValueSpec(status), 16)
    else if directive == 'g' then BaseNatTextSpec(status.ownership.gid, 10)
    else if directive == 'h' then BaseNatTextSpec(status.linkCount, 10)
    else if directive == 'i' then IntTextSpec(status.hostKey.inode)
    else if directive == 'o' then BaseNatTextSpec(status.storage.preferredIoBlockBytes, 10)
    else if directive == 's' then BaseNatTextSpec(status.storage.size, 10)
    else if directive == 'u' then BaseNatTextSpec(status.ownership.uid, 10)
    else if directive == 'X' then IntTextSpec(status.times.atimeSec)
    else if directive == 'Y' then IntTextSpec(status.times.mtimeSec)
    else if directive == 'Z' then IntTextSpec(status.times.ctimeSec)
    else DirectiveTextSpecPart2())
  }

  function WriteErrorText(reason: string): StreamWorld.Bytes
    ensures WriteErrorText(reason) == Model.WriteErrorText(reason)
  {
    WriteErrorTextPart1() + Utf8.Encode(reason) + WriteErrorTextPart2()
  }
}
