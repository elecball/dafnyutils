include "MvSpec.dfy"
include "MvUtf8Core.dfy"
include "MvEscapingCore.dfy"

module MvTextCore {
  import Errno = Errnos
  import Result = Results
  import BenchIO
  import IOContract
  import BenchWorld
  import Basename = MvPathSpec
  import Quote = MvEscapingCore
  import Dirname = MvPathSpec
  import Schema = MvSchema
  import Utf8 = MvUtf8Core
  import SE = MvEscapingCore
  import opened Model = MvSpec

  function MissingDestinationMessageSpec(source: string): BenchWorld.Bytes
    ensures MissingDestinationMessageSpec(source) == Model.MissingDestinationMessageSpec(source)
  {
    MissingDestinationMessageSpecPart1() + Quote.SpecQuoteAfBytes(Utf8.Encode(source)) + MissingDestinationMessageSpecPart2()
    + MissingDestinationMessageSpecPart3()
  }

  function ExtraOperandMessageSpec(operand: string): BenchWorld.Bytes
    ensures ExtraOperandMessageSpec(operand) == Model.ExtraOperandMessageSpec(operand)
  {
    ExtraOperandMessageSpecPart1() + Quote.SpecQuoteAfBytes(Utf8.Encode(operand)) +
    ExtraOperandMessageSpecPart2()
  }

  function InvalidBackupArgumentMessageSpec(value: string): BenchWorld.Bytes
    ensures InvalidBackupArgumentMessageSpec(value) == Model.InvalidBackupArgumentMessageSpec(value)
  {
    InvalidBackupArgumentMessageSpecPart1() + SE.SpecLocaleQuoteBytes(Utf8.Encode(value)) +
    InvalidBackupArgumentMessageSpecPart2()
    + InvalidBackupArgumentMessageSpecPart3()
    + InvalidBackupArgumentMessageSpecPart4()
    + InvalidBackupArgumentMessageSpecPart5()
    + InvalidBackupArgumentMessageSpecPart6()
    + InvalidBackupArgumentMessageSpecPart7()
    + InvalidBackupArgumentMessageSpecPart8()
  }

  function InvalidUpdateArgumentMessageSpec(value: string): BenchWorld.Bytes
    ensures InvalidUpdateArgumentMessageSpec(value) == Model.InvalidUpdateArgumentMessageSpec(value)
  {
    InvalidUpdateArgumentMessageSpecPart1() + SE.SpecLocaleQuoteBytes(Utf8.Encode(value)) +
    InvalidUpdateArgumentMessageSpecPart2()
    + InvalidUpdateArgumentMessageSpecPart3()
    + InvalidUpdateArgumentMessageSpecPart4()
    + InvalidUpdateArgumentMessageSpecPart5()
    + InvalidUpdateArgumentMessageSpecPart6()
    + InvalidUpdateArgumentMessageSpecPart7()
    + InvalidUpdateArgumentMessageSpecPart8()
  }

  function TargetFailureMessageSpec(path: string, explicitTargetDirectory: bool, err: int): BenchWorld.Bytes
    ensures TargetFailureMessageSpec(path, explicitTargetDirectory, err) == Model.TargetFailureMessageSpec(path, explicitTargetDirectory, err)
  {
    if explicitTargetDirectory then
      TargetFailureMessageSpecPart1() + Quote.SpecQuoteAfBytes(Utf8.Encode(path)) +
      TargetFailureMessageSpecPart2() + ErrnoTextSpec(err) + TargetFailureMessageSpecPart3()
    else
      TargetFailureMessageSpecPart4() + Quote.SpecQuoteAfBytes(Utf8.Encode(path)) +
      TargetFailureMessageSpecPart2() + ErrnoTextSpec(err) + TargetFailureMessageSpecPart3()
  }

  function SourceStatFailureMessageSpec(source: string, err: int): BenchWorld.Bytes
    ensures SourceStatFailureMessageSpec(source, err) == Model.SourceStatFailureMessageSpec(source, err)
  {
    SourceStatFailureMessageSpecPart1() + Quote.SpecQuoteAfBytes(Utf8.Encode(source)) +
    SourceStatFailureMessageSpecPart2() + ErrnoTextSpec(err) + SourceStatFailureMessageSpecPart3()
  }

  function ParentStatFailureMessageSpec(path: string, err: int): BenchWorld.Bytes
    ensures ParentStatFailureMessageSpec(path, err) == Model.ParentStatFailureMessageSpec(path, err)
  {
    ParentStatFailureMessageSpecPart1() + Utf8.Encode(path) + ParentStatFailureMessageSpecPart2() + ErrnoTextSpec(err) + ParentStatFailureMessageSpecPart3()
  }

  function RenameFailureMessageSpec(source: string, target: string, err: int): BenchWorld.Bytes
    ensures RenameFailureMessageSpec(source, target, err) == Model.RenameFailureMessageSpec(source, target, err)
  {
    if err == Errno.EISDIR then
      RenameFailureMessageSpecPart1() + Quote.SpecQuoteAfBytes(Utf8.Encode(target)) +
      RenameFailureMessageSpecPart2() + Quote.SpecQuoteAfBytes(Utf8.Encode(source)) + RenameFailureMessageSpecPart3()
    else if err == Errno.ENOTEMPTY then
      RenameFailureMessageSpecPart4() + Quote.SpecQuoteAfBytes(Utf8.Encode(target)) +
      RenameFailureMessageSpecPart5() + ErrnoTextSpec(err) + RenameFailureMessageSpecPart3()
    else
      RenameFailureMessageSpecPart6() + Quote.SpecQuoteAfBytes(Utf8.Encode(source)) +
      RenameFailureMessageSpecPart7() + Quote.SpecQuoteAfBytes(Utf8.Encode(target)) +
      RenameFailureMessageSpecPart5() + ErrnoTextSpec(err) + RenameFailureMessageSpecPart3()
  }

  function SourceRenameFailureMessageSpec(
    source: string,
    target: string,
    err: int,
    directorySourceWithExistingTarget: bool
  ): BenchWorld.Bytes
    ensures SourceRenameFailureMessageSpec(source, target, err, directorySourceWithExistingTarget) == Model.SourceRenameFailureMessageSpec(source, target, err, directorySourceWithExistingTarget)
  {
    if directorySourceWithExistingTarget && err == Errno.ENOTDIR then
      SourceRenameFailureMessageSpecPart1() + Quote.SpecQuoteAfBytes(Utf8.Encode(target)) +
      SourceRenameFailureMessageSpecPart2() + Quote.SpecQuoteAfBytes(Utf8.Encode(source)) + SourceRenameFailureMessageSpecPart3()
    else if err == Errno.EINVAL then
      SourceRenameFailureMessageSpecPart4() + Quote.SpecQuoteAfBytes(Utf8.Encode(source)) +
      SourceRenameFailureMessageSpecPart5() + Quote.SpecQuoteAfBytes(Utf8.Encode(target)) + SourceRenameFailureMessageSpecPart3()
    else
      RenameFailureMessageSpec(source, target, err)
  }

  function SameFileMessageSpec(source: string, target: string): BenchWorld.Bytes
    ensures SameFileMessageSpec(source, target) == Model.SameFileMessageSpec(source, target)
  {
    SameFileMessageSpecPart1() + Quote.SpecQuoteAfBytes(Utf8.Encode(source)) +
    SameFileMessageSpecPart2() + Quote.SpecQuoteAfBytes(Utf8.Encode(target)) +
    SameFileMessageSpecPart3()
  }

  function BackupWouldDestroySourceMessageSpec(
    source: string,
    target: string
  ): BenchWorld.Bytes
    ensures BackupWouldDestroySourceMessageSpec(source, target) == Model.BackupWouldDestroySourceMessageSpec(source, target)
  {
    BackupWouldDestroySourceMessageSpecPart1() +
    Quote.SpecQuoteAfBytes(Utf8.Encode(target)) +
    BackupWouldDestroySourceMessageSpecPart2() +
    Quote.SpecQuoteAfBytes(Utf8.Encode(source)) +
    BackupWouldDestroySourceMessageSpecPart3()
  }

  function VerboseRenameMessageSpec(source: string, target: string): BenchWorld.Bytes
    ensures VerboseRenameMessageSpec(source, target) == Model.VerboseRenameMessageSpec(source, target)
  {
    VerboseRenameMessageSpecPart1() + Quote.SpecQuoteAfBytes(Utf8.Encode(source)) +
    VerboseRenameMessageSpecPart2() + Quote.SpecQuoteAfBytes(Utf8.Encode(target)) + VerboseRenameMessageSpecPart3()
  }

  function VerboseRenameWithBackupMessageSpec(source: string, target: string, backup: string): BenchWorld.Bytes
    ensures VerboseRenameWithBackupMessageSpec(source, target, backup) == Model.VerboseRenameWithBackupMessageSpec(source, target, backup)
  {
    VerboseRenameWithBackupMessageSpecPart1() + Quote.SpecQuoteAfBytes(Utf8.Encode(source)) +
    VerboseRenameWithBackupMessageSpecPart2() + Quote.SpecQuoteAfBytes(Utf8.Encode(target)) +
    VerboseRenameWithBackupMessageSpecPart3() + Quote.SpecQuoteAfBytes(Utf8.Encode(backup)) + VerboseRenameWithBackupMessageSpecPart4()
  }

  function DebugSkipMessageSpec(target: string): BenchWorld.Bytes
    ensures DebugSkipMessageSpec(target) == Model.DebugSkipMessageSpec(target)
  {
    DebugSkipMessageSpecPart1() + Quote.SpecQuoteAfBytes(Utf8.Encode(target)) + DebugSkipMessageSpecPart2()
  }

  function NotReplacingMessageSpec(target: string): BenchWorld.Bytes
    ensures NotReplacingMessageSpec(target) == Model.NotReplacingMessageSpec(target)
  {
    NotReplacingMessageSpecPart1() + Quote.SpecQuoteAfBytes(Utf8.Encode(target)) + NotReplacingMessageSpecPart2()
  }

  function WriteErrorText(reason: string): BenchWorld.Bytes
    ensures WriteErrorText(reason) == Model.WriteErrorText(reason)
  {
    WriteErrorTextPart1() + Utf8.Encode(reason) + WriteErrorTextPart2()
  }
}
