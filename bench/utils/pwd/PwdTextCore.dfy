include "PwdRecoverySpec.dfy"
include "PwdEmissionSpec.dfy"
include "PwdUtf8Core.dfy"

module PwdTextCore {
  import W = BenchWorld
  import BenchWorld
  import Utf8 = PwdUtf8Core
  import opened Model = PwdRecoverySpec
  import Emission = PwdEmissionSpec

  function WriteErrorText(reason: string): BenchWorld.Bytes
    ensures WriteErrorText(reason) == Model.WriteErrorText(reason)
  {
    WriteErrorTextPart1() + Utf8.Encode(reason) + WriteErrorTextPart2()
  }

  function RecoveryFailureText(failure: RecoveryFailure,
    quotedArgument: BenchWorld.Bytes, reason: string): BenchWorld.Bytes
    ensures RecoveryFailureText(failure, quotedArgument, reason) == Model.RecoveryFailureText(failure, quotedArgument, reason)
  {
    var suffix := RecoveryFailureTextPart1() + Utf8.Encode(reason) + RecoveryFailureTextPart2();
    match failure
    case MemoryExhausted => RecoveryFailureTextPart3()
    case RootAttributesFailed(_) =>
      RecoveryFailureTextPart4() + quotedArgument + suffix
    case CurrentDirectoryStatusFailed(_) =>
      RecoveryFailureTextPart5() + quotedArgument + suffix
    case ParentOpenFailed(_, _) =>
      RecoveryFailureTextPart6() + quotedArgument + suffix
    case ParentChdirFailed(_, _) =>
      RecoveryFailureTextPart7() + quotedArgument + suffix
    case ParentStatusFailed(_, _) =>
      RecoveryFailureTextPart5() + quotedArgument + suffix
    case ParentReadFailed(_, _) =>
      RecoveryFailureTextPart8() + quotedArgument + suffix
    case ParentEntryMissing(_) =>
      RecoveryFailureTextPart9() + quotedArgument + RecoveryFailureTextPart10()
  }

  function CurrentDirectoryTextSpec(directory: string): W.Bytes
    ensures CurrentDirectoryTextSpec(directory) == Emission.CurrentDirectoryTextSpec(directory)
  {
    Utf8.Encode(directory)+Emission.CurrentDirectoryTextSpecPart1()
  }
}
