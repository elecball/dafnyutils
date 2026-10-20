include "ChmodSpec.dfy"
include "ChmodUtf8Core.dfy"
include "ChmodEscapingCore.dfy"

module ChmodTextCore {
  import Errno = Errnos
  import Result = Results
  import BenchWorld
  import BenchIO
  import IOContract
  import Utf8 = ChmodUtf8Core
  import Schema = ChmodSchema
  import Quote = ChmodEscapingCore
  import opened Model = ChmodSpec

  function MissingOperandMessageSpec(cmd: Schema.ChmodCmd): BenchWorld.Bytes
    ensures MissingOperandMessageSpec(cmd) == Model.MissingOperandMessageSpec(cmd)
  {
    if cmd.modeExpr != MissingOperandMessageSpecPart1() && !cmd.diagnoseSurprises then
      MissingOperandMessageSpecPart2() +
      Quote.SpecLocaleQuoteBytes(Utf8.Encode(cmd.modeExpr)) +
      MissingOperandMessageSpecPart3()
    else
      MissingOperandMessageSpecPart4()
  }

  function InvalidModeMessageSpec(modeExpr: string): BenchWorld.Bytes
    ensures InvalidModeMessageSpec(modeExpr) == Model.InvalidModeMessageSpec(modeExpr)
  {
    InvalidModeMessageSpecPart1() + Quote.SpecLocaleQuoteBytes(Utf8.Encode(modeExpr)) +
    InvalidModeMessageSpecPart2()
  }

  function ReferenceErrorMessageSpec(path: string, err: string): BenchWorld.Bytes
    ensures ReferenceErrorMessageSpec(path, err) == Model.ReferenceErrorMessageSpec(path, err)
  {
    ReferenceErrorMessageSpecPart1() + Quote.SpecQuoteAfBytes(Utf8.Encode(path)) +
    ReferenceErrorMessageSpecPart2() + Utf8.Encode(err) + ReferenceErrorMessageSpecPart3()
  }

  function GettingNewAttributesMessageSpec(path: string, err: string): BenchWorld.Bytes
    ensures GettingNewAttributesMessageSpec(path, err) == Model.GettingNewAttributesMessageSpec(path, err)
  {
    GettingNewAttributesMessageSpecPart1() +
    Quote.SpecQuoteAfBytes(Utf8.Encode(path)) + GettingNewAttributesMessageSpecPart2() + Utf8.Encode(err) + GettingNewAttributesMessageSpecPart3()
  }

  function ChangeErrorMessageSpec(path: string, err: string): BenchWorld.Bytes
    ensures ChangeErrorMessageSpec(path, err) == Model.ChangeErrorMessageSpec(path, err)
  {
    ChangeErrorMessageSpecPart1() + Quote.SpecQuoteAfBytes(Utf8.Encode(path)) +
    ChangeErrorMessageSpecPart2() + Utf8.Encode(err) + ChangeErrorMessageSpecPart3()
  }

  function AccessErrorMessageSpec(path: string, err: string): BenchWorld.Bytes
    ensures AccessErrorMessageSpec(path, err) == Model.AccessErrorMessageSpec(path, err)
  {
    AccessErrorMessageSpecPart1() + Quote.SpecQuoteAfBytes(Utf8.Encode(path)) +
    AccessErrorMessageSpecPart2() + Utf8.Encode(err) + AccessErrorMessageSpecPart3()
  }

  function DanglingSymlinkMessageSpec(path: string): BenchWorld.Bytes
    ensures DanglingSymlinkMessageSpec(path) == Model.DanglingSymlinkMessageSpec(path)
  {
    DanglingSymlinkMessageSpecPart1() +
    Quote.SpecQuoteAfBytes(Utf8.Encode(path)) + DanglingSymlinkMessageSpecPart2()
  }

  function CannotDereferenceText(path: string, reason: string): BenchWorld.Bytes
    ensures CannotDereferenceText(path, reason) == Model.CannotDereferenceText(path, reason)
  {
    CannotDereferenceTextPart1() + Quote.SpecQuoteAfBytes(Utf8.Encode(path)) +
    CannotDereferenceTextPart2() + Utf8.Encode(reason) + CannotDereferenceTextPart3()
  }

  function CannotDereferenceMessageSpec(path: string, err: int): BenchWorld.Bytes
    ensures CannotDereferenceMessageSpec(path, err) == Model.CannotDereferenceMessageSpec(path, err)
  {
    CannotDereferenceText(path, ErrnoTextSpec(err))
  }

  function NeitherChangedMessageSpec(path: string): BenchWorld.Bytes
    ensures NeitherChangedMessageSpec(path) == Model.NeitherChangedMessageSpec(path)
  {
    NeitherChangedMessageSpecPart1() + Quote.SpecQuoteAfBytes(Utf8.Encode(path)) +
    NeitherChangedMessageSpecPart2()
  }

  function SpecOctalText(mode: bv32): BenchWorld.Bytes
    ensures SpecOctalText(mode) == Model.SpecOctalText(mode)
  {
    [SpecOctDigitChar(((mode >> 9) & (7 as bv32)) as int)] +
    [SpecOctDigitChar(((mode >> 6) & (7 as bv32)) as int)] +
    [SpecOctDigitChar(((mode >> 3) & (7 as bv32)) as int)] +
    [SpecOctDigitChar((mode & (7 as bv32)) as int)]
  }

  function SpecPermissionText(mode: bv32): BenchWorld.Bytes
    ensures SpecPermissionText(mode) == Model.SpecPermissionText(mode)
  {
    [if (mode & Schema.S_IRUSR) != 0 as bv32 then 'r' else '-'] +
    [if (mode & Schema.S_IWUSR) != 0 as bv32 then 'w' else '-'] +
    [if (mode & Schema.S_ISUID) != 0 as bv32 then
       if (mode & Schema.S_IXUSR) != 0 as bv32 then 's' else 'S'
     else if (mode & Schema.S_IXUSR) != 0 as bv32 then 'x' else '-'] +
    [if (mode & Schema.S_IRGRP) != 0 as bv32 then 'r' else '-'] +
    [if (mode & Schema.S_IWGRP) != 0 as bv32 then 'w' else '-'] +
    [if (mode & Schema.S_ISGID) != 0 as bv32 then
       if (mode & Schema.S_IXGRP) != 0 as bv32 then 's' else 'S'
     else if (mode & Schema.S_IXGRP) != 0 as bv32 then 'x' else '-'] +
    [if (mode & Schema.S_IROTH) != 0 as bv32 then 'r' else '-'] +
    [if (mode & Schema.S_IWOTH) != 0 as bv32 then 'w' else '-'] +
    [if (mode & Schema.S_ISVTX) != 0 as bv32 then
       if (mode & Schema.S_IXOTH) != 0 as bv32 then 't' else 'T'
     else if (mode & Schema.S_IXOTH) != 0 as bv32 then 'x' else '-']
  }

  function SpecModeDisplay(mode: bv32): BenchWorld.Bytes
    ensures SpecModeDisplay(mode) == Model.SpecModeDisplay(mode)
  {
    SpecOctalText(mode) + SpecModeDisplayPart1() + SpecPermissionText(mode) + SpecModeDisplayPart2()
  }

  function ChangedMessageSpec(path: string, before: bv32, after: bv32): BenchWorld.Bytes
    ensures ChangedMessageSpec(path, before, after) == Model.ChangedMessageSpec(path, before, after)
  {
    ChangedMessageSpecPart1() + Quote.SpecQuoteAfBytes(Utf8.Encode(path)) +
    ChangedMessageSpecPart2() + SpecModeDisplay(before) +
    ChangedMessageSpecPart3() + SpecModeDisplay(after) + ChangedMessageSpecPart4()
  }

  function FailedChangeMessageSpec(
    path: string,
    before: bv32,
    desired: bv32
  ): BenchWorld.Bytes
    ensures FailedChangeMessageSpec(path, before, desired) == Model.FailedChangeMessageSpec(path, before, desired)
  {
    FailedChangeMessageSpecPart1() + Quote.SpecQuoteAfBytes(Utf8.Encode(path)) +
    FailedChangeMessageSpecPart2() + SpecModeDisplay(before) +
    FailedChangeMessageSpecPart3() + SpecModeDisplay(desired) + FailedChangeMessageSpecPart4()
  }

  function RetainedMessageSpec(path: string, mode: bv32): BenchWorld.Bytes
    ensures RetainedMessageSpec(path, mode) == Model.RetainedMessageSpec(path, mode)
  {
    RetainedMessageSpecPart1() + Quote.SpecQuoteAfBytes(Utf8.Encode(path)) +
    RetainedMessageSpecPart2() + SpecModeDisplay(mode) + RetainedMessageSpecPart3()
  }

  function AccessFailureMessageSpec(path: string): BenchWorld.Bytes
    ensures AccessFailureMessageSpec(path) == Model.AccessFailureMessageSpec(path)
  {
    Quote.SpecQuoteAfBytes(Utf8.Encode(path)) + AccessFailureMessageSpecPart1()
  }

  function SurpriseModeMessageSpec(path: string, actual: bv32, naive: bv32): BenchWorld.Bytes
    ensures SurpriseModeMessageSpec(path, actual, naive) == Model.SurpriseModeMessageSpec(path, actual, naive)
  {
    SurpriseModeMessageSpecPart1() + Quote.SpecQuoteFBytes(Utf8.Encode(path)) +
    SurpriseModeMessageSpecPart2() + SpecPermissionText(actual) +
    SurpriseModeMessageSpecPart3() + SpecPermissionText(naive) + SurpriseModeMessageSpecPart4()
  }

  function WriteErrorText(reason: string): BenchWorld.Bytes
    ensures WriteErrorText(reason) == Model.WriteErrorText(reason)
  {
    WriteErrorTextPart1() + Utf8.Encode(reason) + WriteErrorTextPart2()
  }
}
