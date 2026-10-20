include "CpSpec.dfy"
include "CpUtf8Core.dfy"
include "CpEscapingCore.dfy"

module CpTextCore {
  import BW = BenchWorld
  import Results
  import BenchIO
  import C = IOContract
  import S = CpSchema
  import CliTypes
  import CliModel
  import Utf8 = CpUtf8Core
  import SE = CpEscapingCore
  import Paths = CpPathSpec
  import opened Model = CpSpec

  function ConfigurationDiagnostic(error: S.CpError): BW.Bytes
    ensures ConfigurationDiagnostic(error) == Model.ConfigurationDiagnostic(error)
  {
    ConfigurationError(error,SE.SpecLocaleQuoteBytes(Utf8.Encode(ErrorArgument(error))))
  }

  function CannotStat(path: BW.Bytes, reason: string): BW.Bytes
    ensures CannotStat(path, reason) == Model.CannotStat(path, reason)
  {
    CannotStatPart1() + path + CannotStatPart2() + Utf8.Encode(reason) + CannotStatPart3()
  }

  function CannotCreate(target: BW.Bytes, reason: string): BW.Bytes
    ensures CannotCreate(target, reason) == Model.CannotCreate(target, reason)
  {
    CannotCreatePart1() + target + CannotCreatePart2() + Utf8.Encode(reason) + CannotCreatePart3()
  }

  function CannotOpen(source: BW.Bytes, reason: string): BW.Bytes
    ensures CannotOpen(source, reason) == Model.CannotOpen(source, reason)
  {
    CannotOpenPart1() + source + CannotOpenPart2() + Utf8.Encode(reason) + CannotOpenPart3()
  }

  function ReadError(source: BW.Bytes, reason: string): BW.Bytes
    ensures ReadError(source, reason) == Model.ReadError(source, reason)
  {
    ReadErrorPart1() + source + ReadErrorPart2() + Utf8.Encode(reason) + ReadErrorPart3()
  }

  function WriteError(target: BW.Bytes, reason: string): BW.Bytes
    ensures WriteError(target, reason) == Model.WriteError(target, reason)
  {
    WriteErrorPart1() + target + WriteErrorPart2() + Utf8.Encode(reason) + WriteErrorPart3()
  }

  function CloseError(target: BW.Bytes, reason: string): BW.Bytes
    ensures CloseError(target, reason) == Model.CloseError(target, reason)
  {
    CloseErrorPart1() + target + CloseErrorPart2() + Utf8.Encode(reason) + CloseErrorPart3()
  }

  function CannotRemove(target: BW.Bytes, reason: string): BW.Bytes
    ensures CannotRemove(target, reason) == Model.CannotRemove(target, reason)
  {
    CannotRemovePart1() + target + CannotRemovePart2() + Utf8.Encode(reason) + CannotRemovePart3()
  }

  function TargetError(target: BW.Bytes, reason: string): BW.Bytes
    ensures TargetError(target, reason) == Model.TargetError(target, reason)
  {
    TargetErrorPart1() + target + TargetErrorPart2() + Utf8.Encode(reason) + TargetErrorPart3()
  }

  function DirectoryError(target: BW.Bytes, reason: string): BW.Bytes
    ensures DirectoryError(target, reason) == Model.DirectoryError(target, reason)
  {
    DirectoryErrorPart1() + target + DirectoryErrorPart2() + Utf8.Encode(reason) + DirectoryErrorPart3()
  }

  function CreateDirectoryError(target: BW.Bytes, reason: string): BW.Bytes
    ensures CreateDirectoryError(target, reason) == Model.CreateDirectoryError(target, reason)
  {
    CreateDirectoryErrorPart1() + target + CreateDirectoryErrorPart2() + Utf8.Encode(reason) + CreateDirectoryErrorPart3()
  }

  function ReadDirectoryError(source: BW.Bytes, reason: string): BW.Bytes
    ensures ReadDirectoryError(source, reason) == Model.ReadDirectoryError(source, reason)
  {
    ReadDirectoryErrorPart1() + source + ReadDirectoryErrorPart2() + Utf8.Encode(reason) + ReadDirectoryErrorPart3()
  }

  function LinkError(source: BW.Bytes, target: BW.Bytes, reason: string, symbolic: bool): BW.Bytes
    ensures LinkError(source, target, reason, symbolic) == Model.LinkError(source, target, reason, symbolic)
  {
    if symbolic then LinkErrorPart1() + target + LinkErrorPart2() + source + LinkErrorPart3() + Utf8.Encode(reason) + LinkErrorPart4()
    else LinkErrorPart5() + target + LinkErrorPart2() + source + LinkErrorPart3() + Utf8.Encode(reason) + LinkErrorPart4()
  }

  function CopiedSymlinkError(target: BW.Bytes, reason: string): BW.Bytes
    ensures CopiedSymlinkError(target, reason) == Model.CopiedSymlinkError(target, reason)
  {
    CopiedSymlinkErrorPart1() + target + CopiedSymlinkErrorPart2() + Utf8.Encode(reason) + CopiedSymlinkErrorPart3()
  }

  function ReadSymlinkError(source: BW.Bytes, reason: string): BW.Bytes
    ensures ReadSymlinkError(source, reason) == Model.ReadSymlinkError(source, reason)
  {
    ReadSymlinkErrorPart1() + source + ReadSymlinkErrorPart2() + Utf8.Encode(reason) + ReadSymlinkErrorPart3()
  }

  function RelativeSymlinkError(target: string): BW.Bytes
    ensures RelativeSymlinkError(target) == Model.RelativeSymlinkError(target)
  {
    RelativeSymlinkErrorPart1() + SE.SpecQuoteFBytes(Utf8.Encode(target)) + RelativeSymlinkErrorPart2()
  }

  function ModeError(target: BW.Bytes, reason: string): BW.Bytes
    ensures ModeError(target, reason) == Model.ModeError(target, reason)
  {
    ModeErrorPart1() + target + ModeErrorPart2() + Utf8.Encode(reason) + ModeErrorPart3()
  }

  function TimeError(target: BW.Bytes, reason: string): BW.Bytes
    ensures TimeError(target, reason) == Model.TimeError(target, reason)
  {
    TimeErrorPart1() + target + TimeErrorPart2() + Utf8.Encode(reason) + TimeErrorPart3()
  }

  function StdoutError(reason: string): BW.Bytes
    ensures StdoutError(reason) == Model.StdoutError(reason)
  { StdoutErrorPart1() + Utf8.Encode(reason) + StdoutErrorPart2() }

  function CannotBackup(target: BW.Bytes, reason: string): BW.Bytes
    ensures CannotBackup(target, reason) == Model.CannotBackup(target, reason)
  { CannotBackupPart1() + target + CannotBackupPart2() + Utf8.Encode(reason) + CannotBackupPart3() }

  function CannotUnbackup(target: BW.Bytes, reason: string): BW.Bytes
    ensures CannotUnbackup(target, reason) == Model.CannotUnbackup(target, reason)
  { CannotUnbackupPart1() + target + CannotUnbackupPart2() + Utf8.Encode(reason) + CannotUnbackupPart3() }

  function ParentVerbose(source: string, target: string): BW.Bytes
    ensures ParentVerbose(source, target) == Model.ParentVerbose(source, target)
  {
    Utf8.Encode(source) + ParentVerbosePart1() + Utf8.Encode(target) + ParentVerbosePart2()
  }

  function ParentAttributesError(path: BW.Bytes, reason: string): BW.Bytes
    ensures ParentAttributesError(path, reason) == Model.ParentAttributesError(path, reason)
  {
    ParentAttributesErrorPart1() + path + ParentAttributesErrorPart2() + Utf8.Encode(reason) + ParentAttributesErrorPart3()
  }

  function ParentCreateError(path: BW.Bytes, reason: string): BW.Bytes
    ensures ParentCreateError(path, reason) == Model.ParentCreateError(path, reason)
  {
    ParentCreateErrorPart1() + path + ParentCreateErrorPart2() + Utf8.Encode(reason) + ParentCreateErrorPart3()
  }

  function ParentSetModeError(path: BW.Bytes, reason: string): BW.Bytes
    ensures ParentSetModeError(path, reason) == Model.ParentSetModeError(path, reason)
  {
    ParentSetModeErrorPart1() + path + ParentSetModeErrorPart2() + Utf8.Encode(reason) + ParentSetModeErrorPart3()
  }

  function ParentTimeError(path: BW.Bytes, reason: string): BW.Bytes
    ensures ParentTimeError(path, reason) == Model.ParentTimeError(path, reason)
  {
    ParentTimeErrorPart1() + path + ParentTimeErrorPart2() + Utf8.Encode(reason) + ParentTimeErrorPart3()
  }

  function ParentModeError(path: BW.Bytes, reason: string): BW.Bytes
    ensures ParentModeError(path, reason) == Model.ParentModeError(path, reason)
  {
    ParentModeErrorPart1() + path + ParentModeErrorPart2() + Utf8.Encode(reason) + ParentModeErrorPart3()
  }
}
