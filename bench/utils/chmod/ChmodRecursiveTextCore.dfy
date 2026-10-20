include "ChmodRecursiveSpec.dfy"
include "ChmodUtf8Core.dfy"
include "ChmodEscapingCore.dfy"
include "ChmodTextCore.dfy"

module ChmodRecursiveTextCore {
  import BenchWorld
  import BenchIO
  import ChmodSpec
  import Utf8 = ChmodUtf8Core
  import Schema = ChmodSchema
  import Base = ChmodTextCore
  import Quote = ChmodEscapingCore
  import IOC = IOContract
  import opened Model = ChmodRecursiveSpec

  function RootPreserveMessageSpec(displayPath: string, alias: bool): BenchWorld.Bytes
    ensures RootPreserveMessageSpec(displayPath, alias) == Model.RootPreserveMessageSpec(displayPath, alias)
  {
    if alias then
      RootPreserveMessageSpecPart1() +
      Quote.SpecQuoteAfBytes(Utf8.Encode(displayPath)) + RootPreserveMessageSpecPart2() +
      RootPreserveMessageSpecPart3()
    else
      RootPreserveMessageSpecPart4() +
      RootPreserveMessageSpecPart3()
  }

  function ReadDirectoryMessageSpec(path: string, err: int): BenchWorld.Bytes
    ensures ReadDirectoryMessageSpec(path, err) == Model.ReadDirectoryMessageSpec(path, err)
  {
    ReadDirectoryMessageSpecPart1() +
    Quote.SpecQuoteAfBytes(Utf8.Encode(path)) + ReadDirectoryMessageSpecPart2() +
    ChmodSpec.ErrnoTextSpec(err) + ReadDirectoryMessageSpecPart3()
  }

  function DanglingSymlinkMessageSpec(path: string): BenchWorld.Bytes
    ensures DanglingSymlinkMessageSpec(path) == Model.DanglingSymlinkMessageSpec(path)
  {
    Base.DanglingSymlinkMessageSpec(path)
  }

  function CannotDereferenceMessageSpec(path: string, err: int): BenchWorld.Bytes
    ensures CannotDereferenceMessageSpec(path, err) == Model.CannotDereferenceMessageSpec(path, err)
  {
    CannotDereferenceMessageSpecPart1() +
    Quote.SpecQuoteAfBytes(Utf8.Encode(path)) + CannotDereferenceMessageSpecPart2() +
    ChmodSpec.ErrnoTextSpec(err) + CannotDereferenceMessageSpecPart3()
  }

  function NeitherChangedMessageSpec(path: string): BenchWorld.Bytes
    ensures NeitherChangedMessageSpec(path) == Model.NeitherChangedMessageSpec(path)
  {
    Base.NeitherChangedMessageSpec(path)
  }

  function ReadDirectoryText(path: string, reason: string): BenchWorld.Bytes
    ensures ReadDirectoryText(path, reason) == Model.ReadDirectoryText(path, reason)
  {
    ReadDirectoryTextPart1() + Quote.SpecQuoteAfBytes(Utf8.Encode(path)) + ReadDirectoryTextPart2() + Utf8.Encode(reason) + ReadDirectoryTextPart3()
  }

  function TerminalReadDirectoryText(path: string, hadEntries: bool, reason: string): BenchWorld.Bytes
    ensures TerminalReadDirectoryText(path, hadEntries, reason) == Model.TerminalReadDirectoryText(path, hadEntries, reason)
  {
    if hadEntries then
      TerminalReadDirectoryTextPart1() + Quote.SpecQuoteFBytes(Utf8.Encode(path)) + TerminalReadDirectoryTextPart2() + Utf8.Encode(reason) + TerminalReadDirectoryTextPart3()
    else ReadDirectoryText(path, reason)
  }

  function NativeAccessText(cmd: Schema.ChmodCmd, path: string, kind: RecursiveFailureKind,
    reason: string): BenchWorld.Bytes
    ensures NativeAccessText(cmd, path, kind, reason) == Model.NativeAccessText(cmd, path, kind, reason)
  {
    if cmd.silent then []
    else if kind.RecursiveDangling? then DanglingSymlinkMessageSpec(path)
    else if kind.RecursiveDereference? then Base.CannotDereferenceText(path, reason)
    else Base.AccessErrorMessageSpec(path, reason)
  }

  function RecursiveAccessStdoutSpec(cmd: Schema.ChmodCmd, path: string): BenchWorld.Bytes
    ensures RecursiveAccessStdoutSpec(cmd, path) == Model.RecursiveAccessStdoutSpec(cmd, path)
  {
    if cmd.verbose then Base.AccessFailureMessageSpec(path) else []
  }

  function RecursiveSkipStdoutSpec(cmd: Schema.ChmodCmd, path: string): BenchWorld.Bytes
    ensures RecursiveSkipStdoutSpec(cmd, path) == Model.RecursiveSkipStdoutSpec(cmd, path)
  {
    if cmd.verbose then NeitherChangedMessageSpec(path) else []
  }
}
