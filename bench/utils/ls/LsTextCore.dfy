include "LsSpec.dfy"
include "LsUtf8Core.dfy"
include "LsEscapingCore.dfy"

module LsTextCore {
  import StreamWorld = BenchWorld
  import StreamContract = IOContract
  import Errno = Errnos
  import Result = Results
  import BenchIO
  import Utf8 = LsUtf8Core
  import BenchWorld
  import IOContract
  import Schema = LsSchema
  import Time = LsTime
  import SE = LsEscapingCore
  import Native = LsNativeSpec
  import NativeObservation = LsNativeObservationSpec
  import NativeDirectory = LsNativeDirectorySpec
  import opened Model = LsSpec

  function AccessErrorMessageSpec(path: BenchWorld.Path, err: int): BenchWorld.Bytes
    ensures AccessErrorMessageSpec(path, err) == Model.AccessErrorMessageSpec(path, err)
  {
    AccessErrorMessageSpecPart1() + SE.SpecQuoteAfBytes(Utf8.Encode(path)) +
    AccessErrorMessageSpecPart2() + ErrnoTextSpec(err) + AccessErrorMessageSpecPart3()
  }

  function ReadLinkErrorMessageSpec(path: BenchWorld.Path, err: int): BenchWorld.Bytes
    ensures ReadLinkErrorMessageSpec(path, err) == Model.ReadLinkErrorMessageSpec(path, err)
  {
    if err == 0 then []
    else
      ReadLinkErrorMessageSpecPart1() + SE.SpecQuoteAfBytes(Utf8.Encode(path)) +
      ReadLinkErrorMessageSpecPart2() + ErrnoTextSpec(err) + ReadLinkErrorMessageSpecPart3()
  }

  function EntryErrorTextSpec(path: BenchWorld.Path, observation: EntryObservation): BenchWorld.Bytes
    ensures EntryErrorTextSpec(path, observation) == Model.EntryErrorTextSpec(path, observation)
  {
    if !observation.ok then AccessErrorMessageSpec(path, observation.err)
    else ReadLinkErrorMessageSpec(path, observation.linkErr)
  }

  function ReadDirectoryErrorMessageSpec(path: BenchWorld.Path, err: int): BenchWorld.Bytes
    ensures ReadDirectoryErrorMessageSpec(path, err) == Model.ReadDirectoryErrorMessageSpec(path, err)
  {
    ReadDirectoryErrorMessageSpecPart1() + SE.SpecQuoteAfBytes(Utf8.Encode(path)) +
    ReadDirectoryErrorMessageSpecPart2() + ErrnoTextSpec(err) + ReadDirectoryErrorMessageSpecPart3()
  }

  function CloseDirectoryErrorMessageSpec(path: BenchWorld.Path, err: int): BenchWorld.Bytes
    ensures CloseDirectoryErrorMessageSpec(path, err) == Model.CloseDirectoryErrorMessageSpec(path, err)
  {
    if err == 0 then []
    else
      CloseDirectoryErrorMessageSpecPart1() + SE.SpecQuoteAfBytes(Utf8.Encode(path)) +
      CloseDirectoryErrorMessageSpecPart2() + ErrnoTextSpec(err) + CloseDirectoryErrorMessageSpecPart3()
  }

  function OpenDirectoryErrorMessageSpec(displayPath: BenchWorld.Path, err: int): BenchWorld.Bytes
    ensures OpenDirectoryErrorMessageSpec(displayPath, err) == Model.OpenDirectoryErrorMessageSpec(displayPath, err)
  {
    OpenDirectoryErrorMessageSpecPart1() + SE.SpecQuoteAfBytes(Utf8.Encode(displayPath)) +
    OpenDirectoryErrorMessageSpecPart2() + ErrnoTextSpec(err) + OpenDirectoryErrorMessageSpecPart3()
  }

  function DirectoryIdentityErrorMessageSpec(displayPath: BenchWorld.Path, err: int): BenchWorld.Bytes
    ensures DirectoryIdentityErrorMessageSpec(displayPath, err) == Model.DirectoryIdentityErrorMessageSpec(displayPath, err)
  {
    DirectoryIdentityErrorMessageSpecPart1() +
    SE.SpecQuoteAfBytes(Utf8.Encode(displayPath)) +
    DirectoryIdentityErrorMessageSpecPart2() + ErrnoTextSpec(err) + DirectoryIdentityErrorMessageSpecPart3()
  }

  opaque function DirectoryHeaderSpec(displayPath: BenchWorld.Path): BenchWorld.Bytes
    ensures DirectoryHeaderSpec(displayPath) == Model.DirectoryHeaderSpec(displayPath)
  {
    reveal Model.DirectoryHeaderSpec();
    Utf8.Encode(displayPath) + DirectoryHeaderSpecPart1()
  }

  function InvalidModeMessageSpec(mode: Schema.LsMode): BenchWorld.Bytes
    ensures InvalidModeMessageSpec(mode) == Model.InvalidModeMessageSpec(mode)
  {
    match mode
    case ModeInvalidBlockSize(value) =>
      Utf8.Encode(InvalidModeMessageSpecPart1()) + Utf8.Encode(value) + InvalidModeMessageSpecPart2()
    case ModeInvalidTime(value) =>
      Utf8.Encode(InvalidModeMessageSpecPart3()) + SE.SpecLocaleQuoteBytes(Utf8.Encode(value)) +
      Utf8.Encode(InvalidModeMessageSpecPart4() +
                  InvalidModeMessageSpecPart5() +
                  InvalidModeMessageSpecPart6() +
                  InvalidModeMessageSpecPart7() +
                  InvalidModeMessageSpecPart8() +
                  InvalidModeMessageSpecPart9() +
                  InvalidModeMessageSpecPart10())
    case ModeInvalidTimeStyle(value) =>
      Utf8.Encode(InvalidModeMessageSpecPart3()) + SE.SpecLocaleQuoteBytes(Utf8.Encode(value)) +
      Utf8.Encode(InvalidModeMessageSpecPart11() +
                  InvalidModeMessageSpecPart5() +
                  InvalidModeMessageSpecPart12() +
                  InvalidModeMessageSpecPart13() +
                  InvalidModeMessageSpecPart14() +
                  InvalidModeMessageSpecPart15() +
                  InvalidModeMessageSpecPart16() +
                  InvalidModeMessageSpecPart10())
    case _ => []
  }

  function NatTextSpec(n: nat): string
    ensures NatTextSpec(n) == Model.NatTextSpec(n)
    decreases n
  {
    if n < 10 then [DigitChar(n)]
    else NatTextSpec(n / 10) + [DigitChar(n % 10)]
  }

  function PadColumn(text: string, width: nat, right: bool): string
    ensures PadColumn(text, width, right) == Model.PadColumn(text, width, right)
  {
    var blanks := seq((if width > |text| then width - |text| else 0), i => ' ');
    if right then blanks + text else text + blanks
  }

  function MaximumWidth(values: set<nat>): (maximum: nat)
    ensures MaximumWidth(values) == Model.MaximumWidth(values)
    ensures values == {} ==> maximum == 0
    ensures values != {} ==> maximum in values
    ensures forall value: nat | value in values :: value <= maximum
  {
    Model.MaximumWidth(values)
  } by method {
    if values == {} {
      return 0;
    }
    var member: nat :| member in values;
    maximum := member;
    var remaining := values - {member};
    while remaining != {}
      invariant remaining <= values
      invariant maximum in values
      invariant forall value: nat | value in values - remaining :: value <= maximum
      decreases |remaining|
    {
      ghost var beforeRemaining := remaining;
      ghost var beforeMaximum := maximum;
      var value: nat :| value in remaining;
      remaining := remaining - {value};
      if maximum < value {
        maximum := value;
      }
      assert beforeMaximum <= maximum;
      assert forall item: nat | item in values - remaining :: item <= maximum by {
        forall item: nat | item in values - remaining
          ensures item <= maximum
        {
          if item != value {
            assert item in values - beforeRemaining;
            assert item <= beforeMaximum;
          }
        }
      }
    }
    ghost var modeled := Model.MaximumWidth(values);
    assert modeled in values;
    assert modeled in values - remaining;
    assert modeled <= maximum;
    assert maximum <= modeled;
    return maximum;
  }

  function StatusWidthsSpec(cmd: Schema.LsCmd, statuses: set<BenchWorld.FileStatus>): ColumnWidths
    ensures StatusWidthsSpec(cmd, statuses) == Model.StatusWidthsSpec(cmd, statuses)
  {
    assert forall n: nat :: NatTextSpec(n) == Model.NatTextSpec(n);
    assert (set status <- statuses :: |NatTextSpec(DisplayedBlocksSpec(status.storage.allocatedBlocks, cmd.cliBlockSize))|) ==
           (set status <- statuses :: |Model.NatTextSpec(DisplayedBlocksSpec(status.storage.allocatedBlocks, cmd.cliBlockSize))|);
    assert (set status <- statuses :: |NatTextSpec(status.linkCount)|) ==
           (set status <- statuses :: |Model.NatTextSpec(status.linkCount)|);
    assert (set status <- statuses :: |NatTextSpec(status.ownership.uid)|) ==
           (set status <- statuses :: |Model.NatTextSpec(status.ownership.uid)|);
    assert (set status <- statuses :: |NatTextSpec(status.ownership.gid)|) ==
           (set status <- statuses :: |Model.NatTextSpec(status.ownership.gid)|);
    assert (set status <- statuses :: |NatTextSpec(DisplayedFileSizeSpec(status.storage.size, cmd.fileSizeBlockSize))|) ==
           (set status <- statuses :: |Model.NatTextSpec(DisplayedFileSizeSpec(status.storage.size, cmd.fileSizeBlockSize))|);
    ColumnWidths(
      MaximumWidth(set status <- statuses :: |NatTextSpec(DisplayedBlocksSpec(status.storage.allocatedBlocks, cmd.cliBlockSize))|),
      MaximumWidth(set status <- statuses :: |NatTextSpec(status.linkCount)|),
      MaximumWidth(set status <- statuses :: |NatTextSpec(status.ownership.uid)|),
      MaximumWidth(set status <- statuses :: |NatTextSpec(status.ownership.gid)|),
      MaximumWidth(set status <- statuses :: |NatTextSpec(DisplayedFileSizeSpec(status.storage.size, cmd.fileSizeBlockSize))|))
  }

  function ObservationWidthsSpec(cmd: Schema.LsCmd, observations: seq<EntryObservation>): ColumnWidths
    ensures ObservationWidthsSpec(cmd, observations) == Model.ObservationWidthsSpec(cmd, observations)
  {
    StatusWidthsSpec(cmd, set i: nat | i < |observations| && observations[i].ok :: observations[i].status)
  }

  function OperandWidthsSpec(cmd: Schema.LsCmd, observations: seq<OperandObservation>): ColumnWidths
    ensures OperandWidthsSpec(cmd, observations) == Model.OperandWidthsSpec(cmd, observations)
  {
    StatusWidthsSpec(cmd, set i: nat | i < |observations| && observations[i].ok :: observations[i].status)
  }

  function RenderFailedEntrySpec(
    cmd: Schema.LsCmd, observation: EntryObservation, widths: ColumnWidths
  ): BenchWorld.Bytes
    ensures RenderFailedEntrySpec(cmd, observation, widths) == Model.RenderFailedEntrySpec(cmd, observation, widths)
  {
    var blocks := if cmd.showBlocks then PadColumn(RenderFailedEntrySpecPart1(), widths.blocks, true) + RenderFailedEntrySpecPart2() else RenderFailedEntrySpecPart3();
    Utf8.Encode(blocks + (if cmd.numericLong then
      [DirectoryEntryKindCharSpec(observation.entryKind)] + RenderFailedEntrySpecPart4() +
      PadColumn(RenderFailedEntrySpecPart1(), widths.links, true) + RenderFailedEntrySpecPart2() +
      PadColumn(RenderFailedEntrySpecPart1(), widths.owner, false) + RenderFailedEntrySpecPart2() +
      PadColumn(RenderFailedEntrySpecPart1(), widths.group, false) + RenderFailedEntrySpecPart2() +
      PadColumn(RenderFailedEntrySpecPart1(), widths.size, true) + RenderFailedEntrySpecPart2() +
      PadColumn(RenderFailedEntrySpecPart1(), FailedTimeWidthSpec(cmd), true) + RenderFailedEntrySpecPart2()
    else RenderFailedEntrySpecPart3()) + observation.displayName + RenderFailedEntrySpecPart5())
  }

  function RecursiveCycleMessageSpec(displayPath: BenchWorld.Path): BenchWorld.Bytes
    ensures RecursiveCycleMessageSpec(displayPath) == Model.RecursiveCycleMessageSpec(displayPath)
  {
    RecursiveCycleMessageSpecPart1() + SE.SpecQuoteFBytes(Utf8.Encode(displayPath)) +
    RecursiveCycleMessageSpecPart2()
  }

  function WriteErrorText(reason: string): StreamWorld.Bytes
    ensures WriteErrorText(reason) == Model.WriteErrorText(reason)
  {
    WriteErrorTextPart1() + Utf8.Encode(reason) + WriteErrorTextPart2()
  }
}
