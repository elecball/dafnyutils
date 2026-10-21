include "CommRenderSpec.dfy"
include "../../core/World.dfy"
include "CommSchema.dfy"

module CommRenderCore {
  import Spec = CommRenderSpec

  import BenchWorld
  import Schema = CommSchema

  datatype LineOrder = LineLess | LineEqual | LineGreater
  function RecordsFrom(data: BenchWorld.Bytes, current: BenchWorld.Bytes, delimiter: char): seq<BenchWorld.Bytes>
    decreases |data|
  {
    if |data| == 0 then
      if |current| == 0 then [] else [current]
    else if data[0] == delimiter then
      [current] + RecordsFrom(data[1..], [], delimiter)
    else
      RecordsFrom(data[1..], current + [data[0]], delimiter)
  }

  function Records(data: BenchWorld.Bytes, delimiter: char): seq<BenchWorld.Bytes>
  {
    RecordsFrom(data, [], delimiter)
  }

  function CompareRecords(left: BenchWorld.Bytes, right: BenchWorld.Bytes): LineOrder
    decreases |left| + |right|
  {
    if |left| == 0 && |right| == 0 then
      LineEqual
    else if |left| == 0 then
      LineLess
    else if |right| == 0 then
      LineGreater
    else if (left[0] as int) < (right[0] as int) then
      LineLess
    else if (right[0] as int) < (left[0] as int) then
      LineGreater
    else
      CompareRecords(left[1..], right[1..])
  }

  function RenderRecords(
    cmd: Schema.CommCmd,
    left: seq<BenchWorld.Bytes>,
    right: seq<BenchWorld.Bytes>
  ): BenchWorld.Bytes
    decreases |left| + |right|
  {
    if |left| == 0 then
      if |right| == 0 then
        []
      else
        Spec.RenderFragment(cmd, Spec.OnlySecond, right[0]) + RenderRecords(cmd, left, right[1..])
    else if |right| == 0 then
      Spec.RenderFragment(cmd, Spec.OnlyFirst, left[0]) + RenderRecords(cmd, left[1..], right)
    else
      match CompareRecords(left[0], right[0])
      case LineLess =>
        Spec.RenderFragment(cmd, Spec.OnlyFirst, left[0]) + RenderRecords(cmd, left[1..], right)
      case LineGreater =>
        Spec.RenderFragment(cmd, Spec.OnlySecond, right[0]) + RenderRecords(cmd, left, right[1..])
      case LineEqual =>
        Spec.RenderFragment(cmd, Spec.Both, left[0]) + RenderRecords(cmd, left[1..], right[1..])
  }

  function CountRecords(left: seq<BenchWorld.Bytes>, right: seq<BenchWorld.Bytes>): Spec.ColumnCounts
    decreases |left| + |right|
  {
    if |left| == 0 then
      if |right| == 0 then
        Spec.ColumnCounts(0, 0, 0)
      else
        Spec.AddKind(Spec.OnlySecond, CountRecords(left, right[1..]))
    else if |right| == 0 then
      Spec.AddKind(Spec.OnlyFirst, CountRecords(left[1..], right))
    else
      match CompareRecords(left[0], right[0])
      case LineLess =>
        Spec.AddKind(Spec.OnlyFirst, CountRecords(left[1..], right))
      case LineGreater =>
        Spec.AddKind(Spec.OnlySecond, CountRecords(left, right[1..]))
      case LineEqual =>
        Spec.AddKind(Spec.Both, CountRecords(left[1..], right[1..]))
  }

  function DigitChar(n: nat): char
    requires n < 10
  {
    (('0' as int) + n) as char
  }

  function NatText(n: nat): BenchWorld.Bytes
    decreases n
  {
    if n < 10 then [DigitChar(n)] else NatText(n / 10) + [DigitChar(n % 10)]
  }

  function TotalRow(cmd: Schema.CommCmd, left: seq<BenchWorld.Bytes>, right: seq<BenchWorld.Bytes>): BenchWorld.Bytes
  {
    if !cmd.total then
      []
    else
      var counts := CountRecords(left, right);
      NatText(counts.first) + cmd.outputDelimiter +
      NatText(counts.second) + cmd.outputDelimiter +
      NatText(counts.both) + cmd.outputDelimiter +
      "total" + [Spec.RecordDelimiter(cmd.zeroTerminated)]
  }

  function RenderData(
    cmd: Schema.CommCmd,
    leftData: BenchWorld.Bytes,
    rightData: BenchWorld.Bytes
  ): BenchWorld.Bytes
  {
    var delimiter := Spec.RecordDelimiter(cmd.zeroTerminated);
    var left := Records(leftData, delimiter);
    var right := Records(rightData, delimiter);
    RenderRecords(cmd, left, right) + TotalRow(cmd, left, right)
  }

  function RecordsSorted(records: seq<BenchWorld.Bytes>): bool
    decreases |records|
  {
    if |records| < 2 then
      true
    else
      CompareRecords(records[0], records[1]) != LineGreater && RecordsSorted(records[1..])
  }

  function DataSorted(data: BenchWorld.Bytes, zeroTerminated: bool): bool
  {
    RecordsSorted(Records(data, Spec.RecordDelimiter(zeroTerminated)))
  }

}
