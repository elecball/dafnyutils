include "../../../core/Utf8.dfy"
include "../Spec/CutSpec.dfy"
include "../../../core/World.dfy"
include "../../../core/IO.dfy"
include "../../../core/IOContract.dfy"
include "../Spec/CutSchema.dfy"

module CutCore {
  import StreamContract = IOContract

  import Result = Results
  import BenchIO
  import Utf8 = Utf8Semantics
  import BenchWorld
  import IOContract
  import CutSchema
  import Spec = CutSpec

  // Deferred GNU behavior: field mode, input delimiters, -s suppression, -n
  // multibyte split suppression, and locale-sensitive multibyte characters are
  // outside this benchmark slice. In LC_ALL=C, -b and -c share byte semantics.
  function Selected(ranges: seq<CutSchema.Range>, pos: int): bool
    decreases |ranges|
  {
    if |ranges| == 0 then
      false
    else
      Spec.RangeContains(ranges[0], pos) || Selected(ranges[1..], pos)
  } by method {
    if |ranges| == 0 {
      return false;
    }
    if Spec.RangeContains(ranges[0], pos) {
      return true;
    }
    return Selected(ranges[1..], pos);
  }

  function SelectionIncludes(selection: CutSchema.Selection, pos: int): bool
  {
    var inList := Selected(selection.ranges, pos);
    if selection.complement then !inList else inList
  } by method {
    var inList := Selected(selection.ranges, pos);
    return if selection.complement then !inList else inList;
  }

  function HasCustomOutputDelimiter(delimiter: CutSchema.OutputDelimiter): bool
  {
    delimiter.OutputCustom?
  } by method {
    return delimiter.OutputCustom?;
  }

  function RecordLength(data: BenchWorld.Bytes, delimiter: BenchWorld.RawByte): nat
    ensures RecordLength(data, delimiter) <= |data|
    decreases |data|
  {
    if |data| == 0 || data[0] == delimiter then
      0
    else
      1 + RecordLength(data[1..], delimiter)
  } by method {
    if |data| == 0 || data[0] == delimiter {
      return 0;
    }
    return 1 + RecordLength(data[1..], delimiter);
  }

  function SelectPositions(line: BenchWorld.Bytes, selection: CutSchema.Selection, pos: int): BenchWorld.Bytes
    decreases |line|
  {
    if |line| == 0 then
      []
    else
      (if SelectionIncludes(selection, pos) then [line[0]] else []) +
      SelectPositions(line[1..], selection, pos + 1)
  } by method {
    if |line| == 0 {
      return [];
    }
    var selected := SelectionIncludes(selection, pos);
    return (if selected then [line[0]] else []) +
      SelectPositions(line[1..], selection, pos + 1);
  }

  function AdjacentCoveredByRange(ranges: seq<CutSchema.Range>, pos: int): bool
    decreases |ranges|
  {
    if |ranges| == 0 then
      false
    else
      (Spec.RangeContains(ranges[0], pos - 1) && Spec.RangeContains(ranges[0], pos)) ||
      AdjacentCoveredByRange(ranges[1..], pos)
  } by method {
    if |ranges| == 0 {
      return false;
    }
    if Spec.RangeContains(ranges[0], pos - 1) && Spec.RangeContains(ranges[0], pos) {
      return true;
    }
    return AdjacentCoveredByRange(ranges[1..], pos);
  }

  function GroupBoundaryBefore(selection: CutSchema.Selection, pos: int): bool
  {
    if pos <= 1 then
      false
    else if selection.complement then
      !SelectionIncludes(selection, pos - 1)
    else
      !AdjacentCoveredByRange(selection.ranges, pos)
  } by method {
    if pos <= 1 {
      return false;
    }
    if selection.complement {
      return !SelectionIncludes(selection, pos - 1);
    }
    return !AdjacentCoveredByRange(selection.ranges, pos);
  }

  function SelectPositionsDelimited(
    line: BenchWorld.Bytes,
    selection: CutSchema.Selection,
    outputDelimiter: BenchWorld.Bytes,
    pos: int,
    emitted: bool
  ): BenchWorld.Bytes
    decreases |line|
  {
    if |line| == 0 then
      []
    else if SelectionIncludes(selection, pos) then
      (if emitted && GroupBoundaryBefore(selection, pos) then outputDelimiter else []) +
      [line[0]] +
      SelectPositionsDelimited(line[1..], selection, outputDelimiter, pos + 1, true)
    else
      SelectPositionsDelimited(line[1..], selection, outputDelimiter, pos + 1, emitted)
  } by method {
    if |line| == 0 {
      return [];
    }
    if SelectionIncludes(selection, pos) {
      var boundary := GroupBoundaryBefore(selection, pos);
      return (if emitted && boundary then outputDelimiter else []) +
        [line[0]] +
        SelectPositionsDelimited(line[1..], selection, outputDelimiter, pos + 1, true);
    }
    return SelectPositionsDelimited(
        line[1..], selection, outputDelimiter, pos + 1, emitted
      );
  }

  function SelectRecord(
    line: BenchWorld.Bytes,
    selection: CutSchema.Selection,
    outputDelimiter: CutSchema.OutputDelimiter
  ): BenchWorld.Bytes
  {
    if HasCustomOutputDelimiter(outputDelimiter) then
      SelectPositionsDelimited(line, selection, Spec.OutputDelimiterBytes(outputDelimiter), 1, false)
    else
      SelectPositions(line, selection, 1)
  } by method {
    if HasCustomOutputDelimiter(outputDelimiter) {
      return SelectPositionsDelimited(
          line, selection, Spec.OutputDelimiterBytes(outputDelimiter), 1, false
        );
    }
    return SelectPositions(line, selection, 1);
  }

  function CutData(
    selection: CutSchema.Selection,
    outputDelimiter: CutSchema.OutputDelimiter,
    zeroTerminated: bool,
    data: BenchWorld.Bytes
  ): BenchWorld.Bytes
    decreases |data|
  {
    if |data| == 0 then
      []
    else
      var delimiter := Spec.RecordDelimiter(zeroTerminated);
      var lineLen := RecordLength(data, delimiter);
      var line := data[..lineLen];
      var rest := if lineLen < |data| then data[lineLen + 1..] else [];
      SelectRecord(line, selection, outputDelimiter) + [delimiter] +
      CutData(selection, outputDelimiter, zeroTerminated, rest)
  } by method {
    if |data| == 0 {
      return [];
    }
    var delimiter := Spec.RecordDelimiter(zeroTerminated);
    var lineLen := RecordLength(data, delimiter);
    var line := data[..lineLen];
    var rest := if lineLen < |data| then data[lineLen + 1..] else [];
    var selected := SelectRecord(line, selection, outputDelimiter);
    var tail := CutData(selection, outputDelimiter, zeroTerminated, rest);
    return selected + [delimiter] + tail;
  }

  function OutputPiece(cmd: CutSchema.CutCmdRaw, result: BenchWorld.IOResult<BenchWorld.Bytes>): BenchWorld.Bytes
  {
    match result
    case Ok(data) => CutData(cmd.selection, cmd.outputDelimiter, cmd.zeroTerminated, data)
    case Err(error) => if error.StreamFailure? then CutData(cmd.selection, cmd.outputDelimiter, cmd.zeroTerminated, error.partial) else []
  } by method {
    match result
    case Ok(data) =>
      return CutData(cmd.selection, cmd.outputDelimiter, cmd.zeroTerminated, data);
    case Err(error) =>
      return if error.StreamFailure? then CutData(cmd.selection, cmd.outputDelimiter, cmd.zeroTerminated, error.partial) else [];
  }

  function ErrorPiece(input: CutSchema.Input, result: BenchWorld.IOResult<BenchWorld.Bytes>): BenchWorld.Bytes
  {
    match input
    case Stdin => if result.Err? then Spec.ErrorMessage("-", result.e) else []
    case File(path) =>
      match result
      case Ok(_) => []
      case Err(err) => Spec.ErrorMessage(path, err)
  } by method {
    match input
    case Stdin =>
      return if result.Err? then Spec.ErrorMessage("-", result.e) else [];
    case File(path) =>
      match result
      case Ok(_) =>
        return [];
      case Err(err) =>
        return Spec.ErrorMessage(path, err);
  }

  function HadErrorPiece(input: CutSchema.Input, result: BenchWorld.IOResult<BenchWorld.Bytes>): bool
  {
    match input
    case Stdin => result.Err?
    case File(_) =>
      match result
      case Ok(_) => false
      case Err(_) => true
  } by method {
    match input
    case Stdin =>
      return result.Err?;
    case File(_) =>
      return result.Err?;
  }

  ghost function ShiftNats(values: seq<nat>, amount: nat): seq<nat>
  {
    seq(|values|, i requires 0 <= i < |values| => values[i] + amount)
  }

  ghost function JoinFragments(
    fragments: seq<BenchWorld.Bytes>
  ): BenchWorld.Bytes
    decreases |fragments|
  {
    if |fragments| == 0 then
      []
    else
      fragments[0] + JoinFragments(fragments[1..])
  }

  ghost function FragmentCuts(
    fragments: seq<BenchWorld.Bytes>
  ): seq<nat>
    decreases |fragments|
  {
    if |fragments| == 0 then
      [0]
    else
      [0] + ShiftNats(FragmentCuts(fragments[1..]), |fragments[0]|)
  }

  lemma ShiftNatsIndex(values: seq<nat>, amount: nat, i: nat)
    requires i < |values|
    ensures ShiftNats(values, amount)[i] == values[i] + amount
  {
  }

  lemma JoinFragmentsLengthStep(fragments: seq<BenchWorld.Bytes>)
    requires |fragments| > 0
    ensures |JoinFragments(fragments)| ==
            |fragments[0]| + |JoinFragments(fragments[1..])|
  {
  }

  lemma JoinFragmentsSliceStep(
    fragments: seq<BenchWorld.Bytes>, start: nat, end: nat
  )
    requires |fragments| > 0
    requires start <= end <= |JoinFragments(fragments[1..])|
    ensures JoinFragments(fragments)[|fragments[0]| + start..
            |fragments[0]| + end] ==
            JoinFragments(fragments[1..])[start..end]
  {
  }

  lemma JoinFragmentsSnoc(
    fragments: seq<BenchWorld.Bytes>,
    fragment: BenchWorld.Bytes
  )
    ensures JoinFragments(fragments + [fragment]) ==
            JoinFragments(fragments) + fragment
    decreases |fragments|
  {
    if |fragments| > 0 {
      JoinFragmentsSnoc(fragments[1..], fragment);
      assert (fragments + [fragment])[1..] ==
             fragments[1..] + [fragment];
    }
  }

  lemma FragmentCutsSatisfyRelation(
    fragments: seq<BenchWorld.Bytes>
  )
    ensures Spec.FragmentsConcatenate(
              fragments, JoinFragments(fragments), FragmentCuts(fragments)
            )
    decreases |fragments|
  {
    reveal Spec.FragmentsConcatenate();
    if |fragments| == 0 {
    } else {
      FragmentCutsSatisfyRelation(fragments[1..]);
      JoinFragmentsLengthStep(fragments);
      assert |FragmentCuts(fragments)| == |fragments| + 1;
      assert FragmentCuts(fragments)[0] == 0;
      assert FragmentCuts(fragments)[|FragmentCuts(fragments)| - 1] ==
             |JoinFragments(fragments)| by {
        ShiftNatsIndex(
          FragmentCuts(fragments[1..]),
          |fragments[0]|,
          |FragmentCuts(fragments[1..])| - 1
        );
      }
      assert forall i: nat {:trigger FragmentCuts(fragments)[i]} ::
          i < |fragments| ==>
            FragmentCuts(fragments)[i] <=
            FragmentCuts(fragments)[i + 1] &&
            FragmentCuts(fragments)[i + 1] <=
            |JoinFragments(fragments)| &&
            FragmentCuts(fragments)[i + 1] ==
            FragmentCuts(fragments)[i] + |fragments[i]| &&
            JoinFragments(fragments)[
            FragmentCuts(fragments)[i]..
            FragmentCuts(fragments)[i + 1]
            ] == fragments[i] by {
        forall i: nat {:trigger FragmentCuts(fragments)[i]} |
      i < |fragments|
          ensures FragmentCuts(fragments)[i] <=
                  FragmentCuts(fragments)[i + 1] &&
                  FragmentCuts(fragments)[i + 1] <=
                  |JoinFragments(fragments)| &&
                  FragmentCuts(fragments)[i + 1] ==
                  FragmentCuts(fragments)[i] + |fragments[i]| &&
                  JoinFragments(fragments)[
                  FragmentCuts(fragments)[i]..
                  FragmentCuts(fragments)[i + 1]
                  ] == fragments[i]
        {
          if i == 0 {
            assert JoinFragments(fragments)[0..|fragments[0]|] ==
                   fragments[0];
          } else {
            var j := i - 1;
            ShiftNatsIndex(
              FragmentCuts(fragments[1..]), |fragments[0]|, j
            );
            ShiftNatsIndex(
              FragmentCuts(fragments[1..]), |fragments[0]|, j + 1
            );
            assert fragments[i] == fragments[1..][j];
            JoinFragmentsSliceStep(
              fragments,
              FragmentCuts(fragments[1..])[j],
              FragmentCuts(fragments[1..])[j + 1]
            );
          }
        }
      }
    }
  }

  ghost function SelectionScanIndices(
    selection: CutSchema.Selection,
    record: BenchWorld.Bytes,
    position: nat
  ): seq<nat>
    requires position >= 1
    decreases |record|
  {
    if |record| == 0 then
      []
    else
      (if SelectionIncludes(selection, position)
       then [position - 1]
       else []) +
      SelectionScanIndices(selection, record[1..], position + 1)
  }

  ghost function SelectionScanFragments(
    command: CutSchema.CutCmdRaw,
    record: BenchWorld.Bytes,
    position: nat,
    emitted: bool
  ): seq<BenchWorld.Bytes>
    requires position >= 1
    decreases |record|
  {
    if |record| == 0 then
      []
    else if SelectionIncludes(command.selection, position) then
      [(if emitted && GroupBoundaryBefore(command.selection, position)
        then Spec.OutputDelimiterBytes(command.outputDelimiter)
        else []) + [record[0]]] +
      SelectionScanFragments(command, record[1..], position + 1, true)
    else
      SelectionScanFragments(
        command, record[1..], position + 1, emitted
      )
  }

  lemma SelectedMatchesExists(
    ranges: seq<CutSchema.Range>, position: int
  )
    ensures Selected(ranges, position) ==
            (exists i :: 0 <= i < |ranges| &&
                         Spec.RangeContains(ranges[i], position))
    decreases |ranges|
  {
    if |ranges| > 0 {
      SelectedMatchesExists(ranges[1..], position);
      if Selected(ranges[1..], position) {
        var i :| 0 <= i < |ranges[1..]| &&
                 Spec.RangeContains(ranges[1..][i], position);
        assert Spec.RangeContains(ranges[i + 1], position);
      } else if (
          exists i :: 0 <= i < |ranges| &&
                      Spec.RangeContains(ranges[i], position)
        ) {
        var i :| 0 <= i < |ranges| &&
                 Spec.RangeContains(ranges[i], position);
        if i > 0 {
          assert Spec.RangeContains(ranges[1..][i - 1], position);
        }
      }
    }
  }

  lemma SelectionIncludesMatchesPosition(
    selection: CutSchema.Selection, position: int
  )
    requires position >= 1
    ensures SelectionIncludes(selection, position) ==
            Spec.PositionSelected(selection, position)
  {
    SelectedMatchesExists(selection.ranges, position);
    reveal Spec.PositionSelected();
  }

  lemma AdjacentCoveredMatchesExists(
    ranges: seq<CutSchema.Range>, position: int
  )
    ensures AdjacentCoveredByRange(ranges, position) ==
            (exists i :: 0 <= i < |ranges| &&
                         Spec.RangeContains(ranges[i], position - 1) &&
                         Spec.RangeContains(ranges[i], position))
    decreases |ranges|
  {
    if |ranges| > 0 {
      AdjacentCoveredMatchesExists(ranges[1..], position);
      if AdjacentCoveredByRange(ranges[1..], position) {
        var i :| 0 <= i < |ranges[1..]| &&
                 Spec.RangeContains(ranges[1..][i], position - 1) &&
                 Spec.RangeContains(ranges[1..][i], position);
        assert Spec.RangeContains(ranges[i + 1], position - 1);
        assert Spec.RangeContains(ranges[i + 1], position);
      } else if (
          exists i :: 0 <= i < |ranges| &&
                      Spec.RangeContains(ranges[i], position - 1) &&
                      Spec.RangeContains(ranges[i], position)
        ) {
        var i :| 0 <= i < |ranges| &&
                 Spec.RangeContains(ranges[i], position - 1) &&
                 Spec.RangeContains(ranges[i], position);
        if i > 0 {
          assert Spec.RangeContains(ranges[1..][i - 1], position - 1);
          assert Spec.RangeContains(ranges[1..][i - 1], position);
        }
      }
    }
  }

  lemma GroupBoundaryMatchesDelimiter(
    command: CutSchema.CutCmdRaw, position: int
  )
    requires command.outputDelimiter.OutputCustom?
    requires position >= 1
    ensures GroupBoundaryBefore(command.selection, position) ==
            Spec.DelimiterBeforeSelected(command, position)
  {
    reveal Spec.DelimiterBeforeSelected();
    if position > 1 {
      if command.selection.complement {
        SelectionIncludesMatchesPosition(
          command.selection, position - 1
        );
      } else {
        AdjacentCoveredMatchesExists(
          command.selection.ranges, position
        );
      }
    }
  }

  lemma SelectionScanOutput(
    command: CutSchema.CutCmdRaw,
    record: BenchWorld.Bytes,
    position: nat,
    emitted: bool
  )
    requires position >= 1
    ensures
      (if HasCustomOutputDelimiter(command.outputDelimiter)
       then SelectPositionsDelimited(
                 record,
                 command.selection,
                 Spec.OutputDelimiterBytes(command.outputDelimiter),
                 position,
                 emitted
               )
       else SelectPositions(record, command.selection, position)) ==
      JoinFragments(
        SelectionScanFragments(command, record, position, emitted)
      )
    decreases |record|
  {
    if |record| > 0 {
      SelectionScanOutput(
        command,
        record[1..],
        position + 1,
        emitted || SelectionIncludes(command.selection, position)
      );
    }
  }

  lemma SelectionScanIndicesCorrect(
    selection: CutSchema.Selection,
    record: BenchWorld.Bytes,
    position: nat
  )
    requires position >= 1
    ensures Spec.StrictlyIncreasing(
              SelectionScanIndices(selection, record, position)
            )
    ensures forall k: nat ::
              k < |SelectionScanIndices(selection, record, position)| ==>
                position - 1 <=
                SelectionScanIndices(selection, record, position)[k] <
                position - 1 + |record| &&
                Spec.PositionSelected(
                  selection,
                  SelectionScanIndices(selection, record, position)[k] + 1
                )
    ensures forall i: nat ::
              position - 1 <= i < position - 1 + |record| ==>
                Spec.PositionSelected(selection, i + 1) ==
                (i in SelectionScanIndices(selection, record, position))
    decreases |record|
  {
    reveal Spec.StrictlyIncreasing();
    if |record| > 0 {
      SelectionIncludesMatchesPosition(selection, position);
      SelectionScanIndicesCorrect(selection, record[1..], position + 1);
      var tail := SelectionScanIndices(
        selection, record[1..], position + 1
      );
      if SelectionIncludes(selection, position) {
        assert forall k: nat :: k < |tail| ==>
                                  position <= tail[k] by {
          forall k: nat | k < |tail|
            ensures position <= tail[k]
          {
          }
        }
        assert Spec.StrictlyIncreasing([position - 1] + tail);
      }
      assert forall k: nat ::
          k < |SelectionScanIndices(selection, record, position)| ==>
            position - 1 <=
            SelectionScanIndices(selection, record, position)[k] <
            position - 1 + |record| &&
            Spec.PositionSelected(
              selection,
              SelectionScanIndices(selection, record, position)[k] + 1
            ) by {
        forall k: nat |
          k < |SelectionScanIndices(selection, record, position)|
          ensures position - 1 <=
                  SelectionScanIndices(selection, record, position)[k] <
                  position - 1 + |record| &&
                  Spec.PositionSelected(
                    selection,
                    SelectionScanIndices(selection, record, position)[k] + 1
                  )
        {
          if SelectionIncludes(selection, position) && k == 0 {
          } else {
            var tailIndex :=
              if SelectionIncludes(selection, position) then k - 1 else k;
            assert tailIndex < |tail|;
          }
        }
      }
      assert forall i: nat ::
          position - 1 <= i < position - 1 + |record| ==>
            Spec.PositionSelected(selection, i + 1) ==
            (i in SelectionScanIndices(selection, record, position)) by {
        forall i: nat |
          position - 1 <= i < position - 1 + |record|
          ensures Spec.PositionSelected(selection, i + 1) ==
                  (i in SelectionScanIndices(selection, record, position))
        {
          if i == position - 1 {
          } else {
            assert position <= i;
            assert i < position + |record[1..]|;
          }
        }
      }
    }
  }

  lemma SelectionScanSelectedIndexSequence(
    selection: CutSchema.Selection,
    record: BenchWorld.Bytes
  )
    ensures Spec.SelectedIndexSequence(
              selection, |record|, SelectionScanIndices(selection, record, 1)
            )
  {
    SelectionScanIndicesCorrect(selection, record, 1);
    reveal Spec.SelectedIndexSequence();
    assert forall k {:trigger SelectionScanIndices(
          selection, record, 1
        )[k]} ::
        0 <= k < |SelectionScanIndices(selection, record, 1)| ==>
          SelectionScanIndices(selection, record, 1)[k] < |record| &&
          Spec.PositionSelected(
            selection,
            SelectionScanIndices(selection, record, 1)[k] + 1
          );
    assert forall i {:trigger Spec.PositionSelected(selection, i + 1)} ::
        0 <= i < |record| ==>
          Spec.PositionSelected(selection, i + 1) ==
          (exists k :: 0 <= k <
                       |SelectionScanIndices(selection, record, 1)| &&
                       SelectionScanIndices(selection, record, 1)[k] == i) by {
      forall i {:trigger Spec.PositionSelected(selection, i + 1)} |
    0 <= i < |record|
        ensures Spec.PositionSelected(selection, i + 1) ==
                (exists k :: 0 <= k <
                             |SelectionScanIndices(selection, record, 1)| &&
                             SelectionScanIndices(selection, record, 1)[k] == i)
      {
        if Spec.PositionSelected(selection, i + 1) {
          assert i in SelectionScanIndices(selection, record, 1);
          var k :| 0 <= k <
                   |SelectionScanIndices(selection, record, 1)| &&
                   SelectionScanIndices(selection, record, 1)[k] == i;
          assert exists k :: 0 <= k <
                             |SelectionScanIndices(selection, record, 1)| &&
                             SelectionScanIndices(selection, record, 1)[k] == i;
        } else if (
            exists k :: 0 <= k <
                        |SelectionScanIndices(selection, record, 1)| &&
                        SelectionScanIndices(selection, record, 1)[k] == i
          ) {
          var k :| 0 <= k <
                   |SelectionScanIndices(selection, record, 1)| &&
                   SelectionScanIndices(selection, record, 1)[k] == i;
          assert i in SelectionScanIndices(selection, record, 1);
        }
      }
    }
  }

  lemma {:isolate_assertions} SelectionScanFragmentAt(
    command: CutSchema.CutCmdRaw,
    record: BenchWorld.Bytes,
    position: nat,
    emitted: bool,
    k: nat
  )
    requires position >= 1
    requires k < |SelectionScanIndices(
                   command.selection, record, position
                 )|
    requires k < |SelectionScanFragments(
                   command, record, position, emitted
                 )|
    requires position - 1 <= SelectionScanIndices(
               command.selection, record, position
             )[k] < position - 1 + |record|
    ensures SelectionScanFragments(command, record, position, emitted)[k] ==
            (if (emitted || k > 0) &&
                Spec.DelimiterBeforeSelected(
                  command,
                  SelectionScanIndices(
                    command.selection, record, position
                  )[k] + 1
                )
             then Spec.OutputDelimiterBytes(command.outputDelimiter)
             else []) +
            [record[
             SelectionScanIndices(
               command.selection, record, position
             )[k] - (position - 1)
             ]]
    decreases |record|
  {
    SelectionScanIndicesCorrect(command.selection, record, position);
    assert |record| > 0;
    SelectionIncludesMatchesPosition(command.selection, position);
    if SelectionIncludes(command.selection, position) && k == 0 {
      if command.outputDelimiter.OutputCustom? {
        GroupBoundaryMatchesDelimiter(command, position);
      } else {
        reveal Spec.DelimiterBeforeSelected();
      }
    } else {
      var tailIndex :=
        if SelectionIncludes(command.selection, position) then k - 1 else k;
      SelectionScanIndicesCorrect(
        command.selection, record[1..], position + 1
      );
      assert tailIndex < |SelectionScanIndices(
                           command.selection, record[1..], position + 1
                         )|;
      assert tailIndex < |SelectionScanFragments(
                           command,
                           record[1..],
                           position + 1,
                           emitted || SelectionIncludes(command.selection, position)
                         )|;
      assert position <= SelectionScanIndices(
               command.selection, record[1..], position + 1
             )[tailIndex] < position + |record[1..]|;
      SelectionScanFragmentAt(
        command,
        record[1..],
        position + 1,
        emitted || SelectionIncludes(command.selection, position),
        tailIndex
      );
    }
  }

  lemma SelectionScanFragmentsCorrespond(
    command: CutSchema.CutCmdRaw,
    record: BenchWorld.Bytes,
    position: nat,
    emitted: bool
  )
    requires position >= 1
    ensures |SelectionScanFragments(
              command, record, position, emitted
            )| == |SelectionScanIndices(command.selection, record, position)|
    decreases |record|
  {
    if |record| > 0 {
      SelectionScanFragmentsCorrespond(
        command,
        record[1..],
        position + 1,
        emitted || SelectionIncludes(command.selection, position)
      );
    }
  }

  lemma SelectionFragmentMatches(
    command: CutSchema.CutCmdRaw, record: BenchWorld.Bytes, k: nat
  )
    requires k < |SelectionScanIndices(command.selection, record, 1)|
    requires k < |SelectionScanFragments(command, record, 1, false)|
    requires SelectionScanIndices(command.selection, record, 1)[k] < |record|
    ensures SelectionScanFragments(command, record, 1, false)[k] ==
            (if k > 0 && Spec.DelimiterBeforeSelected(command,
                                                      SelectionScanIndices(command.selection, record, 1)[k] + 1)
             then Spec.OutputDelimiterBytes(command.outputDelimiter) else []) +
            [record[SelectionScanIndices(command.selection, record, 1)[k]]]
  {
    SelectionScanSelectedIndexSequence(command.selection, record);
    SelectionScanFragmentsCorrespond(command, record, 1, false);
    reveal Spec.SelectedIndexSequence();
    assert SelectionScanIndices(command.selection, record, 1)[k] < |record|;
    SelectionScanFragmentAt(command, record, 1, false, k);
  }

  lemma SelectRecordSatisfiesRelation(
    command: CutSchema.CutCmdRaw,
    record: BenchWorld.Bytes
  )
    ensures Spec.RecordSelectionRelation(
              command,
              record,
              SelectRecord(
                record, command.selection, command.outputDelimiter
              )
            )
  {
    var indices := SelectionScanIndices(command.selection, record, 1);
    var fragments := SelectionScanFragments(command, record, 1, false);
    var output := SelectRecord(
      record, command.selection, command.outputDelimiter
    );
    var cuts := FragmentCuts(fragments);
    SelectionScanSelectedIndexSequence(command.selection, record);
    SelectionScanFragmentsCorrespond(command, record, 1, false);
    SelectionScanOutput(command, record, 1, false);
    FragmentCutsSatisfyRelation(fragments);
    reveal Spec.RecordSelectionRelation();
    assert Spec.RecordSelectionWitnessRelation(
        command, record, output, indices, cuts
      ) by {
      reveal Spec.RecordSelectionWitnessRelation();
      assert output == JoinFragments(fragments);
      assert |fragments| == |indices|;
      assert forall k: nat :: k < |indices| ==>
                                fragments[k] ==
                                (if k > 0 && Spec.DelimiterBeforeSelected(
                                      command, indices[k] + 1
                                    )
                                 then Spec.OutputDelimiterBytes(command.outputDelimiter)
                                 else []) +
                                [record[indices[k]]] by {
        forall k: nat | k < |indices|
          ensures fragments[k] ==
                  (if k > 0 && Spec.DelimiterBeforeSelected(
                        command, indices[k] + 1
                      )
                   then Spec.OutputDelimiterBytes(command.outputDelimiter)
                   else []) +
                  [record[indices[k]]]
        {
          assert indices[k] < |record|;
          SelectionFragmentMatches(command, record, k);
        }
      }
      assert exists witnessFragments: seq<BenchWorld.Bytes> ::
          |witnessFragments| == |indices| &&
          (forall k :: 0 <= k < |indices| ==>
                         witnessFragments[k] ==
                         (if k > 0 && Spec.DelimiterBeforeSelected(
                               command, indices[k] + 1
                             )
                          then Spec.OutputDelimiterBytes(command.outputDelimiter)
                          else []) +
                         [record[indices[k]]]) &&
          Spec.FragmentsConcatenate(
            witnessFragments, output, cuts
          ) by {
        assert |fragments| == |indices|;
        assert forall k :: 0 <= k < |indices| ==>
                             fragments[k] ==
                             (if k > 0 && Spec.DelimiterBeforeSelected(
                                   command, indices[k] + 1
                                 )
                              then Spec.OutputDelimiterBytes(command.outputDelimiter)
                              else []) +
                             [record[indices[k]]];
        assert Spec.FragmentsConcatenate(fragments, output, cuts);
      }
    }
  }

  ghost function PartitionRecords(
    data: BenchWorld.Bytes, delimiter: BenchWorld.RawByte
  ): seq<BenchWorld.Bytes>
    decreases |data|
  {
    if |data| == 0 then
      []
    else
      var n := RecordLength(data, delimiter);
      var rest := if n < |data| then data[n + 1..] else [];
      [data[..n]] + PartitionRecords(rest, delimiter)
  }

  ghost function PartitionTerminated(
    data: BenchWorld.Bytes, delimiter: BenchWorld.RawByte
  ): seq<bool>
    decreases |data|
  {
    if |data| == 0 then
      []
    else
      var n := RecordLength(data, delimiter);
      var rest := if n < |data| then data[n + 1..] else [];
      [n < |data|] + PartitionTerminated(rest, delimiter)
  }

  ghost function PartitionInputFragments(
    data: BenchWorld.Bytes, delimiter: BenchWorld.RawByte
  ): seq<BenchWorld.Bytes>
    decreases |data|
  {
    if |data| == 0 then
      []
    else
      var n := RecordLength(data, delimiter);
      var rest := if n < |data| then data[n + 1..] else [];
      [data[..n] + (if n < |data| then [delimiter] else [])] +
      PartitionInputFragments(rest, delimiter)
  }

  ghost function PartitionFragments(
    command: CutSchema.CutCmdRaw,
    data: BenchWorld.Bytes
  ): seq<BenchWorld.Bytes>
    decreases |data|
  {
    if |data| == 0 then
      []
    else
      var delimiter := Spec.RecordDelimiter(command.zeroTerminated);
      var n := RecordLength(data, delimiter);
      var rest := if n < |data| then data[n + 1..] else [];
      [SelectRecord(
         data[..n], command.selection, command.outputDelimiter
       )] + PartitionFragments(command, rest)
  }

  ghost function PartitionRenderedFragments(
    command: CutSchema.CutCmdRaw,
    data: BenchWorld.Bytes
  ): seq<BenchWorld.Bytes>
    decreases |data|
  {
    if |data| == 0 then
      []
    else
      var delimiter := Spec.RecordDelimiter(command.zeroTerminated);
      var n := RecordLength(data, delimiter);
      var rest := if n < |data| then data[n + 1..] else [];
      [SelectRecord(
         data[..n], command.selection, command.outputDelimiter
       ) + [delimiter]] +
      PartitionRenderedFragments(command, rest)
  }

  lemma RecordLengthProperties(
    data: BenchWorld.Bytes, delimiter: BenchWorld.RawByte
  )
    ensures RecordLength(data, delimiter) <= |data|
    ensures forall i: nat :: i < RecordLength(data, delimiter) ==>
                               data[i] != delimiter
    ensures RecordLength(data, delimiter) < |data| ==>
              data[RecordLength(data, delimiter)] == delimiter
    decreases |data|
  {
    if |data| > 0 && data[0] != delimiter {
      RecordLengthProperties(data[1..], delimiter);
      assert forall i: nat :: i < RecordLength(data, delimiter) ==>
                                data[i] != delimiter by {
        forall i: nat | i < RecordLength(data, delimiter)
          ensures data[i] != delimiter
        {
          if i > 0 {
            assert data[i] == data[1..][i - 1];
          }
        }
      }
      if RecordLength(data, delimiter) < |data| {
        assert data[RecordLength(data, delimiter)] ==
               data[1..][RecordLength(data[1..], delimiter)];
      }
    }
  }

  lemma {:isolate_assertions} PartitionInputFacts(
    data: BenchWorld.Bytes, delimiter: BenchWorld.RawByte
  )
    ensures |PartitionRecords(data, delimiter)| ==
            |PartitionTerminated(data, delimiter)| ==
            |PartitionInputFragments(data, delimiter)|
    ensures (|data| == 0) ==
            (|PartitionRecords(data, delimiter)| == 0)
    ensures forall i: nat ::
              i < |PartitionRecords(data, delimiter)| ==>
                |PartitionInputFragments(data, delimiter)[i]| > 0 &&
                PartitionInputFragments(data, delimiter)[i] ==
                PartitionRecords(data, delimiter)[i] +
                (if PartitionTerminated(data, delimiter)[i]
                 then [delimiter]
                 else []) &&
                (forall j: nat ::
                   j < |PartitionRecords(data, delimiter)[i]| ==>
                     PartitionRecords(data, delimiter)[i][j] != delimiter) &&
                (i + 1 < |PartitionRecords(data, delimiter)| ==>
                   PartitionTerminated(data, delimiter)[i])
    ensures JoinFragments(
              PartitionInputFragments(data, delimiter)
            ) == data
    decreases |data|
  {
    if |data| > 0 {
      var n := RecordLength(data, delimiter);
      var rest := if n < |data| then data[n + 1..] else [];
      RecordLengthProperties(data, delimiter);
      PartitionInputFacts(rest, delimiter);
      var records := PartitionRecords(data, delimiter);
      var terminated := PartitionTerminated(data, delimiter);
      var fragments := PartitionInputFragments(data, delimiter);
      if n < |data| {
        assert data[n] == delimiter;
        assert fragments[0] == data[..n + 1];
        assert data == data[..n + 1] + rest;
      } else {
        assert n == |data|;
        assert rest == [];
        assert fragments[0] == data;
      }
      assert JoinFragments(fragments) ==
             fragments[0] +
             JoinFragments(PartitionInputFragments(rest, delimiter));
      assert JoinFragments(fragments) == data;
      assert forall i: nat :: i < |records| ==>
                                |fragments[i]| > 0 &&
                                fragments[i] ==
                                records[i] + (if terminated[i] then [delimiter] else []) &&
                                (forall j: nat :: j < |records[i]| ==>
                                                    records[i][j] != delimiter) &&
                                (i + 1 < |records| ==> terminated[i]) by {
        forall i: nat | i < |records|
          ensures |fragments[i]| > 0 &&
                  fragments[i] ==
                  records[i] +
                  (if terminated[i] then [delimiter] else []) &&
                  (forall j: nat :: j < |records[i]| ==>
                                      records[i][j] != delimiter) &&
                  (i + 1 < |records| ==> terminated[i])
        {
          if i == 0 {
            assert forall j: nat :: j < |records[0]| ==>
                                      records[0][j] != delimiter;
            if |PartitionRecords(rest, delimiter)| > 0 {
              assert |rest| > 0;
              assert n < |data|;
            }
          } else {
            var tailIndex := i - 1;
            assert records[i] ==
                   PartitionRecords(rest, delimiter)[tailIndex];
            assert terminated[i] ==
                   PartitionTerminated(rest, delimiter)[tailIndex];
            assert fragments[i] ==
                   PartitionInputFragments(rest, delimiter)[tailIndex];
          }
        }
      }
    }
  }

  lemma PartitionSatisfiesRelation(
    data: BenchWorld.Bytes, delimiter: BenchWorld.RawByte
  )
    ensures Spec.RecordPartitionRelation(
              data,
              delimiter,
              PartitionRecords(data, delimiter),
              PartitionTerminated(data, delimiter)
            )
  {
    var records := PartitionRecords(data, delimiter);
    var terminated := PartitionTerminated(data, delimiter);
    var fragments := PartitionInputFragments(data, delimiter);
    var cuts := FragmentCuts(fragments);
    PartitionInputFacts(data, delimiter);
    FragmentCutsSatisfyRelation(fragments);
    reveal Spec.RecordPartitionRelation();
    assert Spec.RecordPartitionWitnessRelation(
        data, delimiter, records, terminated, fragments, cuts
      ) by {
      reveal Spec.RecordPartitionWitnessRelation();
    }
  }

  lemma {:isolate_assertions} PartitionSelectionFacts(
    command: CutSchema.CutCmdRaw,
    data: BenchWorld.Bytes
  )
    ensures |PartitionFragments(command, data)| ==
            |PartitionRecords(
              data, Spec.RecordDelimiter(command.zeroTerminated)
            )|
    ensures |PartitionRenderedFragments(command, data)| ==
            |PartitionFragments(command, data)|
    ensures forall i: nat ::
              i < |PartitionRecords(
                data, Spec.RecordDelimiter(command.zeroTerminated)
              )| ==>
                Spec.RecordSelectionRelation(
                  command,
                  PartitionRecords(
                    data, Spec.RecordDelimiter(command.zeroTerminated)
                  )[i],
                  PartitionFragments(command, data)[i]
                ) &&
                PartitionRenderedFragments(command, data)[i] ==
                PartitionFragments(command, data)[i] +
                [Spec.RecordDelimiter(command.zeroTerminated)]
    ensures JoinFragments(
              PartitionRenderedFragments(command, data)
            ) == CutData(
                   command.selection,
                   command.outputDelimiter,
                   command.zeroTerminated,
                   data
                 )
    decreases |data|
  {
    if |data| > 0 {
      var delimiter := Spec.RecordDelimiter(command.zeroTerminated);
      var n := RecordLength(data, delimiter);
      var line := data[..n];
      var rest := if n < |data| then data[n + 1..] else [];
      SelectRecordSatisfiesRelation(command, line);
      PartitionSelectionFacts(command, rest);
      var records := PartitionRecords(data, delimiter);
      var fragments := PartitionFragments(command, data);
      var rendered := PartitionRenderedFragments(command, data);
      assert records[1..] == PartitionRecords(rest, delimiter);
      assert fragments[1..] == PartitionFragments(command, rest);
      assert rendered[1..] == PartitionRenderedFragments(command, rest);
      assert JoinFragments(rendered) ==
             rendered[0] +
             JoinFragments(PartitionRenderedFragments(command, rest));
      assert forall i: nat :: i < |records| ==>
                                Spec.RecordSelectionRelation(
                                  command, records[i], fragments[i]
                                ) &&
                                rendered[i] ==
                                fragments[i] + [Spec.RecordDelimiter(
                                                  command.zeroTerminated
                                                )] by {
        forall i: nat | i < |records|
          ensures Spec.RecordSelectionRelation(
                    command, records[i], fragments[i]
                  ) &&
                  rendered[i] ==
                  fragments[i] + [Spec.RecordDelimiter(
                                    command.zeroTerminated
                                  )]
        {
          if i > 0 {
            var tailIndex := i - 1;
            assert records[i] ==
                   PartitionRecords(rest, delimiter)[tailIndex];
            assert fragments[i] ==
                   PartitionFragments(command, rest)[tailIndex];
            assert rendered[i] ==
                   PartitionRenderedFragments(command, rest)[tailIndex];
          }
        }
      }
    }
  }

  lemma DataSelectionSatisfiesRelation(
    command: CutSchema.CutCmdRaw,
    data: BenchWorld.Bytes
  )
    ensures Spec.DataSelectionRelation(
              command,
              data,
              CutData(
                command.selection,
                command.outputDelimiter,
                command.zeroTerminated,
                data
              )
            )
  {
    var delimiter := Spec.RecordDelimiter(command.zeroTerminated);
    var records := PartitionRecords(data, delimiter);
    var terminated := PartitionTerminated(data, delimiter);
    var fragments := PartitionFragments(command, data);
    var rendered := PartitionRenderedFragments(command, data);
    var output := CutData(
      command.selection,
      command.outputDelimiter,
      command.zeroTerminated,
      data
    );
    var cuts := FragmentCuts(rendered);
    PartitionSatisfiesRelation(data, delimiter);
    PartitionSelectionFacts(command, data);
    FragmentCutsSatisfyRelation(rendered);
    reveal Spec.DataSelectionRelation();
    assert Spec.DataSelectionWitnessRelation(
        command,
        data,
        output,
        records,
        terminated,
        fragments,
        rendered,
        cuts
      ) by {
      reveal Spec.DataSelectionWitnessRelation();
      assert delimiter == Spec.RecordDelimiter(
                            command.zeroTerminated
                          );
    }
  }

  ghost function PrefixStdinCore(command: CutSchema.CutCmdRaw, before: BenchWorld.Bytes,
                                 count: nat, observations: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult): BenchWorld.Bytes
    requires count <= |command.inputs|
    decreases count
  {
    if count == 0 then before else
    var previous := PrefixStdinCore(command, before, count - 1, observations);
    if command.inputs[count - 1].Stdin? then IOContract.ObservedReadStdinRemainingFields(previous, observations)
    else previous
  }

  lemma PrefixStdinStep(command: CutSchema.CutCmdRaw, before: BenchWorld.Bytes,
                        count: nat, observations: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult)
    requires count < |command.inputs|
    ensures PrefixStdinCore(command, before, count + 1, observations) ==
            (if command.inputs[count].Stdin? then IOContract.ObservedReadStdinRemainingFields(
                                                    PrefixStdinCore(command, before, count, observations), observations)
             else PrefixStdinCore(command, before, count, observations))
  {
  }

  ghost predicate InputReadCore(
    command: CutSchema.CutCmdRaw,
    preFs: BenchWorld.FileSystem,
    preStdin: BenchWorld.Bytes,
    index: nat,
    result: BenchWorld.IOResult<BenchWorld.Bytes>,
                                preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult
  )
    requires index < |command.inputs|
  {
    match command.inputs[index]
    case Stdin =>
      result == IOContract.ObservedReadStdinResultFields(PrefixStdinCore(command, preStdin, index, preStreams), preStreams)
    case File(path) =>
      result == IOContract.ObservedReadFileResultFields(preFs, preStreams, path)
  }

  ghost predicate InputTraceCore(
    command: CutSchema.CutCmdRaw,
    preFs: BenchWorld.FileSystem,
    preStdin: BenchWorld.Bytes,
    count: nat,
    readResults: seq<BenchWorld.IOResult<BenchWorld.Bytes>>,
    stdoutFragments: seq<BenchWorld.Bytes>,
    stderrFragments: seq<BenchWorld.Bytes>,
    preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult
  )
    requires count <= |command.inputs|
  {
    |readResults| == count &&
    |stdoutFragments| == count &&
    |stderrFragments| == count &&
    forall i: nat :: i < count ==>
                       InputReadCore(command, preFs, preStdin, i, readResults[i], preStreams) &&
                       stdoutFragments[i] == OutputPiece(command, readResults[i]) &&
                       stderrFragments[i] == ErrorPiece(command.inputs[i], readResults[i])
  }

  twostate predicate PreparedSummary(
    raw: CutSchema.CutCmdRaw,
    io: BenchIO.IO,
    exit: int
  , plannedStdout: BenchWorld.Bytes, plannedStderr: BenchWorld.Bytes)
    reads io.stdinRegion
  {
    if raw.mode == CutSchema.ModeHelp then
      io.stdin() == old(io.stdin()) &&
      plannedStdout == Spec.HelpText() &&
      plannedStderr == [] &&
      exit == 0
    else if raw.mode == CutSchema.ModeVersion then
      io.stdin() == old(io.stdin()) &&
      plannedStdout == Spec.VersionText() &&
      plannedStderr == [] &&
      exit == 0
    else
      exists readResults: seq<BenchWorld.IOResult<BenchWorld.Bytes>>,
        stdoutFragments: seq<BenchWorld.Bytes>,
        stderrFragments: seq<BenchWorld.Bytes> ::
        InputTraceCore(
          raw, old(io.fs()), old(io.stdin()), |raw.inputs|,
          readResults, stdoutFragments, stderrFragments,
          old(io.trustedStreams())
        ) &&
        io.stdin() ==
        PrefixStdinCore(raw, old(io.stdin()), |raw.inputs|, old(io.trustedStreams())) &&
        plannedStdout == JoinFragments(stdoutFragments) &&
        plannedStderr == JoinFragments(stderrFragments) &&
        exit ==
        (if (exists i: nat | i < |raw.inputs| :: readResults[i].Err?)
         then 1
         else 0)
  }

  method {:isolate_assertions} Prepare(
    raw: CutSchema.CutCmdRaw, io: BenchIO.IO
  ) returns (exit: int, plannedOut: BenchWorld.Bytes, plannedErr: BenchWorld.Bytes)
    modifies io.stdinRegion
    ensures PreparedSummary(raw, io, exit, plannedOut, plannedErr)
    decreases *
  {
    plannedOut := [];
    plannedErr := [];

    ghost var preFs := io.fs();
    ghost var preStdin := io.stdin();

    if raw.mode == CutSchema.ModeHelp {
      var help := Spec.HelpText();
      plannedOut := plannedOut + help;
      exit := 0;
      assert io.stdin() == preStdin;
      assert plannedErr == [];
      assert PreparedSummary(raw, io, exit, plannedOut, plannedErr) by {
        reveal PreparedSummary();
      }
      return;
    }

    if raw.mode == CutSchema.ModeVersion {
      var version := Spec.VersionText();
      plannedOut := plannedOut + version;
      exit := 0;
      assert io.stdin() == preStdin;
      assert plannedErr == [];
      assert PreparedSummary(raw, io, exit, plannedOut, plannedErr) by {
        reveal PreparedSummary();
      }
      return;
    }

    assert raw.mode == CutSchema.ModeRun;
    var out: BenchWorld.Bytes := [];
    var err: BenchWorld.Bytes := [];
    var hadError := false;
    ghost var readResults:
      seq<BenchWorld.IOResult<BenchWorld.Bytes>> := [];
    ghost var stdoutFragments: seq<BenchWorld.Bytes> := [];
    ghost var stderrFragments: seq<BenchWorld.Bytes> := [];

    var i := 0;
    while i < |raw.inputs|
      invariant 0 <= i <= |raw.inputs|
      invariant plannedOut == []
      invariant plannedErr == []
      invariant |readResults| == i
      invariant |stdoutFragments| == i
      invariant |stderrFragments| == i
      invariant out == JoinFragments(stdoutFragments)
      invariant err == JoinFragments(stderrFragments)
      invariant io.stdin() ==
                PrefixStdinCore(raw, preStdin, i, old(io.trustedStreams()))
      invariant InputTraceCore(
                  raw, preFs, preStdin, i,
                  readResults, stdoutFragments, stderrFragments,
                  old(io.trustedStreams())
                )
      invariant hadError ==
                (exists j: nat :: j < i &&
                                  readResults[j].Err?)
      decreases |raw.inputs| - i
    {
      var input := raw.inputs[i];
      var readResult: BenchWorld.IOResult<BenchWorld.Bytes>;

      match input {
        case Stdin =>
          ghost var beforeStdin := io.stdin();
          readResult := io.ReadStdin();
          reveal InputReadCore();
        case File(path) =>
          readResult := io.ReadFile(path);
          assert readResult == IOContract.ObservedReadFileResultFields(preFs, old(io.trustedStreams()), path);
          reveal InputReadCore();
      }

      var outPiece := OutputPiece(raw, readResult);
      var errPiece := ErrorPiece(input, readResult);
      var hadPiece := HadErrorPiece(input, readResult);
      JoinFragmentsSnoc(stdoutFragments, outPiece);
      JoinFragmentsSnoc(stderrFragments, errPiece);
      out := out + outPiece;
      err := err + errPiece;
      hadError := hadError || hadPiece;
      readResults := readResults + [readResult];
      stdoutFragments := stdoutFragments + [outPiece];
      stderrFragments := stderrFragments + [errPiece];
      assert InputReadCore(
          raw, preFs, preStdin, i, readResults[i],
          old(io.trustedStreams())
        );
      assert InputTraceCore(
          raw, preFs, preStdin, i + 1,
          readResults, stdoutFragments, stderrFragments,
          old(io.trustedStreams())
        ) by {
        hide *;
        reveal InputTraceCore();
        assert forall j: nat :: j < i + 1 ==>
                                  InputReadCore(raw, preFs, preStdin, j, readResults[j], old(io.trustedStreams())) &&
                                  stdoutFragments[j] == OutputPiece(raw, readResults[j]) &&
                                  stderrFragments[j] ==
                                  ErrorPiece(raw.inputs[j], readResults[j]) by {
          forall j: nat | j < i + 1
            ensures
              InputReadCore(raw, preFs, preStdin, j, readResults[j], old(io.trustedStreams())) &&
              stdoutFragments[j] == OutputPiece(raw, readResults[j]) &&
              stderrFragments[j] ==
              ErrorPiece(raw.inputs[j], readResults[j])
          {
            if j == i {
              assert readResults[j] == readResult;
              assert stdoutFragments[j] == outPiece;
              assert stderrFragments[j] == errPiece;
            } else {
              assert j < i;
            }
          }
        }
      }
      PrefixStdinStep(raw, preStdin, i, old(io.trustedStreams()));
      assert io.stdin() == PrefixStdinCore(raw, preStdin, i + 1, old(io.trustedStreams()));
      i := i + 1;
    }

    plannedOut := out;
    assert plannedOut == out by { hide *; }
    plannedErr := err;
    assert plannedErr == err by { hide *; }
    exit := if hadError then 1 else 0;
    assert PreparedSummary(raw, io, exit, plannedOut, plannedErr) by {
      hide *;
      reveal PreparedSummary();
      assert preFs == old(io.fs());
      assert preStdin == old(io.stdin());
      assert exists witnessReads: seq<BenchWorld.IOResult<BenchWorld.Bytes>>,
          outFragments: seq<BenchWorld.Bytes>,
          errFragments: seq<BenchWorld.Bytes> ::
          |witnessReads| == |raw.inputs| &&
          InputTraceCore(
            raw, old(io.fs()), old(io.stdin()), |raw.inputs|,
            witnessReads, outFragments, errFragments,
            old(io.trustedStreams())
          ) &&
          io.stdin() ==
          PrefixStdinCore(raw, old(io.stdin()), |raw.inputs|, old(io.trustedStreams())) &&
          plannedOut == JoinFragments(outFragments) &&
          plannedErr == JoinFragments(errFragments) &&
          exit ==
          (if (exists j: nat | j < |raw.inputs| :: witnessReads[j].Err?)
           then 1
           else 0);
    }
  }

  twostate predicate CoreSummary(raw: CutSchema.CutCmdRaw, io: BenchIO.IO, exit: int)
    reads io.stdinRegion, io.stdoutRegion, io.stderrRegion
  {
    exists out: BenchWorld.Bytes, diagnostics: BenchWorld.Bytes, normalExit: int ::
      PreparedSummary(raw, io, normalExit,
                      out, diagnostics) &&
      Spec.Emission(raw, io, out, diagnostics, normalExit, exit)
  }

  method Flush(io: BenchIO.IO, out: BenchWorld.Bytes,
               diagnostics: BenchWorld.Bytes, normalExit: int) returns (exit: int)
    modifies io.stdoutRegion, io.stderrRegion
    ensures Spec.EmitFields(old(io.trustedStreams()), old(io.stdout()), old(io.stderr()),
                            io.stdout(), io.stderr(), out, diagnostics, normalExit, exit)
  {
    var outErr := 0;
    if out != [] {
      var written := io.WriteStdout(out);
      outErr := StreamContract.ResultErrno(written);
    }
    var errors := diagnostics;
    if outErr != 0 {
      var message := io.GetCLocaleErrnoText(outErr);
      errors := errors + Spec.StreamWriteErrorMessage(message);
    }
    assert errors == diagnostics + (if outErr == 0 then [] else
                                    Spec.StreamWriteErrorMessage(StreamContract.CLocaleErrnoTextResult(outErr)));
    var errErr := 0;
    if errors != [] {
      var diagnosed := io.WriteStderr(errors);
      errErr := StreamContract.ResultErrno(diagnosed);
      assert StreamContract.WriteStderrSpec(old(io.stderr()), io.trustedStreams(), io.stderr(),
                                            errors, StreamContract.WriteResultCommitted(diagnosed), errErr);
    }
    exit := if outErr != 0 || errErr != 0 then 1 else normalExit;
  }

  method RunCore(raw: CutSchema.CutCmdRaw, io: BenchIO.IO) returns (exit: int)
    modifies io.stdinRegion, io.stdoutRegion, io.stderrRegion
    ensures CoreSummary(raw, io, exit)
    decreases *
  {
    var normalExit, out, diagnostics := Prepare(raw, io);

    assert PreparedSummary(raw, io, normalExit, out, diagnostics);
    if Spec.Emits(raw) {
      exit := Flush(io, out, diagnostics, normalExit);
    } else {
      exit := normalExit;
    }
    assert PreparedSummary(raw, io, normalExit, out, diagnostics);
    assert Spec.Emission(raw, io, out, diagnostics, normalExit, exit);
  }
}
