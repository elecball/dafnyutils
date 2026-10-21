include "CommSpec.dfy"
include "../../core/World.dfy"
include "../../core/IO.dfy"
include "../../core/IOContract.dfy"
include "CommSchema.dfy"
include "CommRenderCore.dfy"

module CommCore {
  import StreamContract = IOContract

  import BenchIO
  import BenchWorld
  import IOContract
  import Schema = CommSchema
  import Render = CommRenderCore
  import RSpec = CommRenderSpec
  import Spec = CommSpec

  function OutputForReads(cmd: Schema.CommCmd,
                          first: BenchWorld.IOResult<BenchWorld.Bytes>, second: BenchWorld.IOResult<BenchWorld.Bytes>): BenchWorld.Bytes
  {
    if first.Err? || second.Err? then FailedReadsPlan(cmd, first, second).output
    else if Render.DataSorted(first.v, cmd.zeroTerminated) && Render.DataSorted(second.v, cmd.zeroTerminated)
    then Render.RenderData(cmd, first.v, second.v) else []
  }


  function ErrorForReads(cmd: Schema.CommCmd,
                         first: BenchWorld.IOResult<BenchWorld.Bytes>, second: BenchWorld.IOResult<BenchWorld.Bytes>): BenchWorld.Bytes
  {
    if first.Err? || second.Err? then
      Spec.FailedReadMessage(cmd, first, second, FailedReadsPlan(cmd, first, second).leftFault)
    else if Render.DataSorted(first.v, cmd.zeroTerminated) && Render.DataSorted(second.v, cmd.zeroTerminated)
    then [] else Spec.UnsortedInputMessageSpec()
  }


  function HadRunError(
    cmd: Schema.CommCmd,
    first: BenchWorld.IOResult<BenchWorld.Bytes>,
                               second: BenchWorld.IOResult<BenchWorld.Bytes>
  ): bool
  {
    match first
    case Err(_) => true
    case Ok(leftData) =>
      match second
      case Err(_) => true
      case Ok(rightData) =>
        !Render.DataSorted(leftData, cmd.zeroTerminated) ||
        !Render.DataSorted(rightData, cmd.zeroTerminated)
  } by method {
    var hadError: bool;
    match first {
      case Err(_) =>
        hadError := true;
      case Ok(leftData) =>
        match second {
          case Err(_) =>
            hadError := true;
          case Ok(rightData) =>
            var leftSorted := Render.DataSorted(leftData, cmd.zeroTerminated);
            var rightSorted := Render.DataSorted(rightData, cmd.zeroTerminated);
            hadError := !leftSorted || !rightSorted;
        }
    }
    return hadError;
  }

  twostate predicate PreparedSummary(raw: Schema.CommCmdRaw, io: BenchIO.IO, exit: int, plannedStdout: BenchWorld.Bytes, plannedStderr: BenchWorld.Bytes)
    reads io.stdinRegion
  {
    var cmd := Spec.CommandRelation(raw);
    match cmd.mode
    case ModeHelp =>
      io.stdin() == old(io.stdin()) &&
      plannedStdout == old(io.stdout()) + Spec.HelpTextSpec() &&
      plannedStderr == old(io.stderr()) &&
      exit == 0
    case ModeVersion =>
      io.stdin() == old(io.stdin()) &&
      plannedStdout == old(io.stdout()) + Spec.VersionTextSpec() &&
      plannedStderr == old(io.stderr()) &&
      exit == 0
    case ModeMissingOperand =>
      io.stdin() == old(io.stdin()) &&
      plannedStdout == old(io.stdout()) &&
      plannedStderr == old(io.stderr()) + Spec.MissingOperandMessageSpec() &&
      exit == 1
    case ModeMissingOperandAfter(operand) =>
      io.stdin() == old(io.stdin()) &&
      plannedStdout == old(io.stdout()) &&
      plannedStderr == old(io.stderr()) + Spec.MissingOperandAfterMessageSpec(operand) &&
      exit == 1
    case ModeExtraOperand(operand) =>
      io.stdin() == old(io.stdin()) &&
      plannedStdout == old(io.stdout()) &&
      plannedStderr == old(io.stderr()) + Spec.ExtraOperandMessageSpec(operand) &&
      exit == 1
    case ModeMultipleOutputDelimiters =>
      io.stdin() == old(io.stdin()) &&
      plannedStdout == old(io.stdout()) &&
      plannedStderr == old(io.stderr()) + Spec.MultipleOutputDelimitersMessageSpec() &&
      exit == 1
    case ModeRepeatedStdinOperand =>
      io.stdin() == old(io.stdin()) &&
      plannedStdout == old(io.stdout()) &&
      plannedStderr == old(io.stderr()) + Spec.RepeatedStdinOperandMessageSpec() &&
      exit == 1
    case ModeRun =>
      var first := Spec.ReadFirstResult(cmd, old(io.fs()), old(io.trustedStreams()), old(io.stdin()));
      if Spec.FirstReadAborts(cmd, first) then
        io.stdin() == Spec.AfterFirstRead(cmd, old(io.stdin()), old(io.trustedStreams())) &&
        plannedStdout == old(io.stdout()) &&
        plannedStderr == old(io.stderr()) + Spec.InputErrorMessageSpec(cmd.input1, first.e) && exit == 1
      else
        var second := Spec.ReadSecondResult(cmd, old(io.fs()), old(io.trustedStreams()), old(io.stdin()));
        io.stdin() == Spec.AfterSecondRead(cmd, old(io.stdin()), old(io.trustedStreams())) &&
        plannedStdout == old(io.stdout()) + OutputForReads(cmd, first, second) &&
        plannedStderr == old(io.stderr()) + ErrorForReads(cmd, first, second) &&
        exit == (if HadRunError(cmd, first, second) then 1 else 0)
  }

  method ReadInputMethod(input: Schema.CommInput, io: BenchIO.IO) returns (result: BenchWorld.IOResult<BenchWorld.Bytes>)
    modifies io.stdinRegion
    ensures result == Spec.InputResult(old(io.fs()), old(io.trustedStreams()), old(io.stdin()), input)
    ensures io.stdin() == Spec.AfterInputRead(old(io.stdin()), input, old(io.trustedStreams()))
  {
    match input
    case Stdin =>
      result := io.ReadStdin();
    case File(path) =>
      result := io.ReadFile(path);
  }

  method {:isolate_assertions} Prepare(raw: Schema.CommCmdRaw, io: BenchIO.IO) returns (exit: int, plannedOut: BenchWorld.Bytes, plannedErr: BenchWorld.Bytes)
    modifies io.stdinRegion
    ensures PreparedSummary(raw, io, exit, old(io.stdout()) + plannedOut, old(io.stderr()) + plannedErr)
    decreases *
  {
    plannedOut := [];
    plannedErr := [];
    ghost var initialStdout := io.stdout();
    ghost var initialStderr := io.stderr();

    ghost var preFs := io.fs();
    ghost var preStreams := io.trustedStreams();
    ghost var preStdin := io.stdin();
    ghost var preStdout := (initialStdout + plannedOut);
    ghost var preStderr := (initialStderr + plannedErr);
    var cmd := Spec.CommandRelation(raw);

    match cmd.mode {
      case ModeHelp =>
        var help := Spec.HelpTextSpec();
        plannedOut := plannedOut + help;
        exit := 0;
        assert io.stdin() == preStdin;
        assert (initialStderr + plannedErr) == preStderr;
        assert (initialStdout + plannedOut) == preStdout + Spec.HelpTextSpec();
        return;
      case ModeVersion =>
        var version := Spec.VersionTextSpec();
        plannedOut := plannedOut + version;
        exit := 0;
        assert io.stdin() == preStdin;
        assert (initialStderr + plannedErr) == preStderr;
        assert (initialStdout + plannedOut) == preStdout + Spec.VersionTextSpec();
        return;
      case ModeMissingOperand =>
        var msg := Spec.MissingOperandMessageSpec();
        plannedErr := plannedErr + msg;
        exit := 1;
        assert io.stdin() == preStdin;
        assert (initialStdout + plannedOut) == preStdout;
        assert (initialStderr + plannedErr) == preStderr + Spec.MissingOperandMessageSpec();
        return;
      case ModeMissingOperandAfter(operand) =>
        var msg := Spec.MissingOperandAfterMessageSpec(operand);
        plannedErr := plannedErr + msg;
        exit := 1;
        assert io.stdin() == preStdin;
        assert (initialStdout + plannedOut) == preStdout;
        assert (initialStderr + plannedErr) == preStderr + Spec.MissingOperandAfterMessageSpec(operand);
        return;
      case ModeExtraOperand(operand) =>
        var msg := Spec.ExtraOperandMessageSpec(operand);
        plannedErr := plannedErr + msg;
        exit := 1;
        assert io.stdin() == preStdin;
        assert (initialStdout + plannedOut) == preStdout;
        assert (initialStderr + plannedErr) == preStderr + Spec.ExtraOperandMessageSpec(operand);
        return;
      case ModeMultipleOutputDelimiters =>
        var msg := Spec.MultipleOutputDelimitersMessageSpec();
        plannedErr := plannedErr + msg;
        exit := 1;
        assert io.stdin() == preStdin;
        assert (initialStdout + plannedOut) == preStdout;
        assert (initialStderr + plannedErr) == preStderr + Spec.MultipleOutputDelimitersMessageSpec();
        return;
      case ModeRepeatedStdinOperand =>
        var msg := Spec.RepeatedStdinOperandMessageSpec();
        plannedErr := plannedErr + msg;
        exit := 1;
        assert io.stdin() == preStdin;
        assert (initialStdout + plannedOut) == preStdout;
        assert (initialStderr + plannedErr) == preStderr + Spec.RepeatedStdinOperandMessageSpec();
        return;
      case ModeRun =>
        var first := ReadInputMethod(cmd.input1, io);
        assert first == Spec.ReadFirstResult(cmd, preFs, preStreams, preStdin);
        assert io.stdin() == Spec.AfterFirstRead(cmd, preStdin, preStreams);
        if Spec.FirstReadAborts(cmd, first) {
          var err := Spec.InputErrorMessageSpec(cmd.input1, first.e);
          plannedErr := plannedErr + err;
          exit := 1;
          assert (initialStdout + plannedOut) == preStdout;
          assert (initialStderr + plannedErr) == preStderr + Spec.InputErrorMessageSpec(cmd.input1, first.e);
          return;
        } else {
          ghost var stdinAfterFirst := io.stdin();
          var second := ReadInputMethod(cmd.input2, io);
          assert stdinAfterFirst == Spec.AfterFirstRead(cmd, preStdin, preStreams);
          assert second == Spec.InputResult(preFs, preStreams, stdinAfterFirst, cmd.input2);
          assert second == Spec.ReadSecondResult(cmd, preFs, preStreams, preStdin);
          assert io.stdin() == Spec.AfterInputRead(stdinAfterFirst, cmd.input2, preStreams);
          assert io.stdin() == Spec.AfterSecondRead(cmd, preStdin, preStreams);
          var out := OutputForReads(cmd, first, second);
          var err := ErrorForReads(cmd, first, second);
          var hadError := HadRunError(cmd, first, second);
          plannedOut := plannedOut + out;
          plannedErr := plannedErr + err;
          exit := if hadError then 1 else 0;
          assert (initialStdout + plannedOut) == preStdout + OutputForReads(cmd, first, second);
          assert (initialStderr + plannedErr) == preStderr + ErrorForReads(cmd, first, second);
          return;
        }
    }
  }

  twostate predicate CoreSummary(raw: Schema.CommCmdRaw, io: BenchIO.IO, exit: int)
    reads io.stdinRegion, io.stdoutRegion, io.stderrRegion
  {
    exists out: BenchWorld.Bytes, diagnostics: BenchWorld.Bytes, normalExit: int ::
      PreparedSummary(raw, io, normalExit,
                      old(io.stdout()) + out, old(io.stderr()) + diagnostics) &&
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

  method RunCore(raw: Schema.CommCmdRaw, io: BenchIO.IO) returns (exit: int)
    modifies io.stdinRegion, io.stdoutRegion, io.stderrRegion
    ensures CoreSummary(raw, io, exit)
    decreases *
  {
    var normalExit, out, diagnostics := Prepare(raw, io);

    assert PreparedSummary(raw, io, normalExit, old(io.stdout()) + out, old(io.stderr()) + diagnostics);
    if Spec.Emits(raw) {
      exit := Flush(io, out, diagnostics, normalExit);
    } else {
      exit := normalExit;
    }
    assert PreparedSummary(raw, io, normalExit, old(io.stdout()) + out, old(io.stderr()) + diagnostics);
    assert Spec.Emission(raw, io, out, diagnostics, normalExit, exit);
  }
  datatype FailedMergePlan = FailedMergePlan(output: BenchWorld.Bytes, leftFault: bool)

  function CompleteRecordsData(data: BenchWorld.Bytes, delimiter: BenchWorld.RawByte): BenchWorld.Bytes
    ensures Spec.CompleteInputPrefixRelation(data, delimiter, CompleteRecordsData(data, delimiter))
    decreases |data|
  {
    if data == [] || data[|data| - 1] == delimiter then data
    else CompleteRecordsData(data[..|data| - 1], delimiter)
  }

  function ReadRecordsData(result: BenchWorld.IOResult<BenchWorld.Bytes>, delimiter: BenchWorld.RawByte): BenchWorld.Bytes
  {
    if result.Ok? then result.v else CompleteRecordsData(IOContract.ReadResultData(result), delimiter)
  }

  function RenderBeforeReadFailure(cmd: Schema.CommCmd, left: seq<BenchWorld.Bytes>, right: seq<BenchWorld.Bytes>,
                                   leftFailed: bool, rightFailed: bool): FailedMergePlan
    requires leftFailed || rightFailed
    decreases |left| + |right|
  {
    if leftFailed && left == [] then FailedMergePlan([], true)
    else if rightFailed && right == [] then FailedMergePlan([], false)
    else if right == [] then
      var tail := RenderBeforeReadFailure(cmd, left[1..], right, leftFailed, rightFailed);
      FailedMergePlan(RSpec.RenderFragment(cmd, RSpec.OnlyFirst, left[0]) + tail.output, tail.leftFault)
    else if left == [] then
      var tail := RenderBeforeReadFailure(cmd, left, right[1..], leftFailed, rightFailed);
      FailedMergePlan(RSpec.RenderFragment(cmd, RSpec.OnlySecond, right[0]) + tail.output, tail.leftFault)
    else
      match Render.CompareRecords(left[0], right[0])
      case LineLess =>
        var tail := RenderBeforeReadFailure(cmd, left[1..], right, leftFailed, rightFailed);
        FailedMergePlan(RSpec.RenderFragment(cmd, RSpec.OnlyFirst, left[0]) + tail.output, tail.leftFault)
      case LineGreater =>
        var tail := RenderBeforeReadFailure(cmd, left, right[1..], leftFailed, rightFailed);
        FailedMergePlan(RSpec.RenderFragment(cmd, RSpec.OnlySecond, right[0]) + tail.output, tail.leftFault)
      case LineEqual =>
        var tail := RenderBeforeReadFailure(cmd, left[1..], right[1..], leftFailed, rightFailed);
        FailedMergePlan(RSpec.RenderFragment(cmd, RSpec.Both, left[0]) + tail.output, tail.leftFault)
  }

  function FailedReadsPlan(cmd: Schema.CommCmd,
                           first: BenchWorld.IOResult<BenchWorld.Bytes>, second: BenchWorld.IOResult<BenchWorld.Bytes>): FailedMergePlan
    requires first.Err? || second.Err?
  {
    var delimiter := RSpec.RecordDelimiter(cmd.zeroTerminated);
    RenderBeforeReadFailure(cmd, Render.Records(ReadRecordsData(first, delimiter), delimiter),
                            Render.Records(ReadRecordsData(second, delimiter), delimiter), first.Err?, second.Err?)
  }
}
