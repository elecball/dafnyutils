include "CsplitTextCore.dfy"
include "../../core/World.dfy"
include "../../core/IO.dfy"
include "../../core/IOContract.dfy"
include "CsplitSchema.dfy"
include "CsplitSpec.dfy"

module CsplitCore {
  import Text = CsplitTextCore
  import StreamContract = IOContract

  import Result = Results
  import BenchIO
  import Utf8 = CsplitUtf8Core
  import BenchWorld
  import IOContract
  import Schema = CsplitSchema
  import Spec = CsplitSpec

  function ZeroLineMessage(line: nat): BenchWorld.Bytes
    ensures ZeroLineMessage(line) == Spec.ZeroLineMessage(line)
  {
    Spec.ZeroLineMessagePart1() + DigitsNat(line) + Spec.ZeroLineMessagePart2()
  }

  function BackwardLineMessage(current: nat, previous: nat): BenchWorld.Bytes
    ensures BackwardLineMessage(current, previous) == Spec.BackwardLineMessage(current, previous)
  {
    Spec.BackwardLineMessagePart1() + DigitsNat(current) + Spec.BackwardLineMessagePart2() +
    DigitsNat(previous) + Spec.BackwardLineMessagePart3()
  }

  function OutOfRangeMessage(line: nat): BenchWorld.Bytes
    ensures OutOfRangeMessage(line) == Spec.OutOfRangeMessage(line)
  {
    Spec.OutOfRangeMessagePart1() + DigitsNat(line) + Spec.OutOfRangeMessagePart2()
  }

  function DuplicateWarning(line: nat): BenchWorld.Bytes
    ensures DuplicateWarning(line) == Spec.DuplicateWarning(line)
  {
    Spec.DuplicateWarningPart1() + DigitsNat(line) + Spec.DuplicateWarningPart2()
  }
  datatype NumberStatus = NumbersOk | NumberZero | NumberBackwards(current: nat, previous: nat)
  datatype NumberValidation = NumberValidation(status: NumberStatus, processed: nat)
  datatype NumberAnalysis = NumberAnalysis(
    status: NumberStatus,
    processed: nat,
    warnings: BenchWorld.Bytes
  )
  datatype SplitPlan = SplitComplete(pieces: seq<BenchWorld.Bytes>) |
                       SplitOutOfRange(pieces: seq<BenchWorld.Bytes>, line: nat)
  datatype LifetimeMutation =
    FreshObject(id: BenchWorld.InodeId) |
    RemovedLastObject(id: BenchWorld.InodeId)

  function LineStart(data: BenchWorld.Bytes, line: nat): nat
    ensures LineStart(data, line) <= |data|
    decreases |data| + line
  {
    if line <= 1 then
      0
    else if |data| == 0 then
      0
    else if data[0] == '\n' then
      1 + LineStart(data[1..], line - 1)
    else
      1 + LineStart(data[1..], line)
  }

  function LineExists(data: BenchWorld.Bytes, line: nat): bool
  {
    line > 0 && LineStart(data, line) < |data|
  }

  function SafeSlice(
    data: BenchWorld.Bytes, start: nat, end: nat
  ): BenchWorld.Bytes
  {
    if start <= end <= |data| then data[start..end] else []
  }

  function ValidateNumbersFrom(
    lines: seq<nat>, previous: nat
  ): NumberValidation
    ensures ValidateNumbersFrom(lines, previous).processed <= |lines|
    decreases |lines|
  {
    if |lines| == 0 then
      NumberValidation(NumbersOk, 0)
    else if lines[0] == 0 then
      NumberValidation(NumberZero, 0)
    else if lines[0] < previous then
      NumberValidation(NumberBackwards(lines[0], previous), 0)
    else
      var tail := ValidateNumbersFrom(lines[1..], lines[0]);
      NumberValidation(tail.status, tail.processed + 1)
  }

  function ValidateNumbers(lines: seq<nat>): NumberValidation
  {
    ValidateNumbersFrom(lines, 0)
  }

  function SplitPlanFrom(
    data: BenchWorld.Bytes, lines: seq<nat>, start: nat
  ): SplitPlan
    decreases |lines|
  {
    if |lines| == 0 then
      SplitComplete([SafeSlice(data, start, |data|)])
    else
      var next := LineStart(data, lines[0]);
      var piece := SafeSlice(data, start, next);
      if !LineExists(data, lines[0]) then
        SplitOutOfRange([piece], lines[0])
      else
        match SplitPlanFrom(data, lines[1..], next)
        case SplitComplete(tail) => SplitComplete([piece] + tail)
        case SplitOutOfRange(tail, line) =>
          SplitOutOfRange([piece] + tail, line)
  }

  function SplitPlanFor(
    data: BenchWorld.Bytes, lines: seq<nat>
  ): SplitPlan
  {
    SplitPlanFrom(data, lines, 0)
  }

  function DuplicateWarningsFrom(
    lines: seq<nat>, previous: nat, hasPrevious: bool
  ): BenchWorld.Bytes
    decreases |lines|
  {
    if |lines| == 0 then
      []
    else
      (if hasPrevious && lines[0] == previous
       then DuplicateWarning(lines[0])
       else []) +
      DuplicateWarningsFrom(lines[1..], lines[0], true)
  }

  function DuplicateWarnings(
    lines: seq<nat>
  ): BenchWorld.Bytes
  {
    DuplicateWarningsFrom(lines, 0, false)
  }

  function AnalyzeNumbers(lines: seq<nat>): NumberAnalysis
  {
    var validation := ValidateNumbers(lines);
    NumberAnalysis(
      validation.status,
      validation.processed,
      DuplicateWarnings(lines[..validation.processed])
    )
  }

  ghost predicate WriteTraceSummaryFields(observations: Spec.ObservationContext,
                                          pieces: seq<BenchWorld.Bytes>,
                                          index: nat,
                                          terminalError: BenchWorld.Bytes,
                                          hasTerminalError: bool,
                                          preFs: BenchWorld.FileSystem,
                                          preNow: int,
                                          fs2: BenchWorld.FileSystem,
                                          stdout: BenchWorld.Bytes,
                                          stderr: BenchWorld.Bytes,
                                          exit: int
  )
    decreases |pieces|
  {
    if |pieces| == 0 then
      fs2 == preFs &&
      stdout == [] &&
      stderr == (if hasTerminalError then terminalError else []) &&
      exit == (if hasTerminalError then 1 else 0)
    else
      exists afterWriteFs: BenchWorld.FileSystem, ok: bool, err: int ::
        Spec.WriteObservation(observations,
                              preFs, preNow, OutputName(index), pieces[0], ok, err, afterWriteFs
        ) &&
        if ok then
          exists tailFs: BenchWorld.FileSystem, tailOut: BenchWorld.Bytes,
            tailErr: BenchWorld.Bytes, tailExit: int
            {:trigger WriteTraceSummaryFields(observations,
                                              pieces[1..],
                                              index + 1,
                                              terminalError,
                                              hasTerminalError,
                                              afterWriteFs,
                                              preNow,
                                              tailFs,
                                              tailOut,
                                              tailErr,
                                              tailExit
            )} ::
            WriteTraceSummaryFields(observations,
                                    pieces[1..],
                                    index + 1,
                                    terminalError,
                                    hasTerminalError,
                                    afterWriteFs,
                                    preNow,
                                    tailFs,
                                    tailOut,
                                    tailErr,
                                    tailExit
            ) &&
            (if hasTerminalError || tailExit != 0 then
               exists deleteOk: bool, deleteErr: int ::
                 Spec.DeleteObservation(observations,
                                        tailFs, OutputName(index), deleteOk, deleteErr, fs2
                 )
             else
               fs2 == tailFs) &&
            stdout == CountLine(|pieces[0]|) + tailOut &&
            stderr == tailErr &&
            exit == tailExit
        else
          Spec.FailedWriteCleanupRelation(observations, preFs, preNow, OutputName(index), pieces[0], err, afterWriteFs, fs2) &&
          stdout == [] &&
          stderr == Spec.WriteErrorMessage(OutputName(index), err) &&
          exit == 1
  }

  ghost predicate WritePiecesSummaryFields(observations: Spec.ObservationContext,
                                           pieces: seq<BenchWorld.Bytes>,
                                           index: nat,
                                           preFs: BenchWorld.FileSystem,
                                           preNow: int,
                                           fs2: BenchWorld.FileSystem,
                                           stdout: BenchWorld.Bytes,
                                           stderr: BenchWorld.Bytes,
                                           exit: int
  )
  {
    WriteTraceSummaryFields(observations,
                            pieces, index, [], false, preFs, preNow, fs2, stdout, stderr, exit
    )
  }

  ghost predicate WritePiecesThenErrorSummaryFields(observations: Spec.ObservationContext,
                                                    pieces: seq<BenchWorld.Bytes>,
                                                    index: nat,
                                                    line: nat,
                                                    preFs: BenchWorld.FileSystem,
                                                    preNow: int,
                                                    fs2: BenchWorld.FileSystem,
                                                    stdout: BenchWorld.Bytes,
                                                    stderr: BenchWorld.Bytes,
                                                    exit: int
  )
  {
    WriteTraceSummaryFields(observations,
                            pieces,
                            index,
                            Spec.OutOfRangeMessage(line),
                            true,
                            preFs,
                            preNow,
                            fs2,
                            stdout,
                            stderr,
                            exit
    )
  }

  ghost function DeferredReadResultFields(raw: Schema.CsplitCmdRaw,
                                          preFs: BenchWorld.FileSystem,
                                          preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult,
                                          preStdin: BenchWorld.Bytes): BenchWorld.IOResult<BenchWorld.Bytes>
  {
    if raw.input.Stdin? && AnalyzeNumbers(raw.lineNumbers).status != NumbersOk then Result.Ok(preStdin)
    else Spec.ReadResultFields(raw.input, preFs, preStreams, preStdin)
  }

  twostate predicate PreparedSummary(raw: Schema.CsplitCmdRaw, io: BenchIO.IO, exit: int, plannedStdout: BenchWorld.Bytes, plannedStderr: BenchWorld.Bytes)
    reads io.fsRegion, io.stdinRegion
  {
    if raw.mode == Schema.ModeHelp then
      io.fs() == old(io.fs()) &&
      io.stdin() == old(io.stdin()) &&
      plannedStdout == Spec.HelpText() &&
      plannedStderr == [] &&
      exit == 0
    else if raw.mode == Schema.ModeVersion then
      io.fs() == old(io.fs()) &&
      io.stdin() == old(io.stdin()) &&
      plannedStdout == Spec.VersionText() &&
      plannedStderr == [] &&
      exit == 0
    else
      match DeferredReadResultFields(raw, old(io.fs()), old(io.trustedStreams()), old(io.stdin()))
      case Err(err) =>
        io.stdin() == Spec.ReadStdinAfterFields(raw.input, old(io.stdin()), old(io.trustedStreams())) &&
        (if raw.input.Stdin? then
           PartialStdinFailureSummary(old(Spec.Context(io)), raw, err, old(io.fs()), old(io.now()), io.fs(), plannedStdout, plannedStderr, exit)
         else
           io.fs() == old(io.fs()) && plannedStdout == [] &&
           plannedStderr == Spec.ReadErrorMessage(raw.input, err) && exit == 1)
      case Ok(data) =>
        var analysis := AnalyzeNumbers(raw.lineNumbers);
        match analysis.status
        case NumberZero =>
          io.fs() == old(io.fs()) &&
          io.stdin() == old(io.stdin()) &&
          plannedStdout == [] &&
          plannedStderr ==
          analysis.warnings + Spec.ZeroLineMessage(0) &&
          exit == 1
        case NumberBackwards(current, previous) =>
          io.fs() == old(io.fs()) &&
          io.stdin() == old(io.stdin()) &&
          plannedStdout == [] &&
          plannedStderr ==
          analysis.warnings +
          Spec.BackwardLineMessage(current, previous) &&
          exit == 1
        case NumbersOk =>
          io.stdin() == Spec.ReadStdinAfterFields(raw.input, old(io.stdin()), old(io.trustedStreams())) &&
          match SplitPlanFor(data, raw.lineNumbers)
          case SplitOutOfRange(pieces, line) =>
            exists writeOut: BenchWorld.Bytes, writeErr: BenchWorld.Bytes ::
              WritePiecesThenErrorSummaryFields(old(Spec.Context(io)),
                                                pieces,
                                                0,
                                                line,
                                                old(io.fs()),
                                                old(io.now()),
                                                io.fs(),
                                                writeOut,
                                                writeErr,
                                                exit
              ) &&
              plannedStdout == writeOut &&
              plannedStderr ==
              analysis.warnings + writeErr
          case SplitComplete(pieces) =>
            exists writeOut: BenchWorld.Bytes, writeErr: BenchWorld.Bytes ::
              WritePiecesSummaryFields(old(Spec.Context(io)),
                                       pieces,
                                       0,
                                       old(io.fs()),
                                       old(io.now()),
                                       io.fs(),
                                       writeOut,
                                       writeErr,
                                       exit
              ) &&
              plannedStdout == writeOut &&
              plannedStderr ==
              analysis.warnings + writeErr
  }

  function DigitChar(d: nat): char
    requires d < 10
  {
    if d == 0 then '0'
    else if d == 1 then '1'
    else if d == 2 then '2'
    else if d == 3 then '3'
    else if d == 4 then '4'
    else if d == 5 then '5'
    else if d == 6 then '6'
    else if d == 7 then '7'
    else if d == 8 then '8'
    else '9'
  } by method {
    var ch: char;
    if d == 0 { ch := '0'; }
    else if d == 1 { ch := '1'; }
    else if d == 2 { ch := '2'; }
    else if d == 3 { ch := '3'; }
    else if d == 4 { ch := '4'; }
    else if d == 5 { ch := '5'; }
    else if d == 6 { ch := '6'; }
    else if d == 7 { ch := '7'; }
    else if d == 8 { ch := '8'; }
    else { ch := '9'; }
    return ch;
  }

  function DigitsNat(n: nat): BenchWorld.Bytes
    decreases n
  {
    if n < 10 then [DigitChar(n)]
    else DigitsNat(n / 10) + [DigitChar(n % 10)]
  } by method {
    var digits: BenchWorld.Bytes;
    if n < 10 {
      var ch := DigitChar(n);
      digits := [ch];
    } else {
      var prefix := DigitsNat(n / 10);
      var ch := DigitChar(n % 10);
      digits := prefix + [ch];
    }
    return digits;
  }

  function CountLine(n: nat): BenchWorld.Bytes
  {
    DigitsNat(n) + "\n"
  } by method {
    var digits := DigitsNat(n);
    return digits + "\n";
  }

  function OutputName(index: nat): BenchWorld.Path
  {
    if index < 10 then
      "xx0" + DigitsNat(index)
    else
      "xx" + DigitsNat(index)
  } by method {
    var digits := DigitsNat(index);
    if index < 10 {
      return "xx0" + digits;
    } else {
      return "xx" + digits;
    }
  }

  ghost predicate NoFreshObjectAfterLastRemoval(events: seq<LifetimeMutation>)
  {
    forall i: int, j: int ::
      0 <= i < j < |events| && events[i].RemovedLastObject? ==>
        !events[j].FreshObject?
  }

  ghost function FreshWriteEventList(
    before: BenchWorld.FileSystem,
    after: BenchWorld.FileSystem,
    path: BenchWorld.Path
  ): seq<LifetimeMutation>
  {
    if !BenchWorld.FsContainsPath(before, path) &&
       BenchWorld.FsContainsPath(after, path) then
      [FreshObject(BenchWorld.FsIdAt(after, path))]
    else
      []
  }

  ghost predicate FreshWriteEvents(
    before: BenchWorld.FileSystem,
    after: BenchWorld.FileSystem,
    path: BenchWorld.Path,
    events: seq<LifetimeMutation>
  )
  {
    events == FreshWriteEventList(before, after, path)
  }

  ghost function LastRemovalEventList(
    before: BenchWorld.FileSystem,
    after: BenchWorld.FileSystem,
    path: BenchWorld.Path
  ): seq<LifetimeMutation>
  {
    if BenchWorld.FsContainsPath(before, path) &&
       !BenchWorld.FsContainsPath(after, path) &&
       BenchWorld.InodeLinkCountAt(before, path) ==
       BenchWorld.LinkCountKnown(1) then
      [RemovedLastObject(BenchWorld.FsIdAt(before, path))]
    else
      []
  }

  ghost predicate LastRemovalEvents(
    before: BenchWorld.FileSystem,
    after: BenchWorld.FileSystem,
    path: BenchWorld.Path,
    events: seq<LifetimeMutation>
  )
  {
    events == LastRemovalEventList(before, after, path)
  }

  ghost predicate LifetimeEvidence(observations: Spec.ObservationContext,
                                   pieces: seq<BenchWorld.Bytes>,
                                   index: nat,
                                   preFs: BenchWorld.FileSystem,
                                   preNow: int,
                                   fs2: BenchWorld.FileSystem,
                                   exit: int,
                                   lifetimeEvents: seq<LifetimeMutation>,
                                   alwaysCleanup: bool
  )
    decreases |pieces|
  {
    if |pieces| == 0 then
      fs2 == preFs &&
      exit == (if alwaysCleanup then 1 else 0) &&
      lifetimeEvents == []
    else
      exists afterWriteFs: BenchWorld.FileSystem, ok: bool, err: int ::
        Spec.WriteObservation(observations,
                              preFs,
                              preNow,
                              OutputName(index),
                              pieces[0],
                              ok,
                              err,
                              afterWriteFs
        ) &&
        if ok then
          exists tailFs: BenchWorld.FileSystem, tailExit: int,
            writeEvents: seq<LifetimeMutation>,
            tailEvents: seq<LifetimeMutation>,
            cleanupEvents: seq<LifetimeMutation>
            {:trigger
            LifetimeEvidence(observations,
                             pieces[1..],
                             index + 1,
                             afterWriteFs,
                             preNow,
                             tailFs,
                             tailExit,
                             tailEvents,
                             alwaysCleanup
            ),
            FreshWriteEvents(
              preFs,
              afterWriteFs,
              OutputName(index),
              writeEvents
            ),
            LastRemovalEvents(
              tailFs,
              fs2,
              OutputName(index),
              cleanupEvents
            )}
            ::
              FreshWriteEvents(
                preFs,
                afterWriteFs,
                OutputName(index),
                writeEvents
              ) &&
              LifetimeEvidence(observations,
                               pieces[1..],
                               index + 1,
                               afterWriteFs,
                               preNow,
                               tailFs,
                               tailExit,
                               tailEvents,
                               alwaysCleanup
              ) &&
              (if alwaysCleanup || tailExit != 0 then
                 exists deleteOk: bool, deleteErr: int ::
                   Spec.DeleteObservation(observations,
                                          tailFs,
                                          OutputName(index),
                                          deleteOk,
                                          deleteErr,
                                          fs2
                   ) &&
                   LastRemovalEvents(
                     tailFs,
                     fs2,
                     OutputName(index),
                     cleanupEvents
                   )
               else
                 fs2 == tailFs && cleanupEvents == []) &&
              exit == tailExit &&
              lifetimeEvents == writeEvents + tailEvents + cleanupEvents
        else
          Spec.FailedWriteCleanupRelation(observations, preFs, preNow, OutputName(index), pieces[0], err, afterWriteFs, fs2) &&
          exit == 1 &&
          lifetimeEvents == FreshWriteEventList(preFs, afterWriteFs, OutputName(index)) +
          LastRemovalEventList(afterWriteFs, fs2, OutputName(index))
  }

  ghost predicate WritePiecesLifetimeEvidence(observations: Spec.ObservationContext,
                                              pieces: seq<BenchWorld.Bytes>,
                                              index: nat,
                                              preFs: BenchWorld.FileSystem,
                                              preNow: int,
                                              fs2: BenchWorld.FileSystem,
                                              exit: int,
                                              lifetimeEvents: seq<LifetimeMutation>
  )
  {
    LifetimeEvidence(observations,
                     pieces,
                     index,
                     preFs,
                     preNow,
                     fs2,
                     exit,
                     lifetimeEvents,
                     false
    )
  }

  ghost predicate WritePiecesThenErrorLifetimeEvidence(observations: Spec.ObservationContext,
                                                       pieces: seq<BenchWorld.Bytes>,
                                                       index: nat,
                                                       line: nat,
                                                       preFs: BenchWorld.FileSystem,
                                                       preNow: int,
                                                       fs2: BenchWorld.FileSystem,
                                                       exit: int,
                                                       lifetimeEvents: seq<LifetimeMutation>
  )
  {
    LifetimeEvidence(observations,
                     pieces,
                     index,
                     preFs,
                     preNow,
                     fs2,
                     exit,
                     lifetimeEvents,
                     true
    )
  }

  lemma ComposeLifetimeEvents(
    writeEvents: seq<LifetimeMutation>,
    tailEvents: seq<LifetimeMutation>,
    cleanupEvents: seq<LifetimeMutation>
  )
    requires writeEvents == [] ||
             exists id: BenchWorld.InodeId :: writeEvents == [FreshObject(id)]
    requires NoFreshObjectAfterLastRemoval(tailEvents)
    requires cleanupEvents == [] ||
             exists id: BenchWorld.InodeId ::
               cleanupEvents == [RemovedLastObject(id)]
    ensures NoFreshObjectAfterLastRemoval(
              writeEvents + tailEvents + cleanupEvents
            )
  {
  }

  method {:isolate_assertions} WritePieces(
    pieces: seq<BenchWorld.Bytes>,
    index: nat,
    io: BenchIO.IO
  ) returns (
      stdout: BenchWorld.Bytes,
      stderr: BenchWorld.Bytes,
      exit: int,
      ghost lifetimeEvents: seq<LifetimeMutation>
    )
    modifies io.fsRegion
    ensures WritePiecesSummaryFields(old(Spec.Context(io)), pieces, index, old(io.fs()), old(io.now()), io.fs(), stdout, stderr, exit)
    ensures WritePiecesLifetimeEvidence(old(Spec.Context(io)),
                                        pieces,
                                        index,
                                        old(io.fs()),
                                        old(io.now()),
                                        io.fs(),
                                        exit,
                                        lifetimeEvents
            )
    ensures NoFreshObjectAfterLastRemoval(lifetimeEvents)
    decreases |pieces|
  {
    ghost var observations := Spec.Context(io);
    ghost var preFs := io.fs();
    ghost var preNow := io.now();
    if |pieces| == 0 {
      stdout := [];
      stderr := [];
      exit := 0;
      lifetimeEvents := [];
      assert WritePiecesSummaryFields(observations, pieces, index, preFs, preNow, io.fs(), stdout, stderr, exit);
      return;
    }

    ghost var beforeWriteFs := io.fs();
    ghost var beforeWriteNow := io.now();
    var path := OutputName(index);
    var writeFileResult := io.WriteFile(path, pieces[0]);
    var ok := writeFileResult.Ok?;
    var err := IOContract.ResultErrno(writeFileResult);
    ghost var afterWriteFs := io.fs();
    assert path == OutputName(index);
    assert Spec.WriteObservation(observations, beforeWriteFs, beforeWriteNow, OutputName(index), pieces[0], ok, err, afterWriteFs);

    if ok {
      ghost var writeEvents :=
        FreshWriteEventList(beforeWriteFs, afterWriteFs, path);
      assert FreshWriteEvents(
          beforeWriteFs,
          afterWriteFs,
          path,
          writeEvents
        );
      var tailOut, tailErr, tailExit;
      ghost var tailEvents;
      tailOut, tailErr, tailExit, tailEvents :=
        WritePieces(pieces[1..], index + 1, io);
      ghost var tailFs := io.fs();
      assert LifetimeEvidence(observations,
                              pieces[1..],
                              index + 1,
                              afterWriteFs,
                              beforeWriteNow,
                              tailFs,
                              tailExit,
                              tailEvents,
                              false
        );
      var count := CountLine(|pieces[0]|);
      ghost var cleanupEvents: seq<LifetimeMutation> := [];
      if tailExit != 0 {
        var deletePathResult := io.DeletePath(path);
        var deleteOk := deletePathResult.Ok?;
        var deleteErr := IOContract.ResultErrno(deletePathResult);
        assert Spec.DeleteObservation(observations, tailFs, OutputName(index), deleteOk, deleteErr, io.fs());
        cleanupEvents := LastRemovalEventList(tailFs, io.fs(), path);
        assert LastRemovalEvents(
            tailFs,
            io.fs(),
            path,
            cleanupEvents
          );
        assert exists cleanupOk: bool, cleanupErr: int ::
            Spec.DeleteObservation(observations, tailFs, OutputName(index), cleanupOk, cleanupErr, io.fs());
      } else {
        assert LastRemovalEvents(
            tailFs,
            io.fs(),
            path,
            cleanupEvents
          );
      }
      stdout := count + tailOut;
      stderr := tailErr;
      exit := tailExit;
      lifetimeEvents := writeEvents + tailEvents + cleanupEvents;
      assert writeEvents == [] ||
             exists id: BenchWorld.InodeId :: writeEvents == [FreshObject(id)];
      assert cleanupEvents == [] ||
             exists id: BenchWorld.InodeId ::
               cleanupEvents == [RemovedLastObject(id)];
      ComposeLifetimeEvents(writeEvents, tailEvents, cleanupEvents);
      assert WritePiecesSummaryFields(observations, pieces[1..], index + 1, afterWriteFs, beforeWriteNow, tailFs, tailOut, tailErr, tailExit);
      assert WritePiecesSummaryFields(observations, pieces, index, beforeWriteFs, beforeWriteNow, io.fs(), stdout, stderr, exit);
      assert LifetimeEvidence(observations,
                              pieces,
                              index,
                              beforeWriteFs,
                              beforeWriteNow,
                              io.fs(),
                              exit,
                              lifetimeEvents,
                              false
        );
    } else {
      ghost var observedCommitted := IOContract.WriteResultCommitted(writeFileResult);
      ghost var observedStage := IOContract.WriteResultStage(writeFileResult);
      assert IOContract.WriteFileSpec(beforeWriteFs, observations.props, beforeWriteNow,
                                      observations.credentials, observations.filesystem, afterWriteFs,
                                      path, pieces[0], false, err, observedCommitted, observedStage);
      if IOContract.WriteResultStage(writeFileResult) != BenchWorld.WriteOpenFailed {
        var cleanup := io.DeletePath(path);
        assert Spec.DeleteObservation(observations, afterWriteFs, path,
                                      cleanup.Ok?, IOContract.ResultErrno(cleanup), io.fs());
        assert exists deleteOk: bool, deleteErr: int ::
            Spec.DeleteObservation(observations, afterWriteFs, path,
                                   deleteOk, deleteErr, io.fs());
      }
      assert observedStage == BenchWorld.WriteOpenFailed ==> io.fs() == afterWriteFs;
      assert observedStage != BenchWorld.WriteOpenFailed ==>
          exists deleteOk: bool, deleteErr: int ::
            Spec.DeleteObservation(observations, afterWriteFs, path,
                                   deleteOk, deleteErr, io.fs());
      assert Spec.FailedWriteCleanupRelation(observations, beforeWriteFs, beforeWriteNow, path, pieces[0], err, afterWriteFs, io.fs()) by {
        hide *;
        reveal Spec.FailedWriteCleanupRelation();
        assert exists committed: nat, stage: BenchWorld.FileWriteStage ::
            committed == observedCommitted && stage == observedStage &&
            IOContract.WriteFileSpec(beforeWriteFs, observations.props, beforeWriteNow,
                                     observations.credentials, observations.filesystem, afterWriteFs,
                                     path, pieces[0], false, err, committed, stage) &&
            (if stage == BenchWorld.WriteOpenFailed then io.fs() == afterWriteFs
             else exists deleteOk: bool, deleteErr: int ::
                    Spec.DeleteObservation(observations, afterWriteFs, path,
                                           deleteOk, deleteErr, io.fs()));
      }
      stdout := [];
      stderr := Text.WriteErrorMessage(path, err);
      exit := 1;
      lifetimeEvents := FreshWriteEventList(beforeWriteFs, afterWriteFs, path) +
      LastRemovalEventList(afterWriteFs, io.fs(), path);
      assert stderr == Spec.WriteErrorMessage(OutputName(index), err);
      assert WritePiecesSummaryFields(observations, pieces, index, beforeWriteFs, beforeWriteNow, io.fs(), stdout, stderr, exit);
    }
  }

  method {:isolate_assertions} WritePiecesThenDiagnostic(
    pieces: seq<BenchWorld.Bytes>,
    index: nat,
    terminalError: BenchWorld.Bytes,
    io: BenchIO.IO
  ) returns (
      stdout: BenchWorld.Bytes,
      stderr: BenchWorld.Bytes,
      exit: int,
      ghost lifetimeEvents: seq<LifetimeMutation>
    )
    modifies io.fsRegion
    ensures WriteTraceSummaryFields(old(Spec.Context(io)), pieces, index, terminalError, true, old(io.fs()), old(io.now()), io.fs(), stdout, stderr, exit)
    ensures LifetimeEvidence(old(Spec.Context(io)), pieces, index, old(io.fs()), old(io.now()), io.fs(), exit, lifetimeEvents, true)
    ensures exit == 1
    ensures NoFreshObjectAfterLastRemoval(lifetimeEvents)
    decreases |pieces|
  {
    ghost var observations := Spec.Context(io);
    ghost var preFs := io.fs();
    ghost var preNow := io.now();
    if |pieces| == 0 {
      stdout := [];
      stderr := terminalError;
      exit := 1;
      lifetimeEvents := [];
      assert WriteTraceSummaryFields(observations, pieces, index, terminalError, true, preFs, preNow, io.fs(), stdout, stderr, exit);
      return;
    }

    ghost var beforeWriteFs := io.fs();
    ghost var beforeWriteNow := io.now();
    var path := OutputName(index);
    var writeFileResult2 := io.WriteFile(path, pieces[0]);
    var ok := writeFileResult2.Ok?;
    var err := IOContract.ResultErrno(writeFileResult2);
    ghost var afterWriteFs := io.fs();
    assert path == OutputName(index);
    assert Spec.WriteObservation(observations, beforeWriteFs, beforeWriteNow, OutputName(index), pieces[0], ok, err, afterWriteFs);

    if ok {
      ghost var writeEvents :=
        FreshWriteEventList(beforeWriteFs, afterWriteFs, path);
      assert FreshWriteEvents(
          beforeWriteFs,
          afterWriteFs,
          path,
          writeEvents
        );
      var tailOut, tailErr, tailExit;
      ghost var tailEvents;
      tailOut, tailErr, tailExit, tailEvents :=
        WritePiecesThenDiagnostic(pieces[1..], index + 1, terminalError, io);
      ghost var tailFs := io.fs();
      assert LifetimeEvidence(observations,
                              pieces[1..],
                              index + 1,
                              afterWriteFs,
                              beforeWriteNow,
                              tailFs,
                              tailExit,
                              tailEvents,
                              true
        );
      var deletePathResult2 := io.DeletePath(path);
      var deleteOk := deletePathResult2.Ok?;
      var deleteErr := IOContract.ResultErrno(deletePathResult2);
      assert Spec.DeleteObservation(observations, tailFs, OutputName(index), deleteOk, deleteErr, io.fs());
      ghost var cleanupEvents :=
        LastRemovalEventList(tailFs, io.fs(), path);
      assert LastRemovalEvents(
          tailFs,
          io.fs(),
          path,
          cleanupEvents
        );
      var count := CountLine(|pieces[0]|);
      stdout := count + tailOut;
      stderr := tailErr;
      exit := tailExit;
      lifetimeEvents := writeEvents + tailEvents + cleanupEvents;
      assert writeEvents == [] ||
             exists id: BenchWorld.InodeId :: writeEvents == [FreshObject(id)];
      assert cleanupEvents == [] ||
             exists id: BenchWorld.InodeId ::
               cleanupEvents == [RemovedLastObject(id)];
      ComposeLifetimeEvents(writeEvents, tailEvents, cleanupEvents);
      assert WriteTraceSummaryFields(observations, pieces[1..], index + 1, terminalError, true, afterWriteFs, beforeWriteNow, tailFs, tailOut, tailErr, tailExit);
      assert exists cleanupOk: bool, cleanupErr: int ::
          Spec.DeleteObservation(observations, tailFs, OutputName(index), cleanupOk, cleanupErr, io.fs());
      assert WriteTraceSummaryFields(observations, pieces, index, terminalError, true, beforeWriteFs, beforeWriteNow, io.fs(), stdout, stderr, exit);
      assert LifetimeEvidence(observations,
                              pieces,
                              index,
                              beforeWriteFs,
                              beforeWriteNow,
                              io.fs(),
                              exit,
                              lifetimeEvents,
                              true
        );
    } else {
      ghost var observedCommitted := IOContract.WriteResultCommitted(writeFileResult2);
      ghost var observedStage := IOContract.WriteResultStage(writeFileResult2);
      assert IOContract.WriteFileSpec(beforeWriteFs, observations.props, beforeWriteNow,
                                      observations.credentials, observations.filesystem, afterWriteFs,
                                      path, pieces[0], false, err, observedCommitted, observedStage);
      if IOContract.WriteResultStage(writeFileResult2) != BenchWorld.WriteOpenFailed {
        var cleanup := io.DeletePath(path);
        assert Spec.DeleteObservation(observations, afterWriteFs, path,
                                      cleanup.Ok?, IOContract.ResultErrno(cleanup), io.fs());
        assert exists deleteOk: bool, deleteErr: int ::
            Spec.DeleteObservation(observations, afterWriteFs, path,
                                   deleteOk, deleteErr, io.fs());
      }
      assert observedStage == BenchWorld.WriteOpenFailed ==> io.fs() == afterWriteFs;
      assert observedStage != BenchWorld.WriteOpenFailed ==>
          exists deleteOk: bool, deleteErr: int ::
            Spec.DeleteObservation(observations, afterWriteFs, path,
                                   deleteOk, deleteErr, io.fs());
      assert Spec.FailedWriteCleanupRelation(observations, beforeWriteFs, beforeWriteNow, path, pieces[0], err, afterWriteFs, io.fs()) by {
        hide *;
        reveal Spec.FailedWriteCleanupRelation();
        assert exists committed: nat, stage: BenchWorld.FileWriteStage ::
            committed == observedCommitted && stage == observedStage &&
            IOContract.WriteFileSpec(beforeWriteFs, observations.props, beforeWriteNow,
                                     observations.credentials, observations.filesystem, afterWriteFs,
                                     path, pieces[0], false, err, committed, stage) &&
            (if stage == BenchWorld.WriteOpenFailed then io.fs() == afterWriteFs
             else exists deleteOk: bool, deleteErr: int ::
                    Spec.DeleteObservation(observations, afterWriteFs, path,
                                           deleteOk, deleteErr, io.fs()));
      }
      stdout := [];
      stderr := Text.WriteErrorMessage(path, err);
      exit := 1;
      lifetimeEvents := FreshWriteEventList(beforeWriteFs, afterWriteFs, path) +
      LastRemovalEventList(afterWriteFs, io.fs(), path);
      assert stderr == Spec.WriteErrorMessage(OutputName(index), err);
      assert WriteTraceSummaryFields(observations, pieces, index, terminalError, true, beforeWriteFs, beforeWriteNow, io.fs(), stdout, stderr, exit);
    }
  }

  method {:isolate_assertions} WritePiecesThenError(
    pieces: seq<BenchWorld.Bytes>,
    index: nat,
    line: nat,
    io: BenchIO.IO
  ) returns (
      stdout: BenchWorld.Bytes,
      stderr: BenchWorld.Bytes,
      exit: int,
      ghost lifetimeEvents: seq<LifetimeMutation>
    )
    modifies io.fsRegion
    ensures WritePiecesThenErrorSummaryFields(old(Spec.Context(io)), pieces, index, line, old(io.fs()), old(io.now()), io.fs(), stdout, stderr, exit)
    ensures WritePiecesThenErrorLifetimeEvidence(old(Spec.Context(io)),
                                                 pieces,
                                                 index,
                                                 line,
                                                 old(io.fs()),
                                                 old(io.now()),
                                                 io.fs(),
                                                 exit,
                                                 lifetimeEvents
            )
    ensures NoFreshObjectAfterLastRemoval(lifetimeEvents)
    decreases |pieces|
  {
    ghost var observations := Spec.Context(io);
    stdout, stderr, exit, lifetimeEvents :=
      WritePiecesThenDiagnostic(pieces, index, OutOfRangeMessage(line), io);
  }

  method {:isolate_assertions} Prepare(raw: Schema.CsplitCmdRaw, io: BenchIO.IO) returns (exit: int, plannedOut: BenchWorld.Bytes, plannedErr: BenchWorld.Bytes)
    modifies io.fsRegion, io.stdinRegion
    ensures PreparedSummary(raw, io, exit, plannedOut, plannedErr)
    decreases *
  {
    ghost var observations := Spec.Context(io);
    plannedOut := [];
    plannedErr := [];

    ghost var preFs := io.fs();
    ghost var preStreams := io.trustedStreams();
    ghost var preStdin := io.stdin();
    ghost var preNow := io.now();
    if raw.mode == Schema.ModeHelp {
      var help := Spec.HelpText();
      plannedOut := plannedOut + help;
      exit := 0;
      assert PreparedSummary(raw, io, exit, plannedOut, plannedErr) by {
        hide *;
        reveal PreparedSummary();
        reveal DeferredReadResultFields();
        reveal Spec.ReadResultFields();
      }
      return;
    }

    if raw.mode == Schema.ModeVersion {
      var version := Spec.VersionText();
      plannedOut := plannedOut + version;
      exit := 0;
      assert PreparedSummary(raw, io, exit, plannedOut, plannedErr) by {
        hide *;
        reveal PreparedSummary();
        reveal DeferredReadResultFields();
        reveal Spec.ReadResultFields();
      }
      return;
    }

    var data: BenchWorld.Bytes := [];
    match raw.input {
      case Stdin =>
      case File(path) =>
        var readResult := io.ReadFile(path);
        assert readResult == DeferredReadResultFields(raw, preFs, preStreams, preStdin);
        match readResult
        case Err(err) =>
          var msg := Text.ReadErrorMessage(raw.input, err);
          plannedErr := msg;
          exit := 1;
          assert DeferredReadResultFields(raw, old(io.fs()), old(io.trustedStreams()), old(io.stdin())) == Result.Err(err);
          assert io.fs() == old(io.fs());
          assert io.stdin() == old(io.stdin());
          assert plannedOut == [];
          assert plannedErr == Spec.ReadErrorMessage(raw.input, err);
          assert PreparedSummary(raw, io, exit, plannedOut, plannedErr) by {
            hide *;
            reveal PreparedSummary();
            reveal Spec.ReadStdinAfterFields();
          }
          return;
        case Ok(fileData) =>
          data := fileData;
          assert DeferredReadResultFields(raw, preFs, preStreams, preStdin) ==
                 Result.Ok(data);
    }

    var numberAnalysis := AnalyzeNumbers(raw.lineNumbers);
    assert numberAnalysis == AnalyzeNumbers(raw.lineNumbers);
    var warnings := numberAnalysis.warnings;
    match numberAnalysis.status
    case NumberZero =>
      assert AnalyzeNumbers(raw.lineNumbers).status == NumberZero;
      var msg := ZeroLineMessage(0);
      plannedErr := plannedErr + warnings + msg;
      exit := 1;
      assert PreparedSummary(raw, io, exit, plannedOut, plannedErr) by {
        hide *;
        reveal PreparedSummary();
        reveal DeferredReadResultFields();
        reveal Spec.ReadResultFields();
      }
      return;
    case NumberBackwards(current, previous) =>
      assert AnalyzeNumbers(raw.lineNumbers).status ==
             NumberBackwards(current, previous);
      var msg := BackwardLineMessage(current, previous);
      plannedErr := plannedErr + warnings + msg;
      exit := 1;
      assert PreparedSummary(raw, io, exit, plannedOut, plannedErr) by {
        hide *;
        reveal PreparedSummary();
        reveal DeferredReadResultFields();
        reveal Spec.ReadResultFields();
      }
      return;
    case NumbersOk =>

      match raw.input {
        case Stdin =>
          var read := io.ReadStdin();
          if read.Err? {
            var pieces := ReadFailurePieces(IOContract.ReadResultData(read), raw.lineNumbers);
            var faultOut, faultErr, faultExit;
            ghost var lifetimeEvents;
            faultOut, faultErr, faultExit, lifetimeEvents :=
              WritePiecesThenDiagnostic(pieces, 0, Text.ReadErrorMessage(raw.input, read.e), io);
            plannedOut := faultOut;
            plannedErr := warnings + faultErr;
            exit := faultExit;
            assert DeferredReadResultFields(raw, old(io.fs()), old(io.trustedStreams()), old(io.stdin())) == read by {
              reveal DeferredReadResultFields();
              reveal Spec.ReadResultFields();
            }
            assert io.stdin() == Spec.ReadStdinAfterFields(raw.input, old(io.stdin()), old(io.trustedStreams()));
            assert PartialStdinFailureSummary(observations, raw, read.e, old(io.fs()), old(io.now()), io.fs(), plannedOut, plannedErr, exit);
            assert PreparedSummary(raw, io, exit, plannedOut, plannedErr) by {
              hide *;
              reveal PreparedSummary();
            }
            return;
          }
          data := read.v;
        case File(path) =>
      }
      assert DeferredReadResultFields(raw, preFs, preStreams, preStdin) ==
             Result.Ok(data);
      assert io.stdin() == Spec.ReadStdinAfterFields(raw.input, preStdin, old(io.trustedStreams()));

      var splitPlan := SplitPlanFor(data, raw.lineNumbers);
      match splitPlan
      case SplitOutOfRange(pieces, line) =>
        assert splitPlan == SplitPlanFor(data, raw.lineNumbers);
        assert SplitPlanFor(data, raw.lineNumbers) == SplitOutOfRange(pieces, line);
        var out, errOut, writeExit;
        ghost var lifetimeEvents;
        assert plannedOut == [];
        assert plannedErr == [];
        out, errOut, writeExit, lifetimeEvents :=
          WritePiecesThenError(pieces, 0, line, io);
        plannedOut := out;
        plannedErr := warnings + errOut;
        assert plannedOut == out;
        assert plannedErr == warnings + errOut by { hide *; }
        assert warnings == AnalyzeNumbers(raw.lineNumbers).warnings;
        assert plannedErr == (warnings + errOut) by { hide *; }
        exit := writeExit;
        assert WritePiecesThenErrorSummaryFields(observations, pieces, 0, line, preFs, preNow, io.fs(), out, errOut, writeExit);
        assert io.stdin() == Spec.ReadStdinAfterFields(raw.input, preStdin, old(io.trustedStreams()));
        assert PreparedSummary(raw, io, exit, plannedOut, plannedErr) by {
          assert AnalyzeNumbers(raw.lineNumbers).status == NumbersOk;
          assert DeferredReadResultFields(raw, preFs, preStreams, preStdin) ==
                 Result.Ok(data);
          assert WritePiecesThenErrorSummaryFields(observations,
                                                   pieces,
                                                   0,
                                                   line,
                                                   preFs,
                                                   preNow,
                                                   io.fs(),
                                                   out,
                                                   errOut,
                                                   writeExit
            );
          assert plannedOut == out;
          calc {
             plannedErr;
          == (warnings + errOut);
          == AnalyzeNumbers(raw.lineNumbers).warnings + errOut;
          }
          assert exit == writeExit;
          assert exists writeFs: BenchWorld.FileSystem,
              writeOut: BenchWorld.Bytes,
              writeErr: BenchWorld.Bytes,
              witnessedExit: int ::
              WritePiecesThenErrorSummaryFields(observations,
                                                pieces,
                                                0,
                                                line,
                                                preFs,
                                                preNow,
                                                writeFs,
                                                writeOut,
                                                writeErr,
                                                witnessedExit
              ) &&
              io.fs() == writeFs &&
              plannedOut == writeOut &&
              plannedErr ==
              AnalyzeNumbers(raw.lineNumbers).warnings +
              writeErr &&
              exit == witnessedExit;
        }
      case SplitComplete(pieces) =>
        assert splitPlan == SplitPlanFor(data, raw.lineNumbers);
        assert SplitPlanFor(data, raw.lineNumbers) == SplitComplete(pieces);
        var out, errOut, writeExit;
        ghost var lifetimeEvents;
        assert plannedOut == [];
        assert plannedErr == [];
        out, errOut, writeExit, lifetimeEvents :=
          WritePieces(pieces, 0, io);
        plannedOut := out;
        plannedErr := warnings + errOut;
        assert plannedOut == out;
        assert plannedErr == warnings + errOut by { hide *; }
        assert warnings == AnalyzeNumbers(raw.lineNumbers).warnings;
        assert plannedErr == (warnings + errOut) by { hide *; }
        exit := writeExit;
        assert WritePiecesSummaryFields(observations, pieces, 0, preFs, preNow, io.fs(), out, errOut, writeExit);
        assert io.stdin() == Spec.ReadStdinAfterFields(raw.input, preStdin, old(io.trustedStreams()));
        assert PreparedSummary(raw, io, exit, plannedOut, plannedErr) by {
          assert AnalyzeNumbers(raw.lineNumbers).status == NumbersOk;
          assert DeferredReadResultFields(raw, preFs, preStreams, preStdin) ==
                 Result.Ok(data);
          assert WritePiecesSummaryFields(observations,
                                          pieces,
                                          0,
                                          preFs,
                                          preNow,
                                          io.fs(),
                                          out,
                                          errOut,
                                          writeExit
            );
          assert plannedOut == out;
          calc {
             plannedErr;
          == (warnings + errOut);
          == AnalyzeNumbers(raw.lineNumbers).warnings + errOut;
          }
          assert exit == writeExit;
          assert exists writeFs: BenchWorld.FileSystem,
              writeOut: BenchWorld.Bytes,
              writeErr: BenchWorld.Bytes,
              witnessedExit: int ::
              WritePiecesSummaryFields(observations,
                                       pieces,
                                       0,
                                       preFs,
                                       preNow,
                                       writeFs,
                                       writeOut,
                                       writeErr,
                                       witnessedExit
              ) &&
              io.fs() == writeFs &&
              plannedOut == writeOut &&
              plannedErr ==
              AnalyzeNumbers(raw.lineNumbers).warnings +
              writeErr &&
              exit == witnessedExit;
        }
  }

  twostate predicate CoreSummary(raw: Schema.CsplitCmdRaw, io: BenchIO.IO, exit: int)
    reads io.fsRegion, io.stdinRegion, io.stdoutRegion, io.stderrRegion
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
      errors := errors + Text.StreamWriteErrorMessage(message);
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

  method RunCore(raw: Schema.CsplitCmdRaw, io: BenchIO.IO) returns (exit: int)
    modifies io.fsRegion, io.stdinRegion, io.stdoutRegion, io.stderrRegion
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

  function CompletedInputPrefix(data: BenchWorld.Bytes): BenchWorld.Bytes
    ensures Spec.CompleteInputPrefixRelation(data, CompletedInputPrefix(data))
    decreases |data|
  {
    if data == [] || data[|data| - 1] == '\n' then data
    else CompletedInputPrefix(data[..|data| - 1])
  }

  function ReadFailurePieces(data: BenchWorld.Bytes, lines: seq<nat>): seq<BenchWorld.Bytes>
  {
    match SplitPlanFor(CompletedInputPrefix(data), lines)
    case SplitComplete(pieces) => pieces
    case SplitOutOfRange(pieces, _) => pieces
  }

  ghost predicate PartialStdinFailureSummary(observations: Spec.ObservationContext, raw: Schema.CsplitCmdRaw, error: BenchWorld.IOError,
                                             beforeFs: BenchWorld.FileSystem, beforeNow: int, afterFs: BenchWorld.FileSystem,
                                             output: BenchWorld.Bytes, diagnostics: BenchWorld.Bytes, exit: int)
  {
    exists writeDiagnostics: BenchWorld.Bytes ::
      WriteTraceSummaryFields(observations, ReadFailurePieces(IOContract.ReadResultData(Result.Err(error)), raw.lineNumbers),
                              0, Spec.ReadErrorMessage(raw.input, error), true, beforeFs, beforeNow, afterFs,
                              output, writeDiagnostics, exit) &&
      diagnostics == AnalyzeNumbers(raw.lineNumbers).warnings + writeDiagnostics && exit == 1
  }
}
