include "../../core/Errno.dfy"
include "../../core/World.dfy"
include "../../core/IO.dfy"
include "../../core/IOContract.dfy"
include "../../core/StringEscaping.dfy"
include "CsplitSchema.dfy"

module CsplitSpec {
  import StreamContract = IOContract
  import StreamUtf8 = Utf8Semantics

  import Errno = Errnos
  import Result = Results
  import BenchIO
  import Utf8 = Utf8Semantics
  import BenchWorld
  import IOContract
  import Schema = CsplitSchema
  import SE = StringEscaping

  datatype NumberStatus = NumbersOk | NumberZero | NumberBackwards(current: nat, previous: nat)
  datatype SplitPlan = SplitComplete(pieces: seq<BenchWorld.Bytes>) |
                       SplitOutOfRange(pieces: seq<BenchWorld.Bytes>, line: nat)

  datatype ObservationContext = ObservationContext(
    props: map<string, string>,
    now: int,
    credentials: BenchWorld.ProcessCredentials,
    filesystem: (BenchWorld.TrustedFilesystemRequest) -> BenchWorld.TrustedFilesystemResult,
    failures: (BenchWorld.NativeFailureRequest) -> int)

  ghost function Context(io: BenchIO.IO): (observations: ObservationContext)
    reads io.propsRegion, io.nowRegion, io.credentialsRegion,
          io.trustedFilesystemRegion, io.trustedNativeFailuresRegion
    ensures observations == ObservationContext(io.props(), io.now(), io.credentials(),
                                               io.trustedFilesystem(), io.trustedNativeFailures())
  {
    ObservationContext(io.props(), io.now(), io.credentials(),
                       io.trustedFilesystem(), io.trustedNativeFailures())
  }

  ghost predicate WriteObservation(observations: ObservationContext,
                                   beforeFs: BenchWorld.FileSystem, now: int, path: BenchWorld.Path,
                                   data: BenchWorld.Bytes, ok: bool, err: int, afterFs: BenchWorld.FileSystem)
  {
    exists committed: nat, stage: BenchWorld.FileWriteStage ::
      IOContract.WriteFileSpec(beforeFs, observations.props, now,
                               observations.credentials, observations.filesystem, afterFs,
                               path, data, ok, err, committed, stage)
  }

  ghost predicate DeleteObservation(observations: ObservationContext,
                                    beforeFs: BenchWorld.FileSystem, path: BenchWorld.Path,
                                    ok: bool, err: int, afterFs: BenchWorld.FileSystem)
  {
    IOContract.DeletePathSpec(beforeFs, observations.now, observations.failures,
                              afterFs, path, ok, err)
  }

  function HelpText(): BenchWorld.Bytes
  {
    "Usage: csplit [OPTION]... FILE PATTERN...\n"
    + "Output pieces of FILE separated by PATTERN(s) to files 'xx00', 'xx01', ...\n"
    + "\n"
    + "This benchmark slice supports positive numeric line-number patterns only.\n"
    + "With FILE as -, read standard input.  Each numeric pattern N starts the\n"
    + "next output file at line N.  Byte counts are printed after successful\n"
    + "output file creation.\n"
    + "\n"
    + "      --help     display this help and exit\n"
    + "      --version  output version information and exit\n"
  }

  function VersionText(): BenchWorld.Bytes
  {
    "csplit (GNU coreutils) 9.10.13-2cf49\n"
    + "Copyright (C) 2026 Free Software Foundation, Inc.\n"
    + "License GPLv3+: GNU GPL version 3 or later <https://gnu.org/licenses/gpl.html>.\n"
    + "This is free software: you are free to change and redistribute it.\n"
    + "There is NO WARRANTY, to the extent permitted by law.\n"
    + "\n"
    + "Written by Stuart Kemp and David MacKenzie.\n"
  }

  function ReadErrnoText(err: BenchWorld.IOError): string
  {
    match err
    case NoSuchFile => "No such file or directory"
    case IsDirectory => "Is a directory"
    case NotDirectory => "Not a directory"
    case PermissionDenied => "Permission denied"
    case InvalidPath => "Too many levels of symbolic links"
    case Other(msg) => msg
    case ReadFailure(_, message, _, _) => message
    case NativeFailure(_, message) => message
    case WriteFailure(_, message, _, _) => message
    case StreamFailure(_, message, _, _) => message
    case TimeParseFailure(message, _, _) => message
  }

  function WriteErrnoText(err: int): string
  {
    if err == Errno.ENOENT then "No such file or directory"
    else if err == Errno.EACCES then "Permission denied"
    else if err == Errno.ENOTDIR then "Not a directory"
    else if err == Errno.EISDIR then "Is a directory"
    else if err == Errno.EFBIG then "File too large"
    else if err == Errno.ENOSPC then "No space left on device"
    else if err == Errno.ELOOP then "Too many levels of symbolic links"
    else "unknown error"
  }

  function ReadErrorMessagePart1(): BenchWorld.Bytes
  {
    "csplit: read error: "
  }

  function ReadErrorMessagePart2(): BenchWorld.Bytes
  {
    "\n"
  }

  function ReadErrorMessagePart3(): BenchWorld.Bytes
  {
    "csplit: cannot open "
  }

  function ReadErrorMessagePart4(): BenchWorld.Bytes
  {
    " for reading: "
  }

  function ReadErrorMessage(input: Schema.Input, err: BenchWorld.IOError): BenchWorld.Bytes
  {
    match input
    case Stdin => ReadErrorMessagePart1() + Utf8.Encode(ReadErrnoText(err)) + ReadErrorMessagePart2()
    case File(path) =>
      ReadErrorMessagePart3() + SE.SpecQuoteAfBytes(Utf8.Encode(path)) +
      ReadErrorMessagePart4() + Utf8.Encode(ReadErrnoText(err)) + ReadErrorMessagePart2()
  }

  function WriteErrorMessagePart1(): BenchWorld.Bytes
  {
    "csplit: "
  }

  function WriteErrorMessagePart2(): BenchWorld.Bytes
  {
    ": "
  }

  function WriteErrorMessagePart3(): BenchWorld.Bytes
  {
    "\n"
  }

  function WriteErrorMessage(path: BenchWorld.Path, err: int): BenchWorld.Bytes
  {
    WriteErrorMessagePart1() + SE.SpecQuoteFBytes(Utf8.Encode(path)) +
    WriteErrorMessagePart2() + Utf8.Encode(WriteErrnoText(err)) + WriteErrorMessagePart3()
  }

  function ZeroLineMessagePart1(): BenchWorld.Bytes
  {
    "csplit: "
  }

  function ZeroLineMessagePart2(): BenchWorld.Bytes
  {
    ": line number must be greater than zero\n"
  }

  function ZeroLineMessage(line: nat): BenchWorld.Bytes
  {
    ZeroLineMessagePart1() + Schema.DigitsNat(line) + ZeroLineMessagePart2()
  }

  function BackwardLineMessagePart1(): BenchWorld.Bytes
  {
    "csplit: line number '"
  }

  function BackwardLineMessagePart2(): BenchWorld.Bytes
  {
    "' is smaller than preceding line number, "
  }

  function BackwardLineMessagePart3(): BenchWorld.Bytes
  {
    "\n"
  }

  function BackwardLineMessage(current: nat, previous: nat): BenchWorld.Bytes
  {
    BackwardLineMessagePart1() + Schema.DigitsNat(current) + BackwardLineMessagePart2() +
    Schema.DigitsNat(previous) + BackwardLineMessagePart3()
  }

  function OutOfRangeMessagePart1(): BenchWorld.Bytes
  {
    "csplit: '"
  }

  function OutOfRangeMessagePart2(): BenchWorld.Bytes
  {
    "': line number out of range\n"
  }

  function OutOfRangeMessage(line: nat): BenchWorld.Bytes
  {
    OutOfRangeMessagePart1() + Schema.DigitsNat(line) + OutOfRangeMessagePart2()
  }

  function DuplicateWarningPart1(): BenchWorld.Bytes
  {
    "csplit: warning: line number '"
  }

  function DuplicateWarningPart2(): BenchWorld.Bytes
  {
    "' is the same as preceding line number\n"
  }

  function DuplicateWarning(line: nat): BenchWorld.Bytes
  {
    DuplicateWarningPart1() + Schema.DigitsNat(line) + DuplicateWarningPart2()
  }

  function CountLinePart1(): BenchWorld.Bytes
  {
    "\n"
  }

  function CountLine(n: nat): BenchWorld.Bytes
  {
    Schema.DigitsNat(n) + CountLinePart1()
  }

  function OutputNamePart1(): BenchWorld.Bytes
  {
    "xx0"
  }

  function OutputNamePart2(): BenchWorld.Bytes
  {
    "xx"
  }

  function OutputName(index: nat): BenchWorld.Path
  {
    if index < 10 then
      OutputNamePart1() + Schema.DigitsNat(index)
    else
      OutputNamePart2() + Schema.DigitsNat(index)
  }

  ghost predicate ValidNumberPrefix(lines: seq<nat>, count: nat)
  {
    count <= |lines| &&
    forall i :: 0 <= i < count ==>
                  lines[i] > 0 &&
                  (i == 0 || lines[i - 1] <= lines[i])
  }

  ghost predicate NumberStatusRelation(lines: seq<nat>, status: NumberStatus)
  {
    exists processed: nat ::
      NumberStatusAtRelation(lines, status, processed)
  }

  ghost predicate NumberStatusAtRelation(
    lines: seq<nat>,
    status: NumberStatus,
    processed: nat
  )
  {
    processed <= |lines| &&
    ValidNumberPrefix(lines, processed) &&
    match status
    case NumbersOk =>
      processed == |lines|
    case NumberZero =>
      processed < |lines| &&
      lines[processed] == 0
    case NumberBackwards(current, previous) =>
      0 < processed < |lines| &&
      lines[processed] > 0 &&
      current == lines[processed] &&
      previous == lines[processed - 1] &&
      current < previous
  }

  ghost predicate LineCutRelation(data: BenchWorld.Bytes, line: nat, cut: nat)
  {
    if line <= 1 then
      cut == 0
    else if multiset(data)['\n'] < line - 1 then
      cut == |data|
    else
      0 < cut <= |data| &&
      data[cut - 1] == '\n' &&
      multiset(data[..cut])['\n'] == line - 1
  }

  ghost predicate PiecePartitionRelation(
    data: BenchWorld.Bytes,
    pieces: seq<BenchWorld.Bytes>,
    cuts: seq<nat>
  )
  {
    |cuts| == |pieces| + 1 &&
    cuts[0] == 0 &&
    cuts[|cuts| - 1] == |data| &&
    forall i {:trigger cuts[i]} :: 0 <= i < |pieces| ==>
                                     cuts[i] <= cuts[i + 1] <= |data| &&
                                     pieces[i] == data[cuts[i]..cuts[i + 1]]
  }

  // Deferred GNU behavior: regular-expression contexts, repeat counts, custom
  // prefixes/suffixes, suppress-matched, quiet mode, and eliding empty files are
  // outside this benchmark slice.  The formal relation intentionally covers
  // decoded numeric line patterns and their write/cleanup transitions.
  ghost predicate SplitPlanRelation(
    data: BenchWorld.Bytes,
    lines: seq<nat>,
    plan: SplitPlan
  )
  {
    match plan
    case SplitComplete(pieces) =>
      exists cuts: seq<nat> ::
        |cuts| == |lines| + 2 &&
        PiecePartitionRelation(data, pieces, cuts) &&
        (forall i :: 0 <= i < |lines| ==>
                       LineCutRelation(data, lines[i], cuts[i + 1]) &&
                       cuts[i + 1] < |data|)
    case SplitOutOfRange(pieces, line) =>
      exists failed: nat, cuts: seq<nat> ::
        failed < |lines| &&
        line == lines[failed] &&
        |cuts| == failed + 2 &&
        PiecePartitionRelation(data, pieces, cuts) &&
        (forall i :: 0 <= i <= failed ==>
                       LineCutRelation(data, lines[i], cuts[i + 1])) &&
        (forall i {:trigger cuts[i + 1]} ::
           0 <= i < failed ==> cuts[i + 1] < |data|) &&
        cuts[failed + 1] == |data|
  }

  ghost predicate FragmentsConcatenate(
    fragments: seq<BenchWorld.Bytes>,
    combined: BenchWorld.Bytes,
    cuts: seq<nat>
  )
  {
    |cuts| == |fragments| + 1 &&
    cuts[0] == 0 &&
    cuts[|cuts| - 1] == |combined| &&
    forall i {:trigger cuts[i]} :: 0 <= i < |fragments| ==>
                                     cuts[i] <= cuts[i + 1] <= |combined| &&
                                     cuts[i + 1] == cuts[i] + |fragments[i]| &&
                                     combined[cuts[i]..cuts[i + 1]] == fragments[i]
  }

  ghost predicate DuplicateWarningsRelation(
    lines: seq<nat>,
    warnings: BenchWorld.Bytes
  )
  {
    exists fragments: seq<BenchWorld.Bytes>, cuts: seq<nat> ::
      |fragments| == |lines| &&
      (forall i :: 0 <= i < |lines| ==>
                     fragments[i] ==
                     if i > 0 && lines[i] == lines[i - 1]
                     then DuplicateWarning(lines[i])
                     else []) &&
      FragmentsConcatenate(fragments, warnings, cuts)
  }

  ghost predicate NumberAnalysisRelation(
    lines: seq<nat>,
    status: NumberStatus,
    processed: nat,
    warnings: BenchWorld.Bytes
  )
  {
    NumberStatusAtRelation(lines, status, processed) &&
    DuplicateWarningsRelation(lines[..processed], warnings)
  }

  ghost function ReadStdinAfterFields(input: Schema.Input, preStdin: BenchWorld.Bytes, preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult): BenchWorld.Bytes
  {
    match input
    case Stdin => IOContract.ObservedReadStdinRemainingFields(preStdin, preStreams)
    case File(_) => preStdin
  }

  ghost function ReadResultFields(
    input: Schema.Input,
    preFs: BenchWorld.FileSystem,
    preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult,
    preStdin: BenchWorld.Bytes
  ): BenchWorld.IOResult<BenchWorld.Bytes>
  {
    match input
    case Stdin => IOContract.ObservedReadStdinResultFields(preStdin, preStreams)
    case File(path) => IOContract.ObservedReadFileResultFields(preFs, preStreams, path)
  }

  ghost function DeferredReadResultFields(raw: Schema.CsplitCmdRaw,
                                          preFs: BenchWorld.FileSystem,
                                          preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult,
                                          preStdin: BenchWorld.Bytes): BenchWorld.IOResult<BenchWorld.Bytes>
  {
    if raw.input.Stdin? && !ValidNumberPrefix(raw.lineNumbers, |raw.lineNumbers|) then
      Result.Ok(preStdin)
    else ReadResultFields(raw.input, preFs, preStreams, preStdin)
  }

  // A failed open preserves its entry; a failed write/close removes the opened output.
  ghost predicate FailedWriteCleanupRelation(observations: ObservationContext,
                                             preFs: BenchWorld.FileSystem, now: int, path: BenchWorld.Path, data: BenchWorld.Bytes,
                                             err: int, afterWriteFs: BenchWorld.FileSystem, afterCleanupFs: BenchWorld.FileSystem
  )
  {
    exists committed: nat, stage: BenchWorld.FileWriteStage ::
      IOContract.WriteFileSpec(preFs, observations.props, now,
                               observations.credentials, observations.filesystem, afterWriteFs,
                               path, data, false, err, committed, stage) &&
      (if stage == BenchWorld.WriteOpenFailed then afterCleanupFs == afterWriteFs
       else exists deleteOk: bool, deleteErr: int ::
              DeleteObservation(observations, afterWriteFs, path, deleteOk, deleteErr, afterCleanupFs))
  }

  ghost predicate WriteAttemptsRelation(observations: ObservationContext,
                                        pieces: seq<BenchWorld.Bytes>,
                                        index: nat,
                                        count: nat,
                                        preFs: BenchWorld.FileSystem,
                                        preNow: int,
                                        states: seq<BenchWorld.FileSystem>,
                                        oks: seq<bool>,
                                        errs: seq<int>
  )
  {
    count <= |pieces| &&
    |states| == count + 1 &&
    |oks| == count &&
    |errs| == count &&
    states[0] == preFs &&
    forall i :: 0 <= i < count ==>
                  WriteObservation(observations,
                                   states[i],
                                   preNow,
                                   OutputName(index + i),
                                   pieces[i],
                                   oks[i],
                                   errs[i],
                                   states[i + 1]
                  )
  }

  ghost predicate CleanupWitnessRelation(observations: ObservationContext,
                                         index: nat,
                                         count: nat,
                                         preFs: BenchWorld.FileSystem,
                                         fs2: BenchWorld.FileSystem,
                                         states: seq<BenchWorld.FileSystem>,
                                         oks: seq<bool>,
                                         errs: seq<int>
  )
  {
    |states| == count + 1 &&
    states[0] == preFs &&
    states[count] == fs2 &&
    |oks| == count &&
    |errs| == count &&
    forall i :: 0 <= i < count ==>
                  DeleteObservation(observations,
                                    states[i],
                                    OutputName(index + count - 1 - i),
                                    oks[i],
                                    errs[i],
                                    states[i + 1]
                  )
  }

  ghost predicate CleanupRelation(observations: ObservationContext,
                                  index: nat,
                                  count: nat,
                                  preFs: BenchWorld.FileSystem,
                                  fs2: BenchWorld.FileSystem,
                                  states: seq<BenchWorld.FileSystem>
  )
  {
    exists oks: seq<bool>, errs: seq<int> ::
      CleanupWitnessRelation(observations,
                             index, count, preFs, fs2, states, oks, errs
      )
  }

  ghost predicate CountOutputRelation(
    pieces: seq<BenchWorld.Bytes>,
    count: nat,
    output: BenchWorld.Bytes
  )
  {
    count <= |pieces| &&
    exists fragments: seq<BenchWorld.Bytes>, cuts: seq<nat> ::
      |fragments| == count &&
      (forall i :: 0 <= i < count ==>
                     fragments[i] == CountLine(|pieces[i]|)) &&
      FragmentsConcatenate(fragments, output, cuts)
  }

  ghost predicate WriteTraceWitnessRelation(observations: ObservationContext,
                                            pieces: seq<BenchWorld.Bytes>,
                                            index: nat,
                                            terminalError: BenchWorld.Bytes,
                                            hasTerminalError: bool,
                                            preFs: BenchWorld.FileSystem,
                                            preNow: int,
                                            fs2: BenchWorld.FileSystem,
                                            stdout: BenchWorld.Bytes,
                                            stderr: BenchWorld.Bytes,
                                            exit: int,
                                            attempted: nat,
                                            writeStates: seq<BenchWorld.FileSystem>,
                                            writeOk: seq<bool>,
                                            writeErr: seq<int>,
                                            cleanupStates: seq<BenchWorld.FileSystem>
  )
  {
    attempted <= |pieces| &&
    WriteAttemptsRelation(observations,
                          pieces, index, attempted, preFs, preNow, writeStates, writeOk, writeErr
    ) &&
    (forall i :: 0 <= i && i + 1 < attempted ==> writeOk[i]) &&
    if attempted > 0 && !writeOk[attempted - 1] then
      CountOutputRelation(pieces, attempted - 1, stdout) &&
      |cleanupStates| > 0 &&
      FailedWriteCleanupRelation(observations, writeStates[attempted - 1], preNow,
                                 OutputName(index + attempted - 1), pieces[attempted - 1], writeErr[attempted - 1],
                                 writeStates[attempted], cleanupStates[0]) &&
      CleanupRelation(observations, index, attempted - 1, cleanupStates[0], fs2, cleanupStates) &&
      stderr == WriteErrorMessage(
        OutputName(index + attempted - 1),
        writeErr[attempted - 1]
      ) &&
      exit == 1
    else
      attempted == |pieces| &&
      (forall i :: 0 <= i < attempted ==> writeOk[i]) &&
      CountOutputRelation(pieces, attempted, stdout) &&
      if hasTerminalError then
        CleanupRelation(observations,
                        index, attempted, writeStates[attempted], fs2, cleanupStates
        ) &&
        stderr == terminalError &&
        exit == 1
      else
        fs2 == writeStates[attempted] &&
        stderr == [] &&
        exit == 0
  }

  ghost predicate WriteTraceRelation(observations: ObservationContext,
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
  {
    exists attempted: nat,
      writeStates: seq<BenchWorld.FileSystem>,
      writeOk: seq<bool>,
      writeErr: seq<int>,
      cleanupStates: seq<BenchWorld.FileSystem> ::
      WriteTraceWitnessRelation(observations,
                                pieces,
                                index,
                                terminalError,
                                hasTerminalError,
                                preFs,
                                preNow,
                                fs2,
                                stdout,
                                stderr,
                                exit,
                                attempted,
                                writeStates,
                                writeOk,
                                writeErr,
                                cleanupStates
      )
  }

  ghost predicate WritePiecesSummaryFields(observations: ObservationContext,
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
    WriteTraceRelation(observations,
                       pieces, index, [], false, preFs, preNow, fs2, stdout, stderr, exit
    )
  }

  ghost predicate WritePiecesThenErrorSummaryFields(observations: ObservationContext,
                                                    pieces: seq<BenchWorld.Bytes>,
                                                    index: nat,
                                                    line: nat,
                                                    preFs: BenchWorld.FileSystem,
                                                    preNow: int,
                                                    fs2: BenchWorld.FileSystem,
                                                    stdout: BenchWorld.Bytes,
                                                    stderr: BenchWorld.Bytes,
                                                    exit: int
  ) {
    WriteTraceRelation(observations,
                       pieces,
                       index,
                       OutOfRangeMessage(line),
                       true,
                       preFs,
                       preNow,
                       fs2,
                       stdout,
                       stderr,
                       exit
    )
  }

  twostate predicate PreparedSpec(raw: Schema.CsplitCmdRaw, io: BenchIO.IO, exit: int, plannedStdout: BenchWorld.Bytes, plannedStderr: BenchWorld.Bytes)
    reads io.fsRegion, io.stdinRegion
  {
    if raw.mode == Schema.ModeHelp then
      io.fs() == old(io.fs()) &&
      io.stdin() == old(io.stdin()) &&
      plannedStdout == HelpText() &&
      plannedStderr == [] &&
      exit == 0
    else if raw.mode == Schema.ModeVersion then
      io.fs() == old(io.fs()) &&
      io.stdin() == old(io.stdin()) &&
      plannedStdout == VersionText() &&
      plannedStderr == [] &&
      exit == 0
    else
      match DeferredReadResultFields(raw, old(io.fs()), old(io.trustedStreams()), old(io.stdin()))
      case Err(err) =>
        io.stdin() == ReadStdinAfterFields(raw.input, old(io.stdin()), old(io.trustedStreams())) &&
        (if raw.input.Stdin? then
           PartialStdinFailureFields(old(Context(io)), raw, err, old(io.fs()), old(io.now()), io.fs(), plannedStdout, plannedStderr, exit)
         else
           io.fs() == old(io.fs()) && plannedStdout == [] &&
           plannedStderr == ReadErrorMessage(raw.input, err) && exit == 1)
      case Ok(data) =>
        exists numberStatus: NumberStatus, processed: nat,
          warnings: BenchWorld.Bytes ::
          NumberAnalysisRelation(
            raw.lineNumbers, numberStatus, processed, warnings
          ) &&
          match numberStatus
          case NumberZero =>
            io.fs() == old(io.fs()) &&
            io.stdin() == old(io.stdin()) &&
            plannedStdout == [] &&
            plannedStderr ==
            warnings + ZeroLineMessage(0) &&
            exit == 1
          case NumberBackwards(current, previous) =>
            io.fs() == old(io.fs()) &&
            io.stdin() == old(io.stdin()) &&
            plannedStdout == [] &&
            plannedStderr ==
            warnings +
            BackwardLineMessage(current, previous) &&
            exit == 1
          case NumbersOk =>
            io.stdin() == ReadStdinAfterFields(raw.input, old(io.stdin()), old(io.trustedStreams())) &&
            exists splitPlan: SplitPlan ::
              SplitPlanRelation(data, raw.lineNumbers, splitPlan) &&
              match splitPlan
              case SplitOutOfRange(pieces, line) =>
                exists writeFs: BenchWorld.FileSystem, writeOut: BenchWorld.Bytes,
                  writeErr: BenchWorld.Bytes, writeExit: int ::
                  WritePiecesThenErrorSummaryFields(old(Context(io)),
                                                    pieces,
                                                    0,
                                                    line,
                                                    old(io.fs()),
                                                    old(io.now()),
                                                    writeFs,
                                                    writeOut,
                                                    writeErr,
                                                    writeExit
                  ) &&
                  io.fs() == writeFs &&
                  plannedStdout == writeOut &&
                  plannedStderr == warnings + writeErr &&
                  exit == writeExit
              case SplitComplete(pieces) =>
                exists writeFs: BenchWorld.FileSystem, writeOut: BenchWorld.Bytes,
                  writeErr: BenchWorld.Bytes, writeExit: int ::
                  WritePiecesSummaryFields(old(Context(io)),
                                           pieces,
                                           0,
                                           old(io.fs()),
                                           old(io.now()),
                                           writeFs,
                                           writeOut,
                                           writeErr,
                                           writeExit
                  ) &&
                  io.fs() == writeFs &&
                  plannedStdout == writeOut &&
                  plannedStderr == warnings + writeErr &&
                  exit == writeExit
  }

  function Emits(raw: Schema.CsplitCmdRaw): bool
  {
    true
  }

  function StreamWriteErrorMessagePart1(): BenchWorld.Bytes
  {
    "csplit: write error: "
  }

  function StreamWriteErrorMessagePart2(): BenchWorld.Bytes
  {
    "\n"
  }

  function StreamWriteErrorMessage(message: string): BenchWorld.Bytes
  {
    StreamUtf8.Encode(StreamWriteErrorMessagePart1() + message + StreamWriteErrorMessagePart2())
  }

  ghost predicate EmitFields(
    observations: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult,
    beforeStdout: BenchWorld.Bytes, beforeStderr: BenchWorld.Bytes,
    afterStdout: BenchWorld.Bytes, afterStderr: BenchWorld.Bytes,
    out: BenchWorld.Bytes, diagnostics: BenchWorld.Bytes,
    normalExit: int, exit: int
  )
  {
    var stdoutResult := if out == [] then BenchWorld.StreamWriteResult(0, beforeStdout, 0)
                        else observations(BenchWorld.StreamWriteStdout(beforeStdout, out));
    stdoutResult.StreamWriteResult? &&
    var errors := diagnostics + (if stdoutResult.err == 0 then [] else
                                 StreamWriteErrorMessage(StreamContract.CLocaleErrnoTextResult(stdoutResult.err)));
    var stderrResult := if errors == [] then BenchWorld.StreamWriteResult(0, beforeStderr, 0)
                        else observations(BenchWorld.StreamWriteStderr(beforeStderr, errors));
    stderrResult.StreamWriteResult? &&
    (if out == [] then afterStdout == beforeStdout else StreamContract.WriteStdoutSpec(
       beforeStdout, observations, afterStdout, out, stdoutResult.committed, stdoutResult.err)) &&
    (if errors == [] then afterStderr == beforeStderr else StreamContract.WriteStderrSpec(
       beforeStderr, observations, afterStderr, errors, stderrResult.committed, stderrResult.err)) &&
    exit == (if stdoutResult.err != 0 || stderrResult.err != 0 then 1 else normalExit)
  }

  twostate predicate Emission(raw: Schema.CsplitCmdRaw, io: BenchIO.IO,
                              out: BenchWorld.Bytes, diagnostics: BenchWorld.Bytes,
                              normalExit: int, exit: int)
    reads io.stdoutRegion, io.stderrRegion
  {
    if Emits(raw) then
      EmitFields(old(io.trustedStreams()), old(io.stdout()), old(io.stderr()),
                 io.stdout(), io.stderr(), out, diagnostics, normalExit, exit)
    else
      io.stdout() == old(io.stdout()) && io.stderr() == old(io.stderr()) &&
      exit == normalExit
  }

  twostate predicate Spec(raw: Schema.CsplitCmdRaw, io: BenchIO.IO, exit: int)
    reads io.fsRegion, io.stdinRegion, io.stdoutRegion, io.stderrRegion
  {
    exists out: BenchWorld.Bytes, diagnostics: BenchWorld.Bytes, normalExit: int ::
      PreparedSpec(raw, io, normalExit,
                   out, diagnostics) &&
      Emission(raw, io, out, diagnostics, normalExit, exit)
  }

  ghost predicate CompleteInputPrefixRelation(data: BenchWorld.Bytes, complete: BenchWorld.Bytes)
  {
    |complete| <= |data| && complete == data[..|complete|] &&
    (complete == [] || complete[|complete| - 1] == '\n') &&
    forall i: nat | |complete| <= i < |data| :: data[i] != '\n'
  }

  ghost predicate ReadFailurePiecesRelation(data: BenchWorld.Bytes, lines: seq<nat>,
                                            pieces: seq<BenchWorld.Bytes>)
  {
    exists complete: BenchWorld.Bytes, plan: SplitPlan ::
      CompleteInputPrefixRelation(data, complete) && SplitPlanRelation(complete, lines, plan) &&
      (match plan
       case SplitComplete(planned) => pieces == planned
       case SplitOutOfRange(planned, _) => pieces == planned)
  }

  ghost predicate PartialStdinFailureFields(observations: ObservationContext, raw: Schema.CsplitCmdRaw, error: BenchWorld.IOError,
                                            beforeFs: BenchWorld.FileSystem, beforeNow: int, afterFs: BenchWorld.FileSystem,
                                            output: BenchWorld.Bytes, diagnostics: BenchWorld.Bytes, exit: int)
  {
    exists pieces: seq<BenchWorld.Bytes>, warnings: BenchWorld.Bytes, writeDiagnostics: BenchWorld.Bytes ::
      DuplicateWarningsRelation(raw.lineNumbers, warnings) &&
      ReadFailurePiecesRelation(IOContract.ReadResultData(Result.Err(error)), raw.lineNumbers, pieces) &&
      WriteTraceRelation(observations, pieces, 0, ReadErrorMessage(raw.input, error), true,
                         beforeFs, beforeNow, afterFs, output, writeDiagnostics, exit) &&
      diagnostics == warnings + writeDiagnostics && exit == 1
  }
}
