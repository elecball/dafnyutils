include "../../core/World.dfy"
include "../../core/IO.dfy"
include "../../core/IOContract.dfy"
include "PasteSchema.dfy"
include "../../core/StringEscaping.dfy"

module PasteSpec {

  const ErrorMessageText0: BenchWorld.Bytes := "paste: "

  const ErrorMessageText1: BenchWorld.Bytes := ": "

  const ErrorMessageText2: BenchWorld.Bytes := "\n"

  const DelimiterBackslashErrorText0: BenchWorld.Bytes := "paste: delimiter list ends with an unescaped backslash: "

  const DelimiterBackslashErrorText1: BenchWorld.Bytes := "\n"

  const StreamWriteErrorMessageText0: BenchWorld.Bytes := "paste: write error: "

  const StreamWriteErrorMessageText1: BenchWorld.Bytes := "\n"

  import StreamContract = IOContract
  import StreamUtf8 = Utf8Semantics

  import Result = Results
  import BenchIO
  import Utf8 = Utf8Semantics
  import BenchWorld
  import IOContract
  import PasteSchema
  import SE = StringEscaping

  datatype Entry = Entry(lines: seq<BenchWorld.Bytes>, readOk: bool)
  type DelimPlan = Result.Result<seq<BenchWorld.Bytes>, BenchWorld.Bytes>
  datatype InputObservation = InputObservation(
    result: BenchWorld.IOResult<BenchWorld.Bytes>,
    entry: Entry,
    errorPiece: BenchWorld.Bytes,
    failed: bool,
    blocking: bool
  )




  function HelpText(): BenchWorld.Bytes
  {
    "Usage: paste [OPTION]... [FILE]...\n"
    + "Write lines consisting of the sequentially corresponding lines from\n"
    + "each FILE, separated by TABs, to standard output.\n"
    + "With no FILE, or when FILE is -, read standard input.\n"
    + "\n"
    + "  -d, --delimiters=LIST   reuse characters from LIST instead of TABs\n"
    + "  -s, --serial            paste one file at a time instead of in parallel\n"
    + "  -z, --zero-terminated    line delimiter is NUL, not newline\n"
    + "      --help              display this help and exit\n"
    + "      --version           output version information and exit\n"
    + "\n"
    + "Report bugs to: bug-coreutils@gnu.org\n"
    + "GNU coreutils home page: <https://www.gnu.org/software/coreutils/>\n"
    + "General help using GNU software: <https://www.gnu.org/gethelp/>\n"
    + "Full documentation <https://www.gnu.org/software/coreutils/paste>\n"
    + "or available locally via: info '(coreutils) paste invocation'\n"
  }

  function VersionText(): BenchWorld.Bytes
  {
    "paste (GNU coreutils) 9.10.13-2cf49\n"
    + "Copyright (C) 2026 Free Software Foundation, Inc.\n"
    + "License GPLv3+: GNU GPL version 3 or later <https://gnu.org/licenses/gpl.html>.\n"
    + "This is free software: you are free to change and redistribute it.\n"
    + "There is NO WARRANTY, to the extent permitted by law.\n"
    + "\n"
    + "Written by David M. Ihnat and David MacKenzie.\n"
  }

  function ErrnoText(err: BenchWorld.IOError): string
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

  ghost function NeedsErrorQuoting(path: string): bool
  {
    var bytes := Utf8.Encode(path);
    |bytes| == 0 || SE.SpecHasShellQuoteTrigger(bytes)
  }

  ghost function ErrorMessage(path: BenchWorld.Path, err: BenchWorld.IOError): BenchWorld.Bytes
  {
    ErrorMessageText0 + SE.SpecQuoteFBytes(Utf8.Encode(path)) +
    ErrorMessageText1 + Utf8.Encode(ErrnoText(err)) + ErrorMessageText2
  }

  ghost function DelimiterBackslashError(text: BenchWorld.Bytes): BenchWorld.Bytes
  {
    var rendered :=
      if exists i: nat :: i < |text| &&
                          (text[i] == ':' || text[i] == '"' || !SE.SpecCPrintableByte(text[i]))
      then SE.SpecDoubleQuote(text)
      else text;
    DelimiterBackslashErrorText0 + rendered + DelimiterBackslashErrorText1
  }

  function RecordDelimiter(zeroTerminated: bool): BenchWorld.RawByte
  {
    if zeroTerminated then '\0' else '\n'
  }

  ghost predicate FragmentsConcatenate<T>(
    fragments: seq<seq<T>>,
    combined: seq<T>,
    cuts: seq<nat>
  )
  {
    |cuts| == |fragments| + 1 &&
    cuts[0] == 0 &&
    cuts[|cuts| - 1] == |combined| &&
    forall i: nat {:trigger cuts[i]} | i < |fragments| ::
      cuts[i] <= cuts[i + 1] <= |combined| &&
      cuts[i + 1] == cuts[i] + |fragments[i]| &&
      combined[cuts[i]..cuts[i + 1]] == fragments[i]
  }

  ghost predicate LinePartitionRelation(
    data: BenchWorld.Bytes,
    recordDelimiter: BenchWorld.RawByte,
    lines: seq<BenchWorld.Bytes>,
    terminated: seq<bool>,
    fragments: seq<BenchWorld.Bytes>,
    cuts: seq<nat>
  )
  {
    |lines| == |terminated| == |fragments| &&
    FragmentsConcatenate(fragments, data, cuts) &&
    (forall i: nat | i < |lines| ::
       |fragments[i]| > 0 &&
       fragments[i] ==
       lines[i] + (if terminated[i] then [recordDelimiter] else []) &&
       recordDelimiter !in lines[i] &&
       (i + 1 < |lines| ==> terminated[i]))
  }

  ghost predicate ReadResultRelation(
    cmd: PasteSchema.PasteCmd,
    preFs: BenchWorld.FileSystem, preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult,
    preStdin: BenchWorld.Bytes,
    i: nat,
    result: BenchWorld.IOResult<BenchWorld.Bytes>
  )
    requires i < |cmd.inputs|
  {
    match cmd.inputs[i]
    case Stdin =>
      result == IOContract.ObservedReadStdinResultFields(preStdin, preStreams)
    case File(path) =>
      result == IOContract.ObservedReadFileResultFields(preFs, preStreams, path)
  }

  function BlockingReadFailure(err: BenchWorld.IOError): bool
  {
    !IOContract.IOErrorIsDirectory(err) && !err.StreamFailure? &&
    !(err.ReadFailure? && err.readStage != BenchWorld.OpenFailed)
  }

  ghost predicate EntryRelation(
    result: BenchWorld.IOResult<BenchWorld.Bytes>,
                                recordDelimiter: BenchWorld.RawByte,
                                entry: Entry
  )
  {
    entry.readOk == (result.Ok? || !BlockingReadFailure(result.e)) &&
    exists terminated: seq<bool>,
      fragments: seq<BenchWorld.Bytes>,
      cuts: seq<nat> ::
      LinePartitionRelation(
        IOContract.ReadResultData(result), recordDelimiter, entry.lines, terminated, fragments, cuts)
  }

  ghost predicate InputObservationRelation(
    cmd: PasteSchema.PasteCmd,
    preFs: BenchWorld.FileSystem, preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult,
    preStdin: BenchWorld.Bytes,
    i: nat,
    observation: InputObservation
  )
    requires i < |cmd.inputs|
  {
    ReadResultRelation(
      cmd, preFs, preStreams, preStdin, i, observation.result) &&
    EntryRelation(
      observation.result,
      RecordDelimiter(cmd.zeroTerminated),
      observation.entry) &&
    match cmd.inputs[i]
    case Stdin =>
      observation.errorPiece == (if observation.result.Ok? then []
                                 else ErrorMessage("-", observation.result.e)) &&
      observation.failed == observation.result.Err? &&
      !observation.blocking
    case File(path) =>
      match observation.result
      case Ok(_) =>
        observation.errorPiece == [] &&
        !observation.failed &&
        !observation.blocking
      case Err(err) =>
        observation.errorPiece == ErrorMessage(path, err) &&
        observation.failed &&
        observation.blocking == BlockingReadFailure(err)
  }

  ghost function ObservationEntries(
    observations: seq<InputObservation>
  ): seq<Entry>
  {
    seq(
    |observations|,
    i requires 0 <= i < |observations| => observations[i].entry)
  }

  ghost predicate SelectedLinesRelation(
    stdinLines: seq<BenchWorld.Bytes>,
    stdinIndex: nat,
    stdinCount: nat,
    selected: seq<BenchWorld.Bytes>
  )
  {
    stdinCount > 0 &&
    (forall k: nat | k < |selected| ::
       stdinIndex + k * stdinCount < |stdinLines| &&
       selected[k] == stdinLines[stdinIndex + k * stdinCount]) &&
    (|selected| == 0 ==> stdinIndex >= |stdinLines|) &&
    (|selected| > 0 ==>
       stdinIndex + (|selected| - 1) * stdinCount < |stdinLines| &&
       stdinIndex + |selected| * stdinCount >= |stdinLines|)
  }

  ghost predicate HasStdinInput(inputs: seq<PasteSchema.Input>)
  {
    PasteSchema.Stdin in inputs
  }

  ghost predicate StdinPositionsRelation(
    inputs: seq<PasteSchema.Input>,
    positions: seq<nat>
  )
  {
    (forall k: nat | k < |positions| ::
       positions[k] < |inputs| &&
       inputs[positions[k]] == PasteSchema.Stdin &&
       (k > 0 ==> positions[k - 1] < positions[k])) &&
    (forall i: nat | i < |inputs| ::
       inputs[i] == PasteSchema.Stdin ==> i in positions)
  }

  datatype EntriesForOutputWitness = EntriesForOutputWitness(
    positions: seq<nat>,
    stdinLines: seq<BenchWorld.Bytes>,
    terminated: seq<bool>,
    fragments: seq<BenchWorld.Bytes>,
    cuts: seq<nat>
  )

  ghost predicate ParallelEntriesForOutputRelation(
    cmd: PasteSchema.PasteCmd,
    preStdin: BenchWorld.Bytes,
    rawEntries: seq<Entry>,
    entries: seq<Entry>,
    trace: EntriesForOutputWitness
  )
  {
    |rawEntries| == |cmd.inputs| &&
    |entries| == |cmd.inputs| &&
    StdinPositionsRelation(cmd.inputs, trace.positions) &&
    LinePartitionRelation(
      if HasStdinInput(cmd.inputs) then preStdin else [],
      RecordDelimiter(cmd.zeroTerminated),
      trace.stdinLines,
      trace.terminated,
      trace.fragments,
      trace.cuts) &&
    forall i: nat | i < |cmd.inputs| ::
      match cmd.inputs[i]
      case File(_) =>
        entries[i] == rawEntries[i]
      case Stdin =>
        exists rank: nat, selected: seq<BenchWorld.Bytes> ::
          rank < |trace.positions| &&
          trace.positions[rank] == i &&
          SelectedLinesRelation(
            trace.stdinLines,
            rank,
            |trace.positions|,
            selected) &&
          entries[i] == Entry(selected, true)
  }

  ghost predicate EntriesForOutputRelation(
    cmd: PasteSchema.PasteCmd,
    preStdin: BenchWorld.Bytes,
    rawEntries: seq<Entry>,
    entries: seq<Entry>
  )
  {
    if cmd.serial then
      entries == rawEntries
    else
      exists trace: EntriesForOutputWitness ::
        ParallelEntriesForOutputRelation(
          cmd, preStdin, rawEntries, entries, trace)
  }

  datatype VisibleErrorAssembly =
    VisibleErrorsDone |
    VisibleErrorStep(
      previous: BenchWorld.Bytes,
      rest: VisibleErrorAssembly)

  ghost predicate VisibleErrorPrefixRelation(
    serial: bool,
    observations: seq<InputObservation>,
    i: nat,
    output: BenchWorld.Bytes,
    assembly: VisibleErrorAssembly
  )
    decreases assembly
  {
    i <= |observations| &&
    match assembly
    case VisibleErrorsDone =>
      i == 0 && output == []
    case VisibleErrorStep(previous, rest) =>
      i > 0 &&
      VisibleErrorPrefixRelation(
        serial, observations, i - 1, previous, rest) &&
      output ==
      if serial then
        previous + observations[i - 1].errorPiece
      else if exists j: nat ::
                j < i - 1 && observations[j].blocking then
        previous
      else if observations[i - 1].blocking then
        observations[i - 1].errorPiece
      else
        previous + observations[i - 1].errorPiece
  }

  ghost predicate VisibleErrorRelation(
    serial: bool,
    observations: seq<InputObservation>,
    output: BenchWorld.Bytes
  )
  {
    exists assembly: VisibleErrorAssembly ::
      VisibleErrorPrefixRelation(
        serial, observations, |observations|, output, assembly)
  }

  ghost predicate InputTraceRelation(
    cmd: PasteSchema.PasteCmd,
    preFs: BenchWorld.FileSystem, preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult,
    preStdin: BenchWorld.Bytes,
    postStdin: BenchWorld.Bytes,
    entries: seq<Entry>,
    errorOutput: BenchWorld.Bytes,
    hadError: bool,
    hadBlockingError: bool
  )
  {
    exists observations: seq<InputObservation>, states: seq<BenchWorld.Bytes>,
      stdinData: BenchWorld.Bytes, cuts: seq<nat> ::
      |observations| == |cmd.inputs| &&
      StdinStatesRelation(cmd, preStreams, preStdin, postStdin, states) &&
      StdinDataRelation(cmd, observations, stdinData, cuts) &&
      (forall i: nat | i < |observations| ::
         InputObservationRelation(
           cmd, preFs, preStreams, states[i], i, observations[i])) &&
      EntriesForOutputRelation(
        cmd, stdinData, ObservationEntries(observations), entries) &&
      VisibleErrorRelation(cmd.serial, observations, errorOutput) &&
      hadError ==
      (exists i: nat ::
         i < |observations| && observations[i].failed) &&
      hadBlockingError ==
      (exists i: nat ::
         i < |observations| && observations[i].blocking)
  }

  ghost predicate StdinStatesRelation(
    cmd: PasteSchema.PasteCmd,
    observations: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult,
    before: BenchWorld.Bytes, after: BenchWorld.Bytes,
    states: seq<BenchWorld.Bytes>
  )
  {
    |states| == |cmd.inputs| + 1 && states[0] == before &&
    states[|cmd.inputs|] == after &&
    forall i: nat {:trigger states[i + 1]} | i < |cmd.inputs| ::
      states[i + 1] == (if cmd.inputs[i].Stdin?
                        then IOContract.ObservedReadStdinRemainingFields(states[i], observations)
                        else states[i])
  }

  ghost predicate StdinDataRelation(
    cmd: PasteSchema.PasteCmd, observations: seq<InputObservation>,
    data: BenchWorld.Bytes, cuts: seq<nat>
  )
  {
    |observations| == |cmd.inputs| && |cuts| == |cmd.inputs| + 1 &&
    cuts[0] == 0 && cuts[|cmd.inputs|] == |data| &&
    forall i: nat {:trigger cuts[i]} | i < |cmd.inputs| ::
      cuts[i] <= cuts[i + 1] <= |data| &&
      data[cuts[i]..cuts[i + 1]] == (if cmd.inputs[i].Stdin?
                                     then IOContract.ReadResultData(observations[i].result) else [])
  }

  ghost predicate EscapedDelimiterRelation(
    ch: BenchWorld.RawByte,
    delimiter: BenchWorld.Bytes
  )
  {
    delimiter ==
    if ch == '0' then []
    else if ch == 'n' then ['\n']
    else if ch == 't' then ['\t']
    else if ch == '\\' then ['\\']
    else if ch == 'b' then [(8 as char)]
    else if ch == 'f' then [(12 as char)]
    else if ch == 'r' then ['\r']
    else if ch == 'v' then [(11 as char)]
    else [ch]
  }

  datatype DelimiterAssembly =
    DelimiterDone |
    DelimiterFailure |
    DelimiterStep(
      index: nat,
      nextIndex: nat,
      delimiter: BenchWorld.Bytes,
      rest: DelimiterAssembly)

  ghost predicate DelimiterParseRelation(
    text: BenchWorld.Bytes,
    i: nat,
    plan: DelimPlan,
    assembly: DelimiterAssembly
  )
    decreases assembly
  {
    i <= |text| &&
    match assembly
    case DelimiterDone =>
      i == |text| && plan == Result.Ok([])
    case DelimiterFailure =>
      i < |text| &&
      text[i] == '\\' &&
      i + 1 == |text| &&
      plan == Result.Err(DelimiterBackslashError(text))
    case DelimiterStep(index, nextIndex, delimiter, rest) =>
      index == i &&
      i < |text| &&
      (if text[i] == '\\' then
         nextIndex == i + 2 &&
         i + 1 < |text| &&
         EscapedDelimiterRelation(text[i + 1], delimiter)
       else
         nextIndex == i + 1 &&
         delimiter == [text[i]]) &&
      exists restPlan: DelimPlan ::
        DelimiterParseRelation(text, nextIndex, restPlan, rest) &&
        plan ==
        match restPlan
        case Err(stderr) => Result.Err(stderr)
        case Ok(delims) => Result.Ok([delimiter] + delims)
  }

  ghost predicate DelimiterPlanRelation(
    text: string,
    plan: DelimPlan
  )
  {
    if |text| == 0 then
      plan == Result.Ok([[]])
    else
      exists assembly: DelimiterAssembly ::
        DelimiterParseRelation(Utf8.Encode(text), 0, plan, assembly)
  }

  function Max(a: nat, b: nat): nat
  {
    if a < b then b else a
  }

  function MaxLineCount(entries: seq<Entry>): nat
    decreases |entries|
  {
    if |entries| == 0 then
      0
    else
      Max(|entries[0].lines|, MaxLineCount(entries[1..]))
  }

  function DelimAt(delims: seq<BenchWorld.Bytes>, i: nat): BenchWorld.Bytes
    requires |delims| > 0
  {
    delims[i % |delims|]
  }

  datatype ColumnAssembly =
    ColumnsDone |
    ColumnStep(cut: nat, nextCut: nat, after: BenchWorld.Bytes, rest: ColumnAssembly)

  datatype RecordAssembly =
    RecordsDone |
    RecordStep(cut: nat, nextCut: nat, record: BenchWorld.Bytes,
               after: BenchWorld.Bytes, columns: ColumnAssembly, rest: RecordAssembly)

  ghost predicate ParallelColumnsRelation(
    entries: seq<Entry>,
    delims: seq<BenchWorld.Bytes>,
    row: nat,
    i: nat,
    before: BenchWorld.Bytes,
    output: BenchWorld.Bytes,
    assembly: ColumnAssembly
  )
    decreases assembly
  {
    |delims| > 0 &&
    match assembly
    case ColumnsDone =>
      i == |entries| && output == before
    case ColumnStep(cut, nextCut, after, rest) =>
      i < |entries| &&
      var fragment :=
        (if row < |entries[i].lines| then entries[i].lines[row] else []) +
        (if i + 1 < |entries| then DelimAt(delims, i) else []);
      cut == |before| &&
      nextCut == cut + |fragment| &&
      after == before + fragment &&
      ParallelColumnsRelation(entries, delims, row, i + 1, after, output, rest)
  }

  ghost predicate ParallelRowRelation(
    entries: seq<Entry>,
    delims: seq<BenchWorld.Bytes>,
    row: nat,
    output: BenchWorld.Bytes
  )
  {
    |delims| > 0 &&
    exists columns: ColumnAssembly ::
      ParallelColumnsRelation(entries, delims, row, 0, [], output, columns)
  }

  ghost predicate ParallelRecordsRelation(
    entries: seq<Entry>,
    delims: seq<BenchWorld.Bytes>,
    recordDelimiter: BenchWorld.RawByte,
    row: nat,
    limit: nat,
    before: BenchWorld.Bytes,
    output: BenchWorld.Bytes,
    assembly: RecordAssembly
  )
    decreases assembly
  {
    |delims| > 0 &&
    match assembly
    case RecordsDone =>
      row == limit && output == before
    case RecordStep(cut, nextCut, record, after, columns, rest) =>
      row < limit &&
      ParallelColumnsRelation(entries, delims, row, 0, [], record, columns) &&
      cut == |before| &&
      nextCut == cut + |record| + 1 &&
      after == before + record + [recordDelimiter] &&
      ParallelRecordsRelation(
        entries, delims, recordDelimiter, row + 1, limit, after, output, rest)
  }

  ghost predicate ParallelOutputRelation(
    entries: seq<Entry>,
    delims: seq<BenchWorld.Bytes>,
    recordDelimiter: BenchWorld.RawByte,
    output: BenchWorld.Bytes
  )
  {
    |delims| > 0 &&
    exists records: RecordAssembly ::
      ParallelRecordsRelation(
        entries, delims, recordDelimiter, 0, MaxLineCount(entries), [], output, records)
  }

  ghost predicate SerialColumnsRelation(
    lines: seq<BenchWorld.Bytes>,
    delims: seq<BenchWorld.Bytes>,
    i: nat,
    before: BenchWorld.Bytes,
    output: BenchWorld.Bytes,
    assembly: ColumnAssembly
  )
    decreases assembly
  {
    |delims| > 0 &&
    match assembly
    case ColumnsDone =>
      i == |lines| && output == before
    case ColumnStep(cut, nextCut, after, rest) =>
      i < |lines| &&
      var fragment := lines[i] +
                      (if i + 1 < |lines| then DelimAt(delims, i) else []);
      cut == |before| &&
      nextCut == cut + |fragment| &&
      after == before + fragment &&
      SerialColumnsRelation(lines, delims, i + 1, after, output, rest)
  }

  ghost predicate SerialRecordsRelation(
    entries: seq<Entry>,
    delims: seq<BenchWorld.Bytes>,
    recordDelimiter: BenchWorld.RawByte,
    i: nat,
    before: BenchWorld.Bytes,
    output: BenchWorld.Bytes,
    assembly: RecordAssembly
  )
    decreases assembly
  {
    |delims| > 0 &&
    match assembly
    case RecordsDone =>
      i == |entries| && output == before
    case RecordStep(cut, nextCut, record, after, columns, rest) =>
      i < |entries| &&
      (if entries[i].readOk then
         SerialColumnsRelation(entries[i].lines, delims, 0, [], record, columns) &&
         cut == |before| &&
         nextCut == cut + |record| + 1 &&
         after == before + record + [recordDelimiter]
       else
         columns == ColumnsDone &&
         record == [] &&
         cut == |before| &&
         nextCut == cut &&
         after == before) &&
      SerialRecordsRelation(
        entries, delims, recordDelimiter, i + 1, after, output, rest)
  }

  ghost predicate SerialOutputRelation(
    entries: seq<Entry>,
    delims: seq<BenchWorld.Bytes>,
    recordDelimiter: BenchWorld.RawByte,
    output: BenchWorld.Bytes
  )
  {
    |delims| > 0 &&
    exists records: RecordAssembly ::
      SerialRecordsRelation(entries, delims, recordDelimiter, 0, [], output, records)
  }

  ghost predicate OutputRelation(
    serial: bool,
    delims: seq<BenchWorld.Bytes>,
    recordDelimiter: BenchWorld.RawByte,
    entries: seq<Entry>,
    output: BenchWorld.Bytes
  )
  {
    if serial then
      SerialOutputRelation(entries, delims, recordDelimiter, output)
    else
      ParallelOutputRelation(entries, delims, recordDelimiter, output)
  }

  twostate predicate SpecCmd(cmd: PasteSchema.PasteCmd, io: BenchIO.IO, exit: int, plannedStdout: BenchWorld.Bytes, plannedStderr: BenchWorld.Bytes)
    reads io.Footprint() - {io.stdoutRegion, io.stderrRegion}
  {
    if cmd.mode == PasteSchema.ModeHelp then
      io.stdin() == old(io.stdin()) &&
      plannedStdout == old(io.stdout()) + HelpText() &&
      plannedStderr == old(io.stderr()) &&
      exit == 0
    else if cmd.mode == PasteSchema.ModeVersion then
      io.stdin() == old(io.stdin()) &&
      plannedStdout == old(io.stdout()) + VersionText() &&
      plannedStderr == old(io.stderr()) &&
      exit == 0
    else
      exists plan: DelimPlan ::
        DelimiterPlanRelation(cmd.delimiterText, plan) &&
        match plan
        case Err(stderr) =>
          io.stdin() == old(io.stdin()) &&
          plannedStdout == old(io.stdout()) &&
          plannedStderr == old(io.stderr()) + stderr &&
          exit == 1
        case Ok(delims) =>
          exists entries: seq<Entry>,
            errorOutput: BenchWorld.Bytes,
            hadError: bool,
            hadBlockingError: bool,
            output: BenchWorld.Bytes ::
            InputTraceRelation(
              cmd, old(io.fs()), old(io.trustedStreams()), old(io.stdin()), io.stdin(), entries,
              errorOutput, hadError, hadBlockingError) &&
            OutputRelation(
              cmd.serial, delims, RecordDelimiter(cmd.zeroTerminated),
              entries, output) &&
            plannedStdout == old(io.stdout()) +
            (if hadBlockingError && !cmd.serial then [] else output) &&
            plannedStderr == old(io.stderr()) + errorOutput &&
            exit == (if hadError then 1 else 0)
  }

  twostate predicate PreparedSpec(raw: PasteSchema.PasteCmdRaw, io: BenchIO.IO, exit: int, plannedStdout: BenchWorld.Bytes, plannedStderr: BenchWorld.Bytes)
    reads io.Footprint() - {
            io.stdoutRegion, io.stderrRegion}
  {
    SpecCmd(PasteSchema.Command(raw), io, exit, plannedStdout, plannedStderr)
  }

  function Emits(raw: PasteSchema.PasteCmdRaw): bool
  {
    true
  }

  ghost function StreamWriteErrorMessage(message: string): BenchWorld.Bytes
  {
    StreamUtf8.Encode(StreamWriteErrorMessageText0 + message + StreamWriteErrorMessageText1)
  }

  ghost predicate EmitFields(
    observations: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult,
    beforeStdout: BenchWorld.Bytes, beforeStderr: BenchWorld.Bytes,
    afterStdout: BenchWorld.Bytes, afterStderr: BenchWorld.Bytes,
    out: BenchWorld.Bytes, diagnostics: BenchWorld.Bytes,
    normalExit: int, exit: int
  )
  {
    var stdoutResult := observations(BenchWorld.StreamWriteStdout(beforeStdout, out));
    stdoutResult.StreamWriteResult? &&
    var errors := diagnostics + (if stdoutResult.err == 0 then [] else
                                 StreamWriteErrorMessage(StreamContract.CLocaleErrnoTextResult(stdoutResult.err)));
    var stderrResult := observations(BenchWorld.StreamWriteStderr(beforeStderr, errors));
    stderrResult.StreamWriteResult? &&
    StreamContract.WriteStdoutSpec(
      beforeStdout, observations, afterStdout, out, stdoutResult.committed, stdoutResult.err) &&
    StreamContract.WriteStderrSpec(
      beforeStderr, observations, afterStderr, errors, stderrResult.committed, stderrResult.err) &&
    exit == (if stdoutResult.err != 0 || stderrResult.err != 0 then 1 else normalExit)
  }

  twostate predicate Emission(raw: PasteSchema.PasteCmdRaw, io: BenchIO.IO,
                              out: BenchWorld.Bytes, diagnostics: BenchWorld.Bytes,
                              normalExit: int, exit: int)
    reads io.Footprint()
  {
    if Emits(raw) then
      EmitFields(old(io.trustedStreams()), old(io.stdout()), old(io.stderr()),
                 io.stdout(), io.stderr(), out, diagnostics, normalExit, exit)
    else
      io.stdout() == old(io.stdout()) && io.stderr() == old(io.stderr()) &&
      exit == normalExit
  }

  twostate predicate Spec(raw: PasteSchema.PasteCmdRaw, io: BenchIO.IO, exit: int)
    reads io.Footprint()
  {
    exists out: BenchWorld.Bytes, diagnostics: BenchWorld.Bytes, normalExit: int ::
      PreparedSpec(raw, io, normalExit,
                   old(io.stdout()) + out, old(io.stderr()) + diagnostics) &&
      Emission(raw, io, out, diagnostics, normalExit, exit)
  }
}
