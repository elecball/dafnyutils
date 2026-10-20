include "WcTextCore.dfy"
include "../../core/World.dfy"
include "../../core/IO.dfy"
include "../../core/IOContract.dfy"
include "WcSchema.dfy"
include "WcSpec.dfy"

module WcCore {
  import Text = WcTextCore

  import StreamContract = IOContract

  import Result = Results
  import BenchIO
  import BenchWorld
  import IOContract
  import Spec = WcSpec
  import WcSchema
  import Utf8 = WcUtf8Core
  import SE = WcEscapingCore

  datatype Counts = Counts(lines: int, words: int, chars: int, bytes: int, maxLine: int)
  datatype ScanState = ScanState(counts: Counts, inWord: bool, lineLen: int)
  datatype Entry = Entry(name: string, counts: Counts, wide: bool)
  datatype CountWitness = CountWitness(
    newlineIndices: set<nat>,
    wordStartIndices: set<nat>,
    columns: seq<nat>
  )
  datatype InputObservation = InputObservation(
    result: BenchWorld.IOResult<BenchWorld.Bytes>,
    entries: seq<Entry>,
    errorOutput: BenchWorld.Bytes,
    failed: bool,
    countWitnesses: seq<CountWitness>
  )

  ghost function ToSpecCounts(counts: Counts): Spec.Counts
  {
    Spec.Counts(counts.lines, counts.words, counts.chars, counts.bytes, counts.maxLine)
  }

  ghost function ToSpecEntry(entry: Entry): Spec.Entry
  {
    Spec.Entry(entry.name, ToSpecCounts(entry.counts), entry.wide)
  }

  ghost function ToSpecEntries(entries: seq<Entry>): seq<Spec.Entry>
    decreases |entries|
  {
    if |entries| == 0 then
      []
    else
      [ToSpecEntry(entries[0])] + ToSpecEntries(entries[1..])
  }

  ghost function IsStdinInput(input: WcSchema.Input): bool
  {
    match input
    case Stdin(_) => true
    case File(_) => false
  }

  function InputName(input: WcSchema.Input): string
  {
    match input
    case Stdin(displayName) => displayName
    case File(path) => path
  } by method {
    match input
    case Stdin(displayName) => return displayName;
    case File(path) => return path;
  }

  ghost function PrefixStdinCore(cmd: WcSchema.WcCmd, preStdin: BenchWorld.Bytes, i: nat, preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult): BenchWorld.Bytes
    requires i <= |cmd.inputs|
    decreases i
  {
    if i == 0 then
      preStdin
    else
      match cmd.inputs[i - 1]
      case Stdin(_) => IOContract.ObservedReadStdinRemainingFields(PrefixStdinCore(cmd, preStdin, i - 1, preStreams), preStreams)
      case File(_) => PrefixStdinCore(cmd, preStdin, i - 1, preStreams)
  }

  ghost function ReadResultCore(
    cmd: WcSchema.WcCmd,
    preFs: BenchWorld.FileSystem,
    preStdin: BenchWorld.Bytes,
    i: nat,
    preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult
  ): BenchWorld.IOResult<BenchWorld.Bytes>
    requires i < |cmd.inputs|
  {
    match cmd.inputs[i]
    case Stdin(_) => IOContract.ObservedReadStdinResultFields(PrefixStdinCore(cmd, preStdin, i, preStreams), preStreams)
    case File(path) => IOContract.ObservedReadFileResultFields(preFs, preStreams, path)
  }

  function ZeroCounts(): Counts
  {
    Counts(0, 0, 0, 0, 0)
  } by method {
    return Counts(0, 0, 0, 0, 0);
  }

  function AddCounts(a: Counts, b: Counts): Counts
  {
    Counts(a.lines + b.lines, a.words + b.words, a.chars + b.chars, a.bytes + b.bytes, Max(a.maxLine, b.maxLine))
  } by method {
    return Counts(
        a.lines + b.lines,
        a.words + b.words,
        a.chars + b.chars,
        a.bytes + b.bytes,
        Max(a.maxLine, b.maxLine)
      );
  }

  ghost predicate CountsNonnegative(counts: Counts)
  {
    0 <= counts.lines &&
    0 <= counts.words &&
    0 <= counts.chars &&
    0 <= counts.bytes &&
    0 <= counts.maxLine
  }

  ghost predicate EntriesNonnegative(entries: seq<Entry>)
  {
    forall i: nat | i < |entries| :: CountsNonnegative(entries[i].counts)
  }

  function Max(a: int, b: int): int
  {
    if a < b then b else a
  } by method {
    return if a < b then b else a;
  }

  function IsWordSpace(ch: char): bool
  {
    ch == ' ' || ch == '\n' || ch == '\t' || ch == '\r' ||
    ch == (11 as char) || ch == (12 as char) || ch == (160 as char)
  } by method {
    return ch == ' ' || ch == '\n' || ch == '\t' || ch == '\r' ||
           ch == (11 as char) || ch == (12 as char) || ch == (160 as char);
  }

  ghost function IsWordChar(ch: char): bool
  {
    !IsWordSpace(ch)
  }

  function NextLineLen(ch: char, current: int): int
    requires 0 <= current
  {
    if ch == '\t' then
      current + (8 - current % 8)
    else if ch == '\r' || ch == (12 as char) then
      0
    else if 32 <= ch as int < 127 then
      current + 1
    else
      current
  } by method {
    if ch == '\t' {
      return current + (8 - current % 8);
    } else if ch == '\r' || ch == (12 as char) {
      return 0;
    } else if 32 <= ch as int < 127 {
      return current + 1;
    } else {
      return current;
    }
  }

  function InitScan(): ScanState
  {
    ScanState(ZeroCounts(), false, 0)
  } by method {
    return ScanState(ZeroCounts(), false, 0);
  }

  ghost function ScanBytes(data: BenchWorld.Bytes, state: ScanState): ScanState
    requires 0 <= state.lineLen
    decreases |data|
  {
    if |data| == 0 then
      state
    else
      var ch := data[0];
      var rest := data[1..];
      var base := Counts(
                    state.counts.lines,
                    state.counts.words,
                    state.counts.chars + 1,
                    state.counts.bytes + 1,
                    state.counts.maxLine
                  );
      if ch == '\n' then
        ScanBytes(
          rest,
          ScanState(
            Counts(base.lines + 1, base.words, base.chars, base.bytes, Max(base.maxLine, state.lineLen)),
            false,
            0
          )
        )
      else
        var space := IsWordSpace(ch);
        var nextLen := NextLineLen(ch, state.lineLen);
        var wordChar := IsWordChar(ch);
        var nextWords := base.words + (if !space && wordChar && !state.inWord then 1 else 0);
        ScanBytes(
          rest,
          ScanState(
            Counts(base.lines, nextWords, base.chars, base.bytes, Max(base.maxLine, nextLen)),
            if space then false else state.inWord || wordChar,
            nextLen
          )
        )
  }

  ghost function CountData(data: BenchWorld.Bytes): Counts
  {
    ScanBytes(data, InitScan()).counts
  }

  ghost function NewlineIndices(data: BenchWorld.Bytes): set<nat>
  {
    set i: nat | i < |data| && data[i] == '\n'
  }

  ghost function WordStartIndices(data: BenchWorld.Bytes): set<nat>
  {
    set i: nat {:trigger data[i]} |
    i < |data| &&
    !IsWordSpace(data[i]) &&
    (i == 0 || IsWordSpace(data[i - 1]))
  }

  ghost predicate LineColumnTraceRelation(data: BenchWorld.Bytes, columns: seq<nat>)
  {
    |columns| == |data| + 1 &&
    columns[0] == 0 &&
    forall i: nat | i < |data| ::
      columns[i + 1] ==
      if data[i] == '\n' then 0
      else NextLineLen(data[i], columns[i])
  }

  ghost predicate MaximumRelation(values: seq<nat>, maximum: int)
  {
    0 <= maximum &&
    (forall i: nat | i < |values| :: values[i] <= maximum) &&
    (maximum == 0 || maximum in values)
  }

  ghost predicate CountWitnessRelation(
    data: BenchWorld.Bytes,
    counts: Counts,
    countTrace: CountWitness
  )
  {
    countTrace.newlineIndices == NewlineIndices(data) &&
    countTrace.wordStartIndices == WordStartIndices(data) &&
    counts.bytes == |data| &&
    counts.chars == |data| &&
    counts.lines == |countTrace.newlineIndices| &&
    counts.words == |countTrace.wordStartIndices| &&
    CountsNonnegative(counts) &&
    LineColumnTraceRelation(data, countTrace.columns) &&
    MaximumRelation(countTrace.columns, counts.maxLine)
  }

  ghost predicate InputStepWitnessRelation(
    input: WcSchema.Input,
    result: BenchWorld.IOResult<BenchWorld.Bytes>,
                              entries: seq<Entry>,
                              errorOutput: BenchWorld.Bytes,
                              failed: bool,
                              countWitnesses: seq<CountWitness>
  )
  {
    EntriesNonnegative(entries) &&
    match input
    case Stdin(displayName) =>
      (match result
       case Ok(data) =>
         exists counts: Counts, countTrace: CountWitness ::
           CountWitnessRelation(data, counts, countTrace) &&
           entries == [Entry(displayName, counts, true)] &&
           errorOutput == [] &&
           !failed &&
           countWitnesses == [countTrace]
       case Err(error) =>
         exists counts: Counts, countTrace: CountWitness ::
           CountWitnessRelation(IOContract.ReadResultData(result), counts, countTrace) &&
           entries == [Entry(displayName, counts, true)] &&
           errorOutput == Text.StdinReadErrorMessage(displayName, error) && failed &&
           countWitnesses == [countTrace])
    case File(path) =>
      (match result
       case Ok(data) =>
         exists counts: Counts, countTrace: CountWitness ::
           CountWitnessRelation(data, counts, countTrace) &&
           entries == [Entry(path, counts, false)] &&
           errorOutput == [] &&
           !failed &&
           countWitnesses == [countTrace]
       case Err(err) =>
         entries ==
         (if IOContract.IOErrorIsDirectory(err)
          then [Entry(path, ZeroCounts(), true)]
          else []) &&
         errorOutput == Text.ErrorMessage(path, err) &&
         failed &&
         countWitnesses == [])
  }

  ghost predicate InputObservationRelation(
    cmd: WcSchema.WcCmd,
    preFs: BenchWorld.FileSystem,
    preStdin: BenchWorld.Bytes,
    i: nat,
    observation: InputObservation,
    preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult
  )
    requires i < |cmd.inputs|
  {
    observation.result == ReadResultCore(cmd, preFs, preStdin, i, preStreams) &&
    InputStepWitnessRelation(
      cmd.inputs[i],
      observation.result,
      observation.entries,
      observation.errorOutput,
      observation.failed,
      observation.countWitnesses
    )
  }

  ghost function ObservationEntryFragments(
    observations: seq<InputObservation>
  ): seq<seq<Entry>>
  {
    seq(
    |observations|,
    i requires 0 <= i < |observations| => observations[i].entries
      )
  }

  ghost function ObservationErrorFragments(
    observations: seq<InputObservation>
  ): seq<BenchWorld.Bytes>
  {
    seq(
    |observations|,
    i requires 0 <= i < |observations| => observations[i].errorOutput
      )
  }

  ghost predicate HasFailedObservation(observations: seq<InputObservation>)
  {
    exists i: nat :: i < |observations| && observations[i].failed
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
      cuts[i] <= cuts[i + 1] &&
      cuts[i + 1] <= |combined| &&
      cuts[i + 1] == cuts[i] + |fragments[i]| &&
      combined[cuts[i]..cuts[i + 1]] == fragments[i]
  }

  ghost predicate InputTraceWitnessRelation(
    cmd: WcSchema.WcCmd,
    preFs: BenchWorld.FileSystem,
    preStdin: BenchWorld.Bytes,
    count: nat,
    currentStdin: BenchWorld.Bytes,
    observations: seq<InputObservation>,
    entries: seq<Entry>,
    entryCuts: seq<nat>,
    errorOutput: BenchWorld.Bytes,
    errorCuts: seq<nat>,
    hadError: bool,
    preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult
  )
  {
    count <= |cmd.inputs| &&
    |observations| == count &&
    (forall i: nat | i < |observations| ::
       InputObservationRelation(
         cmd,
         preFs,
         preStdin,
         i,
         observations[i],
         preStreams
       )) &&
    FragmentsConcatenate(
      ObservationEntryFragments(observations),
      entries,
      entryCuts
    ) &&
    EntriesNonnegative(entries) &&
    FragmentsConcatenate(
      ObservationErrorFragments(observations),
      errorOutput,
      errorCuts
    ) &&
    hadError == HasFailedObservation(observations) &&
    currentStdin == PrefixStdinCore(cmd, preStdin, count, preStreams)
  }

  function TotalCounts(entries: seq<Entry>): Counts
    decreases |entries|
  {
    if |entries| == 0 then
      ZeroCounts()
    else
      AddCounts(entries[0].counts, TotalCounts(entries[1..]))
  } by method {
    if |entries| == 0 {
      return ZeroCounts();
    } else {
      return AddCounts(entries[0].counts, TotalCounts(entries[1..]));
    }
  }

  function SelectedFieldCount(cmd: WcSchema.WcCmd): int
  {
    (if cmd.showLines then 1 else 0) +
    (if cmd.showWords then 1 else 0) +
    (if cmd.showChars then 1 else 0) +
    (if cmd.showBytes then 1 else 0) +
    (if cmd.showMaxLineLength then 1 else 0)
  } by method {
    return (if cmd.showLines then 1 else 0) +
      (if cmd.showWords then 1 else 0) +
      (if cmd.showChars then 1 else 0) +
      (if cmd.showBytes then 1 else 0) +
      (if cmd.showMaxLineLength then 1 else 0);
  }

  function SelectedValues(
    cmd: WcSchema.WcCmd,
    counts: Counts
  ): seq<int>
  {
    (if cmd.showLines then [counts.lines] else []) +
    (if cmd.showWords then [counts.words] else []) +
    (if cmd.showChars then [counts.chars] else []) +
    (if cmd.showBytes then [counts.bytes] else []) +
    (if cmd.showMaxLineLength then [counts.maxLine] else [])
  } by method {
    return (if cmd.showLines then [counts.lines] else []) +
      (if cmd.showWords then [counts.words] else []) +
      (if cmd.showChars then [counts.chars] else []) +
      (if cmd.showBytes then [counts.bytes] else []) +
      (if cmd.showMaxLineLength then [counts.maxLine] else []);
  }

  function MaxSelectedValue(
    cmd: WcSchema.WcCmd,
    counts: Counts
  ): int
  {
    Max(
      Max(if cmd.showLines then counts.lines else 0, if cmd.showWords then counts.words else 0),
      Max(
        Max(if cmd.showChars then counts.chars else 0, if cmd.showBytes then counts.bytes else 0),
        if cmd.showMaxLineLength then counts.maxLine else 0
      )
    )
  } by method {
    return Max(
        Max(
          if cmd.showLines then counts.lines else 0,
          if cmd.showWords then counts.words else 0
        ),
        Max(
          Max(
            if cmd.showChars then counts.chars else 0,
            if cmd.showBytes then counts.bytes else 0
          ),
          if cmd.showMaxLineLength then counts.maxLine else 0
        )
      );
  }

  function MaxEntrySelectedValue(
    cmd: WcSchema.WcCmd,
    entries: seq<Entry>
  ): int
    decreases |entries|
  {
    if |entries| == 0 then
      0
    else
      Max(MaxSelectedValue(cmd, entries[0].counts), MaxEntrySelectedValue(cmd, entries[1..]))
  } by method {
    if |entries| == 0 {
      return 0;
    } else {
      return Max(
          MaxSelectedValue(cmd, entries[0].counts),
          MaxEntrySelectedValue(cmd, entries[1..])
        );
    }
  }

  function MaxEntryBytes(entries: seq<Entry>): int
    decreases |entries|
  {
    if |entries| == 0 then
      0
    else
      Max(entries[0].counts.bytes, MaxEntryBytes(entries[1..]))
  } by method {
    if |entries| == 0 {
      return 0;
    } else {
      return Max(
          entries[0].counts.bytes,
          MaxEntryBytes(entries[1..])
        );
    }
  }

  function HasWideEntry(entries: seq<Entry>): bool
    decreases |entries|
  {
    if |entries| == 0 then
      false
    else
      entries[0].wide || HasWideEntry(entries[1..])
  } by method {
    if |entries| == 0 {
      return false;
    } else {
      return entries[0].wide || HasWideEntry(entries[1..]);
    }
  }

  function DigitChar(d: int): BenchWorld.RawByte
  {
    if 0 <= d < 10 then
      (d + ('0' as int)) as char
    else
      '0'
  } by method {
    return if 0 <= d < 10 then
        (d + ('0' as int)) as char
      else
        '0';
  }

  function Digits(n: int): BenchWorld.Bytes
    decreases n
  {
    if n < 10 then
      [DigitChar(n)]
    else
      Digits(n / 10) + [DigitChar(n % 10)]
  } by method {
    if n < 10 {
      return [DigitChar(n)];
    } else {
      return Digits(n / 10) + [DigitChar(n % 10)];
    }
  }

  function DigitCount(n: int): int
    decreases n
  {
    if n < 10 then
      1
    else
      1 + DigitCount(n / 10)
  } by method {
    if n < 10 {
      return 1;
    } else {
      return 1 + DigitCount(n / 10);
    }
  }

  function PadLeft(text: seq<char>, width: int): seq<char>
    ensures text is BenchWorld.Bytes ==> PadLeft(text, width) is BenchWorld.Bytes
    decreases width - |text|
  {
    if |text| >= width then
      text
    else
      PadLeft([' '] + text, width)
  } by method {
    if |text| >= width {
      return text;
    } else {
      return PadLeft([' '] + text, width);
    }
  }

  function FieldWidth(
    cmd: WcSchema.WcCmd,
    entries: seq<Entry>,
    total: Counts
  ): int
  {
    var maxValue := Max(
                      Max(MaxSelectedValue(cmd, total), MaxEntrySelectedValue(cmd, entries)),
                      Max(total.bytes, MaxEntryBytes(entries))
                    );
    var digits := DigitCount(maxValue);
    if SelectedFieldCount(cmd) <= 1 && !ShouldPrintTotal(cmd) then
      1
    else if HasWideEntry(entries) then
      Max(7, digits)
    else
      Max(1, digits)
  } by method {
    var maxValue := Max(
      Max(
        MaxSelectedValue(cmd, total),
        MaxEntrySelectedValue(cmd, entries)
      ),
      Max(total.bytes, MaxEntryBytes(entries))
    );
    var digits := DigitCount(maxValue);
    if SelectedFieldCount(cmd) <= 1 && !ShouldPrintTotal(cmd) {
      return 1;
    } else if HasWideEntry(entries) {
      return Max(7, digits);
    } else {
      return Max(1, digits);
    }
  }

  function RenderValues(
    values: seq<int>,
    width: int,
    i: nat
  ): BenchWorld.Bytes
    requires i <= |values|
    decreases |values| - i
  {
    if i >= |values| then
      []
    else
      (if i == 0 then [] else [' ']) +
      PadLeft(Digits(values[i]), width) +
      RenderValues(values, width, i + 1)
  } by method {
    if i >= |values| {
      return [];
    } else {
      return (if i == 0 then [] else [' ']) +
        PadLeft(Digits(values[i]), width) +
        RenderValues(values, width, i + 1);
    }
  }

  function RenderCountsLine(
    cmd: WcSchema.WcCmd,
    counts: Counts,
    name: string,
    width: int
  ): BenchWorld.Bytes
  {
    RenderValues(SelectedValues(cmd, counts), width, 0) +
    (if name == "" then [] else
      [' '] + (if '\n' in name then SE.SpecQuoteFBytes(Utf8.Encode(name)) else Utf8.Encode(name))) +
    ['\n']
  } by method {
    return RenderValues(SelectedValues(cmd, counts), width, 0) +
      (if name == "" then [] else
        [' '] + (if '\n' in name then SE.SpecQuoteFBytes(Utf8.Encode(name)) else Utf8.Encode(name))) +
      ['\n'];
  }

  function RenderEntries(
    cmd: WcSchema.WcCmd,
    entries: seq<Entry>,
    width: int
  ): BenchWorld.Bytes
    decreases |entries|
  {
    if |entries| == 0 then
      []
    else
      RenderCountsLine(cmd, entries[0].counts, entries[0].name, width) +
      RenderEntries(cmd, entries[1..], width)
  } by method {
    if |entries| == 0 {
      return [];
    } else {
      return RenderCountsLine(
          cmd, entries[0].counts, entries[0].name, width
        ) + RenderEntries(cmd, entries[1..], width);
    }
  }

  function ShouldPrintTotal(cmd: WcSchema.WcCmd): bool
  {
    |cmd.inputs| > 1
  } by method {
    return |cmd.inputs| > 1;
  }

  function RunOutputFromEntriesCore(
    cmd: WcSchema.WcCmd,
    entries: seq<Entry>
  ): BenchWorld.Bytes
  {
    var total := TotalCounts(entries);
    var width := FieldWidth(cmd, entries, total);
    RenderEntries(cmd, entries, width) +
    (if ShouldPrintTotal(cmd) then
       RenderCountsLine(cmd, total, Spec.TotalName(), width)
     else
       [])
  } by method {
    var total := TotalCounts(entries);
    var width := FieldWidth(cmd, entries, total);
    var rendered := RenderEntries(cmd, entries, width);
    if ShouldPrintTotal(cmd) {
      return rendered +
        RenderCountsLine(cmd, total, Spec.TotalName(), width);
    } else {
      return rendered;
    }
  }

  twostate predicate PreparedSummary(raw: WcSchema.WcCmdRaw, io: BenchIO.IO, exit: int, plannedStdout: BenchWorld.Bytes, plannedStderr: BenchWorld.Bytes)
    reads io.stdinRegion
  {
    var cmd := Command(raw);
    (if cmd.mode == WcSchema.ModeHelp then
       io.stdin() == old(io.stdin()) &&
       plannedStdout == Spec.HelpText() &&
       plannedStderr == [] &&
       exit == 0
     else if cmd.mode == WcSchema.ModeVersion then
       io.stdin() == old(io.stdin()) &&
       plannedStdout == Spec.VersionText() &&
       plannedStderr == [] &&
       exit == 0
     else
       exists observations: seq<InputObservation>,
         entries: seq<Entry>,
         entryCuts: seq<nat>,
         errorOutput: BenchWorld.Bytes,
         errorCuts: seq<nat>,
         hadError: bool ::
         InputTraceWitnessRelation(
           cmd,
           old(io.fs()),
           old(io.stdin()),
           |cmd.inputs|,
           io.stdin(),
           observations,
           entries,
           entryCuts,
           errorOutput,
           errorCuts,
           hadError,
           old(io.trustedStreams())
         ) &&
         plannedStdout ==
         RunOutputFromEntriesCore(cmd, entries) &&
         plannedStderr == errorOutput &&
         exit == (if hadError then 1 else 0))
  }

  lemma PrefixStdinCoreStep(cmd: WcSchema.WcCmd, preStdin: BenchWorld.Bytes, i: nat, preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult)
    requires i < |cmd.inputs|
    ensures PrefixStdinCore(cmd, preStdin, i + 1, preStreams) ==
            match cmd.inputs[i]
            case Stdin(_) => IOContract.ObservedReadStdinRemainingFields(PrefixStdinCore(cmd, preStdin, i, preStreams), preStreams)
            case File(_) => PrefixStdinCore(cmd, preStdin, i, preStreams)
  {
  }

  lemma PrefixStdinRelation(cmd: WcSchema.WcCmd, preStdin: BenchWorld.Bytes,
    preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult)
    ensures Spec.StdinTraceRelation(cmd, preStdin,
      PrefixStdinCore(cmd, preStdin, |cmd.inputs|, preStreams), preStreams,
      seq(|cmd.inputs| + 1, i requires 0 <= i <= |cmd.inputs| => PrefixStdinCore(cmd, preStdin, i, preStreams)))
  {
    forall i: nat | i < |cmd.inputs|
      ensures PrefixStdinCore(cmd, preStdin, i + 1, preStreams) ==
        (if cmd.inputs[i].Stdin? then IOContract.ObservedReadStdinRemainingFields(
          PrefixStdinCore(cmd, preStdin, i, preStreams), preStreams)
         else PrefixStdinCore(cmd, preStdin, i, preStreams))
    {
      PrefixStdinCoreStep(cmd, preStdin, i, preStreams);
    }
  }

  method GetHelpText() returns (out: BenchWorld.Bytes)
    ensures out == Spec.HelpText()
  {
    out := Spec.HelpText();
  }

  method GetVersionText() returns (out: BenchWorld.Bytes)
    ensures out == Spec.VersionText()
  {
    out := Spec.VersionText();
  }

  method GetErrnoText(err: BenchWorld.IOError) returns (text: string)
    ensures text == Spec.ErrnoText(err)
  {
    text := Spec.ErrnoText(err);
  }

  method ErrorMessageMethod(path: BenchWorld.Path, err: BenchWorld.IOError) returns (msg: BenchWorld.Bytes)
    ensures msg == Text.ErrorMessage(path, err)
  {
    msg := Text.ErrorMessage(path, err);
  }

  function InputsFromOperands(operands: seq<string>): seq<WcSchema.Input>
    decreases |operands|
  {
    if |operands| == 0 then
      []
    else
      [(if operands[0] == "-" then WcSchema.Stdin("-") else WcSchema.File(operands[0]))] +
      InputsFromOperands(operands[1..])
  } by method {
    if |operands| == 0 {
      return [];
    } else {
      var head :=
        if operands[0] == "-" then
          WcSchema.Stdin("-")
        else
          WcSchema.File(operands[0]);
      var tail := InputsFromOperands(operands[1..]);
      return [head] + tail;
    }
  }

  function Command(raw: WcSchema.WcCmdRaw): WcSchema.WcCmd
  {
    var mode :=
      if raw.seenHelp && (!raw.seenVersion || raw.helpTokenIndex <= raw.versionTokenIndex) then
        WcSchema.ModeHelp
      else if raw.seenVersion then
        WcSchema.ModeVersion
      else
        WcSchema.ModeRun;
    var selected :=
      raw.seenLines || raw.seenWords || raw.seenChars || raw.seenBytes || raw.seenMaxLineLength;
    var inputs := InputsFromOperands(raw.operands);
    var runInputs := if mode == WcSchema.ModeRun && |inputs| == 0 then [WcSchema.Stdin("")] else inputs;
    WcSchema.WcCmd(
      mode,
      if selected then raw.seenLines else true,
      if selected then raw.seenWords else true,
      if selected then raw.seenChars else false,
      if selected then raw.seenBytes else true,
      if selected then raw.seenMaxLineLength else false,
      runInputs
    )
  } by method {
    var mode :=
      if raw.seenHelp && (!raw.seenVersion || raw.helpTokenIndex <= raw.versionTokenIndex) then
        WcSchema.ModeHelp
      else if raw.seenVersion then
        WcSchema.ModeVersion
      else
        WcSchema.ModeRun;
    var selected :=
      raw.seenLines || raw.seenWords || raw.seenChars || raw.seenBytes || raw.seenMaxLineLength;
    var inputs := InputsFromOperands(raw.operands);
    var runInputs := if mode == WcSchema.ModeRun && |inputs| == 0 then [WcSchema.Stdin("")] else inputs;
    return WcSchema.WcCmd(
        mode,
        if selected then raw.seenLines else true,
        if selected then raw.seenWords else true,
        if selected then raw.seenChars else false,
        if selected then raw.seenBytes else true,
        if selected then raw.seenMaxLineLength else false,
        runInputs
      );
  }

  lemma NewlineIndicesExtend(data: BenchWorld.Bytes, i: nat)
    requires i < |data|
    ensures NewlineIndices(data[..i + 1]) ==
            NewlineIndices(data[..i]) +
            (if data[i] == '\n' then {i} else {})
  {
    assert forall j: nat {:trigger j in NewlineIndices(data[..i + 1])} ::
        j in NewlineIndices(data[..i + 1]) <==>
             j in NewlineIndices(data[..i]) +
                  (if data[i] == '\n' then {i} else {}) by {
      forall j: nat {:trigger j in NewlineIndices(data[..i + 1])}
        ensures
          j in NewlineIndices(data[..i + 1]) <==>
               j in NewlineIndices(data[..i]) +
                    (if data[i] == '\n' then {i} else {})
      {
        if j < i {
          assert data[..i + 1][j] == data[..i][j];
        }
      }
    }
  }

  lemma WordStartIndicesExtend(data: BenchWorld.Bytes, i: nat)
    requires i < |data|
    ensures WordStartIndices(data[..i + 1]) ==
            WordStartIndices(data[..i]) +
            (if !IsWordSpace(data[i]) &&
                (i == 0 || IsWordSpace(data[i - 1]))
             then {i}
             else {})
  {
    assert forall j: nat {:trigger j in WordStartIndices(data[..i + 1])} ::
        j in WordStartIndices(data[..i + 1]) <==>
             j in WordStartIndices(data[..i]) +
                  (if !IsWordSpace(data[i]) &&
                      (i == 0 || IsWordSpace(data[i - 1]))
                   then {i}
                   else {}) by {
      forall j: nat {:trigger j in WordStartIndices(data[..i + 1])}
        ensures
          j in WordStartIndices(data[..i + 1]) <==>
               j in WordStartIndices(data[..i]) +
                    (if !IsWordSpace(data[i]) &&
                        (i == 0 || IsWordSpace(data[i - 1]))
                     then {i}
                     else {})
      {
        if j < i {
          assert data[..i + 1][j] == data[..i][j];
          if j > 0 {
            assert data[..i + 1][j - 1] == data[..i][j - 1];
          }
        }
      }
    }
  }

  lemma LineColumnTraceExtend(
    data: BenchWorld.Bytes,
    i: nat,
    columns: seq<nat>,
    next: nat
  )
    requires i < |data|
    requires LineColumnTraceRelation(data[..i], columns)
    requires next ==
             if data[i] == '\n' then 0
             else NextLineLen(data[i], columns[|columns| - 1])
    ensures LineColumnTraceRelation(data[..i + 1], columns + [next])
  {
    forall j: nat | j < |data[..i + 1]|
      ensures (columns + [next])[j + 1] ==
              if data[..i + 1][j] == '\n' then 0
              else NextLineLen(data[..i + 1][j], (columns + [next])[j])
    {
      if j < i {
        assert data[..i + 1][j] == data[..i][j];
      } else {
        assert j == i;
        assert |columns| == i + 1;
      }
    }
  }

  lemma MaximumExtend(values: seq<nat>, maximum: nat, next: nat)
    requires MaximumRelation(values, maximum)
    ensures MaximumRelation(
              values + [next],
              if maximum < next then next else maximum
            )
  {
    reveal MaximumRelation();
    var extendedMaximum := if maximum < next then next else maximum;
    forall i: nat | i < |values + [next]|
      ensures (values + [next])[i] <= extendedMaximum
    {
      if i < |values| {
      } else {
        assert i == |values|;
      }
    }
    if extendedMaximum != 0 {
      if maximum < next {
        assert extendedMaximum in values + [next];
      } else if maximum != 0 {
        assert maximum in values;
        assert extendedMaximum in values + [next];
      }
    }
  }

  method CountDataMethod(data: BenchWorld.Bytes)
    returns (counts: Counts, ghost countTrace: CountWitness)
    ensures counts == CountData(data)
    ensures CountWitnessRelation(data, counts, countTrace)
  {
    var state := InitScan();
    ghost var initial := state;
    ghost var newlineIndices: set<nat> := {};
    ghost var wordStartIndices: set<nat> := {};
    ghost var columns: seq<nat> := [0];
    var i := 0;
    while i < |data|
      invariant 0 <= i <= |data|
      invariant 0 <= state.lineLen
      invariant ScanBytes(data[i..], state) == ScanBytes(data, initial)
      invariant newlineIndices == NewlineIndices(data[..i])
      invariant wordStartIndices == WordStartIndices(data[..i])
      invariant state.counts.lines == |newlineIndices|
      invariant state.counts.words == |wordStartIndices|
      invariant state.counts.chars == i
      invariant state.counts.bytes == i
      invariant LineColumnTraceRelation(data[..i], columns)
      invariant MaximumRelation(columns, state.counts.maxLine)
      invariant state.lineLen == columns[|columns| - 1]
      invariant state.inWord == (i > 0 && !IsWordSpace(data[i - 1]))
      decreases |data| - i
    {
      var ch := data[i];
      var base := Counts(
        state.counts.lines,
        state.counts.words,
        state.counts.chars + 1,
        state.counts.bytes + 1,
        state.counts.maxLine
      );
      var nextLineLen: nat;
      var nextInWord: bool;
      var nextCounts: Counts;
      if ch == '\n' {
        nextLineLen := 0;
        nextInWord := false;
        var nextMax := Max(base.maxLine, state.lineLen);
        nextCounts := Counts(
          base.lines + 1,
          base.words,
          base.chars,
          base.bytes,
          nextMax
        );
      } else {
        var space := IsWordSpace(ch);
        var computedLineLen := NextLineLen(ch, state.lineLen);
        assert 0 <= computedLineLen;
        nextLineLen := computedLineLen as nat;
        nextInWord := !space;
        var startsWord := !space && !state.inWord;
        var nextMax := Max(base.maxLine, nextLineLen);
        nextCounts := Counts(
          base.lines,
          base.words + (if startsWord then 1 else 0),
          base.chars,
          base.bytes,
          nextMax
        );
      }

      NewlineIndicesExtend(data, i);
      WordStartIndicesExtend(data, i);
      LineColumnTraceExtend(data, i, columns, nextLineLen);
      MaximumExtend(columns, state.counts.maxLine as nat, nextLineLen);
      if ch == '\n' {
        assert state.lineLen in columns;
        assert state.lineLen <= state.counts.maxLine;
        assert nextCounts.maxLine == state.counts.maxLine;
      }
      ghost var nextColumns := columns + [nextLineLen];
      ghost var nextNewlineIndices :=
        newlineIndices + (if ch == '\n' then {i} else {});
      ghost var nextWordStartIndices :=
        wordStartIndices +
        (if !IsWordSpace(ch) &&
            (i == 0 || IsWordSpace(data[i - 1]))
         then {i}
         else {});
      state := ScanState(nextCounts, nextInWord, nextLineLen);
      newlineIndices := nextNewlineIndices;
      wordStartIndices := nextWordStartIndices;
      columns := nextColumns;
      i := i + 1;
    }
    counts := state.counts;
    countTrace := CountWitness(newlineIndices, wordStartIndices, columns);
    assert initial == InitScan();
    assert data[..|data|] == data;
  }

  method ProcessReadMethod(
    input: WcSchema.Input,
    result: BenchWorld.IOResult<BenchWorld.Bytes>
  ) returns (
      entries: seq<Entry>,
      errorPiece: BenchWorld.Bytes,
      hadError: bool,
      ghost countWitnesses: seq<CountWitness>
    )
    ensures InputStepWitnessRelation(
              input,
              result,
              entries,
              errorPiece,
              hadError,
              countWitnesses
            )
  {
    reveal InputStepWitnessRelation();
    var name := InputName(input);
    match result
    case Ok(data) =>
      var counts, countTrace := CountDataMethod(data);
      var wide :=
        match input
        case Stdin(_) => true
        case File(_) => false;
      entries := [Entry(name, counts, wide)];
      errorPiece := [];
      hadError := false;
      countWitnesses := [countTrace];
      match input {
        case Stdin(displayName) =>
          assert name == displayName;
          assert wide;
          assert entries == [Entry(displayName, counts, true)];
        case File(path) =>
          assert name == path;
          assert !wide;
          assert entries == [Entry(path, counts, false)];
      }
    case Err(err) =>
      if input.Stdin? {
        var counts, countTrace := CountDataMethod(IOContract.ReadResultData(result));
        entries := [Entry(name, counts, true)];
        errorPiece := Text.StdinReadErrorMessage(name, err);
        hadError := true;
        countWitnesses := [countTrace];
        return;
      }
      assert input.File?;
      var path := input.path;
      if IOContract.IOErrorIsDirectory(err) {
        var zero := ZeroCounts();
        entries := [Entry(name, zero, true)];
      } else {
        entries := [];
      }
      errorPiece := ErrorMessageMethod(path, err);
      hadError := true;
      countWitnesses := [];
  }

  lemma AppendFragment<T>(
    fragments: seq<seq<T>>,
    combined: seq<T>,
    cuts: seq<nat>,
    tail: seq<T>
  )
    requires FragmentsConcatenate(fragments, combined, cuts)
    ensures FragmentsConcatenate(
              fragments + [tail],
              combined + tail,
              cuts + [|combined + tail|]
            )
  {
    reveal FragmentsConcatenate();
    forall i: nat {:trigger (cuts + [|combined + tail|])[i]} |
      i < |fragments + [tail]|
      ensures (cuts + [|combined + tail|])[i] <=
              (cuts + [|combined + tail|])[i + 1] &&
              (cuts + [|combined + tail|])[i + 1] <= |combined + tail| &&
              (cuts + [|combined + tail|])[i + 1] ==
              (cuts + [|combined + tail|])[i] +
              |(fragments + [tail])[i]| &&
              (combined + tail)[
              (cuts + [|combined + tail|])[i]..
              (cuts + [|combined + tail|])[i + 1]
              ] == (fragments + [tail])[i]
    {
    }
  }

  lemma ObservationEntryFragmentsSnoc(
    observations: seq<InputObservation>,
    observation: InputObservation
  )
    ensures ObservationEntryFragments(observations + [observation]) ==
            ObservationEntryFragments(observations) + [observation.entries]
  {
  }

  lemma ObservationErrorFragmentsSnoc(
    observations: seq<InputObservation>,
    observation: InputObservation
  )
    ensures ObservationErrorFragments(observations + [observation]) ==
            ObservationErrorFragments(observations) + [observation.errorOutput]
  {
  }

  lemma ObservationRelationsSnoc(
    cmd: WcSchema.WcCmd,
    preFs: BenchWorld.FileSystem,
    preStdin: BenchWorld.Bytes,
    observations: seq<InputObservation>,
    observation: InputObservation,
    preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult
  )
    requires |observations| < |cmd.inputs|
    requires forall i: nat | i < |observations| ::
               InputObservationRelation(cmd, preFs, preStdin, i, observations[i], preStreams)
    requires InputObservationRelation(
               cmd,
               preFs,
               preStdin,
               |observations|,
               observation,
               preStreams
             )
    ensures forall i: nat | i < |observations + [observation]| ::
              InputObservationRelation(
                cmd,
                preFs,
                preStdin,
                i,
                (observations + [observation])[i],
                preStreams
              )
  {
    forall i: nat | i < |observations + [observation]|
      ensures InputObservationRelation(
                cmd,
                preFs,
                preStdin,
                i,
                (observations + [observation])[i],
                preStreams
              )
    {
    }
  }

  lemma FailedObservationSnoc(
    observations: seq<InputObservation>,
    observation: InputObservation
  )
    ensures HasFailedObservation(observations + [observation]) ==
            (HasFailedObservation(observations) || observation.failed)
  {
    reveal HasFailedObservation();
    if exists i: nat ::
        i < |observations + [observation]| &&
        (observations + [observation])[i].failed {
      var i: nat :|
        i < |observations + [observation]| &&
        (observations + [observation])[i].failed;
      if i >= |observations| {
        assert i == |observations|;
      }
    }
    if observation.failed {
      assert exists i: nat ::
          i < |observations + [observation]| &&
          (observations + [observation])[i].failed by {
        assert (observations + [observation])[|observations|] ==
               observation;
      }
    } else if exists i: nat ::
        i < |observations| && observations[i].failed {
      var i: nat :| i < |observations| && observations[i].failed;
      assert i < |observations + [observation]|;
      assert (observations + [observation])[i] == observations[i];
    }
  }

  lemma {:isolate_assertions} ExtendInputTraceWitness(
    cmd: WcSchema.WcCmd,
    preFs: BenchWorld.FileSystem,
    preStdin: BenchWorld.Bytes,
    count: nat,
    currentStdin: BenchWorld.Bytes,
    observations: seq<InputObservation>,
    entries: seq<Entry>,
    entryCuts: seq<nat>,
    errorOutput: BenchWorld.Bytes,
    errorCuts: seq<nat>,
    hadError: bool,
    observation: InputObservation,
    nextStdin: BenchWorld.Bytes,
    preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult
  )
    requires InputTraceWitnessRelation(
               cmd,
               preFs,
               preStdin,
               count,
               currentStdin,
               observations,
               entries,
               entryCuts,
               errorOutput,
               errorCuts,
               hadError,
               preStreams
             )
    requires count < |cmd.inputs|
    requires InputObservationRelation(
               cmd,
               preFs,
               preStdin,
               count,
               observation,
               preStreams
             )
    requires nextStdin ==
             if IsStdinInput(cmd.inputs[count]) then IOContract.ObservedReadStdinRemainingFields(currentStdin, preStreams) else currentStdin
    ensures InputTraceWitnessRelation(
              cmd,
              preFs,
              preStdin,
              count + 1,
              nextStdin,
              observations + [observation],
              entries + observation.entries,
              entryCuts + [|entries + observation.entries|],
              errorOutput + observation.errorOutput,
              errorCuts + [|errorOutput + observation.errorOutput|],
              hadError || observation.failed,
              preStreams
            )
  {
    reveal InputTraceWitnessRelation();
    ghost var entryFragments := ObservationEntryFragments(observations);
    ghost var errorFragments := ObservationErrorFragments(observations);
    AppendFragment(entryFragments, entries, entryCuts, observation.entries);
    AppendFragment(errorFragments, errorOutput, errorCuts, observation.errorOutput);
    ObservationEntryFragmentsSnoc(observations, observation);
    ObservationErrorFragmentsSnoc(observations, observation);
    ObservationRelationsSnoc(
      cmd, preFs, preStdin, observations, observation,
      preStreams
    );
    FailedObservationSnoc(observations, observation);
    if IsStdinInput(cmd.inputs[count]) {
      assert exists i: nat :: i < count + 1 && IsStdinInput(cmd.inputs[i]);
    } else if exists i: nat ::
        i < count + 1 && IsStdinInput(cmd.inputs[i]) {
      assert exists i: nat :: i < count && IsStdinInput(cmd.inputs[i]) by {
        var i: nat :| i < count + 1 && IsStdinInput(cmd.inputs[i]);
        if i == count {
          assert !IsStdinInput(cmd.inputs[i]);
        }
      }
    }
  }

  lemma TraceCurrentStdinMatchesPrefix(
    cmd: WcSchema.WcCmd,
    preFs: BenchWorld.FileSystem,
    preStdin: BenchWorld.Bytes,
    count: nat,
    currentStdin: BenchWorld.Bytes,
    observations: seq<InputObservation>,
    entries: seq<Entry>,
    entryCuts: seq<nat>,
    errorOutput: BenchWorld.Bytes,
    errorCuts: seq<nat>,
    hadError: bool,
    preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult
  )
    requires InputTraceWitnessRelation(
               cmd,
               preFs,
               preStdin,
               count,
               currentStdin,
               observations,
               entries,
               entryCuts,
               errorOutput,
               errorCuts,
               hadError,
               preStreams
             )
    ensures currentStdin == PrefixStdinCore(cmd, preStdin, count, preStreams)
  {
    reveal InputTraceWitnessRelation();
  }

  method {:isolate_assertions} Prepare(
    raw: WcSchema.WcCmdRaw,
    io: BenchIO.IO
  ) returns (exit: int, plannedOut: BenchWorld.Bytes, plannedErr: BenchWorld.Bytes)
    modifies io.stdinRegion
    ensures PreparedSummary(raw, io, exit, plannedOut, plannedErr)
    decreases *
  {
    plannedOut := [];
    plannedErr := [];

    ghost var preFs := io.fs();
    ghost var preStreams := io.trustedStreams();
    ghost var preStdin := io.stdin();
    var cmd := Command(raw);

    if cmd.mode == WcSchema.ModeHelp {
      var help := GetHelpText();
      plannedOut := plannedOut + help;
      exit := 0;
      assert io.stdin() == preStdin;
      assert plannedErr == [];
      assert PreparedSummary(raw, io, exit, plannedOut, plannedErr) by {
        hide *;
        reveal PreparedSummary();
      }
      return;
    }

    if cmd.mode == WcSchema.ModeVersion {
      var version := GetVersionText();
      plannedOut := plannedOut + version;
      exit := 0;
      assert io.stdin() == preStdin;
      assert plannedErr == [];
      assert PreparedSummary(raw, io, exit, plannedOut, plannedErr) by {
        hide *;
        reveal PreparedSummary();
      }
      return;
    }

    var entries: seq<Entry> := [];
    var err: BenchWorld.Bytes := [];
    var hadError := false;
    ghost var observations: seq<InputObservation> := [];
    ghost var entryCuts: seq<nat> := [0];
    ghost var errorCuts: seq<nat> := [0];
    assert InputTraceWitnessRelation(
        cmd,
        preFs,
        preStdin,
        0,
        io.stdin(),
        observations,
        entries,
        entryCuts,
        err,
        errorCuts,
        hadError,
        old(io.trustedStreams())
      ) by {
      hide *;
      reveal InputTraceWitnessRelation();
      reveal FragmentsConcatenate();
      reveal ObservationEntryFragments();
      reveal ObservationErrorFragments();
      reveal EntriesNonnegative();
      reveal HasFailedObservation();
      reveal PrefixStdinCore();
    }

    var i := 0;
    while i < |cmd.inputs|
      invariant 0 <= i <= |cmd.inputs|
      invariant plannedOut == []
      invariant plannedErr == []
      invariant InputTraceWitnessRelation(
                  cmd,
                  preFs,
                  preStdin,
                  i,
                  io.stdin(),
                  observations,
                  entries,
                  entryCuts,
                  err,
                  errorCuts,
                  hadError,
                  old(io.trustedStreams())
                )
      decreases |cmd.inputs| - i
    {
      TraceCurrentStdinMatchesPrefix(
        cmd,
        preFs,
        preStdin,
        i,
        io.stdin(),
        observations,
        entries,
        entryCuts,
        err,
        errorCuts,
        hadError,
        old(io.trustedStreams())
      );
      assert io.stdin() == PrefixStdinCore(cmd, preStdin, i, preStreams);
      var input := cmd.inputs[i];
      var readResult: BenchWorld.IOResult<BenchWorld.Bytes>;
      ghost var inputStdin := io.stdin();
      match input {
        case Stdin(_) =>
          ghost var beforeStdin := io.stdin();
          readResult := io.ReadStdin();
          PrefixStdinCoreStep(cmd, preStdin, i, preStreams);
          assert beforeStdin == PrefixStdinCore(cmd, preStdin, i, preStreams);
          assert readResult == IOContract.ObservedReadStdinResultFields(beforeStdin, preStreams);
        case File(path) =>
          readResult := io.ReadFile(path);
      }
      if input.File? {
        PrefixStdinCoreStep(cmd, preStdin, i, preStreams);
      }
      assert readResult == ReadResultCore(cmd, preFs, preStdin, i, old(io.trustedStreams()));

      var entrySeq, errorPiece, inputHadError, countWitnesses :=
        ProcessReadMethod(input, readResult);
      ghost var observation := InputObservation(
        readResult,
        entrySeq,
        errorPiece,
        inputHadError,
        countWitnesses
      );
      assert InputObservationRelation(
          cmd,
          preFs,
          preStdin,
          i,
          observation,
          old(io.trustedStreams())
        );
      assert io.stdin() ==
             (if IsStdinInput(cmd.inputs[i]) then IOContract.ObservedReadStdinRemainingFields(inputStdin, preStreams) else inputStdin);
      ExtendInputTraceWitness(
        cmd,
        preFs,
        preStdin,
        i,
        inputStdin,
        observations,
        entries,
        entryCuts,
        err,
        errorCuts,
        hadError,
        observation,
        io.stdin(),
        old(io.trustedStreams())
      );
      ghost var nextObservations := observations + [observation];
      ghost var nextEntryCuts := entryCuts + [|entries + entrySeq|];
      ghost var nextErrorCuts := errorCuts + [|err + errorPiece|];
      entries := entries + entrySeq;
      err := err + errorPiece;
      hadError := hadError || inputHadError;
      observations := nextObservations;
      entryCuts := nextEntryCuts;
      errorCuts := nextErrorCuts;
      i := i + 1;
    }

    var out := RunOutputFromEntriesCore(cmd, entries);

    plannedOut := out;
    plannedErr := err;
    exit := if hadError then 1 else 0;
    TraceCurrentStdinMatchesPrefix(
      cmd,
      preFs,
      preStdin,
      |cmd.inputs|,
      io.stdin(),
      observations,
      entries,
      entryCuts,
      err,
      errorCuts,
      hadError,
      old(io.trustedStreams())
    );
    PrefixStdinRelation(cmd, preStdin, preStreams);
    assert io.stdin() ==
           PrefixStdinCore(cmd, preStdin, |cmd.inputs|, preStreams);
    assert InputTraceWitnessRelation(
        cmd,
        preFs,
        preStdin,
        |cmd.inputs|,
        io.stdin(),
        observations,
        entries,
        entryCuts,
        err,
        errorCuts,
        hadError,
        old(io.trustedStreams())
      );
    assert plannedOut == RunOutputFromEntriesCore(cmd, entries) by { hide *; }
    assert plannedErr == err by { hide *; }
    assert exists
        trace: seq<InputObservation>,
        coreEntries: seq<Entry>,
        coreEntryCuts: seq<nat>,
        errorOutput: BenchWorld.Bytes,
        coreErrorCuts: seq<nat>,
        failed: bool
        ::
          trace == observations &&
          coreEntries == entries &&
          coreEntryCuts == entryCuts &&
          errorOutput == err &&
          coreErrorCuts == errorCuts &&
          failed == hadError &&
          InputTraceWitnessRelation(
            cmd,
            preFs,
            preStdin,
            |cmd.inputs|,
            io.stdin(),
            trace,
            coreEntries,
            coreEntryCuts,
            errorOutput,
            coreErrorCuts,
            failed,
            old(io.trustedStreams())
          ) &&
          plannedOut ==
          RunOutputFromEntriesCore(cmd, coreEntries) &&
          plannedErr == errorOutput &&
          exit == (if failed then 1 else 0);
  }

  twostate predicate CoreSummary(raw: WcSchema.WcCmdRaw, io: BenchIO.IO, exit: int)
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
      errors := errors + Text.StreamWriteErrorMessage(message);
    }
    assert errors == diagnostics + (if outErr == 0 then [] else
      Text.StreamWriteErrorMessage(StreamContract.CLocaleErrnoTextResult(outErr)));
    var errErr := 0;
    if errors != [] {
      var diagnosed := io.WriteStderr(errors);
      errErr := StreamContract.ResultErrno(diagnosed);
      assert StreamContract.WriteStderrSpec(old(io.stderr()), io.trustedStreams(), io.stderr(),
        errors, StreamContract.WriteResultCommitted(diagnosed), errErr);
    }
    exit := if outErr != 0 || errErr != 0 then 1 else normalExit;
  }

  method RunCore(raw: WcSchema.WcCmdRaw, io: BenchIO.IO) returns (exit: int)
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
