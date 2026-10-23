include "../../core/StringEscaping.dfy"
include "../../core/World.dfy"
include "../../core/Utf8.dfy"
include "../../core/IO.dfy"
include "../../core/IOContract.dfy"
include "NlSchema.dfy"

module NlSpec {

  const UnsupportedRegexBodyStyleMessageText0: BenchWorld.Bytes := "nl: unsupported body numbering style in benchmark: '"

  const UnsupportedRegexBodyStyleMessageText1: BenchWorld.Bytes := "'\n"

  const ErrorMessageText0: BenchWorld.Bytes := "nl: "

  const ErrorMessageText1: BenchWorld.Bytes := ": "

  const ErrorMessageText2: BenchWorld.Bytes := "\n"

  const ErrorPieceText0: BenchWorld.Bytes := "-"

  const StreamWriteErrorMessageText0: BenchWorld.Bytes := "nl: write error: "

  const StreamWriteErrorMessageText1: BenchWorld.Bytes := "\n"

  import StreamContract = IOContract
  import StreamUtf8 = Utf8Semantics

  import Result = Results
  import BenchIO
  import BenchWorld
  import IOContract
  import Utf8 = Utf8Semantics
  import NlSchema
  import SE = StringEscaping

  function HelpText(): BenchWorld.Bytes
  {
    "Usage: nl [OPTION]... [FILE]...\n"
    + "Write each FILE to standard output, with line numbers added.\n"
    + "\n"
    + "With no FILE, or when FILE is -, read standard input.\n"
    + "  -b, --body-numbering=STYLE      use STYLE for numbering body lines\n"
    + "  -n, --number-format=FORMAT      insert line numbers according to FORMAT\n"
    + "  -s, --number-separator=STRING   add STRING after line numbers\n"
    + "      --help                      display this help and exit\n"
    + "      --version                   output version information and exit\n"
    + "\n"
    + "Supported benchmark STYLE values are a, t, and n.\n"
    + "Supported benchmark FORMAT values are ln, rn, and rz.\n"
  }

  function VersionText(): BenchWorld.Bytes
  {
    "nl (GNU coreutils) 9.10.13-2cf49\n"
    + "Copyright (C) 2026 Free Software Foundation, Inc.\n"
    + "License GPLv3+: GNU GPL version 3 or later <https://gnu.org/licenses/gpl.html>.\n"
    + "This is free software: you are free to change and redistribute it.\n"
    + "There is NO WARRANTY, to the extent permitted by law.\n"
    + "\n"
    + "Written by Scott Bartram and David MacKenzie.\n"
  }


  function InvalidBodyStyleMessage(value: string): BenchWorld.Bytes
  {
    NlSchema.InvalidBodyStyleLine(value) + NlSchema.TryHelp()
  }

  // Formal specification gap: pBRE body numbering is part of GNU nl, but this
  // relation intentionally excludes regex-based line selection until the
  // benchmark has a regex model.
  function UnsupportedRegexBodyStyleMessage(value: string): BenchWorld.Bytes
  {
    UnsupportedRegexBodyStyleMessageText0 + Utf8.Encode(value) + UnsupportedRegexBodyStyleMessageText1 + NlSchema.TryHelp()
  }

  function UnsupportedLogicalPageDelimiterMessage(): BenchWorld.Bytes
  {
    "nl: unsupported logical page delimiter in benchmark input\n" + NlSchema.TryHelp()
  }

  function InvalidNumberFormatMessage(value: string): BenchWorld.Bytes
  {
    NlSchema.InvalidNumberFormatLine(value) + NlSchema.TryHelp()
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

  function ErrorMessage(path: BenchWorld.Path, err: BenchWorld.IOError): BenchWorld.Bytes
  {
    ErrorMessageText0 + SE.SpecQuoteFBytes(Utf8.Encode(path)) +
    ErrorMessageText1 + Utf8.Encode(ErrnoText(err)) + ErrorMessageText2
  }

  ghost predicate NormalizedInputRelation(
    data: BenchWorld.Bytes,
    normalized: BenchWorld.Bytes
  )
  {
    normalized ==
    if |data| > 0 && data[|data| - 1] != '\n'
    then data + ['\n']
    else data
  }

  function IsLogicalPageDelimiterLine(line: BenchWorld.Bytes): bool
  {
    line == [(92 as char), ':'] ||
    line == [(92 as char), ':', (92 as char), ':'] ||
    line == [(92 as char), ':', (92 as char), ':', (92 as char), ':']
  }

  function ErrorPiece(input: NlSchema.Input, result: BenchWorld.IOResult<BenchWorld.Bytes>): BenchWorld.Bytes
  {
    match input
    case Stdin => if result.Err? then ErrorMessage(ErrorPieceText0, result.e) else []
    case File(path) =>
      match result
      case Ok(_) => []
      case Err(err) => ErrorMessage(path, err)
  }

  function HadErrorPiece(input: NlSchema.Input, result: BenchWorld.IOResult<BenchWorld.Bytes>): bool
  {
    match input
    case Stdin => result.Err?
    case File(_) =>
      match result
      case Ok(_) => false
      case Err(_) => true
  }

  function RepeatChar(ch: BenchWorld.RawByte, count: int): BenchWorld.Bytes
    decreases count
  {
    if count <= 0 then [] else [ch] + RepeatChar(ch, count - 1)
  }

  function DigitChar(d: int): char
  {
    if 0 <= d < 10 then
      (d + ('0' as int)) as char
    else
      '0'
  }

  function Digits(n: int): BenchWorld.Bytes
    requires 0 <= n
    decreases n
  {
    if n < 10 then
      [DigitChar(n)]
    else
      Digits(n / 10) + [DigitChar(n % 10)]
  }

  function RenderNumber(format: NlSchema.NumberFormat, n: int, width: int): BenchWorld.Bytes
    requires 0 <= n
  {
    var digits := Digits(n);
    if format == NlSchema.FormatLeft then
      digits + RepeatChar(' ', width - |digits|)
    else if format == NlSchema.FormatRightZero then
      RepeatChar('0', width - |digits|) + digits
    else
      RepeatChar(' ', width - |digits|) + digits
  }

  function ShouldNumber(style: NlSchema.BodyStyle, nonempty: bool): bool
  {
    style == NlSchema.NumberAll || (style == NlSchema.NumberNonEmpty && nonempty)
  }

  function LineNumberText(cmd: NlSchema.NlCmd, n: int): BenchWorld.Bytes
    requires 0 <= n
  {
    RenderNumber(cmd.numberFormat, n, 6) + Utf8.Encode(cmd.separator)
  }

  function BlankPrefix(cmd: NlSchema.NlCmd): BenchWorld.Bytes
  {
    RepeatChar(' ', 6 + |Utf8.Encode(cmd.separator)|)
  }

  function LinePrefix(cmd: NlSchema.NlCmd, nonempty: bool, n: int): BenchWorld.Bytes
    requires 0 <= n
  {
    if ShouldNumber(cmd.bodyStyle, nonempty) then
      LineNumberText(cmd, n)
    else
      BlankPrefix(cmd)
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
                                     cuts[i] <= cuts[i + 1] &&
                                     cuts[i + 1] <= |combined| &&
                                     cuts[i + 1] == cuts[i] + |fragments[i]| &&
                                     combined[cuts[i]..cuts[i + 1]] == fragments[i]
  }

  ghost predicate LinePartitionRelation(
    data: BenchWorld.Bytes,
    lines: seq<BenchWorld.Bytes>,
    terminated: seq<bool>,
    fragments: seq<BenchWorld.Bytes>,
    cuts: seq<nat>
  )
  {
    |lines| == |terminated| == |fragments| &&
    (|data| == 0) == (|lines| == 0) &&
    (forall i :: 0 <= i < |lines| ==>
                   |fragments[i]| > 0 &&
                   fragments[i] == lines[i] + (if terminated[i] then ['\n'] else []) &&
                   '\n' !in lines[i] &&
                   (i + 1 < |lines| ==> terminated[i])) &&
    FragmentsConcatenate(fragments, data, cuts)
  }

  ghost predicate LineNumberFromRelation(
    cmd: NlSchema.NlCmd,
    lines: seq<BenchWorld.Bytes>,
    start: nat,
    numbers: seq<nat>
  )
  {
    |numbers| == |lines| + 1 &&
    numbers[0] == start &&
    forall i {:trigger numbers[i]} :: 0 <= i < |lines| ==>
                                        numbers[i + 1] == numbers[i] +
                                        (if ShouldNumber(cmd.bodyStyle, |lines[i]| > 0) then 1 else 0)
  }

  ghost predicate LineNumberRelation(
    cmd: NlSchema.NlCmd,
    lines: seq<BenchWorld.Bytes>,
    numbers: seq<nat>
  )
  {
    LineNumberFromRelation(cmd, lines, 1, numbers)
  }

  ghost predicate LineRenderRelation(
    cmd: NlSchema.NlCmd,
    line: BenchWorld.Bytes,
    terminated: bool,
    number: nat,
    outputFragment: BenchWorld.Bytes
  )
  {
    outputFragment ==
    LinePrefix(cmd, |line| > 0, number as int) + line +
    (if terminated then ['\n'] else [])
  }

  ghost predicate OutputWitnessRelation(
    cmd: NlSchema.NlCmd,
    data: BenchWorld.Bytes,
    output: BenchWorld.Bytes,
    lines: seq<BenchWorld.Bytes>,
    terminated: seq<bool>,
    lineFragments: seq<BenchWorld.Bytes>,
    lineCuts: seq<nat>,
    numbers: seq<nat>,
    outputFragments: seq<BenchWorld.Bytes>,
    outputCuts: seq<nat>
  )
  {
    LinePartitionRelation(data, lines, terminated, lineFragments, lineCuts) &&
    LineNumberRelation(cmd, lines, numbers) &&
    |outputFragments| == |lines| &&
    (forall i :: 0 <= i < |lines| ==>
                   LineRenderRelation(
                     cmd, lines[i], terminated[i], numbers[i], outputFragments[i]
                   )) &&
    FragmentsConcatenate(outputFragments, output, outputCuts)
  }

  ghost predicate OutputRelation(
    cmd: NlSchema.NlCmd,
    data: BenchWorld.Bytes,
    output: BenchWorld.Bytes
  )
  {
    exists lines: seq<BenchWorld.Bytes>,
      terminated: seq<bool>,
      lineFragments: seq<BenchWorld.Bytes>,
      lineCuts: seq<nat>,
      numbers: seq<nat>,
      outputFragments: seq<BenchWorld.Bytes>,
      outputCuts: seq<nat> ::
      OutputWitnessRelation(
        cmd, data, output, lines, terminated, lineFragments, lineCuts, numbers,
        outputFragments, outputCuts
      )
  }

  ghost predicate ReadResultRelation(
    cmd: NlSchema.NlCmd,
    preFs: BenchWorld.FileSystem,
    preStdin: BenchWorld.Bytes,
    i: nat,
    result: BenchWorld.IOResult<BenchWorld.Bytes>,
                                preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult
  )
    requires i < |cmd.inputs|
  {
    match cmd.inputs[i]
    case Stdin =>
      result == IOContract.ObservedReadStdinResultFields(preStdin, preStreams)
    case File(path) =>
      result == IOContract.ObservedReadFileResultFields(preFs, preStreams, path)
  }

  ghost predicate StdinTraceRelation(cmd: NlSchema.NlCmd, before: BenchWorld.Bytes,
                                     after: BenchWorld.Bytes, observations: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult,
                                     states: seq<BenchWorld.Bytes>)
  {
    |states| == |cmd.inputs| + 1 && states[0] == before && states[|cmd.inputs|] == after &&
    forall i: nat | i < |cmd.inputs| ::
      states[i + 1] == (if cmd.inputs[i].Stdin? then
                          IOContract.ObservedReadStdinRemainingFields(states[i], observations) else states[i])
  }

  opaque ghost predicate InputTraceWitnessRelation(
    cmd: NlSchema.NlCmd,
    preFs: BenchWorld.FileSystem,
    preStdin: BenchWorld.Bytes,
    readResults: seq<BenchWorld.IOResult<BenchWorld.Bytes>>,
    inputFragments: seq<BenchWorld.Bytes>,
    combined: BenchWorld.Bytes,
    inputCuts: seq<nat>,
    errorFragments: seq<BenchWorld.Bytes>,
    errorOutput: BenchWorld.Bytes,
    errorCuts: seq<nat>,
    hadError: bool,
    hasDelimiter: bool,
    preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult
  , postStdin: BenchWorld.Bytes, stdinStates: seq<BenchWorld.Bytes>)
  {
    |readResults| == |cmd.inputs| &&
    |inputFragments| == |cmd.inputs| &&
    |errorFragments| == |cmd.inputs| &&
    StdinTraceRelation(cmd, preStdin, postStdin, preStreams, stdinStates) &&
    (forall i :: 0 <= i < |cmd.inputs| ==>
                   ReadResultRelation(cmd, preFs, stdinStates[i], i, readResults[i], preStreams) &&
                   (match readResults[i]
                    case Ok(data) =>
                      NormalizedInputRelation(data, inputFragments[i])
                    case Err(error) =>
                      if error.StreamFailure? then NormalizedInputRelation(error.partial, inputFragments[i])
                      else inputFragments[i] == []) &&
                   errorFragments[i] == ErrorPiece(cmd.inputs[i], readResults[i])) &&
    FragmentsConcatenate(inputFragments, combined, inputCuts) &&
    FragmentsConcatenate(errorFragments, errorOutput, errorCuts) &&
    hadError ==
    (exists i :: 0 <= i < |cmd.inputs| &&
                 HadErrorPiece(cmd.inputs[i], readResults[i])) &&
    (exists lines: seq<BenchWorld.Bytes>,
       terminated: seq<bool>,
       fragments: seq<BenchWorld.Bytes>,
       cuts: seq<nat> ::
       LinePartitionRelation(combined, lines, terminated, fragments, cuts) &&
       hasDelimiter ==
       (exists i :: 0 <= i < |lines| &&
                    IsLogicalPageDelimiterLine(lines[i])))
  }

  ghost predicate InputTraceRelation(
    cmd: NlSchema.NlCmd,
    preFs: BenchWorld.FileSystem,
    preStdin: BenchWorld.Bytes,
    readResults: seq<BenchWorld.IOResult<BenchWorld.Bytes>>,
    inputFragments: seq<BenchWorld.Bytes>,
    combined: BenchWorld.Bytes,
    inputCuts: seq<nat>,
    errorFragments: seq<BenchWorld.Bytes>,
    errorOutput: BenchWorld.Bytes,
    errorCuts: seq<nat>,
    hadError: bool,
    hasDelimiter: bool,
    preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult
  , postStdin: BenchWorld.Bytes)
  {
    exists stdinStates: seq<BenchWorld.Bytes> ::
      InputTraceWitnessRelation(cmd, preFs, preStdin, readResults, inputFragments, combined, inputCuts, errorFragments, errorOutput, errorCuts, hadError, hasDelimiter, preStreams, postStdin, stdinStates)
  }

  function ModeErrorMessage(cmd: NlSchema.NlCmd): BenchWorld.Bytes
  {
    match cmd.mode
    case ModeInvalidBodyStyle(value) => InvalidBodyStyleMessage(value)
    case ModeUnsupportedRegexBodyStyle(value) => UnsupportedRegexBodyStyleMessage(value)
    case ModeInvalidNumberFormat(value) => InvalidNumberFormatMessage(value)
    case ModeInvalidOptions => NlSchema.OptionErrorsText(cmd.optionErrors) + NlSchema.TryHelp()
    case _ => []
  }

  datatype RunWitness = RunWitness(
    readResults: seq<BenchWorld.IOResult<BenchWorld.Bytes>>,
    inputFragments: seq<BenchWorld.Bytes>,
    combined: BenchWorld.Bytes,
    inputCuts: seq<nat>,
    errorFragments: seq<BenchWorld.Bytes>,
    errorOutput: BenchWorld.Bytes,
    errorCuts: seq<nat>,
    hadError: bool,
    hasDelimiter: bool,
    outputPart: BenchWorld.Bytes)

  ghost predicate PreparedRunRelation(cmd: NlSchema.NlCmd,
                                      beforeFs: BenchWorld.FileSystem, beforeStdin: BenchWorld.Bytes, afterStdin: BenchWorld.Bytes,
                                      observations: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult,
                                      plannedStdout: BenchWorld.Bytes, plannedStderr: BenchWorld.Bytes, exit: int,
                                      trace: RunWitness)
  {
    var readResults := trace.readResults;
    var inputFragments := trace.inputFragments;
    var combined := trace.combined;
    var inputCuts := trace.inputCuts;
    var errorFragments := trace.errorFragments;
    var errorOutput := trace.errorOutput;
    var errorCuts := trace.errorCuts;
    var hadError := trace.hadError;
    var hasDelimiter := trace.hasDelimiter;
    var outputPart := trace.outputPart;
    InputTraceRelation(
      cmd, beforeFs, beforeStdin, readResults, inputFragments,
      combined, inputCuts, errorFragments, errorOutput, errorCuts,
      hadError, hasDelimiter,
      observations
    , afterStdin) &&
    (if hasDelimiter then
       outputPart == []
     else
       OutputRelation(cmd, combined, outputPart)) &&
    plannedStdout == outputPart &&
    plannedStderr == errorOutput +
    (if hasDelimiter then
       UnsupportedLogicalPageDelimiterMessage()
     else
       []) &&
    exit == (if hasDelimiter || hadError then 1 else 0)
  }

  twostate predicate PreparedSpec(raw: NlSchema.NlCmdRaw, io: BenchIO.IO, exit: int, plannedStdout: BenchWorld.Bytes, plannedStderr: BenchWorld.Bytes)
    reads io.stdinRegion
  {
    var cmd := NlSchema.Command(raw);
    if cmd.mode == NlSchema.ModeHelp then
      io.stdin() == old(io.stdin()) &&
      plannedStdout == HelpText() &&
      plannedStderr == NlSchema.OptionErrorsText(cmd.optionErrors) &&
      exit == 0
    else if cmd.mode == NlSchema.ModeVersion then
      io.stdin() == old(io.stdin()) &&
      plannedStdout == VersionText() &&
      plannedStderr == NlSchema.OptionErrorsText(cmd.optionErrors) &&
      exit == 0
    else if cmd.mode != NlSchema.ModeRun then
      io.stdin() == old(io.stdin()) &&
      plannedStdout == [] &&
      plannedStderr == ModeErrorMessage(cmd) &&
      exit == 1
    else
      exists trace: RunWitness ::
        PreparedRunRelation(cmd, old(io.fs()), old(io.stdin()), io.stdin(), old(io.trustedStreams()),
                            plannedStdout, plannedStderr, exit, trace)
  }

  function Emits(raw: NlSchema.NlCmdRaw): bool
  {
    true
  }

  function StreamWriteErrorMessage(message: string): BenchWorld.Bytes
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

  twostate predicate Emission(raw: NlSchema.NlCmdRaw, io: BenchIO.IO,
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

  twostate predicate Spec(raw: NlSchema.NlCmdRaw, io: BenchIO.IO, exit: int)
    reads io.stdinRegion, io.stdoutRegion, io.stderrRegion
  {
    exists out: BenchWorld.Bytes, diagnostics: BenchWorld.Bytes, normalExit: int ::
      PreparedSpec(raw, io, normalExit,
                   out, diagnostics) &&
      Emission(raw, io, out, diagnostics, normalExit, exit)
  }
}
