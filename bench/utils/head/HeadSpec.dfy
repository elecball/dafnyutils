include "../../core/World.dfy"
include "../../core/IO.dfy"
include "../../core/IOContract.dfy"
include "../../core/StringEscaping.dfy"
include "HeadSchema.dfy"
include "HeadRecordSpec.dfy"

module HeadSpec {
  import StreamContract = IOContract
  import StreamUtf8 = Utf8Semantics

  import Result = Results
  import BenchIO
  import Utf8 = Utf8Semantics
  import BenchWorld
  import IOContract
  import HeadSchema
  import HeadRecordSpec
  import SE = StringEscaping





  function HelpText(): BenchWorld.Bytes
  {
    "Usage: head [OPTION]... [FILE]...\n"
    + "Print the first 10 lines of each FILE to standard output.\n"
    + "With more than one FILE, precede each with a header giving the file name.\n"
    + "\n"
    + "With no FILE, or when FILE is -, read standard input.\n"
    + "  -c, --bytes=[-]NUM       print the first NUM bytes of each file;\n"
    + "                             with '-', print all but the last NUM bytes\n"
    + "  -n, --lines=[-]NUM       print the first NUM lines instead of 10;\n"
    + "                             with '-', print all but the last NUM lines\n"
    + "  -z, --zero-terminated    line delimiter is NUL, not newline\n"
    + "  -q, --quiet, --silent    never print headers giving file names\n"
    + "  -v, --verbose            always print headers giving file names\n"
    + "      --help               display this help and exit\n"
    + "      --version            output version information and exit\n"
    + "\n"
    + "Report bugs to: bug-coreutils@gnu.org\n"
    + "GNU coreutils home page: <https://www.gnu.org/software/coreutils/>\n"
    + "General help using GNU software: <https://www.gnu.org/gethelp/>\n"
    + "Full documentation <https://www.gnu.org/software/coreutils/head>\n"
    + "or available locally via: info '(coreutils) head invocation'\n"
  }

  function VersionText(): BenchWorld.Bytes
  {
    "head (GNU coreutils) 9.10.13-2cf49\n"
    + "Copyright (C) 2026 Free Software Foundation, Inc.\n"
    + "License GPLv3+: GNU GPL version 3 or later <https://gnu.org/licenses/gpl.html>.\n"
    + "This is free software: you are free to change and redistribute it.\n"
    + "There is NO WARRANTY, to the extent permitted by law.\n"
    + "\n"
    + "Written by David MacKenzie and Jim Meyering.\n"
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

  ghost function ErrorMessage(path: BenchWorld.Path, err: BenchWorld.IOError): BenchWorld.Bytes
  {
    Utf8.Encode(ErrorMessageText(SE.SpecQuoteAfBytes(Utf8.Encode(path)), err))
  }


  ghost function InvalidCountMessage(unit: HeadSchema.CountUnit, value: string): BenchWorld.Bytes
  {
    var displayValue := if |value| > 0 && value[0] == '-' then value[1..] else value;
    Utf8.Encode(InvalidCountText(unit, SE.SpecLocaleQuoteBytes(Utf8.Encode(displayValue))))
  }


  ghost function InputsFromOperands(operands: seq<string>): seq<HeadSchema.Input>
    decreases |operands|
  {
    if |operands| == 0 then
      []
    else
      [(if operands[0] == "-" then HeadSchema.Stdin("standard input") else HeadSchema.File(operands[0]))] +
      InputsFromOperands(operands[1..])
  }

  function HelpBeforeOther(raw: HeadSchema.HeadCmdRaw): bool
  {
    raw.seenHelp &&
    (!raw.seenVersion || raw.helpTokenIndex <= raw.versionTokenIndex) &&
    (raw.invalidCountTokenIndex == -1 || raw.helpTokenIndex <= raw.invalidCountTokenIndex)
  }

  function VersionBeforeInvalid(raw: HeadSchema.HeadCmdRaw): bool
  {
    raw.seenVersion &&
    (raw.invalidCountTokenIndex == -1 || raw.versionTokenIndex <= raw.invalidCountTokenIndex)
  }

  ghost function Command(raw: HeadSchema.HeadCmdRaw): HeadSchema.HeadCmd
  {
    var mode :=
      if HelpBeforeOther(raw) then
        HeadSchema.ModeHelp
      else if VersionBeforeInvalid(raw) then
        HeadSchema.ModeVersion
      else if raw.invalidCountTokenIndex != -1 then
        HeadSchema.ModeInvalidCount
      else
        HeadSchema.ModeRun;
    var inputs := InputsFromOperands(raw.operands);
    var runInputs := if mode == HeadSchema.ModeRun && |inputs| == 0 then [HeadSchema.Stdin("standard input")] else inputs;
    HeadSchema.HeadCmd(
      mode,
      raw.selection,
      raw.headerMode,
      raw.zeroTerminated,
      raw.invalidCountUnit,
      raw.invalidCountValue,
      runInputs
    )
  }

  function IsStdinInput(input: HeadSchema.Input): bool
  {
    match input
    case Stdin(_) => true
    case File(_) => false
  }

  function InputName(input: HeadSchema.Input): string
  {
    match input
    case Stdin(displayName) => displayName
    case File(path) => path
  }

  ghost predicate ReadResultRelation(
    cmd: HeadSchema.HeadCmd,
    preFs: BenchWorld.FileSystem, preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult,
    preStdin: BenchWorld.Bytes,
    i: nat,
    result: BenchWorld.IOResult<BenchWorld.Bytes>
  )
    requires i < |cmd.inputs|
  {
    match cmd.inputs[i]
    case Stdin(_) =>
      result == IOContract.ObservedReadStdinResultFields(preStdin, preStreams)
    case File(path) =>
      result == IOContract.ObservedReadFileResultFields(preFs, preStreams, path)
  }

  ghost predicate ByteSelectionRelation(
    data: BenchWorld.Bytes,
    count: nat,
    fromEnd: bool,
    output: BenchWorld.Bytes
  )
  {
    var cut :=
      if fromEnd
      then if |data| <= count then 0 else |data| - count
      else if |data| <= count then |data| else count;
    output == data[..cut]
  }

  // HeadSchema decodes modern and obsolete GNU count syntaxes, including
  // deterministic multiplier suffixes, into this shared finite selection model.
  ghost predicate DataSelectionRelation(
    cmd: HeadSchema.HeadCmd,
    data: BenchWorld.Bytes,
    output: BenchWorld.Bytes
  )
  {
    if cmd.selection.unit == HeadSchema.CountBytes then
      ByteSelectionRelation(
        data, cmd.selection.amount, cmd.selection.fromEnd, output
      )
    else
      HeadRecordSpec.RecordSelectionRelation(
        data,
        cmd.selection.amount,
        HeadRecordSpec.RecordDelimiter(cmd.zeroTerminated),
        cmd.selection.fromEnd,
        output
      )
  }

  function ShouldPrintHeaders(cmd: HeadSchema.HeadCmd): bool
  {
    cmd.headerMode == HeadSchema.HeadersAlways ||
    (cmd.headerMode == HeadSchema.HeadersMultiple && |cmd.inputs| > 1)
  }

  ghost function HeaderForInput(cmd: HeadSchema.HeadCmd, input: HeadSchema.Input, printedHeaders: int): BenchWorld.Bytes
  {
    if ShouldPrintHeaders(cmd) then
      (if printedHeaders == 0 then [] else ['\n']) +
      HeaderText(InputName(input))
    else
      []
  }

  ghost function StdinReadErrorMessage(error: BenchWorld.IOError): BenchWorld.Bytes
  {
    StdinReadErrorPrefix() + Utf8.Encode(ErrnoText(error)) + DiagnosticSuffix()
  }


  ghost predicate StdinTraceRelation(
    cmd: HeadSchema.HeadCmd, before: BenchWorld.Bytes, after: BenchWorld.Bytes,
    observations: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult,
    states: seq<BenchWorld.Bytes>
  )
  {
    |states| == |cmd.inputs| + 1 && states[0] == before && states[|cmd.inputs|] == after &&
    forall i: nat | i < |cmd.inputs| ::
      states[i + 1] == (if cmd.inputs[i].Stdin? then
                          IOContract.ObservedReadStdinRemainingFields(states[i], observations) else states[i])
  }

  ghost predicate InputObservationRelation(
    cmd: HeadSchema.HeadCmd,
    preFs: BenchWorld.FileSystem, preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult,
    preStdin: BenchWorld.Bytes,
    i: nat,
    result: BenchWorld.IOResult<BenchWorld.Bytes>,
                                printedHeaders: nat,
                                output: BenchWorld.Bytes,
                                errorOutput: BenchWorld.Bytes,
                                successful: bool,
                                failed: bool
  )
    requires i < |cmd.inputs|
  {
    ReadResultRelation(cmd, preFs, preStreams, preStdin, i, result) &&
    (match cmd.inputs[i]
     case Stdin(_) =>
       (match result
        case Ok(data) =>
          exists selected: BenchWorld.Bytes ::
            DataSelectionRelation(cmd, data, selected) &&
            output == HeaderForInput(cmd, cmd.inputs[i], printedHeaders) + selected &&
            errorOutput == [] &&
            successful &&
            !failed
        case Err(error) =>
          if error.StreamFailure? then
            exists selected: BenchWorld.Bytes ::
              DataSelectionRelation(cmd, error.partial, selected) &&
              output == HeaderForInput(cmd, cmd.inputs[i], printedHeaders) + selected &&
              errorOutput == StdinReadErrorMessage(error) && successful && failed
          else output == [] && errorOutput == StdinReadErrorMessage(error) && !successful && failed)
     case File(path) =>
       (match result
        case Ok(data) =>
          exists selected: BenchWorld.Bytes ::
            DataSelectionRelation(cmd, data, selected) &&
            output == HeaderForInput(cmd, cmd.inputs[i], printedHeaders) + selected &&
            errorOutput == [] &&
            successful &&
            !failed
        case Err(err) =>
          if err.ReadFailure? && err.readStage == BenchWorld.CloseFailed then
            exists selected: BenchWorld.Bytes ::
              DataSelectionRelation(cmd, err.partial, selected) &&
              output == HeaderForInput(cmd, cmd.inputs[i], printedHeaders) + selected &&
              errorOutput == ErrorMessage(path, err) && successful && failed
          else
            output == [] &&
            errorOutput == ErrorMessage(path, err) &&
            !successful &&
            failed))
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
    forall i: nat {:trigger cuts[i]} | i < |fragments| ::
      cuts[i] <= cuts[i + 1] &&
      cuts[i + 1] <= |combined| &&
      cuts[i + 1] == cuts[i] + |fragments[i]| &&
      combined[cuts[i]..cuts[i + 1]] == fragments[i]
  }

  opaque ghost predicate InputTraceWitnessRelation(
    cmd: HeadSchema.HeadCmd,
    preFs: BenchWorld.FileSystem, preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult,
    preStdin: BenchWorld.Bytes,
    postStdin: BenchWorld.Bytes,
    output: BenchWorld.Bytes,
    errorOutput: BenchWorld.Bytes,
    hadError: bool,
    results: seq<BenchWorld.IOResult<BenchWorld.Bytes>>,
    outputFragments: seq<BenchWorld.Bytes>,
    errorFragments: seq<BenchWorld.Bytes>,
    successful: seq<bool>,
    failed: seq<bool>,
    outputCuts: seq<nat>,
    errorCuts: seq<nat>
  )
  {
    exists stdinStates: seq<BenchWorld.Bytes> ::
      StdinTraceRelation(cmd, preStdin, postStdin, preStreams, stdinStates) &&
      |results| == |cmd.inputs| &&
      |outputFragments| == |cmd.inputs| &&
      |errorFragments| == |cmd.inputs| &&
      |successful| == |cmd.inputs| &&
      |failed| == |cmd.inputs| &&
      (forall i: nat | i < |cmd.inputs| ::
         InputObservationRelation(
           cmd, preFs, preStreams, stdinStates[i], i, results[i],
           |set j: nat | j < i && successful[j]|,
           outputFragments[i], errorFragments[i], successful[i], failed[i]
         )) &&
      FragmentsConcatenate(outputFragments, output, outputCuts) &&
      FragmentsConcatenate(errorFragments, errorOutput, errorCuts) &&
      hadError == (true in failed)
  }

  opaque ghost predicate InputTraceRelation(
    cmd: HeadSchema.HeadCmd,
    preFs: BenchWorld.FileSystem, preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult,
    preStdin: BenchWorld.Bytes,
    postStdin: BenchWorld.Bytes,
    output: BenchWorld.Bytes,
    errorOutput: BenchWorld.Bytes,
    hadError: bool
  )
  {
    exists results: seq<BenchWorld.IOResult<BenchWorld.Bytes>>,
      outputFragments: seq<BenchWorld.Bytes>,
      errorFragments: seq<BenchWorld.Bytes>,
      successful: seq<bool>,
      failed: seq<bool>,
      outputCuts: seq<nat>,
      errorCuts: seq<nat> ::
      InputTraceWitnessRelation(
        cmd, preFs, preStreams, preStdin, postStdin, output, errorOutput, hadError,
        results, outputFragments, errorFragments, successful, failed,
        outputCuts, errorCuts
      )
  }

  twostate predicate PreparedSpec(raw: HeadSchema.HeadCmdRaw, io: BenchIO.IO, exit: int, plannedStdout: BenchWorld.Bytes, plannedStderr: BenchWorld.Bytes)
    reads io.stdinRegion
  {
    var cmd := Command(raw);
    if cmd.mode == HeadSchema.ModeHelp then
      io.stdin() == old(io.stdin()) &&
      plannedStdout == old(io.stdout()) + HelpText() &&
      plannedStderr == old(io.stderr()) &&
      exit == 0
    else if cmd.mode == HeadSchema.ModeVersion then
      io.stdin() == old(io.stdin()) &&
      plannedStdout == old(io.stdout()) + VersionText() &&
      plannedStderr == old(io.stderr()) &&
      exit == 0
    else if cmd.mode == HeadSchema.ModeInvalidCount then
      io.stdin() == old(io.stdin()) &&
      plannedStdout == old(io.stdout()) &&
      plannedStderr == old(io.stderr()) + InvalidCountMessage(cmd.invalidCountUnit, cmd.invalidCountValue) &&
      exit == 1
    else
      exists output: BenchWorld.Bytes,
        errorOutput: BenchWorld.Bytes,
        hadError: bool ::
        InputTraceRelation(
          cmd, old(io.fs()), old(io.trustedStreams()), old(io.stdin()), io.stdin(),
          output, errorOutput, hadError
        ) &&
        plannedStdout == old(io.stdout()) + output &&
        plannedStderr == old(io.stderr()) + errorOutput &&
        exit == (if hadError then 1 else 0)
  }

  function Emits(raw: HeadSchema.HeadCmdRaw): bool
  {
    true
  }

  ghost function StreamWriteErrorMessage(message: string): BenchWorld.Bytes
  {
    StreamUtf8.Encode(StreamWriteErrorText(message))
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

  twostate predicate Emission(raw: HeadSchema.HeadCmdRaw, io: BenchIO.IO,
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

  twostate predicate Spec(raw: HeadSchema.HeadCmdRaw, io: BenchIO.IO, exit: int)
    reads io.stdinRegion, io.stdoutRegion, io.stderrRegion
  {
    exists out: BenchWorld.Bytes, diagnostics: BenchWorld.Bytes, normalExit: int ::
      PreparedSpec(raw, io, normalExit,
                   old(io.stdout()) + out, old(io.stderr()) + diagnostics) &&
      Emission(raw, io, out, diagnostics, normalExit, exit)
  }
  function ErrorMessageText(quoted: BenchWorld.Bytes, err: BenchWorld.IOError): string
  {
    if err.ReadFailure? && err.readStage == BenchWorld.CloseFailed then
      "head: failed to close " + quoted + ": " + ErrnoText(err) + "\n"
    else if IOContract.IOErrorIsReadFailure(err) then
      "head: error reading " + quoted + ": " + ErrnoText(err) + "\n"
    else
      "head: cannot open " + quoted + " for reading: " + ErrnoText(err) + "\n"
  }

  function InvalidCountText(unit: HeadSchema.CountUnit, quoted: BenchWorld.Bytes): string
  {
    "head: invalid number of " +
    (if unit == HeadSchema.CountLines then "lines" else "bytes") + ": " + quoted + "\n"
  }

  ghost function HeaderText(name: string): BenchWorld.Bytes
  {
    HeaderPrefix() + Utf8.Encode(name) + HeaderSuffix()
  }

  function HeaderPrefix(): BenchWorld.Bytes { "==> " }
  function HeaderSuffix(): BenchWorld.Bytes { " <==\n" }
  function DiagnosticSuffix(): BenchWorld.Bytes { "\n" }
  function StdinReadErrorPrefix(): BenchWorld.Bytes { "head: error reading 'standard input': " }
  function StreamWriteErrorText(message: string): string { "head: write error: " + message + "\n" }

}
