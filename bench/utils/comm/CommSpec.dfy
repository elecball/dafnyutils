include "../../core/World.dfy"
include "../../core/IO.dfy"
include "../../core/IOContract.dfy"
include "../../core/StringEscaping.dfy"
include "CommSchema.dfy"
include "CommRenderSpec.dfy"

module CommSpec {

  const FileErrorMessageSpecText0: BenchWorld.Bytes := "comm: "

  const FileErrorMessageSpecText1: BenchWorld.Bytes := ": "

  const FileErrorMessageSpecText2: BenchWorld.Bytes := "\n"

  const InputErrorMessageSpecText0: BenchWorld.Bytes := "comm: -: "

  const InputErrorMessageSpecText1: BenchWorld.Bytes := "\n"

  const MissingOperandAfterMessageSpecText0: BenchWorld.Bytes := "comm: missing operand after "

  const MissingOperandAfterMessageSpecText1: BenchWorld.Bytes := "\n"

  const MissingOperandAfterMessageSpecText2: BenchWorld.Bytes := "Try 'comm --help' for more information.\n"

  const ExtraOperandMessageSpecText0: BenchWorld.Bytes := "comm: extra operand "

  const ExtraOperandMessageSpecText1: BenchWorld.Bytes := "\n"

  const ExtraOperandMessageSpecText2: BenchWorld.Bytes := "Try 'comm --help' for more information.\n"

  const StreamWriteErrorMessageText0: BenchWorld.Bytes := "comm: write error: "

  const StreamWriteErrorMessageText1: BenchWorld.Bytes := "\n"

  import StreamContract = IOContract
  import StreamUtf8 = Utf8Semantics

  import Result = Results
  import BenchIO
  import Utf8 = Utf8Semantics
  import BenchWorld
  import IOContract
  import Schema = CommSchema
  import Render = CommRenderSpec
  import SE = StringEscaping

  function HelpTextSpec(): BenchWorld.Bytes
  {
    "Usage: comm [OPTION]... FILE1 FILE2\n"
    + "Compare sorted files FILE1 and FILE2 line by line.\n"
    + "\n"
    + "  -1                      suppress lines unique to FILE1\n"
    + "  -2                      suppress lines unique to FILE2\n"
    + "  -3                      suppress lines common to both files\n"
    + "      --output-delimiter=STR  separate columns with STR\n"
    + "      --total             output a summary row\n"
    + "  -z, --zero-terminated   line delimiter is NUL, not newline\n"
    + "      --help              display this help and exit\n"
    + "      --version           output version information and exit\n"
    + "\n"
    + "Benchmark note: sorted byte records, one optional stdin operand, and no locale collation.\n"
    + "Deferred: precise GNU sortedness diagnostics, repeated stdin operands, and locale.\n"
  }

  function VersionTextSpec(): BenchWorld.Bytes
  {
    "comm (GNU coreutils) 9.10.13-2cf49\n"
    + "Copyright (C) 2026 Free Software Foundation, Inc.\n"
    + "License GPLv3+: GNU GPL version 3 or later <https://gnu.org/licenses/gpl.html>.\n"
    + "This is free software: you are free to change and redistribute it.\n"
    + "There is NO WARRANTY, to the extent permitted by law.\n"
    + "\n"
    + "Written by Richard M. Stallman and David MacKenzie.\n"
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

  function ContainsDiagnosticBlank(path: string): bool
    decreases |path|
  {
    if |path| == 0 then
      false
    else
      path[0] == ' ' || path[0] == '\t' || ContainsDiagnosticBlank(path[1..])
  }

  function FileErrorMessageSpec(path: BenchWorld.Path, err: BenchWorld.IOError): BenchWorld.Bytes
  {
    FileErrorMessageSpecText0 + SE.SpecQuoteFBytes(Utf8.Encode(path)) + FileErrorMessageSpecText1 + Utf8.Encode(ErrnoText(err)) + FileErrorMessageSpecText2
  }

  function InputErrorMessageSpec(input: Schema.CommInput, err: BenchWorld.IOError): BenchWorld.Bytes
  {
    match input
    case Stdin => InputErrorMessageSpecText0 + Utf8.Encode(ErrnoText(err)) + InputErrorMessageSpecText1
    case File(path) => FileErrorMessageSpec(path, err)
  }

  function MissingOperandMessageSpec(): BenchWorld.Bytes
  {
    "comm: missing operand\nTry 'comm --help' for more information.\n"
  }

  function MissingOperandAfterMessageSpec(operand: string): BenchWorld.Bytes
  {
    MissingOperandAfterMessageSpecText0 + SE.SpecLocaleQuoteBytes(Utf8.Encode(operand)) + MissingOperandAfterMessageSpecText1 +
    MissingOperandAfterMessageSpecText2
  }

  function ExtraOperandMessageSpec(operand: string): BenchWorld.Bytes
  {
    ExtraOperandMessageSpecText0 + SE.SpecLocaleQuoteBytes(Utf8.Encode(operand)) + ExtraOperandMessageSpecText1 +
    ExtraOperandMessageSpecText2
  }

  function MultipleOutputDelimitersMessageSpec(): BenchWorld.Bytes
  {
    "comm: multiple output delimiters specified\n"
  }

  function UnsortedInputMessageSpec(): BenchWorld.Bytes
  {
    "comm: input is not sorted in the benchmark-supported byte order\n"
  }

  function RepeatedStdinOperandMessageSpec(): BenchWorld.Bytes
  {
    "comm: repeated standard input operands are not supported by this benchmark slice\n" +
    "Try 'comm --help' for more information.\n"
  }

  function FirstOperand(operands: seq<string>): string
  {
    if |operands| > 0 then operands[0] else ""
  }

  function SecondOperand(operands: seq<string>): string
  {
    if |operands| > 1 then operands[1] else ""
  }

  function InputFromOperand(operand: string): Schema.CommInput
  {
    if operand == "-" then Schema.Stdin else Schema.File(operand)
  }

  function CommandRelation(raw: Schema.CommCmdRaw): Schema.CommCmd
  {
    var first := FirstOperand(raw.operands);
    var second := SecondOperand(raw.operands);
    var mode :=
      if raw.seenHelp && (!raw.seenVersion || raw.helpTokenIndex <= raw.versionTokenIndex) then
        Schema.ModeHelp
      else if raw.seenVersion then
        Schema.ModeVersion
      else if Render.HasConflictingOutputDelimitersRelation(raw.outputDelimiters) then
        Schema.ModeMultipleOutputDelimiters
      else if |raw.operands| == 0 then
        Schema.ModeMissingOperand
      else if |raw.operands| == 1 then
        Schema.ModeMissingOperandAfter(raw.operands[0])
      else if |raw.operands| > 2 then
        Schema.ModeExtraOperand(raw.operands[2])
      else if first == "-" && second == "-" then
        Schema.ModeRepeatedStdinOperand
      else
        Schema.ModeRun;
    Schema.CommCmd(
      mode,
      raw.suppress1,
      raw.suppress2,
      raw.suppress3,
      raw.total,
      raw.zeroTerminated,
      Render.OutputDelimiterFromValues(raw.outputDelimiters),
      InputFromOperand(first),
      InputFromOperand(second)
    )
  }

  ghost function InputResult(
    preFs: BenchWorld.FileSystem, preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult,
    preStdin: BenchWorld.Bytes,
    input: Schema.CommInput
  ): BenchWorld.IOResult<BenchWorld.Bytes>
  {
    match input
    case Stdin => IOContract.ObservedReadStdinResultFields(preStdin, preStreams)
    case File(path) => IOContract.ObservedReadFileResultFields(preFs, preStreams, path)
  }

  ghost function AfterInputRead(preStdin: BenchWorld.Bytes, input: Schema.CommInput, preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult): BenchWorld.Bytes
  {
    match input
    case Stdin => IOContract.ObservedReadStdinRemainingFields(preStdin, preStreams)
    case File(_) => preStdin
  }

  ghost function ReadFirstResult(
    cmd: Schema.CommCmd,
    preFs: BenchWorld.FileSystem, preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult,
    preStdin: BenchWorld.Bytes
  ): BenchWorld.IOResult<BenchWorld.Bytes>
  {
    if cmd.mode == Schema.ModeRun then
      InputResult(preFs, preStreams, preStdin, cmd.input1)
    else
      Result.Ok([])
  }

  ghost function AfterFirstRead(cmd: Schema.CommCmd, preStdin: BenchWorld.Bytes, preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult): BenchWorld.Bytes
  {
    if cmd.mode == Schema.ModeRun then AfterInputRead(preStdin, cmd.input1, preStreams) else preStdin
  }

  ghost function ReadSecondResult(
    cmd: Schema.CommCmd,
    preFs: BenchWorld.FileSystem, preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult,
    preStdin: BenchWorld.Bytes
  ): BenchWorld.IOResult<BenchWorld.Bytes>
  {
    if cmd.mode == Schema.ModeRun then
      InputResult(preFs, preStreams, AfterFirstRead(cmd, preStdin, preStreams), cmd.input2)
    else
      Result.Ok([])
  }

  ghost function AfterSecondRead(cmd: Schema.CommCmd, preStdin: BenchWorld.Bytes, preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult): BenchWorld.Bytes
  {
    if cmd.mode == Schema.ModeRun then AfterInputRead(AfterFirstRead(cmd, preStdin, preStreams), cmd.input2, preStreams) else preStdin
  }

  // Formal specification gap: this relation intentionally preserves the
  // benchmark's simple byte-order sortedness diagnostic and excludes locale
  // collation, --check-order/--nocheck-order partial-output behavior, and
  // repeated-stdin file-descriptor diagnostics.
  twostate predicate SpecCmd(cmd: Schema.CommCmd, io: BenchIO.IO, exit: int, plannedStdout: BenchWorld.Bytes, plannedStderr: BenchWorld.Bytes)
    reads io.stdinRegion
  {
    match cmd.mode
    case ModeHelp =>
      io.stdin() == old(io.stdin()) &&
      plannedStdout == old(io.stdout()) + HelpTextSpec() &&
      plannedStderr == old(io.stderr()) &&
      exit == 0
    case ModeVersion =>
      io.stdin() == old(io.stdin()) &&
      plannedStdout == old(io.stdout()) + VersionTextSpec() &&
      plannedStderr == old(io.stderr()) &&
      exit == 0
    case ModeMissingOperand =>
      io.stdin() == old(io.stdin()) &&
      plannedStdout == old(io.stdout()) &&
      plannedStderr == old(io.stderr()) + MissingOperandMessageSpec() &&
      exit == 1
    case ModeMissingOperandAfter(operand) =>
      io.stdin() == old(io.stdin()) &&
      plannedStdout == old(io.stdout()) &&
      plannedStderr == old(io.stderr()) + MissingOperandAfterMessageSpec(operand) &&
      exit == 1
    case ModeExtraOperand(operand) =>
      io.stdin() == old(io.stdin()) &&
      plannedStdout == old(io.stdout()) &&
      plannedStderr == old(io.stderr()) + ExtraOperandMessageSpec(operand) &&
      exit == 1
    case ModeMultipleOutputDelimiters =>
      io.stdin() == old(io.stdin()) &&
      plannedStdout == old(io.stdout()) &&
      plannedStderr == old(io.stderr()) + MultipleOutputDelimitersMessageSpec() &&
      exit == 1
    case ModeRepeatedStdinOperand =>
      io.stdin() == old(io.stdin()) &&
      plannedStdout == old(io.stdout()) &&
      plannedStderr == old(io.stderr()) + RepeatedStdinOperandMessageSpec() &&
      exit == 1
    case ModeRun =>
      var first := ReadFirstResult(cmd, old(io.fs()), old(io.trustedStreams()), old(io.stdin()));
      if FirstReadAborts(cmd, first) then
        io.stdin() == AfterFirstRead(cmd, old(io.stdin()), old(io.trustedStreams())) &&
        plannedStdout == old(io.stdout()) &&
        plannedStderr == old(io.stderr()) + InputErrorMessageSpec(cmd.input1, first.e) && exit == 1
      else
        var second := ReadSecondResult(cmd, old(io.fs()), old(io.trustedStreams()), old(io.stdin()));
        io.stdin() == AfterSecondRead(cmd, old(io.stdin()), old(io.trustedStreams())) &&
        (if first.Err? || second.Err? then
           exists output: BenchWorld.Bytes, leftFault: bool ::
             FailedReadOutputRelation(cmd, first, second, output, leftFault) &&
             plannedStdout == old(io.stdout()) + output &&
             plannedStderr == old(io.stderr()) + FailedReadMessage(cmd, first, second, leftFault) && exit == 1
         else
           var leftData := first.v;
           var rightData := second.v;
           ((Render.DataSortedRelation(leftData, cmd.zeroTerminated) &&
             Render.DataSortedRelation(rightData, cmd.zeroTerminated) &&
             (exists stdoutPart: BenchWorld.Bytes ::
                Render.OutputRelation(cmd, leftData, rightData, stdoutPart) &&
                plannedStdout == old(io.stdout()) + stdoutPart) &&
             plannedStderr == old(io.stderr()) &&
             exit == 0) ||
            ((Render.DataUnsorted(leftData, cmd.zeroTerminated) ||
              Render.DataUnsorted(rightData, cmd.zeroTerminated)) &&
             plannedStdout == old(io.stdout()) &&
             plannedStderr == old(io.stderr()) + UnsortedInputMessageSpec() &&
             exit == 1)))
  }

  twostate predicate PreparedSpec(raw: Schema.CommCmdRaw, io: BenchIO.IO, exit: int, plannedStdout: BenchWorld.Bytes, plannedStderr: BenchWorld.Bytes)
    reads io.stdinRegion
  {
    SpecCmd(CommandRelation(raw), io, exit, plannedStdout, plannedStderr)
  }

  function Emits(raw: Schema.CommCmdRaw): bool
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

  twostate predicate Emission(raw: Schema.CommCmdRaw, io: BenchIO.IO,
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

  twostate predicate Spec(raw: Schema.CommCmdRaw, io: BenchIO.IO, exit: int)
    reads io.stdinRegion, io.stdoutRegion, io.stderrRegion
  {
    exists out: BenchWorld.Bytes, diagnostics: BenchWorld.Bytes, normalExit: int ::
      PreparedSpec(raw, io, normalExit,
                   old(io.stdout()) + out, old(io.stderr()) + diagnostics) &&
      Emission(raw, io, out, diagnostics, normalExit, exit)
  }
  ghost predicate CompleteInputPrefixRelation(data: BenchWorld.Bytes, delimiter: BenchWorld.RawByte, complete: BenchWorld.Bytes)
  {
    |complete| <= |data| && complete == data[..|complete|] &&
    (complete == [] || complete[|complete| - 1] == delimiter) &&
    forall i: nat | |complete| <= i < |data| :: data[i] != delimiter
  }

  predicate FirstReadAborts(cmd: Schema.CommCmd, first: BenchWorld.IOResult<BenchWorld.Bytes>)
    ensures FirstReadAborts(cmd, first) ==> first.Err?
  {
    first.Err? && Render.RecordDelimiter(cmd.zeroTerminated) !in IOContract.ReadResultData(first)
  }

  function FailedReadMessage(cmd: Schema.CommCmd, first: BenchWorld.IOResult<BenchWorld.Bytes>,
                                                                             second: BenchWorld.IOResult<BenchWorld.Bytes>, leftFault: bool): BenchWorld.Bytes
  {
    var result := if leftFault then first else second;
    match result
    case Err(error) => InputErrorMessageSpec(if leftFault then cmd.input1 else cmd.input2, error)
    case Ok(_) => []
  }

  ghost predicate ReadRecordsRelation(result: BenchWorld.IOResult<BenchWorld.Bytes>, delimiter: BenchWorld.RawByte,
                                                                  records: seq<BenchWorld.Bytes>)
  {
    exists data: BenchWorld.Bytes ::
      (if result.Ok? then data == result.v else CompleteInputPrefixRelation(IOContract.ReadResultData(result), delimiter, data)) &&
      Render.RecordPartition(data, delimiter, records)
  }

  ghost predicate FailedMergeWitness(cmd: Schema.CommCmd, left: seq<BenchWorld.Bytes>, right: seq<BenchWorld.Bytes>,
                                     leftFailed: bool, rightFailed: bool, output: BenchWorld.Bytes, leftFault: bool,
                                     kinds: seq<Render.MergeKind>, leftStates: seq<seq<BenchWorld.Bytes>>, rightStates: seq<seq<BenchWorld.Bytes>>,
                                     fragments: seq<BenchWorld.Bytes>, cuts: seq<nat>)
  {
    (leftFailed || rightFailed) &&
    |leftStates| == |rightStates| == |kinds| + 1 && |fragments| == |kinds| &&
    leftStates[0] == left && rightStates[0] == right &&
    leftFault == (leftFailed && leftStates[|kinds|] == []) &&
    (leftFault || (rightFailed && rightStates[|kinds|] == [])) &&
    (forall i: nat | i < |kinds| ::
       (!leftFailed || leftStates[i] != []) && (!rightFailed || rightStates[i] != []) &&
       Render.MergeStepRelation(cmd, kinds[i], leftStates[i], leftStates[i + 1],
                                rightStates[i], rightStates[i + 1], fragments[i])) &&
    Render.FragmentsConcatenate(fragments, output, cuts)
  }

  // Partial read failures extend the existing byte-order model. GNU's per-file
  // disorder-warning timing remains part of the documented sortedness gap above.
  ghost predicate FailedReadOutputRelation(cmd: Schema.CommCmd,
                                           first: BenchWorld.IOResult<BenchWorld.Bytes>, second: BenchWorld.IOResult<BenchWorld.Bytes>,
                                                                                                                     output: BenchWorld.Bytes, leftFault: bool)
  {
    exists left: seq<BenchWorld.Bytes>, right: seq<BenchWorld.Bytes>, kinds: seq<Render.MergeKind>,
      leftStates: seq<seq<BenchWorld.Bytes>>, rightStates: seq<seq<BenchWorld.Bytes>>,
      fragments: seq<BenchWorld.Bytes>, cuts: seq<nat> ::
      ReadRecordsRelation(first, Render.RecordDelimiter(cmd.zeroTerminated), left) &&
      ReadRecordsRelation(second, Render.RecordDelimiter(cmd.zeroTerminated), right) &&
      FailedMergeWitness(cmd, left, right, first.Err?, second.Err?, output, leftFault,
                         kinds, leftStates, rightStates, fragments, cuts)
  }
}
