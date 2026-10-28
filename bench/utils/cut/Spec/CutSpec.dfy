include "../../../core/World.dfy"
include "../../../core/IO.dfy"
include "../../../core/IOContract.dfy"
include "../../../core/StringEscaping.dfy"
include "CutSchema.dfy"

module CutSpec {

  const ErrorMessageText0: BenchWorld.Bytes := "cut: "

  const ErrorMessageText1: BenchWorld.Bytes := ": "

  const ErrorMessageText2: BenchWorld.Bytes := "\n"

  const StreamWriteErrorMessageText0: BenchWorld.Bytes := "cut: write error: "

  const StreamWriteErrorMessageText1: BenchWorld.Bytes := "\n"

  import StreamContract = IOContract
  import StreamUtf8 = Utf8Semantics

  import Result = Results
  import BenchIO
  import Utf8 = Utf8Semantics
  import BenchWorld
  import IOContract
  import CutSchema
  import SE = StringEscaping

  function HelpText(): BenchWorld.Bytes
  {
    "Usage: cut OPTION... [FILE]...\n"
    + "Print selected bytes or characters from each line of each FILE.\n"
    + "\n"
    + "With no FILE, or when FILE is -, read standard input.\n"
    + "  -b, --bytes=LIST        select only these bytes\n"
    + "  -c, --characters=LIST   select only these characters\n"
    + "      --complement        complement the set of selected bytes or characters\n"
    + "  -n                      parsed for compatibility; no effect in byte mode\n"
    + "      --output-delimiter=STRING  use STRING between selected byte/character ranges\n"
    + "  -z, --zero-terminated   line delimiter is NUL, not newline\n"
    + "      --help              display this help and exit\n"
    + "      --version           output version information and exit\n"
    + "\n"
    + "Full documentation <https://www.gnu.org/software/coreutils/cut>\n"
    + "or available locally via: info '(coreutils) cut invocation'\n"
  }

  function VersionText(): BenchWorld.Bytes
  {
    "cut (GNU coreutils) 9.10.13-2cf49\n"
    + "Copyright (C) 2026 Free Software Foundation, Inc.\n"
    + "License GPLv3+: GNU GPL version 3 or later <https://gnu.org/licenses/gpl.html>.\n"
    + "This is free software: you are free to change and redistribute it.\n"
    + "There is NO WARRANTY, to the extent permitted by law.\n"
    + "\n"
    + "Written by David M. Ihnat, David MacKenzie, and Jim Meyering.\n"
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
    ErrorMessageText0 + SE.SpecQuoteFBytes(Utf8.Encode(path)) + ErrorMessageText1 + Utf8.Encode(ErrnoText(err)) + ErrorMessageText2
  }

  function RangeContains(range: CutSchema.Range, pos: int): bool
  {
    if range.openEnd then
      range.first <= pos
    else
      range.first <= pos <= range.last
  }

  function RecordDelimiter(zeroTerminated: bool): BenchWorld.RawByte
  {
    if zeroTerminated then '\0' else '\n'
  }

  function OutputDelimiterBytes(delimiter: CutSchema.OutputDelimiter): BenchWorld.Bytes
  {
    match delimiter
    case OutputDefault => []
    case OutputCustom(text) => if |text| == 0 then ['\0'] else Utf8.Encode(text)
  }

  ghost predicate StrictlyIncreasing(indices: seq<nat>)
  {
    forall i, j :: 0 <= i < j < |indices| ==> indices[i] < indices[j]
  }

  predicate PositionSelected(selection: CutSchema.Selection, position: int)
  {
    1 <= position &&
    selection.complement !=
    (exists i :: 0 <= i < |selection.ranges| &&
                 RangeContains(selection.ranges[i], position))
  }

  predicate DelimiterBeforeSelected(
    command: CutSchema.CutCmdRaw,
    position: int
  )
  {
    command.outputDelimiter.OutputCustom? &&
    1 < position &&
    if command.selection.complement then
      !PositionSelected(command.selection, position - 1)
    else
      (!(exists i :: 0 <= i < |command.selection.ranges| &&
                     RangeContains(command.selection.ranges[i], position - 1) &&
                     RangeContains(command.selection.ranges[i], position)))
  }

  ghost predicate SelectedIndexSequence(
    selection: CutSchema.Selection,
    recordLength: nat,
    selectedIndices: seq<nat>
  )
  {
    StrictlyIncreasing(selectedIndices) &&
    (forall k {:trigger selectedIndices[k]} ::
       0 <= k < |selectedIndices| ==>
         selectedIndices[k] < recordLength &&
         PositionSelected(selection, selectedIndices[k] + 1)) &&
    (forall i {:trigger PositionSelected(selection, i + 1)} ::
       0 <= i < recordLength ==>
         PositionSelected(selection, i + 1) ==
         (i in selectedIndices))
  }

  ghost predicate RecordSelectionWitnessRelation(
    command: CutSchema.CutCmdRaw,
    record: BenchWorld.Bytes,
    output: BenchWorld.Bytes,
    selectedIndices: seq<nat>,
    outputCuts: seq<nat>
  )
  {
    SelectedIndexSequence(
      command.selection, |record|, selectedIndices
    ) &&
    exists fragments: seq<BenchWorld.Bytes> ::
      |fragments| == |selectedIndices| &&
      (forall k :: 0 <= k < |selectedIndices| ==>
                     fragments[k] ==
                     (if k > 0 && DelimiterBeforeSelected(
                           command, selectedIndices[k] + 1
                         )
                      then OutputDelimiterBytes(command.outputDelimiter)
                      else []) +
                     [record[selectedIndices[k]]]) &&
      FragmentsConcatenate(fragments, output, outputCuts)
  }

  ghost predicate RecordSelectionRelation(
    command: CutSchema.CutCmdRaw,
    record: BenchWorld.Bytes,
    output: BenchWorld.Bytes
  )
  {
    exists selectedIndices: seq<nat>, outputCuts: seq<nat> ::
      RecordSelectionWitnessRelation(
        command, record, output, selectedIndices, outputCuts
      )
  }

  ghost predicate RecordPartitionWitnessRelation(
    data: BenchWorld.Bytes,
    delimiter: BenchWorld.RawByte,
    records: seq<BenchWorld.Bytes>,
    terminated: seq<bool>,
    fragments: seq<BenchWorld.Bytes>,
    cuts: seq<nat>
  )
  {
    |records| == |terminated| == |fragments| &&
    (|data| == 0) == (|records| == 0) &&
    (forall i :: 0 <= i < |records| ==>
                   |fragments[i]| > 0 &&
                   fragments[i] ==
                   records[i] + (if terminated[i] then [delimiter] else []) &&
                   delimiter !in records[i] &&
                   (i + 1 < |records| ==> terminated[i])) &&
    FragmentsConcatenate(fragments, data, cuts)
  }

  ghost predicate RecordPartitionRelation(
    data: BenchWorld.Bytes,
    delimiter: BenchWorld.RawByte,
    records: seq<BenchWorld.Bytes>,
    terminated: seq<bool>
  )
  {
    exists fragments: seq<BenchWorld.Bytes>, cuts: seq<nat> ::
      RecordPartitionWitnessRelation(
        data, delimiter, records, terminated, fragments, cuts
      )
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

  ghost predicate DataSelectionWitnessRelation(
    command: CutSchema.CutCmdRaw,
    data: BenchWorld.Bytes,
    output: BenchWorld.Bytes,
    records: seq<BenchWorld.Bytes>,
    terminated: seq<bool>,
    fragments: seq<BenchWorld.Bytes>,
    renderedFragments: seq<BenchWorld.Bytes>,
    outputCuts: seq<nat>
  )
  {
    RecordPartitionRelation(
      data, RecordDelimiter(command.zeroTerminated), records, terminated
    ) &&
    |fragments| == |records| &&
    |renderedFragments| == |fragments| &&
    (forall i :: 0 <= i < |records| ==>
                   RecordSelectionRelation(command, records[i], fragments[i]) &&
                   renderedFragments[i] ==
                   fragments[i] + [RecordDelimiter(command.zeroTerminated)]) &&
    FragmentsConcatenate(renderedFragments, output, outputCuts)
  }

  ghost predicate DataSelectionRelation(
    command: CutSchema.CutCmdRaw,
    data: BenchWorld.Bytes,
    output: BenchWorld.Bytes
  )
  {
    exists records: seq<BenchWorld.Bytes>,
      terminated: seq<bool>,
      fragments: seq<BenchWorld.Bytes>,
      renderedFragments: seq<BenchWorld.Bytes>,
      outputCuts: seq<nat> ::
      DataSelectionWitnessRelation(
        command, data, output, records, terminated, fragments,
        renderedFragments, outputCuts
      )
  }

  ghost predicate InputReadRelation(
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
      result == IOContract.ObservedReadStdinResultFields(preStdin, preStreams)
    case File(path) =>
      result == IOContract.ObservedReadFileResultFields(preFs, preStreams, path)
  }

  ghost predicate StdinTraceRelation(
    command: CutSchema.CutCmdRaw, before: BenchWorld.Bytes, after: BenchWorld.Bytes,
    observations: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult,
    states: seq<BenchWorld.Bytes>
  )
  {
    |states| == |command.inputs| + 1 && states[0] == before && states[|command.inputs|] == after &&
    forall i: nat | i < |command.inputs| ::
      states[i + 1] == (if command.inputs[i].Stdin? then
                          IOContract.ObservedReadStdinRemainingFields(states[i], observations) else states[i])
  }

  opaque ghost predicate InputTraceWitnessRelation(
    command: CutSchema.CutCmdRaw, preFs: BenchWorld.FileSystem,
    beforeStdin: BenchWorld.Bytes, afterStdin: BenchWorld.Bytes,
    observations: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult,
    readResults: seq<BenchWorld.IOResult<BenchWorld.Bytes>>,
    stdoutPart: BenchWorld.Bytes, stderrPart: BenchWorld.Bytes, hadError: bool,
    stdinStates: seq<BenchWorld.Bytes>, stdoutFragments: seq<BenchWorld.Bytes>,
    stderrFragments: seq<BenchWorld.Bytes>, stdoutCuts: seq<nat>, stderrCuts: seq<nat>)
  {
    StdinTraceRelation(command, beforeStdin, afterStdin, observations, stdinStates) &&
    |readResults| == |command.inputs| &&
    |stdoutFragments| == |command.inputs| &&
    |stderrFragments| == |command.inputs| &&
    (forall i :: 0 <= i < |command.inputs| ==>
                   InputReadRelation(
                     command, preFs, stdinStates[i], i, readResults[i],
                     observations
                   ) &&
                   match command.inputs[i]
                   case Stdin =>
                     (match readResults[i]
                      case Ok(data) =>
                        DataSelectionRelation(command, data, stdoutFragments[i]) &&
                        stderrFragments[i] == []
                      case Err(error) =>
                        (if error.StreamFailure? then DataSelectionRelation(command, error.partial, stdoutFragments[i])
                         else stdoutFragments[i] == []) &&
                        stderrFragments[i] == ErrorMessage("-", error))
                   case File(path) =>
                     (match readResults[i]
                      case Ok(data) =>
                        DataSelectionRelation(command, data, stdoutFragments[i]) &&
                        stderrFragments[i] == []
                      case Err(err) =>
                        stdoutFragments[i] == [] &&
                        stderrFragments[i] == ErrorMessage(path, err))) &&
    FragmentsConcatenate(stdoutFragments, stdoutPart, stdoutCuts) &&
    FragmentsConcatenate(stderrFragments, stderrPart, stderrCuts) &&
    hadError ==
    (exists i :: 0 <= i < |command.inputs| &&
                 readResults[i].Err?)
  }

  twostate predicate InputTraceRelation(
    command: CutSchema.CutCmdRaw,
    io: BenchIO.IO,
    new readResults: seq<BenchWorld.IOResult<BenchWorld.Bytes>>,
    new stdoutPart: BenchWorld.Bytes,
    new stderrPart: BenchWorld.Bytes,
    hadError: bool
  )
    reads io.stdinRegion
  {
    exists stdinStates: seq<BenchWorld.Bytes>, stdoutFragments: seq<BenchWorld.Bytes>,
      stderrFragments: seq<BenchWorld.Bytes>, stdoutCuts: seq<nat>, stderrCuts: seq<nat> ::
      InputTraceWitnessRelation(command, old(io.fs()), old(io.stdin()), io.stdin(), old(io.trustedStreams()),
                                readResults, stdoutPart, stderrPart, hadError, stdinStates, stdoutFragments, stderrFragments, stdoutCuts, stderrCuts)
  }

  twostate predicate PreparedSpec(raw: CutSchema.CutCmdRaw, io: BenchIO.IO, exit: int, plannedStdout: BenchWorld.Bytes, plannedStderr: BenchWorld.Bytes)
    reads io.stdinRegion
  {
    if raw.mode == CutSchema.ModeHelp then
      io.stdin() == old(io.stdin()) &&
      plannedStdout == HelpText() &&
      plannedStderr == [] &&
      exit == 0
    else if raw.mode == CutSchema.ModeVersion then
      io.stdin() == old(io.stdin()) &&
      plannedStdout == VersionText() &&
      plannedStderr == [] &&
      exit == 0
    else
      exists readResults: seq<BenchWorld.IOResult<BenchWorld.Bytes>>,
        stdoutPart: BenchWorld.Bytes,
        stderrPart: BenchWorld.Bytes,
        hadError: bool ::
        InputTraceRelation(
          raw, io, readResults, stdoutPart, stderrPart, hadError
        ) &&
        plannedStdout == stdoutPart &&
        plannedStderr == stderrPart &&
        exit == (if hadError then 1 else 0)
  }

  function Emits(raw: CutSchema.CutCmdRaw): bool
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

  twostate predicate Emission(raw: CutSchema.CutCmdRaw, io: BenchIO.IO,
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

  twostate predicate Spec(raw: CutSchema.CutCmdRaw, io: BenchIO.IO, exit: int)
    reads io.stdinRegion, io.stdoutRegion, io.stderrRegion
  {
    exists out: BenchWorld.Bytes, diagnostics: BenchWorld.Bytes, normalExit: int ::
      PreparedSpec(raw, io, normalExit,
                   out, diagnostics) &&
      Emission(raw, io, out, diagnostics, normalExit, exit)
  }
}
