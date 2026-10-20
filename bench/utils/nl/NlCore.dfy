include "NlTextCore.dfy"
include "../../core/World.dfy"
include "../../core/IO.dfy"
include "../../core/IOContract.dfy"
include "NlSchema.dfy"
include "NlSpec.dfy"

module NlCore {
  import Text = NlTextCore

  import StreamContract = IOContract

  import Result = Results
  import BenchIO
  import Utf8 = NlUtf8Core
  import BenchWorld
  import IOContract
  import NlSchema
  import Spec = NlSpec

  twostate predicate PreparedSummary(
    raw: NlSchema.NlCmdRaw,
    io: BenchIO.IO,
    exit: int,
    new readResults: seq<BenchWorld.IOResult<BenchWorld.Bytes>>,
    new inputFragments: seq<BenchWorld.Bytes>,
    new combined: BenchWorld.Bytes,
    new inputCuts: seq<nat>,
    new errorFragments: seq<BenchWorld.Bytes>,
    new errorOutput: BenchWorld.Bytes,
    new errorCuts: seq<nat>,
    hadError: bool,
    hasDelimiter: bool,
    new outputPart: BenchWorld.Bytes
  , plannedStdout: BenchWorld.Bytes, plannedStderr: BenchWorld.Bytes)
    reads io.stdinRegion
  {
    var cmd := NlSchema.Command(raw);
    if cmd.mode == NlSchema.ModeHelp then
      io.stdin() == old(io.stdin()) &&
      plannedStdout == Spec.HelpText() &&
      plannedStderr == Text.OptionErrorsText(cmd.optionErrors) &&
      exit == 0
    else if cmd.mode == NlSchema.ModeVersion then
      io.stdin() == old(io.stdin()) &&
      plannedStdout == Spec.VersionText() &&
      plannedStderr == Text.OptionErrorsText(cmd.optionErrors) &&
      exit == 0
    else if cmd.mode != NlSchema.ModeRun then
      io.stdin() == old(io.stdin()) &&
      plannedStdout == [] &&
      plannedStderr == Text.ModeErrorMessage(cmd) &&
      exit == 1
    else
      InputTraceSummary(
        cmd, old(io.fs()), old(io.stdin()), readResults, inputFragments,
        combined, inputCuts, errorFragments, errorOutput, errorCuts,
        hadError, hasDelimiter,
        old(io.trustedStreams())
      , io.stdin()) &&
      (if hasDelimiter then
         outputPart == []
       else
         OutputSummary(cmd, combined, outputPart)) &&
      plannedStdout == outputPart &&
      plannedStderr == errorOutput +
      (if hasDelimiter then
         Spec.UnsupportedLogicalPageDelimiterMessage()
       else
         []) &&
      exit == (if hasDelimiter || hadError then 1 else 0)
  }

  opaque function NormalizeInputData(data: BenchWorld.Bytes): BenchWorld.Bytes
  {
    if |data| > 0 && data[|data| - 1] != '\n' then
      data + ['\n']
    else
      data
  } by method {
    reveal NormalizeInputData();
    if |data| > 0 && data[|data| - 1] != '\n' {
      return data + ['\n'];
    } else {
      return data;
    }
  }

  opaque function IsLogicalPageDelimiterLine(
    line: BenchWorld.Bytes
  ): bool
  {
    line == [(92 as char), ':'] ||
    line == [(92 as char), ':', (92 as char), ':'] ||
    line == [(92 as char), ':', (92 as char), ':', (92 as char), ':']
  } by method {
    reveal IsLogicalPageDelimiterLine();
    return line == [(92 as char), ':'] ||
           line == [(92 as char), ':', (92 as char), ':'] ||
           line == [(92 as char), ':', (92 as char), ':', (92 as char), ':'];
  }

  opaque ghost function PrefixStdinCore(cmd: NlSchema.NlCmd, before: BenchWorld.Bytes, count: nat,
    observations: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult): BenchWorld.Bytes
    requires count <= |cmd.inputs|
    decreases count
  {
    if count == 0 then before else
      var previous := PrefixStdinCore(cmd, before, count - 1, observations);
      if cmd.inputs[count - 1].Stdin? then IOContract.ObservedReadStdinRemainingFields(previous, observations) else previous
  }

  lemma PrefixStdinStep(cmd: NlSchema.NlCmd, before: BenchWorld.Bytes, count: nat,
    observations: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult)
    requires count < |cmd.inputs|
    ensures PrefixStdinCore(cmd, before, count + 1, observations) ==
      (if cmd.inputs[count].Stdin? then IOContract.ObservedReadStdinRemainingFields(
        PrefixStdinCore(cmd, before, count, observations), observations)
       else PrefixStdinCore(cmd, before, count, observations))
  {
      reveal PrefixStdinCore();
  }

  ghost predicate InputTraceSummary(
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
    postStdin == PrefixStdinCore(cmd, preStdin, |cmd.inputs|, preStreams) &&
    |readResults| == |cmd.inputs| &&
    |inputFragments| == |cmd.inputs| &&
    |errorFragments| == |cmd.inputs| &&
    (forall i :: 0 <= i < |cmd.inputs| ==>
                   Spec.ReadResultRelation(cmd, preFs, PrefixStdinCore(cmd, preStdin, i, preStreams), i, readResults[i], preStreams) &&
                   inputFragments[i] ==
                   (match readResults[i]
                    case Ok(data) => NormalizeInputData(data)
                    case Err(error) => if error.StreamFailure? then NormalizeInputData(error.partial) else []) &&
                   errorFragments[i] ==
                   Text.ErrorPiece(cmd.inputs[i], readResults[i])) &&
    Spec.FragmentsConcatenate(
      inputFragments, combined, inputCuts) &&
    Spec.FragmentsConcatenate(
      errorFragments, errorOutput, errorCuts) &&
    hadError ==
    (exists i :: 0 <= i < |cmd.inputs| &&
                 Spec.HadErrorPiece(cmd.inputs[i], readResults[i])) &&
    (exists lines: seq<BenchWorld.Bytes>,
       terminated: seq<bool>,
       fragments: seq<BenchWorld.Bytes>,
       cuts: seq<nat> ::
       Spec.LinePartitionRelation(
         combined, lines, terminated, fragments, cuts) &&
       hasDelimiter ==
       (exists i :: 0 <= i < |lines| &&
                    IsLogicalPageDelimiterLine(lines[i])))
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

  function RenderNumber(
    format: NlSchema.NumberFormat,
    n: int,
    width: int
  ): BenchWorld.Bytes
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

  function ShouldNumber(
    style: NlSchema.BodyStyle,
    nonempty: bool
  ): bool
  {
    style == NlSchema.NumberAll ||
    (style == NlSchema.NumberNonEmpty && nonempty)
  }

  function LinePrefix(
    cmd: NlSchema.NlCmd,
    nonempty: bool,
    n: int
  ): BenchWorld.Bytes
    requires 0 <= n
  {
    if ShouldNumber(cmd.bodyStyle, nonempty) then
      RenderNumber(cmd.numberFormat, n, 6) + cmd.separator
    else
      RepeatChar(' ', 6 + |cmd.separator|)
  }

  ghost predicate LineNumberFromSummary(
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

  ghost predicate LineNumberSummary(
    cmd: NlSchema.NlCmd,
    lines: seq<BenchWorld.Bytes>,
    numbers: seq<nat>
  )
  {
    LineNumberFromSummary(cmd, lines, 1, numbers)
  }

  ghost predicate LineRenderSummary(
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

  ghost predicate OutputWitnessSummary(
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
    Spec.LinePartitionRelation(
      data, lines, terminated, lineFragments, lineCuts) &&
    LineNumberSummary(cmd, lines, numbers) &&
    |outputFragments| == |lines| &&
    (forall i :: 0 <= i < |lines| ==>
                   LineRenderSummary(
                     cmd, lines[i], terminated[i], numbers[i], outputFragments[i])) &&
    Spec.FragmentsConcatenate(outputFragments, output, outputCuts)
  }

  ghost predicate OutputSummary(
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
      OutputWitnessSummary(
        cmd, data, output, lines, terminated, lineFragments, lineCuts,
        numbers, outputFragments, outputCuts)
  }

  ghost function ShiftCuts(cuts: seq<nat>, offset: nat): seq<nat>
  {
    seq(|cuts|, i requires 0 <= i < |cuts| => cuts[i] + offset)
  }

  lemma SliceAfterPrefix(
    head: BenchWorld.Bytes,
    tail: BenchWorld.Bytes,
    start: nat,
    end: nat
  )
    requires start <= end <= |tail|
    ensures (head + tail)[|head| + start..|head| + end] ==
            tail[start..end]
  {
  }

  lemma {:isolate_assertions} PrependByteFragment(
    head: BenchWorld.Bytes,
    tailFragments: seq<BenchWorld.Bytes>,
    tail: BenchWorld.Bytes,
    tailCuts: seq<nat>
  )
    requires Spec.FragmentsConcatenate(
               tailFragments, tail, tailCuts
             )
    ensures Spec.FragmentsConcatenate(
              [head] + tailFragments,
              head + tail,
              [0] + ShiftCuts(tailCuts, |head|)
            )
  {
    reveal Spec.FragmentsConcatenate();
    forall i: nat {:trigger ([0] + ShiftCuts(
      tailCuts, |head|
      ))[i]} | i < |[head] + tailFragments|
      ensures ([0] + ShiftCuts(tailCuts, |head|))[i] <=
              ([0] + ShiftCuts(tailCuts, |head|))[i + 1] &&
              ([0] + ShiftCuts(tailCuts, |head|))[i + 1] <=
              |head + tail| &&
              ([0] + ShiftCuts(tailCuts, |head|))[i + 1] ==
              ([0] + ShiftCuts(tailCuts, |head|))[i] +
              |([head] + tailFragments)[i]| &&
              (head + tail)[
              ([0] + ShiftCuts(tailCuts, |head|))[i]..
              ([0] + ShiftCuts(tailCuts, |head|))[i + 1]
              ] == ([head] + tailFragments)[i]
    {
      if i > 0 {
        SliceAfterPrefix(
          head, tail, tailCuts[i - 1], tailCuts[i]
        );
      }
    }
  }

  lemma {:isolate_assertions} AppendByteFragment(
    fragments: seq<BenchWorld.Bytes>,
    combined: BenchWorld.Bytes,
    cuts: seq<nat>,
    tail: BenchWorld.Bytes
  )
    requires Spec.FragmentsConcatenate(fragments, combined, cuts)
    ensures Spec.FragmentsConcatenate(
              fragments + [tail],
              combined + tail,
              cuts + [|combined + tail|]
            )
  {
    reveal Spec.FragmentsConcatenate();
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

  method LinesFromMethod(
    data: BenchWorld.Bytes,
    current: BenchWorld.Bytes
  ) returns (
      lines: seq<BenchWorld.Bytes>,
      terminated: seq<bool>,
      ghost fragments: seq<BenchWorld.Bytes>,
      ghost cuts: seq<nat>
    )
    requires forall j: nat :: j < |current| ==> current[j] != '\n'
    ensures Spec.LinePartitionRelation(
              current + data, lines, terminated, fragments, cuts
            )
  {
    var all := current + data;
    var i := 0;
    lines := [];
    terminated := [];
    fragments := [];
    cuts := [0];
    reveal Spec.LinePartitionRelation();
    reveal Spec.FragmentsConcatenate();
    while i < |all|
      invariant 0 <= i <= |all|
      invariant Spec.LinePartitionRelation(all[..i], lines, terminated, fragments, cuts)
      invariant i < |all| ==> forall k: nat :: k < |terminated| ==> terminated[k]
      decreases |all| - i
    {
      var j := i;
      while j < |all| && all[j] != '\n'
        invariant i <= j <= |all|
        invariant forall k: nat :: i <= k < j ==> all[k] != '\n'
        decreases |all| - j
      {
        j := j + 1;
      }
      var line := all[i..j];
      var hasNewline := j < |all|;
      var next := if hasNewline then j + 1 else j;
      var fragment := all[i..next];
      assert '\n' !in line;
      assert fragment == line + (if hasNewline then ['\n'] else []);
      AppendByteFragment(fragments, all[..i], cuts, fragment);
      assert all[..i] + fragment == all[..next];
      lines := lines + [line];
      terminated := terminated + [hasNewline];
      fragments := fragments + [fragment];
      cuts := cuts + [next];
      i := next;
    }
  }

  method LinesMethod(data: BenchWorld.Bytes) returns (
      lines: seq<BenchWorld.Bytes>,
      terminated: seq<bool>,
      ghost fragments: seq<BenchWorld.Bytes>,
      ghost cuts: seq<nat>
    )
    ensures Spec.LinePartitionRelation(
              data, lines, terminated, fragments, cuts
            )
  {
    lines, terminated, fragments, cuts := LinesFromMethod(data, []);
  }

  method HasDelimiterLinesMethod(
    lines: seq<BenchWorld.Bytes>
  ) returns (found: bool)
    ensures found == (exists i ::
                        (0 <= i < |lines| &&
                         IsLogicalPageDelimiterLine(lines[i])))
  {
    found := false;
    var i := 0;
    while i < |lines|
      invariant 0 <= i <= |lines|
      invariant found == (exists j :: 0 <= j < i && IsLogicalPageDelimiterLine(lines[j]))
      decreases |lines| - i
    {
      found := found || IsLogicalPageDelimiterLine(lines[i]);
      i := i + 1;
    }
  }

  method RenderLineMethod(
    cmd: NlSchema.NlCmd,
    line: BenchWorld.Bytes,
    terminated: bool,
    number: nat
  ) returns (out: BenchWorld.Bytes)
    ensures LineRenderSummary(cmd, line, terminated, number, out)
  {
    var prefix := LinePrefix(cmd, |line| > 0, number as int);
    out := prefix + line + (if terminated then ['\n'] else []);
    reveal LineRenderSummary();
  }

  method RenderLinesMethod(
    cmd: NlSchema.NlCmd,
    lines: seq<BenchWorld.Bytes>,
    terminated: seq<bool>,
    start: nat
  ) returns (
      out: BenchWorld.Bytes,
      ghost numbers: seq<nat>,
      ghost outputFragments: seq<BenchWorld.Bytes>,
      ghost outputCuts: seq<nat>
    )
    requires |terminated| == |lines|
    ensures LineNumberFromSummary(cmd, lines, start, numbers)
    ensures |outputFragments| == |lines|
    ensures forall i: nat :: i < |lines| ==>
                               LineRenderSummary(
                                 cmd, lines[i], terminated[i], numbers[i], outputFragments[i]
                               )
    ensures Spec.FragmentsConcatenate(
              outputFragments, out, outputCuts
            )
  {
    out := [];
    numbers := [start];
    outputFragments := [];
    outputCuts := [0];
    reveal LineNumberFromSummary();
    reveal Spec.FragmentsConcatenate();
    var i := 0;
    var number := start;
    while i < |lines|
      invariant 0 <= i <= |lines|
      invariant |numbers| == i + 1
      invariant number == numbers[i]
      invariant LineNumberFromSummary(cmd, lines[..i], start, numbers)
      invariant |outputFragments| == i
      invariant forall j: nat :: j < i ==>
        LineRenderSummary(cmd, lines[j], terminated[j], numbers[j], outputFragments[j])
      invariant Spec.FragmentsConcatenate(outputFragments, out, outputCuts)
      decreases |lines| - i
    {
      var part := RenderLineMethod(cmd, lines[i], terminated[i], number);
      var selected := ShouldNumber(cmd.bodyStyle, |lines[i]| > 0);
      var next := number + (if selected then 1 else 0);
      AppendByteFragment(outputFragments, out, outputCuts, part);
      out := out + part;
      numbers := numbers + [next];
      outputFragments := outputFragments + [part];
      outputCuts := outputCuts + [|out|];
      number := next;
      i := i + 1;
    }
  }

  method {:isolate_assertions} Prepare(
    raw: NlSchema.NlCmdRaw,
    io: BenchIO.IO
  ) returns (
      exit: int,
      ghost readResults: seq<BenchWorld.IOResult<BenchWorld.Bytes>>,
      ghost inputFragments: seq<BenchWorld.Bytes>,
      ghost combinedWitness: BenchWorld.Bytes,
      ghost inputCuts: seq<nat>,
      ghost errorFragments: seq<BenchWorld.Bytes>,
      ghost errorOutput: BenchWorld.Bytes,
      ghost errorCuts: seq<nat>,
      ghost hadErrorWitness: bool,
      ghost hasDelimiterWitness: bool,
      ghost outputPart: BenchWorld.Bytes
    , plannedOut: BenchWorld.Bytes, plannedErr: BenchWorld.Bytes)
    modifies io.stdinRegion
    ensures PreparedSummary(
              raw, io, exit, readResults, inputFragments, combinedWitness,
              inputCuts, errorFragments, errorOutput, errorCuts, hadErrorWitness,
              hasDelimiterWitness, outputPart
            , plannedOut, plannedErr)
    decreases *
  {
    plannedOut := [];
    plannedErr := [];

    ghost var preFs := io.fs();
    ghost var preStreams := io.trustedStreams();
    ghost var preStdin := io.stdin();
    var cmd := NlSchema.Command(raw);
    readResults := [];
    inputFragments := [];
    combinedWitness := [];
    inputCuts := [0];
    errorFragments := [];
    errorOutput := [];
    errorCuts := [0];
    hadErrorWitness := false;
    hasDelimiterWitness := false;
    outputPart := [];

    if cmd.mode == NlSchema.ModeHelp {
      var help := Spec.HelpText();
      var diagnostics := Text.OptionErrorsText(cmd.optionErrors);
      plannedOut := plannedOut + help;
      plannedErr := plannedErr + diagnostics;
      exit := 0;
      assert io.stdin() == preStdin;
      assert plannedOut == help;
      assert plannedErr == diagnostics;
      assert PreparedSummary(
              raw, io, exit, readResults, inputFragments, combinedWitness,
              inputCuts, errorFragments, errorOutput, errorCuts, hadErrorWitness,
              hasDelimiterWitness, outputPart
            , plannedOut, plannedErr) by {
        hide *;
        reveal PreparedSummary();
      }
      return;
    }

    if cmd.mode == NlSchema.ModeVersion {
      var version := Spec.VersionText();
      var diagnostics := Text.OptionErrorsText(cmd.optionErrors);
      plannedOut := plannedOut + version;
      plannedErr := plannedErr + diagnostics;
      exit := 0;
      assert io.stdin() == preStdin;
      assert plannedOut == version;
      assert plannedErr == diagnostics;
      assert PreparedSummary(
              raw, io, exit, readResults, inputFragments, combinedWitness,
              inputCuts, errorFragments, errorOutput, errorCuts, hadErrorWitness,
              hasDelimiterWitness, outputPart
            , plannedOut, plannedErr) by {
        hide *;
        reveal PreparedSummary();
      }
      return;
    }

    if cmd.mode != NlSchema.ModeRun {
      var err := Text.ModeErrorMessage(cmd);
      plannedErr := plannedErr + err;
      exit := 1;
      assert io.stdin() == preStdin;
      assert plannedOut == [];
      assert plannedErr == err;
      assert PreparedSummary(
              raw, io, exit, readResults, inputFragments, combinedWitness,
              inputCuts, errorFragments, errorOutput, errorCuts, hadErrorWitness,
              hasDelimiterWitness, outputPart
            , plannedOut, plannedErr) by {
        hide *;
        reveal PreparedSummary();
      }
      return;
    }

    var combined: BenchWorld.Bytes := [];
    var err: BenchWorld.Bytes := [];
    var hadError := false;
    var seenStdin := false;

    assert PrefixStdinCore(cmd, preStdin, 0, preStreams) == preStdin by { reveal PrefixStdinCore(); }
    var i := 0;
    assert io.stdin() == PrefixStdinCore(cmd, preStdin, i, preStreams) by {
      hide *;
      reveal PrefixStdinCore();
    }
    while i < |cmd.inputs|
      invariant 0 <= i <= |cmd.inputs|
      invariant plannedOut == []
      invariant plannedErr == []
      invariant |readResults| == i
      invariant |inputFragments| == i
      invariant |errorFragments| == i
      invariant forall j: nat :: j < i ==>
                                   Spec.ReadResultRelation(cmd, preFs, PrefixStdinCore(cmd, preStdin, j, preStreams), j, readResults[j],
                                     preStreams
                                   ) &&
                                   inputFragments[j] ==
                                   (match readResults[j]
                                    case Ok(data) => NormalizeInputData(data)
                                    case Err(error) => if error.StreamFailure? then NormalizeInputData(error.partial) else []) &&
                                   errorFragments[j] ==
                                   Text.ErrorPiece(cmd.inputs[j], readResults[j])
      invariant Spec.FragmentsConcatenate(
                  inputFragments, combined, inputCuts
                )
      invariant Spec.FragmentsConcatenate(
                  errorFragments, err, errorCuts
                )
      invariant hadError ==
                (exists j :: 0 <= j < i &&
                             Spec.HadErrorPiece(cmd.inputs[j], readResults[j]))
      invariant seenStdin ==
                (exists j :: 0 <= j < i &&
                             cmd.inputs[j] == NlSchema.Stdin)
      invariant io.stdin() == PrefixStdinCore(cmd, preStdin, i, preStreams)
      decreases |cmd.inputs| - i
    {
      var input := cmd.inputs[i];
      ghost var beforeReadStdin := io.stdin();
      assert beforeReadStdin == PrefixStdinCore(cmd, preStdin, i, preStreams);
      var readResult: BenchWorld.IOResult<BenchWorld.Bytes>;
      var piece: BenchWorld.Bytes;
      var errorPiece: BenchWorld.Bytes;
      var pieceHadError: bool;
      match input {
        case Stdin =>
          readResult := io.ReadStdin();
          piece := NormalizeInputData(IOContract.ReadResultData(readResult));
          errorPiece := Text.ErrorPiece(input, readResult);
          pieceHadError := readResult.Err?;
        case File(path) =>
          readResult := io.ReadFile(path);
          assert readResult ==
                 IOContract.ObservedReadFileResultFields(preFs, preStreams, path);
          if readResult.Ok? {
            piece := NormalizeInputData(readResult.v);
            errorPiece := [];
            pieceHadError := false;
          } else {
            piece := [];
            errorPiece := Text.ErrorMessage(path, readResult.e);
            pieceHadError := true;
          }
      }
      assert io.stdin() == (if input.Stdin? then
        IOContract.ObservedReadStdinRemainingFields(beforeReadStdin, preStreams) else beforeReadStdin) by { hide *; }
      assert Spec.ReadResultRelation(cmd, preFs, PrefixStdinCore(cmd, preStdin, i, preStreams), i, readResult,
          preStreams
        ) by {
        reveal Spec.ReadResultRelation();
      }
      assert piece ==
             (match readResult
              case Ok(data) => NormalizeInputData(data)
              case Err(error) => if error.StreamFailure? then NormalizeInputData(error.partial) else []);
      assert errorPiece == Text.ErrorPiece(input, readResult);
      assert pieceHadError ==
             Spec.HadErrorPiece(input, readResult);
      AppendByteFragment(inputFragments, combined, inputCuts, piece);
      AppendByteFragment(errorFragments, err, errorCuts, errorPiece);
      ghost var nextInputCut: nat := |combined + piece|;
      ghost var nextErrorCut: nat := |err + errorPiece|;
      readResults, inputFragments, inputCuts, combined :=
        readResults + [readResult],
        inputFragments + [piece],
        inputCuts + [nextInputCut],
        combined + piece;
      errorFragments, errorCuts, err :=
        errorFragments + [errorPiece],
        errorCuts + [nextErrorCut],
        err + errorPiece;
      assert Spec.FragmentsConcatenate(
          inputFragments, combined, inputCuts);
      assert Spec.FragmentsConcatenate(
          errorFragments, err, errorCuts);
      assert forall j: nat :: j < i + 1 ==>
                                Spec.ReadResultRelation(cmd, preFs, PrefixStdinCore(cmd, preStdin, j, preStreams), j, readResults[j],
                                  preStreams
                                ) &&
                                inputFragments[j] ==
                                (match readResults[j]
                                 case Ok(data) => NormalizeInputData(data)
                                 case Err(error) => if error.StreamFailure? then NormalizeInputData(error.partial) else []) &&
                                errorFragments[j] ==
                                Text.ErrorPiece(cmd.inputs[j], readResults[j]) by {
        forall j: nat | j < i + 1
          ensures Spec.ReadResultRelation(cmd, preFs, PrefixStdinCore(cmd, preStdin, j, preStreams), j, readResults[j],
                    preStreams
                  ) &&
                  inputFragments[j] ==
                  (match readResults[j]
                   case Ok(data) => NormalizeInputData(data)
                   case Err(error) => if error.StreamFailure? then NormalizeInputData(error.partial) else []) &&
                  errorFragments[j] ==
                  Text.ErrorPiece(cmd.inputs[j], readResults[j])
        {
          if j == i {
            assert readResults[j] == readResult;
            assert inputFragments[j] == piece;
          }
        }
      }
      ghost var priorHadError := hadError;
      hadError := hadError || pieceHadError;
      assert priorHadError ==
             (exists j :: (0 <= j < i &&
                           Spec.HadErrorPiece(cmd.inputs[j], readResults[j])));
      assert (exists j :: (0 <= j < i + 1 &&
                           Spec.HadErrorPiece(cmd.inputs[j], readResults[j]))) <==>
             ((exists j :: (0 <= j < i &&
                            Spec.HadErrorPiece(cmd.inputs[j], readResults[j]))) ||
              Spec.HadErrorPiece(cmd.inputs[i], readResults[i])) by {
        if exists j :: (0 <= j < i + 1 &&
                        Spec.HadErrorPiece(cmd.inputs[j], readResults[j])) {
          var j :| (0 <= j < i + 1 &&
                    Spec.HadErrorPiece(cmd.inputs[j], readResults[j]));
          if j < i {
            assert exists k :: (0 <= k < i &&
                                Spec.HadErrorPiece(cmd.inputs[k], readResults[k]));
          } else {
            assert j == i;
          }
        }
        if (exists j :: (0 <= j < i &&
                         Spec.HadErrorPiece(cmd.inputs[j], readResults[j]))) ||
           Spec.HadErrorPiece(cmd.inputs[i], readResults[i]) {
          if exists j :: (0 <= j < i &&
                          Spec.HadErrorPiece(cmd.inputs[j], readResults[j])) {
            var j :| (0 <= j < i &&
                      Spec.HadErrorPiece(cmd.inputs[j], readResults[j]));
            assert exists k :: (0 <= k < i + 1 &&
                                Spec.HadErrorPiece(cmd.inputs[k], readResults[k]));
          } else {
            assert exists k :: (0 <= k < i + 1 &&
                                Spec.HadErrorPiece(cmd.inputs[k], readResults[k]));
          }
        }
      }
      assert hadError ==
             (exists j :: (0 <= j < i + 1 &&
                           Spec.HadErrorPiece(cmd.inputs[j], readResults[j])));
      ghost var priorSeenStdin := seenStdin;
      seenStdin := seenStdin || input == NlSchema.Stdin;
      assert priorSeenStdin ==
             (exists j :: (0 <= j < i &&
                           cmd.inputs[j] == NlSchema.Stdin));
      assert (exists j :: (0 <= j < i + 1 &&
                           cmd.inputs[j] == NlSchema.Stdin)) <==>
             ((exists j :: (0 <= j < i &&
                            cmd.inputs[j] == NlSchema.Stdin)) ||
              cmd.inputs[i] == NlSchema.Stdin) by {
        if exists j :: (0 <= j < i + 1 &&
                        cmd.inputs[j] == NlSchema.Stdin) {
          var j :| (0 <= j < i + 1 &&
                    cmd.inputs[j] == NlSchema.Stdin);
          if j < i {
            assert exists k :: (0 <= k < i &&
                                cmd.inputs[k] == NlSchema.Stdin);
          } else {
            assert j == i;
          }
        }
        if (exists j :: (0 <= j < i &&
                         cmd.inputs[j] == NlSchema.Stdin)) ||
           cmd.inputs[i] == NlSchema.Stdin {
          if exists j :: (0 <= j < i &&
                          cmd.inputs[j] == NlSchema.Stdin) {
            var j :| (0 <= j < i &&
                      cmd.inputs[j] == NlSchema.Stdin);
            assert exists k :: (0 <= k < i + 1 &&
                                cmd.inputs[k] == NlSchema.Stdin);
          } else {
            assert exists k :: (0 <= k < i + 1 &&
                                cmd.inputs[k] == NlSchema.Stdin);
          }
        }
      }
      assert seenStdin ==
             (exists j :: (0 <= j < i + 1 &&
                           cmd.inputs[j] == NlSchema.Stdin));
      PrefixStdinStep(cmd, preStdin, i, preStreams);
      assert io.stdin() == PrefixStdinCore(cmd, preStdin, i + 1, preStreams) by { hide *; }
      hide *;
      assert |readResults| == i + 1;
      assert |inputFragments| == i + 1;
      assert |errorFragments| == i + 1;
      i := i + 1;
    }

    var lines, terminated, lineFragments, lineCuts :=
      LinesMethod(combined);
    var hasDelimiter := HasDelimiterLinesMethod(lines);
    combinedWitness := combined;
    errorOutput := err;
    hadErrorWitness := hadError;
    hasDelimiterWitness := hasDelimiter;
    assert exists ls: seq<BenchWorld.Bytes>,
        ts: seq<bool>,
        fs: seq<BenchWorld.Bytes>,
        cs: seq<nat> ::
        Spec.LinePartitionRelation(
          combined, ls, ts, fs, cs
        ) &&
        hasDelimiter ==
        (exists j :: 0 <= j < |ls| &&
                     IsLogicalPageDelimiterLine(ls[j])) by {
      assert Spec.LinePartitionRelation(
          combined, lines, terminated, lineFragments, lineCuts
        );
    }
    assert InputTraceSummary(
        cmd, preFs, preStdin, readResults, inputFragments, combined,
        inputCuts, errorFragments, err, errorCuts, hadError, hasDelimiter,
        preStreams
      , io.stdin()) by {
      hide *;
      reveal InputTraceSummary();
    }
    if hasDelimiter {
      var delimiterErr := Spec.UnsupportedLogicalPageDelimiterMessage();
      plannedErr := err + delimiterErr;
      exit := 1;
      assert plannedOut == [];
      assert plannedErr == err + delimiterErr;
      assert PreparedSummary(
              raw, io, exit, readResults, inputFragments, combinedWitness,
              inputCuts, errorFragments, errorOutput, errorCuts, hadErrorWitness,
              hasDelimiterWitness, outputPart
            , plannedOut, plannedErr) by {
        hide *;
        reveal PreparedSummary();
      }
      return;
    }

    var rendered, numbers, outputFragments, outputCuts :=
      RenderLinesMethod(cmd, lines, terminated, 1);
    reveal LineNumberSummary();
    reveal OutputWitnessSummary();
    reveal OutputSummary();
    assert OutputWitnessSummary(
        cmd, combined, rendered, lines, terminated, lineFragments, lineCuts,
        numbers, outputFragments, outputCuts
      );
    assert exists ls: seq<BenchWorld.Bytes>,
        ts: seq<bool>,
        lfs: seq<BenchWorld.Bytes>,
        lcs: seq<nat>,
        ns: seq<nat>,
        ofs: seq<BenchWorld.Bytes>,
        ocs: seq<nat> ::
        OutputWitnessSummary(
          cmd, combined, rendered, ls, ts, lfs, lcs, ns, ofs, ocs
        ) by {
      assert OutputWitnessSummary(
          cmd, combined, rendered, lines, terminated, lineFragments, lineCuts,
          numbers, outputFragments, outputCuts
        );
    }
    assert OutputSummary(cmd, combined, rendered);
    outputPart := rendered;
    plannedOut := rendered;
    plannedErr := err;
    exit := if hadError then 1 else 0;
    assert plannedOut == rendered;
    assert plannedErr == err;
      assert PreparedSummary(
              raw, io, exit, readResults, inputFragments, combinedWitness,
              inputCuts, errorFragments, errorOutput, errorCuts, hadErrorWitness,
              hasDelimiterWitness, outputPart
            , plannedOut, plannedErr) by {
        hide *;
        reveal PreparedSummary();
      }
  }

  twostate predicate CoreSummary(
    raw: NlSchema.NlCmdRaw,
    io: BenchIO.IO,
    exit: int,
    new readResults: seq<BenchWorld.IOResult<BenchWorld.Bytes>>,
    new inputFragments: seq<BenchWorld.Bytes>,
    new combined: BenchWorld.Bytes,
    new inputCuts: seq<nat>,
    new errorFragments: seq<BenchWorld.Bytes>,
    new errorOutput: BenchWorld.Bytes,
    new errorCuts: seq<nat>,
    hadError: bool,
    hasDelimiter: bool,
    new outputPart: BenchWorld.Bytes
  )
    reads io.stdinRegion, io.stdoutRegion, io.stderrRegion
  {
    exists out: BenchWorld.Bytes, diagnostics: BenchWorld.Bytes, normalExit: int ::
      PreparedSummary(raw, io, normalExit, readResults, inputFragments, combined, inputCuts, errorFragments, errorOutput, errorCuts, hadError, hasDelimiter, outputPart,
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

  method RunCore(raw: NlSchema.NlCmdRaw, io: BenchIO.IO) returns (
      exit: int,
      ghost readResults: seq<BenchWorld.IOResult<BenchWorld.Bytes>>,
      ghost inputFragments: seq<BenchWorld.Bytes>,
      ghost combinedWitness: BenchWorld.Bytes,
      ghost inputCuts: seq<nat>,
      ghost errorFragments: seq<BenchWorld.Bytes>,
      ghost errorOutput: BenchWorld.Bytes,
      ghost errorCuts: seq<nat>,
      ghost hadErrorWitness: bool,
      ghost hasDelimiterWitness: bool,
      ghost outputPart: BenchWorld.Bytes
    )
    modifies io.stdinRegion, io.stdoutRegion, io.stderrRegion
    ensures CoreSummary(
              raw, io, exit, readResults, inputFragments, combinedWitness,
              inputCuts, errorFragments, errorOutput, errorCuts, hadErrorWitness,
              hasDelimiterWitness, outputPart
            )
    decreases *
  {
    var normalExit: int;
    var out: BenchWorld.Bytes;
    var diagnostics: BenchWorld.Bytes;
    normalExit, readResults, inputFragments, combinedWitness, inputCuts, errorFragments, errorOutput, errorCuts, hadErrorWitness, hasDelimiterWitness, outputPart, out, diagnostics := Prepare(raw, io);

    assert PreparedSummary(
              raw, io, normalExit, readResults, inputFragments, combinedWitness,
              inputCuts, errorFragments, errorOutput, errorCuts, hadErrorWitness,
              hasDelimiterWitness, outputPart
            , out, diagnostics);
    if Spec.Emits(raw) {
      exit := Flush(io, out, diagnostics, normalExit);
    } else {
      exit := normalExit;
    }
    assert PreparedSummary(
              raw, io, normalExit, readResults, inputFragments, combinedWitness,
              inputCuts, errorFragments, errorOutput, errorCuts, hadErrorWitness,
              hasDelimiterWitness, outputPart
            , out, diagnostics);
    assert Spec.Emission(raw, io, out, diagnostics, normalExit, exit);
  }
}
