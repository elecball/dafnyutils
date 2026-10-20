include "../../core/World.dfy"
include "NlSchema.dfy"
include "NlCore.dfy"
include "NlSpec.dfy"

module NlProof {
  import IOContract
  import BenchWorld

  import Result = Results
  import BenchIO
  import BW = BenchWorld
  import Schema = NlSchema
  import Core = NlCore
  import Spec = NlSpec

  lemma RepeatCharRefines(ch: BW.RawByte, count: int)
    ensures Core.RepeatChar(ch, count) == Spec.RepeatChar(ch, count)
    decreases count
  {
    if count > 0 {
      RepeatCharRefines(ch, count - 1);
    }
  }

  lemma DigitCharRefines(d: int)
    ensures Core.DigitChar(d) == Spec.DigitChar(d)
  {
  }

  lemma DigitsRefines(n: int)
    requires 0 <= n
    ensures Core.Digits(n) == Spec.Digits(n)
    decreases n
  {
    DigitCharRefines(n % 10);
    if n >= 10 {
      DigitsRefines(n / 10);
    }
  }

  lemma RenderNumberRefines(
    format: Schema.NumberFormat,
    n: int,
    width: int
  )
    requires 0 <= n
    ensures Core.RenderNumber(format, n, width) ==
            Spec.RenderNumber(format, n, width)
  {
    DigitsRefines(n);
    RepeatCharRefines(' ', width - |Core.Digits(n)|);
    RepeatCharRefines('0', width - |Core.Digits(n)|);
  }

  lemma ShouldNumberRefines(
    style: Schema.BodyStyle,
    nonempty: bool
  )
    ensures Core.ShouldNumber(style, nonempty) ==
            Spec.ShouldNumber(style, nonempty)
  {
  }

  lemma LinePrefixRefines(
    cmd: Schema.NlCmd,
    nonempty: bool,
    n: int
  )
    requires 0 <= n
    ensures Core.LinePrefix(cmd, nonempty, n) ==
            Spec.LinePrefix(cmd, nonempty, n)
  {
    ShouldNumberRefines(cmd.bodyStyle, nonempty);
    if Core.ShouldNumber(cmd.bodyStyle, nonempty) {
      RenderNumberRefines(cmd.numberFormat, n, 6);
    } else {
      RepeatCharRefines(' ', 6 + |cmd.separator|);
    }
  }

  lemma LineNumberFromRefines(
    cmd: Schema.NlCmd,
    lines: seq<BW.Bytes>,
    start: nat,
    numbers: seq<nat>
  )
    requires Core.LineNumberFromSummary(cmd, lines, start, numbers)
    ensures Spec.LineNumberFromRelation(cmd, lines, start, numbers)
  {
    reveal Core.LineNumberFromSummary();
    reveal Spec.LineNumberFromRelation();
    forall i: nat | i < |lines|
      ensures numbers[i + 1] == numbers[i] +
                                (if Spec.ShouldNumber(
                                      cmd.bodyStyle, |lines[i]| > 0
                                    ) then 1 else 0)
    {
      ShouldNumberRefines(cmd.bodyStyle, |lines[i]| > 0);
    }
  }

  lemma LineRenderRefines(
    cmd: Schema.NlCmd,
    line: BW.Bytes,
    terminated: bool,
    number: nat,
    outputFragment: BW.Bytes
  )
    requires Core.LineRenderSummary(
               cmd, line, terminated, number, outputFragment)
    ensures Spec.LineRenderRelation(
              cmd, line, terminated, number, outputFragment)
  {
    reveal Core.LineRenderSummary();
    reveal Spec.LineRenderRelation();
    LinePrefixRefines(cmd, |line| > 0, number as int);
  }

  lemma OutputWitnessRefines(
    cmd: Schema.NlCmd,
    data: BW.Bytes,
    output: BW.Bytes,
    lines: seq<BW.Bytes>,
    terminated: seq<bool>,
    lineFragments: seq<BW.Bytes>,
    lineCuts: seq<nat>,
    numbers: seq<nat>,
    outputFragments: seq<BW.Bytes>,
    outputCuts: seq<nat>
  )
    requires Core.OutputWitnessSummary(
               cmd, data, output, lines, terminated, lineFragments, lineCuts,
               numbers, outputFragments, outputCuts)
    ensures Spec.OutputWitnessRelation(
              cmd, data, output, lines, terminated, lineFragments, lineCuts,
              numbers, outputFragments, outputCuts)
  {
    reveal Core.OutputWitnessSummary();
    reveal Core.LineNumberSummary();
    reveal Spec.OutputWitnessRelation();
    reveal Spec.LineNumberRelation();
    LineNumberFromRefines(cmd, lines, 1, numbers);
    assert forall i :: 0 <= i < |lines| ==>
                         Spec.LineRenderRelation(
                           cmd, lines[i], terminated[i], numbers[i], outputFragments[i]) by {
      forall i | 0 <= i < |lines|
        ensures Spec.LineRenderRelation(
                  cmd, lines[i], terminated[i], numbers[i], outputFragments[i])
      {
        LineRenderRefines(
          cmd, lines[i], terminated[i], numbers[i], outputFragments[i]);
      }
    }
  }

  lemma OutputSummaryRefines(
    cmd: Schema.NlCmd,
    data: BW.Bytes,
    output: BW.Bytes
  )
    requires Core.OutputSummary(cmd, data, output)
    ensures Spec.OutputRelation(cmd, data, output)
  {
    reveal Core.OutputSummary();
    reveal Spec.OutputRelation();
    var lines: seq<BW.Bytes>,
        terminated: seq<bool>,
        lineFragments: seq<BW.Bytes>,
        lineCuts: seq<nat>,
        numbers: seq<nat>,
        outputFragments: seq<BW.Bytes>,
        outputCuts: seq<nat> :|
      Core.OutputWitnessSummary(
        cmd, data, output, lines, terminated, lineFragments, lineCuts,
        numbers, outputFragments, outputCuts);
    OutputWitnessRefines(
      cmd, data, output, lines, terminated, lineFragments, lineCuts,
      numbers, outputFragments, outputCuts);
  }

  lemma NormalizeInputDataRefines(data: BW.Bytes)
    ensures Spec.NormalizedInputRelation(
              data, Core.NormalizeInputData(data))
  {
    reveal Core.NormalizeInputData();
    reveal Spec.NormalizedInputRelation();
  }

  lemma LogicalPageDelimiterRefines(line: BW.Bytes)
    ensures Core.IsLogicalPageDelimiterLine(line) ==
            Spec.IsLogicalPageDelimiterLine(line)
  {
    reveal Core.IsLogicalPageDelimiterLine();
  }

  lemma HasLogicalPageDelimiterRefines(lines: seq<BW.Bytes>)
    ensures
      (exists i ::
         0 <= i < |lines| &&
         Core.IsLogicalPageDelimiterLine(lines[i])) <==>
      (exists i ::
         0 <= i < |lines| &&
         Spec.IsLogicalPageDelimiterLine(lines[i]))
  {
    if exists i :: 0 <= i < |lines| &&
                   Core.IsLogicalPageDelimiterLine(lines[i]) {
      var i: nat :| i < |lines| &&
                    Core.IsLogicalPageDelimiterLine(lines[i]);
      LogicalPageDelimiterRefines(lines[i]);
    }
    if exists i :: 0 <= i < |lines| &&
                   Spec.IsLogicalPageDelimiterLine(lines[i]) {
      var i: nat :| i < |lines| &&
                    Spec.IsLogicalPageDelimiterLine(lines[i]);
      LogicalPageDelimiterRefines(lines[i]);
    }
  }

  lemma InputTraceRefines(
    cmd: Schema.NlCmd,
    preFs: BW.FileSystem,
    preStdin: BW.Bytes,
    readResults: seq<BW.IOResult<BW.Bytes>>,
    inputFragments: seq<BW.Bytes>,
    combined: BW.Bytes,
    inputCuts: seq<nat>,
    errorFragments: seq<BW.Bytes>,
    errorOutput: BW.Bytes,
    errorCuts: seq<nat>,
    hadError: bool,
    hasDelimiter: bool,
    preStreams: (BW.TrustedStreamRequest) -> BW.TrustedStreamResult
  , postStdin: BenchWorld.Bytes)
    requires Core.InputTraceSummary(
               cmd, preFs, preStdin, readResults, inputFragments,
               combined, inputCuts, errorFragments, errorOutput, errorCuts,
               hadError, hasDelimiter, preStreams, postStdin)
    ensures Spec.InputTraceRelation(
              cmd, preFs, preStdin, readResults, inputFragments,
              combined, inputCuts, errorFragments, errorOutput, errorCuts,
              hadError, hasDelimiter, preStreams, postStdin)
  {
    reveal Core.InputTraceSummary();
    var states := seq(|cmd.inputs| + 1, i requires 0 <= i <= |cmd.inputs| => Core.PrefixStdinCore(cmd, preStdin, i, preStreams));
    forall i: nat | i < |cmd.inputs|
      ensures states[i + 1] == (if cmd.inputs[i].Stdin? then
        IOContract.ObservedReadStdinRemainingFields(states[i], preStreams) else states[i])
    { Core.PrefixStdinStep(cmd, preStdin, i, preStreams); }
    assert states[0] == preStdin by { reveal Core.PrefixStdinCore(); }
    assert Spec.StdinTraceRelation(cmd, preStdin, postStdin, preStreams, states);
    assert forall i :: 0 <= i < |cmd.inputs| ==>
                         Spec.ReadResultRelation(cmd, preFs, states[i], i, readResults[i], preStreams) &&
                         (match readResults[i]
                          case Ok(data) =>
                            Spec.NormalizedInputRelation(data, inputFragments[i])
                          case Err(error) =>
                            if error.StreamFailure? then Spec.NormalizedInputRelation(error.partial, inputFragments[i]) else inputFragments[i] == []) &&
                         errorFragments[i] ==
                         Spec.ErrorPiece(cmd.inputs[i], readResults[i]) by {
      forall i | 0 <= i < |cmd.inputs|
        ensures Spec.ReadResultRelation(cmd, preFs, states[i], i, readResults[i], preStreams) &&
                (match readResults[i]
                 case Ok(data) =>
                   Spec.NormalizedInputRelation(data, inputFragments[i])
                 case Err(error) =>
                   if error.StreamFailure? then Spec.NormalizedInputRelation(error.partial, inputFragments[i]) else inputFragments[i] == []) &&
                errorFragments[i] ==
                Spec.ErrorPiece(cmd.inputs[i], readResults[i])
      {
        assert states[i] == Core.PrefixStdinCore(cmd, preStdin, i, preStreams);
        match readResults[i]
        case Ok(data) =>
          NormalizeInputDataRefines(data);
        case Err(error) =>
          if error.StreamFailure? { NormalizeInputDataRefines(error.partial); }
      }
    }
    var lines: seq<BW.Bytes>,
        terminated: seq<bool>,
        fragments: seq<BW.Bytes>,
        cuts: seq<nat> :|
      Spec.LinePartitionRelation(
        combined, lines, terminated, fragments, cuts) &&
      hasDelimiter ==
      (exists i :: 0 <= i < |lines| &&
                   Core.IsLogicalPageDelimiterLine(lines[i]));
    HasLogicalPageDelimiterRefines(lines);
    assert exists ls: seq<BW.Bytes>,
        ts: seq<bool>,
        fs: seq<BW.Bytes>,
        cs: seq<nat> ::
        Spec.LinePartitionRelation(combined, ls, ts, fs, cs) &&
        hasDelimiter ==
        (exists i :: 0 <= i < |ls| &&
                     Spec.IsLogicalPageDelimiterLine(ls[i])) by {
      assert Spec.LinePartitionRelation(
          combined, lines, terminated, fragments, cuts);
    }
    assert |readResults| == |cmd.inputs|;
    assert |inputFragments| == |cmd.inputs|;
    assert |errorFragments| == |cmd.inputs|;
    assert Spec.FragmentsConcatenate(inputFragments, combined, inputCuts);
    assert Spec.FragmentsConcatenate(errorFragments, errorOutput, errorCuts);
    assert hadError == (exists i :: 0 <= i < |cmd.inputs| && Spec.HadErrorPiece(cmd.inputs[i], readResults[i]));
    assert Spec.InputTraceWitnessRelation(cmd, preFs, preStdin, readResults, inputFragments, combined, inputCuts, errorFragments, errorOutput, errorCuts, hadError, hasDelimiter, preStreams, postStdin, states) by {
      hide *;
      reveal Spec.InputTraceWitnessRelation();
    }
    assert Spec.InputTraceRelation(cmd, preFs, preStdin, readResults, inputFragments, combined, inputCuts, errorFragments, errorOutput, errorCuts, hadError, hasDelimiter, preStreams, postStdin) by {
      hide *;
      reveal Spec.InputTraceRelation();
    }
  }

  twostate lemma PreparedSpecFromTrace(
    raw: Schema.NlCmdRaw, io: BenchIO.IO, exit: int,
    new readResults: seq<BW.IOResult<BW.Bytes>>, new inputFragments: seq<BW.Bytes>,
    new combined: BW.Bytes, new inputCuts: seq<nat>, new errorFragments: seq<BW.Bytes>,
    new errorOutput: BW.Bytes, new errorCuts: seq<nat>, hadError: bool, hasDelimiter: bool,
    new outputPart: BW.Bytes, new plannedStdout: BW.Bytes, new plannedStderr: BW.Bytes)
    requires Schema.Command(raw).mode == Schema.ModeRun
    requires Spec.InputTraceRelation(Schema.Command(raw), old(io.fs()), old(io.stdin()), readResults,
      inputFragments, combined, inputCuts, errorFragments, errorOutput, errorCuts,
      hadError, hasDelimiter, old(io.trustedStreams()), io.stdin())
    requires if hasDelimiter then outputPart == [] else Spec.OutputRelation(Schema.Command(raw), combined, outputPart)
    requires plannedStdout == outputPart
    requires plannedStderr == errorOutput + (if hasDelimiter then Spec.UnsupportedLogicalPageDelimiterMessage() else [])
    requires exit == (if hasDelimiter || hadError then 1 else 0)
    ensures Spec.PreparedSpec(raw, io, exit, plannedStdout, plannedStderr)
  {
    var trace := Spec.RunWitness(readResults, inputFragments, combined, inputCuts, errorFragments,
      errorOutput, errorCuts, hadError, hasDelimiter, outputPart);
    assert Spec.PreparedRunRelation(Schema.Command(raw), old(io.fs()), old(io.stdin()), io.stdin(),
      old(io.trustedStreams()), plannedStdout, plannedStderr, exit, trace) by {
      hide *;
      reveal Spec.PreparedRunRelation();
    }
    assert Spec.PreparedSpec(raw, io, exit, plannedStdout, plannedStderr) by {
      hide *;
      reveal Spec.PreparedSpec();
    }
  }

  twostate lemma PreparedSummaryImpliesPreparedSpec(
    raw: Schema.NlCmdRaw,
    io: BenchIO.IO,
    exit: int,
    new readResults: seq<BW.IOResult<BW.Bytes>>,
    new inputFragments: seq<BW.Bytes>,
    new combined: BW.Bytes,
    new inputCuts: seq<nat>,
    new errorFragments: seq<BW.Bytes>,
    new errorOutput: BW.Bytes,
    new errorCuts: seq<nat>,
    hadError: bool,
    hasDelimiter: bool,
    new outputPart: BW.Bytes
  , new plannedStdout: BenchWorld.Bytes, new plannedStderr: BenchWorld.Bytes)
    requires Core.PreparedSummary(
               raw, io, exit, readResults, inputFragments, combined, inputCuts,
               errorFragments, errorOutput, errorCuts, hadError, hasDelimiter,
               outputPart
             , plannedStdout, plannedStderr)
    ensures Spec.PreparedSpec(raw, io, exit, plannedStdout, plannedStderr)
  {
    reveal Core.PreparedSummary();
    var cmd := Schema.Command(raw);
    if cmd.mode == Schema.ModeRun {
      InputTraceRefines(
        cmd, old(io.fs()), old(io.stdin()), readResults, inputFragments,
        combined, inputCuts, errorFragments, errorOutput, errorCuts,
        hadError, hasDelimiter, old(io.trustedStreams()), io.stdin());
      if !hasDelimiter {
        OutputSummaryRefines(cmd, combined, outputPart);
      }
      assert Spec.InputTraceRelation(cmd, old(io.fs()), old(io.stdin()), readResults,
        inputFragments, combined, inputCuts, errorFragments, errorOutput, errorCuts,
        hadError, hasDelimiter, old(io.trustedStreams()), io.stdin());
      assert (if hasDelimiter then outputPart == [] else Spec.OutputRelation(cmd, combined, outputPart));
      assert plannedStdout == outputPart;
      assert plannedStderr == errorOutput + (if hasDelimiter then Spec.UnsupportedLogicalPageDelimiterMessage() else []);
      assert exit == (if hasDelimiter || hadError then 1 else 0);
      PreparedSpecFromTrace(raw, io, exit, readResults, inputFragments, combined, inputCuts,
        errorFragments, errorOutput, errorCuts, hadError, hasDelimiter, outputPart, plannedStdout, plannedStderr);
      return;
    }
    assert Spec.PreparedSpec(raw, io, exit, plannedStdout, plannedStderr) by {
      hide *;
      reveal Core.PreparedSummary();
      reveal Spec.PreparedSpec();
    }
  }

  twostate lemma CoreSummaryImpliesSpec(
    raw: Schema.NlCmdRaw,
    io: BenchIO.IO,
    exit: int,
    new readResults: seq<BW.IOResult<BW.Bytes>>,
    new inputFragments: seq<BW.Bytes>,
    new combined: BW.Bytes,
    new inputCuts: seq<nat>,
    new errorFragments: seq<BW.Bytes>,
    new errorOutput: BW.Bytes,
    new errorCuts: seq<nat>,
    hadError: bool,
    hasDelimiter: bool,
    new outputPart: BW.Bytes
  )
    requires Core.CoreSummary(raw, io, exit, readResults, inputFragments, combined, inputCuts, errorFragments, errorOutput, errorCuts, hadError, hasDelimiter, outputPart)
    ensures Spec.Spec(raw, io, exit)
  {
    var out: BenchWorld.Bytes, diagnostics: BenchWorld.Bytes, normalExit: int :|
      Core.PreparedSummary(raw, io, normalExit, readResults, inputFragments, combined, inputCuts, errorFragments, errorOutput, errorCuts, hadError, hasDelimiter, outputPart,
        out, diagnostics) &&
      Spec.Emission(raw, io, out, diagnostics, normalExit, exit);
    PreparedSummaryImpliesPreparedSpec(raw, io, normalExit, readResults, inputFragments, combined, inputCuts, errorFragments, errorOutput, errorCuts, hadError, hasDelimiter, outputPart,
      out, diagnostics);
  }
}
