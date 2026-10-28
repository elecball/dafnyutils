include "../../../core/World.dfy"
include "../Spec/CutSchema.dfy"
include "../Impl/CutCore.dfy"
include "../Spec/CutSpec.dfy"

module CutProof {
  import IOContract
  import Result = Results
  import BenchIO
  import BenchWorld
  import Schema = CutSchema
  import Core = CutCore
  import Spec = CutSpec

  lemma InputReadCoreRefines(
    command: Schema.CutCmdRaw,
    preFs: BenchWorld.FileSystem,
    preStdin: BenchWorld.Bytes,
    index: nat,
    result: BenchWorld.IOResult<BenchWorld.Bytes>,
                                preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult
  )
    requires index < |command.inputs|
    requires Core.InputReadCore(
               command, preFs, preStdin, index, result,
               preStreams
             )
    ensures Spec.InputReadRelation(
              command, preFs, Core.PrefixStdinCore(command, preStdin, index, preStreams), index, result,
              preStreams
            )
  {
    reveal Core.InputReadCore();
    reveal Spec.InputReadRelation();
  }

  lemma OutputPieceRefines(
    command: Schema.CutCmdRaw,
    result: BenchWorld.IOResult<BenchWorld.Bytes>
  )
    ensures match result
            case Ok(data) =>
              Spec.DataSelectionRelation(
                command, data, Core.OutputPiece(command, result)
              )
            case Err(error) =>
              if error.StreamFailure? then Spec.DataSelectionRelation(command, error.partial, Core.OutputPiece(command, result))
              else Core.OutputPiece(command, result) == []
  {
    match result
    case Ok(data) =>
      Core.DataSelectionSatisfiesRelation(command, data);
    case Err(error) =>
      if error.StreamFailure? { Core.DataSelectionSatisfiesRelation(command, error.partial); }
  }

  twostate lemma {:isolate_assertions} InputTraceCoreRefines(
    command: Schema.CutCmdRaw,
    io: BenchIO.IO,
    readResults: seq<BenchWorld.IOResult<BenchWorld.Bytes>>,
    stdoutFragments: seq<BenchWorld.Bytes>,
    stderrFragments: seq<BenchWorld.Bytes>
  )
    requires Core.InputTraceCore(
               command, old(io.fs()), old(io.stdin()), |command.inputs|,
               readResults, stdoutFragments, stderrFragments,
               old(io.trustedStreams())
             )
    requires io.stdin() == Core.PrefixStdinCore(command, old(io.stdin()), |command.inputs|, old(io.trustedStreams()))
    ensures Spec.InputTraceRelation(
              command,
              io,
              readResults,
              Core.JoinFragments(stdoutFragments),
              Core.JoinFragments(stderrFragments),
              exists i: nat | i < |command.inputs| ::
                readResults[i].Err?
            )
  {
    reveal Core.InputTraceCore();
    var states := seq(|command.inputs| + 1, i requires 0 <= i <= |command.inputs| => Core.PrefixStdinCore(command, old(io.stdin()), i, old(io.trustedStreams())));
    forall i: nat | i < |command.inputs|
      ensures states[i + 1] == (if command.inputs[i].Stdin? then
                                  IOContract.ObservedReadStdinRemainingFields(states[i], old(io.trustedStreams())) else states[i])
    {
      Core.PrefixStdinStep(command, old(io.stdin()), i, old(io.trustedStreams()));
    }
    assert Spec.StdinTraceRelation(command, old(io.stdin()), io.stdin(), old(io.trustedStreams()), states);
    assert forall i: nat :: i < |command.inputs| ==>
                              Spec.InputReadRelation(
                                command, old(io.fs()), states[i], i, readResults[i],
                                old(io.trustedStreams())
                              ) &&
                              match command.inputs[i]
                              case Stdin =>
                                (match readResults[i]
                                 case Ok(data) =>
                                   Spec.DataSelectionRelation(
                                     command, data, stdoutFragments[i]
                                   ) &&
                                   stderrFragments[i] == []
                                 case Err(error) =>
                                   (if error.StreamFailure? then Spec.DataSelectionRelation(command, error.partial, stdoutFragments[i]) else stdoutFragments[i] == []) &&
                                   stderrFragments[i] == Spec.ErrorMessage("-", error))
                              case File(path) =>
                                (match readResults[i]
                                 case Ok(data) =>
                                   Spec.DataSelectionRelation(
                                     command, data, stdoutFragments[i]
                                   ) &&
                                   stderrFragments[i] == []
                                 case Err(readError) =>
                                   stdoutFragments[i] == [] &&
                                   stderrFragments[i] ==
                                   Spec.ErrorMessage(path, readError)) by {
      forall i: nat | i < |command.inputs|
        ensures
          Spec.InputReadRelation(
            command, old(io.fs()), states[i], i, readResults[i],
            old(io.trustedStreams())
          ) &&
          match command.inputs[i]
          case Stdin =>
            (match readResults[i]
             case Ok(data) =>
               Spec.DataSelectionRelation(
                 command, data, stdoutFragments[i]
               ) &&
               stderrFragments[i] == []
             case Err(error) =>
               (if error.StreamFailure? then Spec.DataSelectionRelation(command, error.partial, stdoutFragments[i]) else stdoutFragments[i] == []) &&
               stderrFragments[i] == Spec.ErrorMessage("-", error))
          case File(path) =>
            (match readResults[i]
             case Ok(data) =>
               Spec.DataSelectionRelation(
                 command, data, stdoutFragments[i]
               ) &&
               stderrFragments[i] == []
             case Err(readError) =>
               stdoutFragments[i] == [] &&
               stderrFragments[i] ==
               Spec.ErrorMessage(path, readError))
      {
        InputReadCoreRefines(
          command, old(io.fs()), old(io.stdin()), i, readResults[i],
          old(io.trustedStreams())
        );
        OutputPieceRefines(command, readResults[i]);
        match command.inputs[i]
        case Stdin =>
          reveal Core.InputReadCore();
        case File(_) =>
      }
    }

    Core.FragmentCutsSatisfyRelation(stdoutFragments);
    Core.FragmentCutsSatisfyRelation(stderrFragments);
    assert |readResults| == |command.inputs|;
    assert |stdoutFragments| == |command.inputs|;
    assert |stderrFragments| == |command.inputs|;
    assert Spec.FragmentsConcatenate(stdoutFragments, Core.JoinFragments(stdoutFragments), Core.FragmentCuts(stdoutFragments));
    assert Spec.FragmentsConcatenate(stderrFragments, Core.JoinFragments(stderrFragments), Core.FragmentCuts(stderrFragments));
    assert Spec.InputTraceWitnessRelation(command, old(io.fs()), old(io.stdin()), io.stdin(), old(io.trustedStreams()), readResults, Core.JoinFragments(stdoutFragments), Core.JoinFragments(stderrFragments), (exists i: nat | i < |command.inputs| :: readResults[i].Err?), states, stdoutFragments, stderrFragments, Core.FragmentCuts(stdoutFragments), Core.FragmentCuts(stderrFragments)) by {
      hide *;
      reveal Spec.InputTraceWitnessRelation();
    }
    assert Spec.InputTraceRelation(command, io, readResults, Core.JoinFragments(stdoutFragments),
                                   Core.JoinFragments(stderrFragments), exists i: nat | i < |command.inputs| :: readResults[i].Err?) by {
      hide *;
      reveal Spec.InputTraceRelation();
    }
  }

  twostate lemma {:isolate_assertions} PreparedSummaryImpliesPreparedSpec(
    raw: Schema.CutCmdRaw,
    io: BenchIO.IO,
    exit: int
  , new plannedStdout: BenchWorld.Bytes, new plannedStderr: BenchWorld.Bytes)
    requires Core.PreparedSummary(raw, io, exit, plannedStdout, plannedStderr)
    ensures Spec.PreparedSpec(raw, io, exit, plannedStdout, plannedStderr)
  {
    reveal Core.PreparedSummary();
    reveal Spec.PreparedSpec();

    if raw.mode == Schema.ModeRun {
      ghost var readResults: seq<BenchWorld.IOResult<BenchWorld.Bytes>>,
                stdoutFragments: seq<BenchWorld.Bytes>,
                stderrFragments: seq<BenchWorld.Bytes> :|
        Core.InputTraceCore(
          raw, old(io.fs()), old(io.stdin()), |raw.inputs|,
          readResults, stdoutFragments, stderrFragments,
          old(io.trustedStreams())
        ) &&
        io.stdin() ==
        Core.PrefixStdinCore(raw, old(io.stdin()), |raw.inputs|, old(io.trustedStreams())) &&
        plannedStdout ==
        Core.JoinFragments(stdoutFragments) &&
        plannedStderr ==
        Core.JoinFragments(stderrFragments) &&
        exit ==
        (if (exists i: nat | i < |raw.inputs| :: readResults[i].Err?)
         then 1
         else 0);
      InputTraceCoreRefines(
        raw, io, readResults, stdoutFragments, stderrFragments
      );
    }
  }

  twostate lemma CoreSummaryImpliesSpec(raw: Schema.CutCmdRaw, io: BenchIO.IO, exit: int)
    requires Core.CoreSummary(raw, io, exit)
    ensures Spec.Spec(raw, io, exit)
  {
    var out: BenchWorld.Bytes, diagnostics: BenchWorld.Bytes, normalExit: int :|
      Core.PreparedSummary(raw, io, normalExit,
                           out, diagnostics) &&
      Spec.Emission(raw, io, out, diagnostics, normalExit, exit);
    PreparedSummaryImpliesPreparedSpec(raw, io, normalExit,
                                       out, diagnostics);
  }
}
