include "../../core/IO.dfy"
include "TsortSchema.dfy"
include "TsortGraphBuildCore.dfy"
include "TsortSortCore.dfy"
include "TsortStepCore.dfy"
include "TsortCycleCore.dfy"
include "TsortSpec.dfy"
include "TsortProof.dfy"

module TsortCore {
  import BenchIO
  import BenchWorld
  import Schema = TsortSchema
  import Spec = TsortSpec
  import Proof = TsortProof
  import C = IOContract
  import Utf8 = Utf8Semantics
  import Build = TsortGraphBuildCore
  import GraphProof = TsortGraphBuildProof
  import State = TsortState
  import Sort = TsortSortCore
  import SortSpec = TsortSortSpec
  import SortProof = TsortSortProof
  import Step = TsortStepCore
  import StepSpec = TsortStepSpec
  import Trace = TsortStepProof
  import Cycle = TsortCycleCore
  import CycleProof = TsortCycleProof

  method Serialize(names: seq<BenchWorld.Bytes>, diagnostic: bool) returns (text: BenchWorld.Bytes)
    ensures text == (if diagnostic then Spec.CycleLines(names) else Spec.Lines(names))
  {
    text := [];
    var i := 0;
    while i < |names|
      invariant 0 <= i <= |names|
      invariant text + (if diagnostic then Spec.CycleLines(names[i..]) else Spec.Lines(names[i..])) ==
                (if diagnostic then Spec.CycleLines(names) else Spec.Lines(names))
      decreases |names| - i
    {
      text := text + Spec.OneLine(names[i], diagnostic);
      i := i + 1;
    }
  }

  method SortTokens(tokens: seq<BenchWorld.Bytes>, quoted: BenchWorld.Bytes)
    returns (output: BenchWorld.Bytes, diagnostics: BenchWorld.Bytes, exit: int)
    requires |tokens| % 2 == 0
    ensures Spec.SortResult(tokens, quoted, output, diagnostics, exit)
  {
    var vertices, graph := Build.BuildGraph(tokens);
    GraphProof.Fields(tokens, graph);
    output, diagnostics, exit := SortGraph(vertices, graph, quoted);
    reveal Spec.SortResult();
    assert Spec.InputGraph(tokens, graph);
  }

  method {:isolate_assertions} SortGraph(
    vertices: seq<BenchWorld.Bytes>,
    initial: map<BenchWorld.Bytes, seq<BenchWorld.Bytes>>,
    quoted: BenchWorld.Bytes
  )
    returns (output: BenchWorld.Bytes, diagnostics: BenchWorld.Bytes, exit: int)
    requires (set v | v in vertices) == initial.Keys
    requires forall i: nat, j: nat | i < j < |vertices| :: vertices[i] != vertices[j]
    requires forall source | source in initial ::
               forall target | target in initial[source] ::
                 target in initial
    ensures Spec.GraphResult(initial, quoted, output, diagnostics, exit)
  {
    var graph := initial;
    var sorted := Sort.SortVertices(vertices);
    var state := new State.SortState(vertices);
    Sort.ComputeIndegrees(state, graph);
    SortProof.InitialLive(graph, state.visited, state.indeg);
    Sort.BuildPendingQueue(state, sorted, graph);
    ghost var origins := Trace.Identity(initial, state.visited, state.queue);
    Trace.ObserveReady(initial, graph, origins, state.visited, state.queue, state.indeg);
    ghost var run := Trace.Start(initial, Trace.SnapshotOf(initial, origins, state.visited, state.queue));
    ghost var offsets: seq<nat> := [0];
    ghost var errOffsets: seq<nat> := [0];
    var ordered: seq<BenchWorld.Bytes> := [];
    output, diagnostics, exit := [], [], 0;
    Proof.EmptyText(quoted);
    while |ordered| < |vertices|
      invariant state.WellFormed(graph) && StepSpec.Ready(graph, state.queue, state.visited, state.indeg)
      invariant forall v | v in state.queue :: !state.visited[v]
      invariant (set v | v in vertices) == graph.Keys && |ordered| <= |vertices|
      invariant forall v | v in graph :: state.visited[v] == (v in ordered)
      invariant SortSpec.TopologicalPrefix(graph, ordered)
      invariant Trace.Projection(initial, graph, origins) && Trace.Schedule(initial, run)
      invariant |run.states| == |run.events| + 1
      invariant run.states[|run.events|] == Trace.SnapshotOf(initial, origins, state.visited, state.queue)
      invariant Proof.Text(run.events, quoted, output, diagnostics, exit, offsets, errOffsets)
      decreases |vertices| - |ordered|, SortSpec.EdgeCount(vertices, graph)
    {
      ghost var beforeEvents := run.events;
      ghost var beforeQueue, beforeVisited, beforeIndeg := state.queue, state.visited, state.indeg;
      ghost var beforeOut, beforeErr, beforeExit := output, diagnostics, exit;
      ghost var event: Spec.Event;
      assert StepSpec.Ready(graph, beforeQueue, beforeVisited, beforeIndeg) by { hide *; }
      if |state.queue| > 0 {
        var vertex := state.queue[0];
        SortProof.AppendPrefix(graph, ordered, state.visited, state.indeg, vertex);
        Step.Step(state, graph);
        Trace.RecordEmit(initial, graph, origins, beforeQueue, beforeVisited, beforeIndeg,
                         state.queue, state.visited, state.indeg);
        event := Spec.Emit(vertex);
        ordered := ordered + [vertex];
        output := output + Spec.OneLine(vertex, false);
        assert output == beforeOut + (if event.Emit? then event.vertex + "\n" else []) by {
          hide *;
          reveal Spec.OneLine();
        }
      } else {
        SortProof.SizeFields(vertices, graph, ordered);
        assert exists v | v in graph :: !state.visited[v];
        var remaining, cycle, index := Cycle.BreakStalledCycle(state, sorted, graph);
        ghost var cutIndeg := state.indeg;
        CycleProof.RecoveryCut(graph, remaining, beforeIndeg, cutIndeg, cycle, index);
        var source := cycle[|cycle| - 1];
        event := Spec.Cut(cycle, (source, origins[source][index]));
        assert output == beforeOut + (if event.Emit? then event.vertex + "\n" else []) by { hide *; }
        SortProof.AfterCut(vertices, graph, remaining, source, index, ordered);
        SortProof.ProcessedPredecessors(remaining, ordered, state.visited);
        var pending := map v | v in remaining :: if state.visited[v] then [] else remaining[v];
        assert state.WellFormed(pending) by { hide *; reveal state.WellFormed(); }
        {
          hide *;
          Sort.ComputeIndegrees(state, pending);
        }
        {
          hide *;
          SortProof.FilteredLive(remaining, state.visited, state.indeg);
        }
        Sort.BuildPendingQueue(state, sorted, remaining);
        {
          hide *;
          CycleProof.RecordCut(
            initial, graph, origins, beforeVisited, beforeIndeg, cutIndeg, remaining,
            state.queue, state.indeg, cycle, index
          );
        }
        origins := origins[source := origins[source][..index] + origins[source][index + 1..]];
        graph := remaining;
        var lines := Serialize(cycle, true);
        diagnostics := diagnostics + Spec.LoopText(quoted) + lines;
        exit := 1;
      }
      assert diagnostics == beforeErr + (if event.Cut? then Spec.LoopText(quoted) + Spec.CycleLines(event.cycle) else []) by { hide *; }
      assert exit == (if event.Cut? then 1 else beforeExit) by { hide *; }
      assert origins.Keys == initial.Keys == state.visited.Keys;
      {
        hide *;
        run := Trace.Extend(initial, run, Trace.SnapshotOf(initial, origins, state.visited, state.queue), event);
        Proof.AppendText(beforeEvents, quoted, beforeOut, beforeErr, beforeExit, offsets, errOffsets, event);
        offsets := offsets + [|output|];
        errOffsets := errOffsets + [|diagnostics|];
      }
      assert Proof.Text(run.events, quoted, output, diagnostics, exit, offsets, errOffsets) by { hide *; }
      assert run.states[|run.events|] == Trace.SnapshotOf(initial, origins, state.visited, state.queue) by { hide *; }
      assert state.WellFormed(graph) && StepSpec.Ready(graph, state.queue, state.visited, state.indeg) by { hide *; }
      SortProof.SizeFields(vertices, graph, ordered);
    }
    SortProof.SizeFields(vertices, graph, ordered);
    assert forall v | v in graph :: state.visited[v];
    Proof.Finish(initial, run, quoted, output, diagnostics, exit, offsets, errOffsets);
  }

  method Prepare(raw: Schema.TsortCmdRaw, io: BenchIO.IO)
    returns (exit: int, output: BenchWorld.Bytes, diagnostics: BenchWorld.Bytes)
    modifies (if raw.mode == Schema.ModeRun && Spec.InputPath(raw) == "-" then {io.stdinRegion} else {})
    ensures Spec.Prepared(raw, io, exit, output, diagnostics)
  {
    output := [];
    diagnostics := [];
    exit := 0;
    if raw.mode == Schema.ModeHelp { output := Spec.HelpTextSpec(); return; }
    if raw.mode == Schema.ModeVersion { output := Spec.VersionTextSpec(); return; }
    if raw.mode.ModeExtraOperand? {
      var quoted := io.QuoteArgument(Utf8.Encode(raw.mode.operand));
      diagnostics := Spec.ExtraOperandText(quoted);
      exit := 1;
      return;
    }
    var path := Spec.InputPath(raw);
    assert raw.mode == Schema.ModeRun;
    assert path == Spec.InputPath(raw);
    var read: BenchWorld.IOResult<BenchWorld.Bytes>;
    if path == "-" { read := io.ReadStdin(); } else { read := io.ReadFile(path); }
    if path == "-" {
      assert read == C.ObservedReadStdinResultFields(old(io.stdin()), io.trustedStreams());
      assert io.stdin() == C.ObservedReadStdinRemainingFields(old(io.stdin()), io.trustedStreams());
    } else {
      assert read == C.ObservedReadFileResultFields(io.fs(), io.trustedStreams(), path);
    }
    var alwaysQuoted := io.QuoteafPath(path);
    var quoted := Spec.FilenameText(path, alwaysQuoted);
    assert quoted == Spec.FilenameText(path, C.QuoteafPathResult(path));
    if read.Err? && C.ReadResultStage(read) != BenchWorld.CloseFailed {
      var reason := io.GetCLocaleErrnoText(C.ResultErrno(read));
      diagnostics := if path != "-" && C.ReadResultStage(read) == BenchWorld.OpenFailed
      then Spec.FileErrorText(quoted, reason) else Spec.ReadErrorText(quoted, reason);
      exit := 1;
      return;
    }
    assert !(read.Err? && C.ReadResultStage(read) != BenchWorld.CloseFailed);
    var data := C.ReadResultData(read);
    var tokens := Build.Tokenize(data);
    ghost var starts: seq<nat>, ends: seq<nat> :| Spec.Tokenization(data, tokens, starts, ends);
    reveal Spec.DataResult();
    if |tokens| % 2 != 0 {
      diagnostics := Spec.OddTokensText(quoted);
      exit := 1;
    } else {
      output, diagnostics, exit := SortTokens(tokens, quoted);
    }
    assert Spec.DataResult(data, quoted, output, diagnostics, exit);
    var normalExit := exit;
    var errors := diagnostics;
    if C.ReadResultStage(read) == BenchWorld.CloseFailed && !(exit == 1 && output == []) {
      var reason := io.GetCLocaleErrnoText(C.ResultErrno(read));
      assert Spec.FileErrorText(quoted, reason) ==
             Spec.FileErrorText(quoted, C.CLocaleErrnoTextResult(C.ResultErrno(read)));
      diagnostics := diagnostics + Spec.FileErrorText(quoted, reason);
      exit := 1;
    }
    assert Spec.DataResult(C.ReadResultData(read), quoted, output, errors, normalExit);
    assert exists expectedExit: int, expectedErrors: BenchWorld.Bytes ::
        Spec.DataResult(data, quoted, output, expectedErrors, expectedExit) &&
        var closeError := C.ReadResultStage(read) == BenchWorld.CloseFailed && !(expectedExit == 1 && output == []);
        diagnostics == expectedErrors +
        (if closeError then Spec.FileErrorText(quoted, C.CLocaleErrnoTextResult(C.ResultErrno(read))) else []) &&
        exit == (if closeError then 1 else expectedExit);
  }

  method Flush(io: BenchIO.IO, output: BenchWorld.Bytes, diagnostics: BenchWorld.Bytes, normalExit: int)
    returns (exit: int)
    modifies io.stdoutRegion, io.stderrRegion
    ensures Spec.Emission(
              old(io.stdout()), old(io.stderr()), io.stdout(), io.stderr(),
              io.trustedStreams(), output, diagnostics, normalExit, exit
            )
  {
    reveal Spec.Emission();
    var committed: nat := 0;
    var outErr := 0;
    if output != [] {
      var written := io.WriteStdout(output);
      committed := C.WriteResultCommitted(written);
      outErr := C.ResultErrno(written);
    }
    var errors := diagnostics;
    if outErr != 0 {
      var reason := io.GetCLocaleErrnoText(outErr);
      errors := errors + Spec.WriteErrorText(reason);
    }
    assert errors == diagnostics + (if outErr == 0 then [] else Spec.WriteErrorText(C.CLocaleErrnoTextResult(outErr)));
    var errCommitted: nat := 0;
    var errErr := 0;
    if errors != [] {
      var written := io.WriteStderr(errors);
      errCommitted := C.WriteResultCommitted(written);
      errErr := C.ResultErrno(written);
      assert C.WriteStderrSpec(old(io.stderr()), io.trustedStreams(), io.stderr(), errors, errCommitted, errErr);
    }
    exit := if outErr != 0 || errErr != 0 then 1 else normalExit;
    assert Spec.EmissionOutcome(
        old(io.stdout()), old(io.stderr()), io.stdout(), io.stderr(),
        io.trustedStreams(), output, diagnostics, normalExit, exit, committed, outErr, errCommitted, errErr
      );
  }

  method RunCore(raw: Schema.TsortCmdRaw, io: BenchIO.IO) returns (exit: int)
    modifies (if raw.mode == Schema.ModeRun && Spec.InputPath(raw) == "-" then {io.stdinRegion} else {}),
             io.stdoutRegion, io.stderrRegion
    ensures Spec.Spec(raw, io, exit)
  {
    reveal Spec.Spec();
    var normalExit, output, diagnostics := Prepare(raw, io);
    exit := Flush(io, output, diagnostics, normalExit);
  }
}
