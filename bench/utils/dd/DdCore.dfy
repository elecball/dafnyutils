include "DdSpec.dfy"

module DdCore {
  import BenchIO
  import BW = BenchWorld
  import C = IOContract
  import S = DdSchema
  import Spec = DdSpec

  function Render(raw: S.DdCmdRaw, data: BW.Bytes): BW.Bytes {
    seq(|data|, i requires 0 <= i < |data| =>
      Spec.CaseByte(raw, data[Spec.SourceIndex(i, |data|, raw.swab)]))
  }

  function RenderSlice(raw: S.DdCmdRaw, data: BW.Bytes, start: nat, end: nat): BW.Bytes
    requires start <= end <= |data|
    ensures RenderSlice(raw, data, start, end) == Render(raw, data)[start..end]
  {
    seq(end - start, i requires 0 <= i < end - start =>
      Spec.CaseByte(raw, data[Spec.SourceIndex(start + i, |data|, raw.swab)]))
  }

  function Pad(raw: S.DdCmdRaw, data: BW.Bytes): BW.Bytes
    requires |data| <= raw.ibs
    ensures Spec.Padded(raw, data, Pad(raw, data))
  {
    if data == [] || !raw.sync then data
    else data + seq(raw.ibs - |data|, i => '\0')
  }

  lemma RenderPrefix(raw: S.DdCmdRaw, a: BW.Bytes, b: BW.Bytes, length: nat)
    requires |a| <= |b| && b[..|a|] == a
    requires length <= Spec.Ready(|a|, raw.swab)
    ensures Render(raw, a)[..length] == Render(raw, b)[..length]
  {
    forall i: nat | i < length
      ensures Render(raw, a)[i] == Render(raw, b)[i]
    {
      assert Spec.SourceIndex(i, |a|, raw.swab) == Spec.SourceIndex(i, |b|, raw.swab);
    }
  }

  lemma ReadObservationAppend(
    before: BW.Bytes, streams: (BW.TrustedStreamRequest) -> BW.TrustedStreamResult,
    limit: nat, cuts: seq<nat>, states: seq<BW.Bytes>, errors: seq<int>,
    after: BW.Bytes, end: nat, err: int
  )
    requires |cuts| == |errors| + 1 && |states| == |cuts|
    requires cuts[|errors|] <= end <= |before| && cuts[|errors|] < limit && end <= limit
    requires forall j: nat | j < |errors| :: Spec.ReadAt(before, streams, limit, cuts, states, errors, j)
    requires forall j: nat | j < |errors| :: Spec.ReadProgress(cuts, errors, limit, j)
    requires C.ReadStdinChunkSpec(states[|errors|], streams, after, limit - cuts[|errors|],
                                  before[cuts[|errors|]..end], err)
    ensures forall j: nat | j < |errors| + 1 ::
              Spec.ReadAt(before, streams, limit, cuts + [end], states + [after], errors + [err], j)
    ensures err == 0 && cuts[|errors|] < end < limit ==>
              forall j: nat | j < |errors| + 1 :: Spec.ReadProgress(cuts + [end], errors + [err], limit, j)
  {
    reveal Spec.ReadAt();
    forall j: nat | j < |errors| + 1
      ensures Spec.ReadAt(before, streams, limit, cuts + [end], states + [after], errors + [err], j)
    {
      if j < |errors| {
        assert Spec.ReadAt(before, streams, limit, cuts, states, errors, j);
        assert Spec.ReadProgress(cuts, errors, limit, j);
      }
    }
    if err == 0 && cuts[|errors|] < end < limit {
      forall j: nat | j < |errors| + 1
        ensures Spec.ReadProgress(cuts + [end], errors + [err], limit, j)
      {
        if j < |errors| { assert Spec.ReadProgress(cuts, errors, limit, j); }
      }
    }
  }

  method ReadBlock(io: BenchIO.IO, limit: nat, fullblock: bool)
    returns (data: BW.Bytes, err: int)
    requires 0 < limit <= 9223372036854775806
    modifies io.stdinRegion
    ensures Spec.BlockRead(old(io.stdin()), io.stdin(), io.trustedStreams(), limit, fullblock, data, err)
    ensures |io.stdin()| <= |old(io.stdin())|
    ensures 0 <= err && |data| <= limit
    ensures err != 0 ==> data == []
    ensures err == 0 ==> data + io.stdin() == old(io.stdin())
    ensures err == 0 && data == [] ==> io.stdin() == []
  {
    reveal Spec.ReadPartition();
    reveal Spec.BlockRead();
    ghost var before := io.stdin();
    ghost var streams := io.trustedStreams();
    data := [];
    err := 0;
    ghost var cuts: seq<nat> := [0];
    ghost var states := [before];
    ghost var errors: seq<int> := [];
    while true
      invariant |data| < limit
      invariant before == data + io.stdin()
      invariant |cuts| == |errors| + 1 && |states| == |cuts|
      invariant cuts[0] == 0 && cuts[|errors|] == |data|
      invariant states[0] == before && states[|errors|] == io.stdin()
      invariant !fullblock ==> |errors| == 0
      invariant forall j: nat | j < |errors| :: Spec.ReadAt(before, streams, limit, cuts, states, errors, j)
      invariant forall j: nat | j < |errors| :: Spec.ReadProgress(cuts, errors, limit, j)
      decreases limit - |data|
    {
      ghost var previous := data;
      var read := io.ReadStdinChunk(limit - |data|);
      var part := C.ReadResultData(read);
      err := C.ResultErrno(read);
      var consumed := data + part;
      assert before == consumed + io.stdin();
      assert before[|data|..|consumed|] == part;
      ReadObservationAppend(before, streams, limit, cuts, states, errors, io.stdin(), |consumed|, err);
      cuts := cuts + [|consumed|];
      states := states + [io.stdin()];
      errors := errors + [err];
      if err != 0 || part == [] || |consumed| == limit || !fullblock {
        data := if err == 0 then consumed else [];
        assert Spec.ReadPartition(before, io.stdin(), streams, limit, fullblock,
                                  data, err, cuts, states, errors);
        return;
      }
      data := consumed;
    }
  }

  lemma InputAppend(
    raw: S.DdCmdRaw, streams: (BW.TrustedStreamRequest) -> BW.TrustedStreamResult,
    before: BW.Bytes, middle: BW.Bytes, after: BW.Bytes,
    records: seq<Spec.Record>, states: seq<BW.Bytes>, data: BW.Bytes, cuts: seq<nat>,
    record: Spec.Record, padded: BW.Bytes
  )
    requires Spec.InputPartition(raw, streams, before, middle, records, states, data, cuts)
    requires forall i: nat | i < |records| :: records[i].err == 0 && records[i].data != []
    requires Spec.CountAllows(raw, |records|)
    requires Spec.BlockRead(middle, after, streams, Spec.ReadLimit(raw, |records|), raw.fullblock, record.data, record.err)
    requires Spec.Padded(raw, record.data, padded)
    ensures Spec.InputPartition(raw, streams, before, after, records + [record], states + [after],
                                data + padded, cuts + [|data + padded|])
  {
    reveal Spec.InputAt();
    forall i: nat | i < |records| + 1
      ensures Spec.InputAt(raw, streams, records + [record], states + [after],
                           data + padded, cuts + [|data + padded|], i)
    {
      if i < |records| {
        assert Spec.InputAt(raw, streams, records, states, data, cuts, i);
        assert (data + padded)[cuts[i]..cuts[i + 1]] == data[cuts[i]..cuts[i + 1]];
      } else {
        assert (data + padded)[|data|..] == padded;
      }
    }

  }

  lemma OutputExtend(
    raw: S.DdCmdRaw, streams: (BW.TrustedStreamRequest) -> BW.TrustedStreamResult,
    before: BW.Bytes, after: BW.Bytes, records: seq<Spec.Record>, dataCuts: seq<nat>,
    data: BW.Bytes, added: BW.Bytes, record: Spec.Record,
    writes: seq<Spec.Write>, states: seq<BW.Bytes>, cuts: seq<nat>
  )
    requires Spec.OutputPartition(raw, streams, before, after, records, dataCuts,
                                  Render(raw, data), writes, states, cuts)
    requires forall j: nat | j < |writes| :: !writes[j].final
    requires |writes| == 0 || writes[|writes| - 1].err == 0
    requires cuts[|writes|] <= Spec.Ready(|data|, raw.swab)
    requires forall i: nat | i < |dataCuts| :: dataCuts[i] <= |data|
    ensures Spec.OutputPartition(raw, streams, before, after, records + [record], dataCuts + [|data + added|],
                                 Render(raw, data + added), writes, states, cuts)
  {
    reveal Spec.OutputAt();
    RenderPrefix(raw, data, data + added, cuts[|writes|]);
    forall j: nat | j < |writes|
      ensures Spec.OutputAt(raw, streams, records + [record], dataCuts + [|data + added|],
                            Render(raw, data + added), writes, states, cuts, j)
    {
      assert Spec.OutputAt(raw, streams, records, dataCuts, Render(raw, data), writes, states, cuts, j);
      assert Render(raw, data)[cuts[j]..cuts[j + 1]] ==
             Render(raw, data)[..cuts[|writes|]][cuts[j]..cuts[j + 1]];
      assert Render(raw, data + added)[cuts[j]..cuts[j + 1]] ==
             Render(raw, data + added)[..cuts[|writes|]][cuts[j]..cuts[j + 1]];
    }

  }

  lemma OutputAppend(
    raw: S.DdCmdRaw, streams: (BW.TrustedStreamRequest) -> BW.TrustedStreamResult,
    before: BW.Bytes, middle: BW.Bytes, after: BW.Bytes,
    records: seq<Spec.Record>, dataCuts: seq<nat>, output: BW.Bytes,
    writes: seq<Spec.Write>, states: seq<BW.Bytes>, cuts: seq<nat>, write: Spec.Write
  )
    requires Spec.OutputPartition(raw, streams, before, middle, records, dataCuts, output, writes, states, cuts)
    requires |writes| == 0 || writes[|writes| - 1].err == 0
    requires forall j: nat | j < |writes| :: !writes[j].final
    requires Spec.OutputAt(raw, streams, records, dataCuts, output,
                           writes + [write], states + [after], cuts + [write.end], |writes|)
    ensures Spec.OutputPartition(raw, streams, before, after, records, dataCuts, output,
                                 writes + [write], states + [after], cuts + [write.end])
  {
    reveal Spec.OutputAt();
    forall j: nat | j < |writes| + 1
      ensures Spec.OutputAt(raw, streams, records, dataCuts, output,
                            writes + [write], states + [after], cuts + [write.end], j)
    {
      if j < |writes| {
        assert Spec.OutputAt(raw, streams, records, dataCuts, output, writes, states, cuts, j);
      }
    }
  }

  method EmitSlice(
    raw: S.DdCmdRaw, io: BenchIO.IO, data: BW.Bytes, start: nat, end: nat, final: bool,
    ghost preOut: BW.Bytes, ghost records: seq<Spec.Record>, ghost dc: seq<nat>,
    ghost writes: seq<Spec.Write>, ghost outs: seq<BW.Bytes>, ghost oc: seq<nat>
  ) returns (err: int, ghost observation: Spec.Write)
    requires Spec.OutputPartition(raw, io.trustedStreams(), preOut, io.stdout(), records, dc, Render(raw, data), writes, outs, oc)
    requires start == oc[|writes|]
    requires |writes| == 0 || writes[|writes| - 1].err == 0
    requires forall j: nat | j < |writes| :: !writes[j].final
    requires Spec.WriteBoundary(raw, records, dc, |data|, |writes|, start, end, |records|, final)
    modifies io.stdoutRegion
    ensures observation.err == err && observation.end == end &&
            observation.readCount == |records| && observation.final == final
    ensures Spec.OutputPartition(raw, io.trustedStreams(), preOut, io.stdout(), records, dc, Render(raw, data),
                                 writes + [observation], outs + [io.stdout()], oc + [end])
  {
    ghost var beforeWrite := io.stdout();
    assert Spec.OutputPartition(raw, io.trustedStreams(), preOut, beforeWrite, records, dc, Render(raw, data), writes, outs, oc);
    var result := io.WriteStdout(RenderSlice(raw, data, start, end));
    err := C.ResultErrno(result);
    observation := Spec.Write(end, |records|, final, C.WriteResultCommitted(result), err);
    assert Spec.OutputAt(raw, io.trustedStreams(), records, dc, Render(raw, data),
                         writes + [observation], outs + [io.stdout()], oc + [end], |writes|) by {
      reveal Spec.OutputAt();
    }
    OutputAppend(raw, io.trustedStreams(), preOut, beforeWrite, io.stdout(), records, dc,
                 Render(raw, data), writes, outs, oc, observation);
  }

  method FlushFull(
    raw: S.DdCmdRaw, io: BenchIO.IO, data: BW.Bytes, start: nat,
    ghost preOut: BW.Bytes, ghost records: seq<Spec.Record>, ghost dc: seq<nat>,
    ghost oldWrites: seq<Spec.Write>, ghost oldOuts: seq<BW.Bytes>, ghost oldCuts: seq<nat>
  ) returns (submitted: nat, err: int, ghost writes: seq<Spec.Write>, ghost outs: seq<BW.Bytes>, ghost oc: seq<nat>)
    requires !Spec.Direct(raw) && |records| > 0
    requires Spec.OutputPartition(raw, io.trustedStreams(), preOut, io.stdout(), records, dc, Render(raw, data), oldWrites, oldOuts, oldCuts)
    requires start == oldCuts[|oldWrites|] && start <= Spec.Ready(|data|, raw.swab)
    requires start == |oldWrites| * raw.obs
    requires Spec.Ready(dc[|records| - 1], raw.swab) < start + raw.obs
    requires |oldWrites| == 0 || oldWrites[|oldWrites| - 1].err == 0
    requires forall j: nat | j < |oldWrites| :: !oldWrites[j].final
    modifies io.stdoutRegion
    ensures Spec.OutputPartition(raw, io.trustedStreams(), preOut, io.stdout(), records, dc, Render(raw, data), writes, outs, oc)
    ensures submitted == oc[|writes|] && submitted <= Spec.Ready(|data|, raw.swab)
    ensures submitted == |writes| * raw.obs
    ensures err == (if |writes| == 0 then 0 else writes[|writes| - 1].err)
    ensures forall j: nat | j < |writes| :: !writes[j].final
    ensures err == 0 ==> Spec.Ready(|data|, raw.swab) < submitted + raw.obs
    ensures err != 0 ==> |writes| > 0 && writes[|writes| - 1].readCount == |records|
  {
    submitted := start;
    err := 0;
    writes, outs, oc := oldWrites, oldOuts, oldCuts;
    while submitted + raw.obs <= Spec.Ready(|data|, raw.swab) && err == 0
      invariant Spec.OutputPartition(raw, io.trustedStreams(), preOut, io.stdout(), records, dc, Render(raw, data), writes, outs, oc)
      invariant submitted == oc[|writes|] && submitted <= Spec.Ready(|data|, raw.swab)
      invariant submitted == |writes| * raw.obs
      invariant Spec.Ready(dc[|records| - 1], raw.swab) < submitted + raw.obs
      invariant forall j: nat | j < |writes| :: !writes[j].final
      invariant err == (if |writes| == 0 then 0 else writes[|writes| - 1].err)
      invariant err != 0 ==> |writes| > 0 && writes[|writes| - 1].readCount == |records|
      decreases |data| - submitted
    {
      var end := submitted + raw.obs;
      var error, observation := EmitSlice(raw, io, data, submitted, end, false, preOut, records, dc, writes, outs, oc);
      err := error;
      writes := writes + [observation];
      outs := outs + [io.stdout()];
      oc := oc + [end];
      submitted := end;
    }
  }

  datatype CopyWitness = CopyWitness(
    data: BW.Bytes, records: seq<Spec.Record>, ins: seq<BW.Bytes>, dc: seq<nat>,
    writes: seq<Spec.Write>, outs: seq<BW.Bytes>, oc: seq<nat>,
    readErr: int, writeErr: int, committed: nat, stderrErr: int
  )

  opaque ghost predicate Completed(
    raw: S.DdCmdRaw, streams: (BW.TrustedStreamRequest) -> BW.TrustedStreamResult,
    preIn: BW.Bytes, postIn: BW.Bytes, preOut: BW.Bytes, postOut: BW.Bytes,
    preErr: BW.Bytes, postErr: BW.Bytes, exit: int, w: CopyWitness
  ) {
    raw.mode == S.Copy && raw.error == S.None &&
    Spec.CopyRelation(raw, streams, preIn, postIn, preOut, postOut,
                      w.data, Render(raw, w.data), w.records, w.ins, w.dc, w.writes, w.outs, w.oc, w.readErr, w.writeErr) &&
    C.WriteStderrSpec(preErr, streams, postErr,
                      Spec.Warnings(raw.warnings) + Spec.ReadError(w.readErr) +
                      Spec.WriteError(w.writeErr, Spec.BufferedFailure(raw, w.writes)), w.committed, w.stderrErr) &&
    exit == (if w.readErr == 0 && w.writeErr == 0 && w.stderrErr == 0 then 0 else 1)
  }

  opaque twostate predicate WitnessSummary(raw: S.DdCmdRaw, io: BenchIO.IO, exit: int, new w: CopyWitness)
    reads io.stdinRegion, io.stdoutRegion, io.stderrRegion, io.trustedStreamsRegion
  {
    Completed(raw, io.trustedStreams(), old(io.stdin()), io.stdin(), old(io.stdout()), io.stdout(),
              old(io.stderr()), io.stderr(), exit, w)
  }

  twostate predicate CoreSummary(raw: S.DdCmdRaw, io: BenchIO.IO, exit: int)
    reads io.stdinRegion, io.stdoutRegion, io.stderrRegion, io.trustedStreamsRegion
  {
    if raw.mode != S.Copy || raw.error != S.None then Spec.Spec(raw, io, exit)
    else exists w: CopyWitness :: WitnessSummary(raw, io, exit, w)
  }

  twostate lemma SummarizeCopy(raw: S.DdCmdRaw, io: BenchIO.IO, exit: int, new w: CopyWitness)
    requires raw.mode == S.Copy && raw.error == S.None
    requires Completed(raw, io.trustedStreams(), old(io.stdin()), io.stdin(), old(io.stdout()), io.stdout(),
                       old(io.stderr()), io.stderr(), exit, w)
    ensures CoreSummary(raw, io, exit)
  {
    assert WitnessSummary(raw, io, exit, w) by {
      reveal WitnessSummary();
    }
  }

  twostate lemma SummarizeEarly(
    raw: S.DdCmdRaw, io: BenchIO.IO, exit: int, new out: BW.Bytes, new diagnostics: BW.Bytes,
    committedOut: nat, writeErr: int, committedErr: nat, stderrErr: int
  )
    requires raw.mode != S.Copy || raw.error != S.None
    requires out == (if raw.mode == S.Help then Spec.HelpText() else if raw.mode == S.Version then Spec.VersionText() else [])
    requires diagnostics == (if raw.mode == S.Copy then Spec.Warnings(raw.warnings) + Spec.ErrorText(raw.error) else [])
    requires C.WriteStdoutSpec(old(io.stdout()), io.trustedStreams(), io.stdout(), out, committedOut, writeErr)
    requires C.WriteStderrSpec(old(io.stderr()), io.trustedStreams(), io.stderr(),
                               diagnostics + Spec.EarlyWriteError(writeErr), committedErr, stderrErr)
    requires exit == (if writeErr != 0 || stderrErr != 0 || (raw.error != S.None && raw.mode == S.Copy) then 1 else 0)
    ensures Spec.Spec(raw, io, exit)
  {
  }

  method {:isolate_assertions} RunEarly(raw: S.DdCmdRaw, io: BenchIO.IO) returns (exit: int)
    requires raw.mode != S.Copy || raw.error != S.None
    modifies io.stdoutRegion, io.stderrRegion
    ensures Spec.Spec(raw, io, exit)
  {
    var out: BW.Bytes := if raw.mode == S.Help then Spec.HelpText() else if raw.mode == S.Version then Spec.VersionText() else [];
    var diagnostics: BW.Bytes := if raw.mode == S.Copy then Spec.Warnings(raw.warnings) + Spec.ErrorText(raw.error) else [];
    var write := io.WriteStdout(out);
    var we := C.ResultErrno(write);
    var message := io.GetCLocaleErrnoText(we);
    var stderr := io.WriteStderr(diagnostics + (if we == 0 then [] else Spec.EarlyWriteDiagnostic(message)));
    exit := if we != 0 || C.ResultErrno(stderr) != 0 || (raw.error != S.None && raw.mode == S.Copy) then 1 else 0;
    SummarizeEarly(raw, io, exit, out, diagnostics, C.WriteResultCommitted(write), we,
                   C.WriteResultCommitted(stderr), C.ResultErrno(stderr));
  }

  method {:isolate_assertions} ReadAndAppend(
    raw: S.DdCmdRaw, io: BenchIO.IO, data: BW.Bytes, ordinal: nat,
    ghost preIn: BW.Bytes, ghost preOut: BW.Bytes,
    ghost records: seq<Spec.Record>, ghost ins: seq<BW.Bytes>, ghost dc: seq<nat>,
    ghost writes: seq<Spec.Write>, ghost outs: seq<BW.Bytes>, ghost oc: seq<nat>
  ) returns (block: BW.Bytes, padded: BW.Bytes, err: int)
    requires ordinal == |records| && Spec.CountAllows(raw, ordinal)
    requires Spec.InputPartition(raw, io.trustedStreams(), preIn, io.stdin(), records, ins, data, dc)
    requires Spec.OutputPartition(raw, io.trustedStreams(), preOut, io.stdout(), records, dc, Render(raw, data), writes, outs, oc)
    requires forall i: nat | i < |records| :: records[i].err == 0 && records[i].data != []
    requires forall j: nat | j < |writes| :: !writes[j].final
    requires |writes| == 0 || writes[|writes| - 1].err == 0
    requires oc[|writes|] <= Spec.Ready(|data|, raw.swab)
    requires forall i: nat | i < |dc| :: dc[i] <= |data|
    modifies io.stdinRegion
    ensures Spec.InputPartition(raw, io.trustedStreams(), preIn, io.stdin(),
                                records + [Spec.Record(block, err)], ins + [io.stdin()], data + padded, dc + [|data + padded|])
    ensures Spec.OutputPartition(raw, io.trustedStreams(), preOut, io.stdout(),
                                 records + [Spec.Record(block, err)], dc + [|data + padded|], Render(raw, data + padded), writes, outs, oc)
    ensures Spec.Padded(raw, block, padded)
    ensures 0 <= err && |block| <= raw.ibs
    ensures |io.stdin()| <= |old(io.stdin())|
    ensures err != 0 ==> block == []
    ensures err == 0 ==> block + io.stdin() == old(io.stdin())
    ensures err == 0 && block == [] ==> io.stdin() == []
  {
    var limit := Spec.ReadLimit(raw, ordinal);
    assert 0 < limit <= raw.ibs;
    ghost var previousIn := io.stdin();
    var input, error := ReadBlock(io, limit, raw.fullblock);
    block, err := input, error;
    padded := Pad(raw, block);
    InputAppend(raw, io.trustedStreams(), preIn, previousIn, io.stdin(), records, ins,
                data, dc, Spec.Record(block, err), padded);
    OutputExtend(raw, io.trustedStreams(), preOut, io.stdout(), records, dc, data, padded,
                 Spec.Record(block, err), writes, outs, oc);
  }

  // The exact conjunction of implementation progress facts is packaged to
  // avoid rechecking each sequence bound at every loop verification boundary.
  opaque ghost predicate LoopProgress(
    raw: S.DdCmdRaw, data: BW.Bytes, ordinal: nat, submitted: nat,
    records: seq<Spec.Record>, dc: seq<nat>, writes: seq<Spec.Write>, oc: seq<nat>,
    readErr: int, writeErr: int, buffered: bool, done: bool
  ) {
    |dc| == |records| + 1 && |oc| == |writes| + 1 &&
    ordinal == |records| && submitted == oc[|writes|] &&
    (forall i: nat | i < |dc| :: dc[i] <= |data|) &&
    (Spec.Direct(raw) ==> !raw.swab) &&
    (forall j: nat | j < |writes| :: !writes[j].final) &&
    readErr == (if ordinal == 0 then 0 else records[ordinal - 1].err) &&
    writeErr == (if |writes| == 0 then 0 else writes[|writes| - 1].err) &&
    (writeErr != 0 ==> buffered == Spec.BufferedFailure(raw, writes)) &&
    (!done ==> (readErr == 0 && writeErr == 0 &&
                (forall i: nat | i < ordinal :: records[i].err == 0 && records[i].data != []))) &&
    (done ==> Spec.InputEnded(raw, records) || writeErr != 0) &&
    (writeErr != 0 ==> |writes| > 0 && writes[|writes| - 1].readCount == ordinal) &&
    (!Spec.Direct(raw) ==> submitted == |writes| * raw.obs) &&
    (writeErr == 0 ==> (
         if Spec.Direct(raw) then submitted == |data|
         else submitted <= Spec.Ready(|data|, raw.swab) < submitted + raw.obs))
  }

  method {:isolate_assertions} FinishCopy(
    raw: S.DdCmdRaw, io: BenchIO.IO, data: BW.Bytes, initialSubmitted: nat,
    readErr: int, initialWriteErr: int, initialBuffered: bool,
    ghost ordinal: nat, ghost done: bool, ghost preIn: BW.Bytes, ghost preOut: BW.Bytes,
    ghost records: seq<Spec.Record>, ghost ins: seq<BW.Bytes>, ghost dc: seq<nat>,
    ghost initialWrites: seq<Spec.Write>, ghost initialOuts: seq<BW.Bytes>, ghost initialCuts: seq<nat>
  ) returns (exit: int, ghost trace: CopyWitness)
    requires raw.mode == S.Copy && raw.error == S.None
    requires Spec.InputPartition(raw, io.trustedStreams(), preIn, io.stdin(), records, ins, data, dc)
    requires Spec.OutputPartition(raw, io.trustedStreams(), preOut, io.stdout(), records, dc,
                                  Render(raw, data), initialWrites, initialOuts, initialCuts)
    requires LoopProgress(raw, data, ordinal, initialSubmitted, records, dc, initialWrites, initialCuts,
                          readErr, initialWriteErr, initialBuffered, done)
    requires initialWriteErr == 0 ==> Spec.InputEnded(raw, records)
    modifies io.stdoutRegion, io.stderrRegion
    ensures Completed(raw, io.trustedStreams(), preIn, io.stdin(), preOut, io.stdout(),
                      old(io.stderr()), io.stderr(), exit, trace)
  {
    reveal LoopProgress();
    ghost var streams := io.trustedStreams();
    var submitted := initialSubmitted;
    var writeErr := initialWriteErr;
    var buffered := initialBuffered;
    ghost var writes, outs, oc := initialWrites, initialOuts, initialCuts;
    if writeErr == 0 && !Spec.Direct(raw) && submitted < |data| {
      assert |data| - submitted <= raw.obs;
      var error, observation := EmitSlice(raw, io, data, submitted, |data|, true, preOut, records, dc, writes, outs, oc);
      writeErr := error;
      buffered := |data| % raw.obs == 0;
      writes := writes + [observation];
      outs := outs + [io.stdout()];
      oc := oc + [|data|];
      submitted := |data|;
    }
    assert Spec.CopyRelation(raw, streams, preIn, io.stdin(), preOut, io.stdout(),
                             data, Render(raw, data), records, ins, dc, writes, outs, oc, readErr, writeErr);
    var readMessage := io.GetCLocaleErrnoText(readErr);
    var writeMessage := io.GetCLocaleErrnoText(writeErr);
    var diagnostics := Spec.Warnings(raw.warnings) +
    (if readErr == 0 then [] else Spec.ReadDiagnostic(readMessage)) +
    (if writeErr == 0 then [] else Spec.WriteDiagnostic(writeMessage, buffered));
    var stderr := io.WriteStderr(diagnostics);
    exit := if readErr == 0 && writeErr == 0 && C.ResultErrno(stderr) == 0 then 0 else 1;
    trace := CopyWitness(data, records, ins, dc, writes, outs, oc,
                         readErr, writeErr, C.WriteResultCommitted(stderr), C.ResultErrno(stderr));
    assert Completed(raw, streams, preIn, io.stdin(), preOut, io.stdout(), old(io.stderr()), io.stderr(), exit, trace) by {
      reveal Completed();
    }
  }

  method {:isolate_assertions} RunCore(raw: S.DdCmdRaw, io: BenchIO.IO) returns (exit: int)
    modifies if raw.mode == S.Copy && raw.error == S.None
             then {io.stdinRegion as object, io.stdoutRegion, io.stderrRegion}
             else {io.stdoutRegion as object, io.stderrRegion}
    ensures CoreSummary(raw, io, exit)
  {
    if raw.mode != S.Copy || raw.error != S.None {
      exit := RunEarly(raw, io);
      return;
    }
    reveal LoopProgress();
    ghost var preIn := io.stdin();
    ghost var preOut := io.stdout();
    ghost var streams := io.trustedStreams();
    var data: BW.Bytes := [];
    var submitted: nat := 0;
    var readErr, writeErr := 0, 0;
    var buffered := false;
    var done := false;
    ghost var records: seq<Spec.Record> := [];
    ghost var ins := [preIn];
    ghost var dc: seq<nat> := [0];
    ghost var writes: seq<Spec.Write> := [];
    ghost var outs := [preOut];
    ghost var oc: seq<nat> := [0];
    var ordinal: nat := 0;
    while !done && Spec.CountAllows(raw, ordinal)
      modifies io.stdinRegion, io.stdoutRegion
      invariant Spec.InputPartition(raw, streams, preIn, io.stdin(), records, ins, data, dc)
      invariant Spec.OutputPartition(raw, streams, preOut, io.stdout(), records, dc, Render(raw, data), writes, outs, oc)
      invariant LoopProgress(raw, data, ordinal, submitted, records, dc, writes, oc,
                             readErr, writeErr, buffered, done)
      decreases |io.stdin()| + (if done then 0 else 1)
    {
      ghost var previousIn := io.stdin();
      var block, padded, err := ReadAndAppend(raw, io, data, ordinal,
                                              preIn, preOut, records, ins, dc, writes, outs, oc);
      data := data + padded;
      records := records + [Spec.Record(block, err)];
      ins := ins + [io.stdin()];
      dc := dc + [|data|];
      ordinal := ordinal + 1;
      readErr := err;
      done := err != 0 || block == [];
      if Spec.Direct(raw) {
        if padded != [] {
          var error, observation := EmitSlice(raw, io, data, submitted, |data|, false, preOut, records, dc, writes, outs, oc);
          writeErr := error;
          buffered := false;
          writes := writes + [observation];
          outs := outs + [io.stdout()];
          oc := oc + [|data|];
          submitted := |data|;
        }
      } else {
        var next, error, nextWrites, nextOuts, nextCuts := FlushFull(raw, io, data, submitted, preOut, records, dc, writes, outs, oc);
        submitted, writeErr := next, error;
        writes, outs, oc := nextWrites, nextOuts, nextCuts;
        buffered := writeErr != 0;
      }
      if writeErr != 0 { done := true; }
      if !done { assert |io.stdin()| < |previousIn|; }
    }
    assert writeErr == 0 ==> Spec.InputEnded(raw, records);
    var code, trace := FinishCopy(raw, io, data, submitted, readErr, writeErr, buffered,
                                  ordinal, done, preIn, preOut, records, ins, dc, writes, outs, oc);
    exit := code;
    SummarizeCopy(raw, io, exit, trace);
  }
}
