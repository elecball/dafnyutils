include "RmdirTextCore.dfy"
include "RmdirSpec.dfy"
include "RmdirProof.dfy"
include "RmdirPathCore.dfy"

module RmdirCore {
  import Text = RmdirTextCore
  import BenchIO
  import opened BenchWorld
  import C = IOContract
  import Errno = Errnos
  import S = RmdirSchema
  import Spec = RmdirSpec
  import Proof = RmdirProof
  import PathCore = RmdirPathCore

  method Parent(path: string) returns (available: bool, parent: string)
    ensures available <==> Spec.HasParent(path)
    ensures available ==> Spec.ParentRelation(path, parent) && |parent| < |path|
  {
    var trimmed := PathCore.TrimTrailingSlashes(path);
    var slash := PathCore.LastSlashIndex(trimmed, |trimmed|);
    Proof.ParentAvailability(path, trimmed, slash);
    if trimmed == "/" || slash < 0 {
      return false, "";
    }
    parent := if slash == 0 then "/" else "";
    if slash > 0 {
      parent := PathCore.TrimTrailingSlashes(trimmed[..slash]);
    }
    Proof.ParentValue(path, trimmed, slash, parent);
    available := true;
  }

  method ProbeNonempty(io: BenchIO.IO, path: string) returns (nonempty: bool)
    modifies io.dirHandlesRegion
    ensures io.dirHandles() == old(io.dirHandles())
    ensures Spec.NonemptyObservation(Spec.ObservationContextFor(io), io.fs(), path, nonempty)
  {
    ghost var context := Spec.ObservationContextFor(io);
    var linkResult := io.IsSymlink(path);
    if linkResult.Ok? && linkResult.v {
      nonempty := false;
      Proof.NonemptyWitness(context, io.fs(), path,
                            true, true, 0, map[], map[], 0, false, 0,
                            false, "", UnknownDirentKind, 0, false, 0, nonempty);
      return;
    }
    var openResult := io.OpenDir(path, false);
    ghost var openHandles := io.dirHandles();
    nonempty := false;
    if openResult.Ok? {
      var item := io.ReadDir(openResult.v);
      ghost var afterRead := io.dirHandles();
      nonempty := item.Ok? && item.v.DirectoryItem?;
      var closeResult := io.CloseDir(openResult.v);
      assert io.dirHandles() == context.handles;
      // Cleanup-close failure is observed; GNU uses the saved readdir result.
      Proof.NonemptyWitness(context, io.fs(), path,
                            linkResult.Ok?, C.ResultValue(linkResult, false), C.ResultErrno(linkResult),
                            openHandles, afterRead, openResult.v, true, 0,
                            item.Ok? && item.v.DirectoryItem?,
                            if item.Ok? && item.v.DirectoryItem? then item.v.name else "",
                            if item.Ok? && item.v.DirectoryItem? then item.v.kind else UnknownDirentKind,
                            C.ResultErrno(item), closeResult.Ok?, C.ResultErrno(closeResult), nonempty);
    } else {
      Proof.NonemptyWitness(context, io.fs(), path,
                            linkResult.Ok?, C.ResultValue(linkResult, false), C.ResultErrno(linkResult),
                            openHandles, openHandles, 0, false, C.ResultErrno(openResult),
                            false, "", UnknownDirentKind, 0, false, 0, nonempty);
    }
  }

  method IgnoreFailure(raw: S.RmdirCmdRaw, io: BenchIO.IO,
                       path: string, err: int) returns (ignored: bool)
    modifies io.dirHandlesRegion
    ensures io.dirHandles() == old(io.dirHandles())
    ensures Spec.IgnoredFailure(Spec.ObservationContextFor(io), raw, io.fs(), path, err, ignored)
  {
    ignored := false;
    if raw.ignoreNonempty {
      if Spec.KnownNonempty(err) {
        ignored := true;
      } else if Spec.MayBeNonempty(err) {
        ignored := ProbeNonempty(io, path);
      }
    }
  }

  method DiagnosticPath(io: BenchIO.IO, path: string, parent: bool, err: int)
    returns (display: string, custom: bool)
    ensures Spec.FailureDisplay(Spec.ObservationContextFor(io), io.fs(), path, parent, err, display, custom)
  {
    hide Spec.FailureDisplay();
    ghost var context := Spec.ObservationContextFor(io);
    ghost var statOk, statDirectory := false, false;
    ghost var statErr := 0;
    ghost var observedTrimmed := path;
    ghost var linkOk, symbolicLink := false, false;
    ghost var linkErr := 0;
    display, custom := path, false;
    if !parent && err == Errno.ENOTDIR && C.HasTrailingSlash(path) {
      var directory := io.IsDirectory(path, true);
      statOk, statDirectory, statErr := directory.Ok?, C.ResultValue(directory, false), C.ResultErrno(directory);
      assert C.IsDirectorySpec(io.fs(), context.failures, path, true,
                               directory.Ok?, C.ResultValue(directory, false), C.ResultErrno(directory));
      if (!directory.Ok? && C.ResultErrno(directory) != Errno.ENOTDIR) ||
         (directory.Ok? && directory.v) {
        var stripped := PathCore.TrimTrailingSlashes(path);
        Proof.TrimmedRelation(path, stripped);
        var link := io.IsSymlink(stripped);
        observedTrimmed := stripped;
        linkOk, symbolicLink, linkErr := link.Ok?, C.ResultValue(link, false), C.ResultErrno(link);
        assert C.IsSymlinkSpec(io.fs(), context.failures, stripped,
                               link.Ok?, C.ResultValue(link, false), C.ResultErrno(link));
        custom := link.Ok? && link.v;
        display := if custom then path else stripped;
      }
    }
    Proof.FailureDisplayWitness(context, io.fs(), path, parent, err, display, custom,
                                statOk, statDirectory, statErr, observedTrimmed, linkOk, symbolicLink, linkErr);
  }

  method {:isolate_assertions} Attempt(raw: S.RmdirCmdRaw, io: BenchIO.IO, path: string, parent: bool)
    returns (removed: bool, accepted: bool, output: Bytes, diagnostic: Bytes,
             ghost record: Spec.Removal)
    modifies io.fsRegion, io.dirHandlesRegion
    ensures io.dirHandles() == old(io.dirHandles())
    ensures Spec.RemovalRelation(Spec.ObservationContextFor(io), raw, io.now(), io.trustedFilesystem(), record)
    ensures record.path == path && record.parent == parent
    ensures record.before == old(io.fs()) && record.after == io.fs()
    ensures removed <==> record.err == 0
    ensures accepted <==> record.err == 0 || record.ignored
    ensures output == Spec.OutputChunk(raw, record)
    ensures diagnostic == Spec.ErrorChunk(record)
  {
    hide C.RemoveDirectorySpec();
    hide Spec.IgnoredFailure();
    hide Spec.FailureDisplay();
    ghost var before := io.fs();
    output, diagnostic := [], [];
    if raw.verbose {
      var quoted := io.QuoteafPath(path);
      output := Spec.AttemptText(quoted);
    }
    var result := io.RemoveDirectory(path);
    removed := result.Ok?;
    var err := C.ResultErrno(result);
    assert C.RemoveDirectorySpec(before, io.now(), io.trustedFilesystem(), io.fs(), path, removed, err) by {
      hide *;
    }
    assert removed <==> err == 0 by {
      hide *;
      Proof.RemovalFacts(before, io.fs(), path, io.now(), io.trustedFilesystem(), removed, err);
    }
    var ignored, custom, display := false, false, path;
    if !removed {
      ignored := IgnoreFailure(raw, io, path, err);
      if !ignored {
        display, custom := DiagnosticPath(io, path, parent, err);
        var quoted := io.QuoteafPath(display);
        var reason := io.GetCLocaleErrnoText(err);
        diagnostic := Text.FailureText(parent, err, custom, quoted, reason);
      }
    }
    accepted := removed || ignored;
    record := Spec.Removal(path, parent, before, io.fs(), err, ignored, display, custom);
    assert Spec.RemovalRelation(Spec.ObservationContextFor(io), raw, io.now(), io.trustedFilesystem(), record) by {
      hide *;
      Proof.RemovalWitness(Spec.ObservationContextFor(io), raw, io.now(), io.trustedFilesystem(), record);
    }
  }

  method RemoveOperand(raw: S.RmdirCmdRaw, io: BenchIO.IO, path: string)
    returns (good: bool, out: Bytes, error: Bytes)
    modifies io.fsRegion, io.dirHandlesRegion
    ensures io.dirHandles() == old(io.dirHandles())
    ensures Spec.ChainEffect(Spec.ObservationContextFor(io), raw, path, io.now(), io.trustedFilesystem(),
                             old(io.fs()), io.fs(), out, error, good)
  {
    hide *;
    reveal Spec.ObservationContextFor(), Spec.ChainPrefix();
    reveal Spec.BytePartition();
    ghost var before := io.fs();
    ghost var records: seq<Spec.Removal> := [];
    ghost var outCuts: seq<nat> := [0];
    ghost var errCuts: seq<nat> := [0];
    ghost var outputs: seq<Bytes> := [];
    ghost var errors: seq<Bytes> := [];
    out, error := [], [];
    var current := path;
    var parent := false;
    while true
      invariant io.dirHandles() == old(io.dirHandles())
      invariant Spec.ChainPrefix(Spec.ObservationContextFor(io), raw, path, io.now(), io.trustedFilesystem(), records)
      invariant |records| == 0 ==> current == path && !parent && io.fs() == before
      invariant |records| > 0 ==>
                  (parent && records[0].before == before &&
                   records[|records| - 1].after == io.fs() && records[|records| - 1].err == 0 &&
                   raw.parents && Spec.ParentRelation(records[|records| - 1].path, current))
      invariant outputs == seq(|records|, i requires 0 <= i < |records| => Spec.OutputChunk(raw, records[i]))
      invariant errors == seq(|records|, i requires 0 <= i < |records| => Spec.ErrorChunk(records[i]))
      invariant Spec.BytePartition(outputs, out, outCuts)
      invariant Spec.BytePartition(errors, error, errCuts)
      decreases |current|
    {
      var removed, accepted, addedOut, addedErr, record := Attempt(raw, io, current, parent);
      Proof.AppendChain(Spec.ObservationContextFor(io), raw, path, io.now(), io.trustedFilesystem(), records, record);
      Proof.AppendPartition(outputs, out, outCuts, Spec.OutputChunk(raw, record));
      Proof.AppendPartition(errors, error, errCuts, Spec.ErrorChunk(record));
      records := records + [record];
      outputs := outputs + [Spec.OutputChunk(raw, record)];
      errors := errors + [Spec.ErrorChunk(record)];
      out := out + addedOut;
      error := error + addedErr;
      outCuts := outCuts + [|out|];
      errCuts := errCuts + [|error|];
      assert outputs == seq(|records|, i requires 0 <= i < |records| => Spec.OutputChunk(raw, records[i]));
      assert errors == seq(|records|, i requires 0 <= i < |records| => Spec.ErrorChunk(records[i]));
      var available, next := Parent(current);
      if !removed || !raw.parents || !available {
        good := accepted;
        assert good == (forall i :: 0 <= i < |records| ==> records[i].err == 0 || records[i].ignored) by {
          hide *;
          reveal Spec.ChainPrefix();
          assert records[|records| - 1] == record;
          if good {
            forall j | 0 <= j < |records|
              ensures records[j].err == 0 || records[j].ignored
            {
              if j < |records| - 1 {
                assert records[j + 1].parent;
              }
            }
          }
          if forall j :: 0 <= j < |records| ==> records[j].err == 0 || records[j].ignored {
            assert records[|records| - 1].err == 0 || records[|records| - 1].ignored;
          }
        }
        assert Spec.ChainWitness(Spec.ObservationContextFor(io), raw, path, io.now(), io.trustedFilesystem(),
                                 before, io.fs(), out, error, good, records, outCuts, errCuts) by {
          hide *;
          reveal Spec.ChainWitness();
        }
        Proof.ChainExists(Spec.ObservationContextFor(io), raw, path, io.now(), io.trustedFilesystem(),
                          before, io.fs(), out, error, good, records, outCuts, errCuts);
        return;
      }
      current := next;
      parent := true;
    }
  }

  method Flush(output: Bytes, diagnostics: Bytes, removalExit: int, io: BenchIO.IO)
    returns (exit: int)
    modifies io.stdoutRegion, io.stderrRegion
    ensures Spec.StreamResults(old(io.stdout()), io.stdout(), old(io.stderr()), io.stderr(),
                               io.trustedStreams(), output, diagnostics, removalExit, exit)
  {
    ghost var observations := io.trustedStreams();
    ghost var beforeOut, beforeErr := io.stdout(), io.stderr();
    var outResult := io.WriteStdout(output);
    var outErr := C.ResultErrno(outResult);
    ghost var outObservation := observations(StreamWriteStdout(beforeOut, output));
    assert outObservation.StreamWriteResult? && outObservation.err == outErr;
    var finalDiagnostic := diagnostics;
    if outErr != 0 {
      if |diagnostics| != 0 {
        // GNU error() flushes the preceding verbose attempt before diagnostics.
        // close_stream later reports that prior failure without an errno suffix.
        finalDiagnostic := diagnostics + Spec.PriorWriteErrorText();
      } else {
        var reason := io.GetCLocaleErrnoText(outErr);
        finalDiagnostic := diagnostics + Text.WriteErrorText(reason);
      }
    }
    assert finalDiagnostic == diagnostics + (if outObservation.err == 0 then []
                                             else if |diagnostics| != 0 then Spec.PriorWriteErrorText()
                                             else Spec.WriteErrorText(C.CLocaleErrnoTextResult(outObservation.err)));
    var errResult := io.WriteStderr(finalDiagnostic);
    ghost var errObservation := observations(StreamWriteStderr(beforeErr, finalDiagnostic));
    assert errObservation.StreamWriteResult? && errObservation.err == C.ResultErrno(errResult);
    exit := if removalExit == 0 && outErr == 0 && C.ResultErrno(errResult) == 0 then 0 else 1;
  }

  method {:isolate_assertions} RunCore(raw: S.RmdirCmdRaw, io: BenchIO.IO) returns (exit: int)
    modifies if raw.mode != S.ModeRun || |raw.operands| == 0
             then {io.stdoutRegion as object, io.stderrRegion}
             else {io.fsRegion, io.stdoutRegion, io.stderrRegion, io.dirHandlesRegion}
    ensures Spec.Spec(raw, io, exit)
  {
    hide *;
    reveal Spec.ObservationContextFor(), Spec.BatchWitness();
    reveal Spec.BytePartition();
    if raw.mode == S.ModeHelp {
      exit := Flush(Spec.HelpText(), [], 0, io);
      assert Spec.Spec(raw, io, exit) by { hide *; reveal Spec.Spec(); }
      return;
    }
    if raw.mode == S.ModeVersion {
      exit := Flush(Spec.VersionText(), [], 0, io);
      assert Spec.Spec(raw, io, exit) by { hide *; reveal Spec.Spec(); }
      return;
    }
    if |raw.operands| == 0 {
      exit := Flush([], Spec.MissingOperandText(), 1, io);
      assert Spec.Spec(raw, io, exit) by { hide *; reveal Spec.Spec(); }
      return;
    }
    ghost var before := io.fs();
    ghost var states: seq<FileSystem> := [before];
    ghost var outputs: seq<Bytes> := [];
    ghost var errors: seq<Bytes> := [];
    ghost var goods: seq<bool> := [];
    ghost var outCuts: seq<nat> := [0];
    ghost var errCuts: seq<nat> := [0];
    var out: Bytes := [];
    var error: Bytes := [];
    var allGood := true;
    var i := 0;
    while i < |raw.operands|
      modifies io.fsRegion, io.dirHandlesRegion
      invariant io.dirHandles() == old(io.dirHandles())
      invariant 0 <= i <= |raw.operands|
      invariant Spec.BatchWitness(Spec.ObservationContextFor(io), raw, raw.operands[..i], io.now(), io.trustedFilesystem(),
                                  before, io.fs(), out, error, allGood, states, outputs, errors, goods, outCuts, errCuts)
      decreases |raw.operands| - i
    {
      ghost var fsBefore := io.fs();
      var good, partOut, partErr := RemoveOperand(raw, io, raw.operands[i]);
      Proof.ExtendBatch(Spec.ObservationContextFor(io), raw, raw.operands[..i], io.now(), io.trustedFilesystem(),
                        before, fsBefore, out, error, allGood, states, outputs, errors, goods, outCuts, errCuts,
                        raw.operands[i], io.fs(), partOut, partErr, good);
      states := states + [io.fs()];
      outputs := outputs + [partOut];
      errors := errors + [partErr];
      goods := goods + [good];
      out := out + partOut;
      error := error + partErr;
      outCuts := outCuts + [|out|];
      errCuts := errCuts + [|error|];
      allGood := allGood && good;
      i := i + 1;
    }
    Proof.BatchExists(Spec.ObservationContextFor(io), raw, io.now(), io.trustedFilesystem(), before, io.fs(), out, error,
                      allGood, states, outputs, errors, goods, outCuts, errCuts);
    exit := Flush(out, error, if allGood then 0 else 1, io);
    Proof.Complete(raw, io, out, error, allGood, exit);
  }
}
