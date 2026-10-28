include "../../../core/Utf8.dfy"
include "../Spec/MkdirSpec.dfy"
include "../Proof/MkdirProof.dfy"

module MkdirCore {
  import BenchIO
  import BW = BenchWorld
  import C = IOContract
  import Schema = MkdirSchema
  import Spec = MkdirSpec
  import Proof = MkdirProof
  import Utf8 = Utf8Semantics

  method FormatResult(path: string, verbose: bool, ok: bool, err: int, io: BenchIO.IO)
    returns (output: BW.Bytes, diagnostic: BW.Bytes)
    ensures output == Spec.OutputPiece(verbose, path, ok)
    ensures diagnostic == Spec.ErrorPiece(path, ok, err)
  {
    output := [];
    diagnostic := [];
    if ok {
      if verbose {
        var quoted := io.QuoteafPath(path);
        output := Spec.AnnouncementText(quoted);
      }
    } else {
      var quoted := io.QuoteArgument(Utf8.Encode(path));
      var reason := io.GetCLocaleErrnoText(err);
      diagnostic := Spec.DiagnosticText(quoted, reason);
    }
  }

  method Flush(output: BW.Bytes, diagnostics: BW.Bytes, creationExit: int, io: BenchIO.IO)
    returns (exit: int)
    modifies io.stdoutRegion, io.stderrRegion
    ensures Spec.StreamResults(old(io.stdout()), io.stdout(), old(io.stderr()), io.stderr(),
                               io.trustedStreams(), output, diagnostics, creationExit, exit)
  {
    ghost var observations := io.trustedStreams();
    ghost var beforeOut := io.stdout();
    ghost var beforeErr := io.stderr();
    var outResult := io.WriteStdout(output);
    var outErr := C.ResultErrno(outResult);
    ghost var outObservation := observations(BW.StreamWriteStdout(beforeOut, output));
    assert outObservation.StreamWriteResult? && outObservation.err == outErr;
    var finalDiagnostic := diagnostics;
    if outErr != 0 {
      var reason := io.GetCLocaleErrnoText(outErr);
      finalDiagnostic := diagnostics + Spec.WriteErrorText(reason);
    }
    assert finalDiagnostic == diagnostics + (if outObservation.err == 0 then []
                                             else Spec.WriteErrorText(C.CLocaleErrnoTextResult(outObservation.err)));
    var errResult := io.WriteStderr(finalDiagnostic);
    ghost var errObservation := observations(BW.StreamWriteStderr(beforeErr, finalDiagnostic));
    assert errObservation.StreamWriteResult? && errObservation.err == C.ResultErrno(errResult);
    exit := if creationExit == 0 && outErr == 0 && C.ResultErrno(errResult) == 0 then 0 else 1;
  }

  method {:isolate_assertions} RunCore(raw: Schema.MkdirCmdRaw, io: BenchIO.IO) returns (exit: int)
    modifies io.fsRegion, io.stdoutRegion, io.stderrRegion
    ensures Spec.Spec(raw, io, exit)
  {
    // Use the unchanged native contract as a fact; this proof needs no expansion
    // of its complete inode model to retain each call's filesystem observation.
    hide C.CreateDirectorySpec();
    // Preserve already-proved formatting equations without expanding native quoting.
    hide Spec.OutputPiece();
    hide Spec.ErrorPiece();
    var paths := Schema.Operands(raw);
    var output: BW.Bytes := [];
    var diagnostics: BW.Bytes := [];
    ghost var states := [io.fs()];
    ghost var successes: seq<bool> := [];
    ghost var errors: seq<int> := [];
    ghost var outCuts: seq<nat> := [0];
    ghost var errCuts: seq<nat> := [0];
    var i := 0;
    exit := 0;
    while i < |paths|
      modifies io.fsRegion
      invariant 0 <= i <= |paths|
      invariant |states| == i + 1 && states[0] == old(io.fs()) && states[i] == io.fs()
      invariant |successes| == i && |errors| == i
      invariant Spec.CreationResults(paths[..i], states, successes, errors, io.now(), io.umask(), io.trustedFilesystem())
      invariant Spec.OrderedPieces(paths[..i], raw.verbose, successes, errors, output, diagnostics, outCuts, errCuts)
      invariant exit == (if forall j | 0 <= j < i :: successes[j] then 0 else 1)
      decreases |paths| - i
    {
      var result := io.CreateDirectory(paths[i], 511 as bv32);
      var ok := result.Ok?;
      var err := C.ResultErrno(result);
      var addedOut, addedErr := FormatResult(paths[i], raw.verbose, ok, err, io);
      ghost var nextStates := states + [io.fs()];
      ghost var nextSuccesses := successes + [ok];
      ghost var nextErrors := errors + [err];
      ghost var nextOutCuts := outCuts + [|output| + |addedOut|];
      ghost var nextErrCuts := errCuts + [|diagnostics| + |addedErr|];
      Proof.ExtendCreations(paths[..i], states, successes, errors,
                            io.now(), io.umask(), io.trustedFilesystem(), paths[i], io.fs(), ok, err);
      Proof.ExtendPieces(paths[..i], raw.verbose, successes, errors, output, diagnostics,
                         outCuts, errCuts, paths[i], ok, err, addedOut, addedErr);
      Proof.AllSuccessSnoc(successes, ok);
      states, successes, errors, outCuts, errCuts :=
        nextStates, nextSuccesses, nextErrors, nextOutCuts, nextErrCuts;
      output := output + addedOut;
      diagnostics := diagnostics + addedErr;
      if !ok {
        exit := 1;
      }
      i := i + 1;
    }
    assert paths[..i] == paths;
    assert Spec.CreationResults(paths, states, successes, errors,
                                io.now(), io.umask(), io.trustedFilesystem());
    assert Spec.OrderedPieces(paths, raw.verbose, successes, errors,
                              output, diagnostics, outCuts, errCuts);
    // The loop already established every component; aggregate their proved facts.
    hide *;
    Proof.AssembleRun(raw, old(io.fs()), io.fs(), io.now(), io.umask(), io.trustedFilesystem(),
                      output, diagnostics, exit, states, successes, errors, outCuts, errCuts);
    ghost var creationExit := exit;
    exit := Flush(output, diagnostics, exit, io);
    // AssembleRun and Flush have proved both complete component relations;
    // Complete separately proves their conjunction implies the principal Spec.
    hide *;
    assert Spec.RunRelation(raw, old(io.fs()), io.fs(), io.now(), io.umask(),
                            io.trustedFilesystem(), output, diagnostics, creationExit);
    Proof.Complete(raw, io, output, diagnostics, creationExit, exit);
  }
}
