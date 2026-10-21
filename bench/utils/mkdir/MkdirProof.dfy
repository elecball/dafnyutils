include "MkdirSpec.dfy"

module MkdirProof {
  import BenchIO
  import BW = BenchWorld
  import C = IOContract
  import Spec = MkdirSpec
  import Schema = MkdirSchema

  lemma ExtendCreations(
    paths: seq<string>, states: seq<BW.FileSystem>, successes: seq<bool>, errors: seq<int>,
    now: int, mask: bv32, observations: C.ValidFilesystemObservations,
    path: string, after: BW.FileSystem, ok: bool, err: int)
    requires Spec.CreationResults(paths, states, successes, errors, now, mask, observations)
    requires C.CreateDirectorySpec(states[|paths|], now, observations, mask, after,
                                   path, 511 as bv32, ok, err)
    ensures Spec.CreationResults(paths + [path], states + [after],
                                 successes + [ok], errors + [err], now, mask, observations)
  {
    hide C.CreateDirectorySpec();
    forall j | 0 <= j < |paths| + 1
      ensures C.CreateDirectorySpec((states + [after])[j], now, observations, mask,
                                    (states + [after])[j + 1], (paths + [path])[j], 511 as bv32,
                                    (successes + [ok])[j], (errors + [err])[j])
    {
      if j < |paths| {
        assert C.CreateDirectorySpec(states[j], now, observations, mask,
                                     states[j + 1], paths[j], 511 as bv32, successes[j], errors[j]);
      }
    }
  }

  lemma {:isolate_assertions} ExtendPieces(
    paths: seq<string>, verbose: bool, successes: seq<bool>, errors: seq<int>,
    output: BW.Bytes, diagnostics: BW.Bytes, outCuts: seq<nat>, errCuts: seq<nat>,
    path: string, ok: bool, err: int, addedOut: BW.Bytes, addedErr: BW.Bytes)
    requires Spec.OrderedPieces(paths, verbose, successes, errors,
                                output, diagnostics, outCuts, errCuts)
    requires addedOut == Spec.OutputPiece(verbose, path, ok)
    requires addedErr == Spec.ErrorPiece(path, ok, err)
    ensures Spec.OrderedPieces(paths + [path], verbose, successes + [ok], errors + [err],
                               output + addedOut, diagnostics + addedErr,
                               outCuts + [|output| + |addedOut|], errCuts + [|diagnostics| + |addedErr|])
  {
    // Formatting is proved separately; this lemma only preserves piece positions.
    hide Spec.OutputPiece();
    hide Spec.ErrorPiece();
    var nextOut := output + addedOut;
    var nextErr := diagnostics + addedErr;
    var nextOutCuts := outCuts + [|nextOut|];
    var nextErrCuts := errCuts + [|nextErr|];
    forall j {:trigger nextOutCuts[j]} {:trigger nextErrCuts[j]} | 0 <= j < |paths| + 1
      ensures nextOutCuts[j] <= nextOutCuts[j + 1] <= |nextOut|
      ensures nextErrCuts[j] <= nextErrCuts[j + 1] <= |nextErr|
      ensures nextOut[nextOutCuts[j]..nextOutCuts[j + 1]] ==
              Spec.OutputPiece(verbose, (paths + [path])[j], (successes + [ok])[j])
      ensures nextErr[nextErrCuts[j]..nextErrCuts[j + 1]] ==
              Spec.ErrorPiece((paths + [path])[j], (successes + [ok])[j], (errors + [err])[j])
    {
      if j < |paths| {
        assert outCuts[j] <= outCuts[j + 1] <= |output|;
        assert errCuts[j] <= errCuts[j + 1] <= |diagnostics|;
        assert output[outCuts[j]..outCuts[j + 1]] ==
               Spec.OutputPiece(verbose, paths[j], successes[j]);
        assert diagnostics[errCuts[j]..errCuts[j + 1]] ==
               Spec.ErrorPiece(paths[j], successes[j], errors[j]);
        assert nextOutCuts[j] == outCuts[j] && nextOutCuts[j + 1] == outCuts[j + 1];
        assert nextErrCuts[j] == errCuts[j] && nextErrCuts[j + 1] == errCuts[j + 1];
        assert nextOut[..|output|] == output && nextErr[..|diagnostics|] == diagnostics;
        assert nextOut[nextOutCuts[j]..nextOutCuts[j + 1]] == output[outCuts[j]..outCuts[j + 1]];
        assert nextErr[nextErrCuts[j]..nextErrCuts[j + 1]] == diagnostics[errCuts[j]..errCuts[j + 1]];
      } else {
        assert j == |paths|;
        assert nextOutCuts[j] == |output| && nextErrCuts[j] == |diagnostics|;
        assert nextOutCuts[j + 1] == |nextOut| && nextErrCuts[j + 1] == |nextErr|;
        assert nextOut[nextOutCuts[j]..nextOutCuts[j + 1]] == addedOut;
        assert nextErr[nextErrCuts[j]..nextErrCuts[j + 1]] == addedErr;
      }
    }
  }

  lemma AllSuccessSnoc(successes: seq<bool>, ok: bool)
    ensures (forall j | 0 <= j < |successes + [ok]| :: (successes + [ok])[j]) <==>
            ((forall j | 0 <= j < |successes| :: successes[j]) && ok)
  {
    if (forall j | 0 <= j < |successes| :: successes[j]) && ok {
      forall j | 0 <= j < |successes + [ok]|
        ensures (successes + [ok])[j]
      {
        if j < |successes| {
          assert successes[j];
        }
      }
    }
    if forall j | 0 <= j < |successes + [ok]| :: (successes + [ok])[j] {
      assert (successes + [ok])[|successes|] == ok;
      forall j | 0 <= j < |successes|
        ensures successes[j]
      {
        assert (successes + [ok])[j];
      }
    }
  }

  lemma AssembleRun(
    raw: Schema.MkdirCmdRaw, before: BW.FileSystem, after: BW.FileSystem,
    now: int, mask: bv32, observations: C.ValidFilesystemObservations,
    output: BW.Bytes, diagnostics: BW.Bytes, exit: int,
    states: seq<BW.FileSystem>, successes: seq<bool>, errors: seq<int>,
    outCuts: seq<nat>, errCuts: seq<nat>)
    requires Spec.CreationResults(Schema.Operands(raw), states, successes, errors,
                                  now, mask, observations)
    requires states[0] == before && states[|Schema.Operands(raw)|] == after
    requires Spec.OrderedPieces(Schema.Operands(raw), raw.verbose, successes, errors,
                                output, diagnostics, outCuts, errCuts)
    requires exit == (if forall j | 0 <= j < |Schema.Operands(raw)| :: successes[j] then 0 else 1)
    ensures Spec.RunRelation(raw, before, after, now, mask, observations,
                             output, diagnostics, exit)
  {
    hide C.CreateDirectorySpec();
    assert exists chosenStates: seq<BW.FileSystem>, chosenSuccesses: seq<bool>, chosenErrors: seq<int>,
        chosenOutCuts: seq<nat>, chosenErrCuts: seq<nat> ::
        chosenStates == states && chosenSuccesses == successes && chosenErrors == errors &&
        chosenOutCuts == outCuts && chosenErrCuts == errCuts &&
        Spec.CreationResults(Schema.Operands(raw), chosenStates, chosenSuccesses, chosenErrors,
                             now, mask, observations) &&
        chosenStates[0] == before && chosenStates[|Schema.Operands(raw)|] == after &&
        Spec.OrderedPieces(Schema.Operands(raw), raw.verbose, chosenSuccesses, chosenErrors,
                           output, diagnostics, chosenOutCuts, chosenErrCuts) &&
        exit == (if forall j | 0 <= j < |Schema.Operands(raw)| :: chosenSuccesses[j] then 0 else 1);
  }

  twostate lemma Complete(
    raw: Schema.MkdirCmdRaw, io: BenchIO.IO,
    output: BW.Bytes, diagnostics: BW.Bytes, creationExit: int, exit: int)
    requires Spec.RunRelation(raw, old(io.fs()), io.fs(), io.now(), io.umask(),
                              io.trustedFilesystem(), output, diagnostics, creationExit)
    requires Spec.StreamResults(old(io.stdout()), io.stdout(), old(io.stderr()), io.stderr(),
                                io.trustedStreams(), output, diagnostics, creationExit, exit)
    ensures Spec.Spec(raw, io, exit)
  {
    // Supply the concrete witnesses to the unchanged existential specification.
    assert exists chosenOutput: BW.Bytes, chosenDiagnostics: BW.Bytes, chosenExit: int ::
        chosenOutput == output && chosenDiagnostics == diagnostics && chosenExit == creationExit &&
        Spec.RunRelation(raw, old(io.fs()), io.fs(), io.now(), io.umask(),
                         io.trustedFilesystem(), chosenOutput, chosenDiagnostics, chosenExit) &&
        Spec.StreamResults(old(io.stdout()), io.stdout(), old(io.stderr()), io.stderr(),
                           io.trustedStreams(), chosenOutput, chosenDiagnostics, chosenExit, exit);
  }
}
