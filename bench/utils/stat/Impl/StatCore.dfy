include "../../../core/Utf8.dfy"
include "../Spec/StatSpec.dfy"
include "../../../core/World.dfy"
include "../../../core/IO.dfy"
include "../../../core/IOContract.dfy"
include "../Spec/StatSchema.dfy"

module StatCore {
  import StreamWorld = BenchWorld
  import StreamContract = IOContract

  import BenchWorld
  import BenchIO
  import Utf8 = Utf8Semantics
  import IOContract
  import Schema = StatSchema
  import Spec = StatSpec

  ghost predicate PrefixRenderingRelation(
    format: string,
    status: BenchWorld.FileStatus,
    end: nat,
    rendered: BenchWorld.Bytes,
    cuts: seq<nat>,
    pieces: seq<BenchWorld.Bytes>
  )
  {
    Spec.PrefixRenderingWitnessRelation(format, status, end, rendered, cuts, pieces)
  }

  lemma ConcatPiecesSnoc(pieces: seq<BenchWorld.Bytes>, piece: BenchWorld.Bytes)
    ensures Spec.ConcatPiecesSpec(pieces + [piece]) == Spec.ConcatPiecesSpec(pieces) + piece
    decreases |pieces|
  {
    if |pieces| > 0 {
      ConcatPiecesSnoc(pieces[1..], piece);
      assert pieces + [piece] == [pieces[0]] + (pieces[1..] + [piece]);
    }
  }

  method RenderFormat(
    format: string,
    status: BenchWorld.FileStatus
  ) returns (
      rendered: BenchWorld.Bytes,
      cuts: seq<nat>,
      pieces: seq<BenchWorld.Bytes>
    )
    ensures Spec.FormatRenderingRelation(format, status, rendered)
    ensures Spec.RenderingWitnessRelation(format, status, rendered, cuts, pieces)
  {
    var index: nat := 0;
    rendered := [];
    cuts := [0];
    pieces := [];

    while index < |format|
      invariant index <= |format|
      invariant PrefixRenderingRelation(format, status, index, rendered, cuts, pieces)
      decreases |format| - index
    {
      var nextIndex: nat;
      var piece: BenchWorld.Bytes;
      if format[index] != '%' {
        nextIndex := index + 1;
        piece := Utf8.EncodeChar(format[index]);
      } else if index + 1 == |format| {
        nextIndex := index + 1;
        piece := "%";
      } else {
        var directive := format[index + 1];
        nextIndex := index + 2;
        piece := Spec.DirectiveTextSpec(directive, status);
      }
      assert Spec.FormatStepRelation(format, status, index, nextIndex, piece);
      ConcatPiecesSnoc(pieces, piece);
      ghost var oldPieces := pieces;
      ghost var oldCuts := cuts;
      assert forall i: nat {:trigger oldCuts[i], oldCuts[i + 1]} | i < |oldPieces| ::
          Spec.FormatStepRelation(
            format, status, oldCuts[i], oldCuts[i + 1], oldPieces[i]
          ) by {
        forall i: nat {:trigger oldCuts[i], oldCuts[i + 1]} | i < |oldPieces|
          ensures Spec.FormatStepRelation(
                    format, status, oldCuts[i], oldCuts[i + 1], oldPieces[i]
                  )
        {
          assert oldCuts == cuts;
          assert oldPieces == pieces;
          assert Spec.FormatStepRelation(format, status, cuts[i], cuts[i + 1], pieces[i]);
        }
      }
      pieces := pieces + [piece];
      cuts := cuts + [nextIndex];
      rendered := rendered + piece;
      assert forall i: nat {:trigger cuts[i], cuts[i + 1]} | i < |pieces| ::
          Spec.FormatStepRelation(format, status, cuts[i], cuts[i + 1], pieces[i]) by {
        forall i: nat {:trigger cuts[i], cuts[i + 1]} | i < |pieces|
          ensures Spec.FormatStepRelation(format, status, cuts[i], cuts[i + 1], pieces[i])
        {
          if i < |oldPieces| {
            assert Spec.FormatStepRelation(
                format, status, oldCuts[i], oldCuts[i + 1], oldPieces[i]
              );
            assert cuts[i] == oldCuts[i];
            assert cuts[i + 1] == oldCuts[i + 1];
            assert pieces[i] == oldPieces[i];
          } else {
            assert i == |oldPieces|;
            assert cuts[i] == index;
            assert cuts[i + 1] == nextIndex;
            assert pieces[i] == piece;
          }
        }
      }
      index := nextIndex;
    }

    assert Spec.RenderingWitnessRelation(format, status, rendered, cuts, pieces);
    assert Spec.FormatRenderingRelation(format, status, rendered);
  }

  method RenderUsingTemplate(
    format: string,
    status: BenchWorld.FileStatus,
    templateText: BenchWorld.Bytes,
    cuts: seq<nat>,
    templatePieces: seq<BenchWorld.Bytes>
  ) returns (rendered: BenchWorld.Bytes)
    requires Spec.RenderingWitnessRelation(
               format, BenchWorld.DEFAULT_FILE_STATUS, templateText, cuts, templatePieces
             )
    ensures Spec.FormatRenderingRelation(format, status, rendered)
  {
    assert Spec.PrefixRenderingWitnessRelation(
        format, BenchWorld.DEFAULT_FILE_STATUS, |format|, templateText, cuts, templatePieces
      );
    rendered := "";
    ghost var pieces: seq<BenchWorld.Bytes> := [];
    var step: nat := 0;
    while step + 1 < |cuts|
      invariant step < |cuts|
      invariant |pieces| == step
      invariant rendered == Spec.ConcatPiecesSpec(pieces)
      invariant forall i: nat {:trigger cuts[i], cuts[i + 1]} | i < step ::
                  Spec.FormatStepRelation(format, status, cuts[i], cuts[i + 1], pieces[i])
      decreases |cuts| - step
    {
      var lo := cuts[step];
      var hi := cuts[step + 1];
      assert Spec.FormatStepRelation(
          format, BenchWorld.DEFAULT_FILE_STATUS, lo, hi, templatePieces[step]
        );
      var piece :=
        if format[lo] != '%' then Utf8.EncodeChar(format[lo])
        else if lo + 1 == hi then "%"
        else Spec.DirectiveTextSpec(format[lo + 1], status);
      assert Spec.FormatStepRelation(format, status, lo, hi, piece);
      ConcatPiecesSnoc(pieces, piece);
      ghost var oldPieces := pieces;
      pieces := pieces + [piece];
      rendered := rendered + piece;
      assert forall i: nat {:trigger cuts[i], cuts[i + 1]} | i < step + 1 ::
          Spec.FormatStepRelation(format, status, cuts[i], cuts[i + 1], pieces[i]) by {
        forall i: nat {:trigger cuts[i], cuts[i + 1]} | i < step + 1
          ensures Spec.FormatStepRelation(format, status, cuts[i], cuts[i + 1], pieces[i])
        {
          if i < step {
            assert pieces[i] == oldPieces[i];
          } else {
            assert i == step;
          }
        }
      }
      step := step + 1;
    }
    assert step + 1 == |cuts|;
    assert Spec.RenderingWitnessRelation(format, status, rendered, cuts, pieces);
  }

  lemma RenderingIgnoresRawMetadata(
    format: string,
    observed: BenchWorld.FileStatus,
    expected: BenchWorld.FileStatus,
    rendered: BenchWorld.Bytes
  )
    requires observed == expected
    requires Spec.FormatRenderingRelation(format, observed, rendered)
    ensures Spec.FormatRenderingRelation(format, expected, rendered)
  {
  }

  ghost predicate FileStepSummaryFields(
    cmd: Schema.StatCmd,
    index: nat,
    path: BenchWorld.Path,
    fs: BenchWorld.FileSystem,
    hadError: bool,
    out: BenchWorld.Bytes,
    errOut: BenchWorld.Bytes
  )
  {
    var observation := Spec.StatusResultSpec(cmd, fs, index, path);
    match observation
    case Ok(status) =>
      !hadError && errOut == "" &&
      exists rendered: BenchWorld.Bytes ::
        Spec.FormatRenderingRelation(cmd.format, status, rendered) &&
        out == rendered + "\n"
    case Err(error) =>
      hadError && out == "" &&
      errOut == Spec.ErrorMessageSpec(path, IOContract.IOErrorErrno(error))
  }

  ghost predicate RunFilesSummaryFields(
    cmd: Schema.StatCmd,
    files: seq<BenchWorld.Path>,
    fs: BenchWorld.FileSystem,
    hadError: bool,
    out: BenchWorld.Bytes,
    errOut: BenchWorld.Bytes
  )
    decreases |files|
  {
    if |files| == 0 then
      !hadError && out == "" && errOut == ""
    else
      exists prefixError: bool, prefixOut: BenchWorld.Bytes, prefixErrOut: BenchWorld.Bytes,
        stepError: bool, stepOut: BenchWorld.Bytes, stepErrOut: BenchWorld.Bytes
        {:trigger RunFilesSummaryFields(
          cmd, files[..|files| - 1], fs, prefixError, prefixOut, prefixErrOut
        ), FileStepSummaryFields(
          cmd, |files| - 1, files[|files| - 1], fs,
          stepError, stepOut, stepErrOut
        )} ::
        RunFilesSummaryFields(
          cmd, files[..|files| - 1], fs, prefixError, prefixOut, prefixErrOut
        ) &&
        FileStepSummaryFields(
          cmd, |files| - 1, files[|files| - 1], fs,
          stepError, stepOut, stepErrOut
        ) &&
        hadError == (prefixError || stepError) &&
        out == prefixOut + stepOut && errOut == prefixErrOut + stepErrOut
  }

  lemma {:induction false} RunFilesSummarySnoc(
    cmd: Schema.StatCmd, prefix: seq<BenchWorld.Path>, path: BenchWorld.Path,
    fs: BenchWorld.FileSystem,
    prefixError: bool, prefixOut: BenchWorld.Bytes, prefixErrOut: BenchWorld.Bytes,
    stepError: bool, stepOut: BenchWorld.Bytes, stepErrOut: BenchWorld.Bytes
  )
    requires RunFilesSummaryFields(cmd, prefix, fs, prefixError, prefixOut, prefixErrOut)
    requires FileStepSummaryFields(cmd, |prefix|, path, fs, stepError, stepOut, stepErrOut)
    ensures RunFilesSummaryFields(cmd, prefix + [path], fs,
                                  prefixError || stepError, prefixOut + stepOut, prefixErrOut + stepErrOut)
  {
    assert (prefix + [path])[..|prefix|] == prefix;
    assert (prefix + [path])[|prefix|] == path;
  }

  opaque twostate predicate PreparedSummary(raw: Schema.StatCmdRaw, io: BenchIO.IO, exit: int, plannedStdout: StreamWorld.Bytes, plannedStderr: StreamWorld.Bytes)
    reads io.statusObservationsRegion
  {
    var cmd := Schema.WithStatusObservations(
                 Schema.Command(raw), io.statusObservations(), old(io.statusCursor()), old(io.trustedNativeFailures())
               );
    io.statusCursor() == old(io.statusCursor()) +
    (if cmd.mode == Schema.ModeRun then |cmd.files| else 0) &&
    if cmd.mode == Schema.ModeHelp then
      plannedStdout == [] + Spec.HelpTextSpec() && plannedStderr == [] && exit == 0
    else if cmd.mode == Schema.ModeVersion then
      plannedStdout == [] + Spec.VersionTextSpec() && plannedStderr == [] && exit == 0
    else if cmd.mode == Schema.ModeMissingFormat then
      plannedStdout == [] &&
      plannedStderr == [] + Spec.MissingFormatMessageSpec() && exit == 1
    else if cmd.mode == Schema.ModeMissingOperand then
      plannedStdout == [] &&
      plannedStderr == [] + Spec.MissingOperandMessageSpec() && exit == 1
    else
      Spec.FormatValidSpec(cmd.format) &&
      exists hadError: bool, out: BenchWorld.Bytes, errOut: BenchWorld.Bytes ::
        RunFilesSummaryFields(cmd, cmd.files, old(io.fs()), hadError, out, errOut) &&
        plannedStdout == [] + out && plannedStderr == [] + errOut &&
        exit == (if hadError then 1 else 0)
  }

  twostate predicate CoreSummary(raw: Schema.StatCmdRaw, io: BenchIO.IO, exit: int)
    reads io.Footprint()
  {
    exists output: StreamWorld.Bytes, diagnostics: StreamWorld.Bytes, normalExit: int ::
      PreparedSummary(raw, io, normalExit, output, diagnostics) &&
      Spec.EmissionFields(old(io.stdout()), old(io.stderr()), io.stdout(), io.stderr(),
                          io.trustedStreams(), output, diagnostics, normalExit, exit)
  }

  method Prepare(raw: Schema.StatCmdRaw, io: BenchIO.IO) returns (exit: int, plannedStdout: StreamWorld.Bytes, plannedStderr: StreamWorld.Bytes)
    modifies io.statusObservationsRegion
    ensures PreparedSummary(raw, io, exit, plannedStdout, plannedStderr)
    decreases *
  {

    ghost var emissionBeforeOut: StreamWorld.Bytes := [];
    ghost var emissionBeforeErr: StreamWorld.Bytes := [];
    plannedStdout := [];
    plannedStderr := [];
    ghost var preFs := io.fs();
    ghost var preObservations := io.statusObservations();
    ghost var preFailures := io.trustedNativeFailures();
    ghost var preStatus := io.statusCursor();
    ghost var preStdout := (emissionBeforeOut + plannedStdout);
    ghost var preStderr := (emissionBeforeErr + plannedStderr);
    var cmd := Schema.Command(raw);
    ghost var summaryCmd := Schema.WithStatusObservations(
      cmd, preObservations, preStatus, preFailures
    );

    if cmd.mode == Schema.ModeHelp {
      plannedStdout := plannedStdout + (Spec.HelpTextSpec());
      exit := 0;
      assert PreparedSummary(raw, io, exit, plannedStdout, plannedStderr) by { hide *; reveal PreparedSummary(), Schema.WithStatusObservations(), Schema.Command(); }
      return;
    }
    if cmd.mode == Schema.ModeVersion {
      plannedStdout := plannedStdout + (Spec.VersionTextSpec());
      exit := 0;
      assert PreparedSummary(raw, io, exit, plannedStdout, plannedStderr) by { hide *; reveal PreparedSummary(), Schema.WithStatusObservations(), Schema.Command(); }
      return;
    }
    if cmd.mode == Schema.ModeMissingFormat {
      plannedStderr := plannedStderr + (Spec.MissingFormatMessageSpec());
      exit := 1;
      assert PreparedSummary(raw, io, exit, plannedStdout, plannedStderr) by { hide *; reveal PreparedSummary(), Schema.WithStatusObservations(), Schema.Command(); }
      return;
    }
    if cmd.mode == Schema.ModeMissingOperand {
      plannedStderr := plannedStderr + (Spec.MissingOperandMessageSpec());
      exit := 1;
      assert PreparedSummary(raw, io, exit, plannedStdout, plannedStderr) by { hide *; reveal PreparedSummary(), Schema.WithStatusObservations(), Schema.Command(); }
      return;
    }

    var templateText, validCuts, templatePieces := RenderFormat(
      cmd.format, BenchWorld.DEFAULT_FILE_STATUS
    );
    assert Spec.FormatValidSpec(cmd.format);

    var output: BenchWorld.Bytes := "";
    var errors: BenchWorld.Bytes := "";
    var hadError := false;
    var index := 0;
    while index < |cmd.files|
      invariant 0 <= index <= |cmd.files|
      invariant (emissionBeforeOut + plannedStdout) == preStdout && (emissionBeforeErr + plannedStderr) == preStderr
      invariant io.statusCursor() == preStatus + index
      invariant RunFilesSummaryFields(
                  summaryCmd, cmd.files[..index], preFs,
                  hadError, output, errors
                )
      decreases |cmd.files| - index
    {
      var path := cmd.files[index];
      ghost var statusIndex := index;
      ghost var beforeStatus := io.statusCursor();
      var getFileStatusResult := io.GetFileStatus(path, cmd.followSymlink);
      assert io.statusCursor() == beforeStatus + 1 by {
        hide *;
        reveal IOContract.GetFileStatusSpec();
      }
      var ok := getFileStatusResult.Ok?;
      var status := IOContract.ResultValue(getFileStatusResult, BenchWorld.DEFAULT_FILE_STATUS);
      var errno := IOContract.ResultErrno(getFileStatusResult);
      ghost var expected := Spec.StatusResultSpec(summaryCmd, preFs, statusIndex, path);
      assert expected.Ok? <==> ok by {
        hide *;
        reveal IOContract.GetFileStatusSpec(), IOContract.ObservedNativeFileStatusContractFields();
        reveal Spec.StatusResultSpec(), Schema.WithStatusObservations();
      }
      assert ok ==> expected.v == status by {
        hide *;
        reveal IOContract.GetFileStatusSpec(), IOContract.ObservedNativeFileStatusContractFields();
        reveal Spec.StatusResultSpec(), Schema.WithStatusObservations();
      }
      assert !ok ==> IOContract.IOErrorErrno(expected.e) == errno by {
        hide *;
        reveal IOContract.GetFileStatusSpec(), IOContract.ObservedNativeFileStatusContractFields();
        reveal Spec.StatusResultSpec(), Schema.WithStatusObservations();
      }
      var stepError := false;
      var stepOut: BenchWorld.Bytes := "";
      var stepErrOut: BenchWorld.Bytes := "";
      if ok {
        var text := RenderUsingTemplate(
          cmd.format, status, templateText, validCuts, templatePieces
        );
        stepOut := text + "\n";
        assert FileStepSummaryFields(
            summaryCmd, statusIndex, path, preFs,
            stepError, stepOut, stepErrOut
          ) by {
          hide *;
          reveal FileStepSummaryFields(), Spec.ErrorMessageSpec(), Spec.ErrnoTextSpec();
          reveal Schema.WithStatusObservations();
          reveal IOContract.GetCLocaleErrnoTextSpec();
        }
      } else {
        stepError := true;
        var reason := io.GetCLocaleErrnoText(errno);
        stepErrOut := Spec.ErrorMessageWithReasonSpec(path, reason);
        assert FileStepSummaryFields(
            summaryCmd, statusIndex, path, preFs,
            stepError, stepOut, stepErrOut
          ) by {
          hide *;
          reveal FileStepSummaryFields(), Spec.ErrorMessageSpec(), Spec.ErrnoTextSpec();
          reveal Schema.WithStatusObservations();
          reveal IOContract.GetCLocaleErrnoTextSpec();
        }
      }
      ghost var prefixError := hadError;
      ghost var prefixOut := output;
      ghost var prefixErrOut := errors;
      ghost var prefixFiles := cmd.files[..index];
      hadError := hadError || stepError;
      output := output + stepOut;
      errors := errors + stepErrOut;
      index := index + 1;
      assert cmd.files[..index] == prefixFiles + [path] by { hide *; }
      RunFilesSummarySnoc(summaryCmd, prefixFiles, path, preFs,
                          prefixError, prefixOut, prefixErrOut, stepError, stepOut, stepErrOut);
    }

    assert cmd.files[..|cmd.files|] == cmd.files;
    assert RunFilesSummaryFields(
        summaryCmd, cmd.files, preFs, hadError, output, errors
      );
    plannedStdout := plannedStdout + (output);
    assert (emissionBeforeOut + plannedStdout) == preStdout + output by { hide *; }
    assert (emissionBeforeErr + plannedStderr) == preStderr;
    plannedStderr := plannedStderr + (errors);
    assert (emissionBeforeOut + plannedStdout) == preStdout + output by { hide *; }
    assert (emissionBeforeErr + plannedStderr) == preStderr + errors by { hide *; }
    exit := if hadError then 1 else 0;
    assert exists finalHadError: bool,
        finalOut: BenchWorld.Bytes,
        finalErrOut: BenchWorld.Bytes
        {:trigger RunFilesSummaryFields(
          summaryCmd, cmd.files, preFs, finalHadError, finalOut, finalErrOut
        )} ::
        RunFilesSummaryFields(
          summaryCmd, cmd.files, preFs, finalHadError, finalOut, finalErrOut
        ) &&
        (emissionBeforeOut + plannedStdout) == preStdout + finalOut &&
        (emissionBeforeErr + plannedStderr) == preStderr + finalErrOut &&
        exit == (if finalHadError then 1 else 0);
    assert PreparedSummary(raw, io, exit, emissionBeforeOut + plannedStdout, emissionBeforeErr + plannedStderr) by {
      hide *;
      reveal PreparedSummary(), Schema.WithStatusObservations(), Schema.Command();
    }
  }


  method Flush(output: StreamWorld.Bytes, diagnostics: StreamWorld.Bytes,
               normalExit: int, io: BenchIO.IO) returns (exit: int)
    modifies io.stdoutRegion, io.stderrRegion
    ensures Spec.EmissionFields(old(io.stdout()), old(io.stderr()), io.stdout(), io.stderr(),
                                io.trustedStreams(), output, diagnostics, normalExit, exit)
  {
    var committed: nat := 0;
    var outErr := 0;
    if |output| != 0 {
      var result := io.WriteStdout(output);
      committed := StreamContract.WriteResultCommitted(result);
      outErr := StreamContract.ResultErrno(result);
    }
    var finalDiagnostics := diagnostics;
    if outErr != 0 {
      var reason := io.GetCLocaleErrnoText(outErr);
      finalDiagnostics := diagnostics + Spec.WriteErrorText(reason);
    }
    assert finalDiagnostics == diagnostics + (if outErr == 0 then []
                                              else Spec.WriteErrorText(StreamContract.CLocaleErrnoTextResult(outErr)));
    var errCommitted: nat := 0;
    var errErr := 0;
    if |finalDiagnostics| != 0 {
      var result := io.WriteStderr(finalDiagnostics);
      errCommitted := StreamContract.WriteResultCommitted(result);
      errErr := StreamContract.ResultErrno(result);
      assert StreamContract.WriteStderrSpec(old(io.stderr()), io.trustedStreams(), io.stderr(),
                                            finalDiagnostics, errCommitted, errErr);
    }
    exit := if outErr != 0 || errErr != 0 then 1 else normalExit;
    assert Spec.EmissionOutcomeFields(old(io.stdout()), old(io.stderr()), io.stdout(), io.stderr(),
                                      io.trustedStreams(), output, diagnostics, normalExit, exit, committed, outErr, errCommitted, errErr);
  }

  method RunCore(raw: Schema.StatCmdRaw, io: BenchIO.IO) returns (exit: int)
    modifies io.statusObservationsRegion, io.stdoutRegion, io.stderrRegion
    ensures CoreSummary(raw, io, exit)
    decreases *
  {
    var normalExit, output, diagnostics := Prepare(raw, io);
    exit := Flush(output, diagnostics, normalExit, io);
  }
}
