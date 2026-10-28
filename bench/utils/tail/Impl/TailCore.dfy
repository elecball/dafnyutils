include "../Spec/TailSpec.dfy"
include "../../../core/World.dfy"
include "../../../core/IO.dfy"
include "../../../core/IOContract.dfy"
include "../Spec/TailSchema.dfy"
include "TailRecordCore.dfy"

module TailCore {
  import StreamContract = IOContract

  import Result = Results
  import BenchIO
  import BenchWorld
  import IOContract
  import TailSchema
  import TailRecordCore
  import TailRecordSpec
  import Spec = TailSpec

  ghost function PrefixStdinCore(cmd: TailSchema.TailCmd, preStdin: BenchWorld.Bytes, i: nat, preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult): BenchWorld.Bytes
    requires i <= |cmd.inputs|
    decreases i
  {
    if i == 0 then
      preStdin
    else
      match cmd.inputs[i - 1]
      case Stdin(_) => IOContract.ObservedReadStdinRemainingFields(PrefixStdinCore(cmd, preStdin, i - 1, preStreams), preStreams)
      case File(_) => PrefixStdinCore(cmd, preStdin, i - 1, preStreams)
  }

  ghost function ReadResultCore(
    cmd: TailSchema.TailCmd,
    preFs: BenchWorld.FileSystem,
    preStdin: BenchWorld.Bytes,
    i: nat,
    preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult
  ): BenchWorld.IOResult<BenchWorld.Bytes>
    requires i < |cmd.inputs|
  {
    match cmd.inputs[i]
    case Stdin(_) => IOContract.ObservedReadStdinResultFields(PrefixStdinCore(cmd, preStdin, i, preStreams), preStreams)
    case File(path) => IOContract.ObservedReadFileResultFields(preFs, preStreams, path)
  }

  function DropFirstBytes(data: BenchWorld.Bytes, count: nat): BenchWorld.Bytes
  {
    if count == 0 then data else if |data| <= count then [] else data[count..]
  } by method {
    if count == 0 {
      return data;
    } else if |data| <= count {
      return [];
    } else {
      return data[count..];
    }
  }

  function TakeLastBytes(data: BenchWorld.Bytes, count: nat): BenchWorld.Bytes
  {
    if |data| <= count then data else data[|data| - count..]
  } by method {
    if |data| <= count {
      return data;
    } else {
      return data[|data| - count..];
    }
  }

  function RenderData(cmd: TailSchema.TailCmd, data: BenchWorld.Bytes): BenchWorld.Bytes
  {
    if cmd.selection.unit == TailSchema.CountBytes then
      if cmd.selection.fromStart then
        DropFirstBytes(data, if cmd.selection.amount == 0 then 0 else cmd.selection.amount - 1)
      else
        TakeLastBytes(data, cmd.selection.amount)
    else
      var delimiter := TailRecordSpec.RecordDelimiter(cmd.zeroTerminated);
      if cmd.selection.fromStart then
        TailRecordCore.DropFirstRecords(data, if cmd.selection.amount == 0 then 0 else cmd.selection.amount - 1, delimiter)
      else
        TailRecordCore.TakeLastRecords(data, cmd.selection.amount, delimiter)
  } by method {
    if cmd.selection.unit == TailSchema.CountBytes {
      if cmd.selection.fromStart {
        return DropFirstBytes(
            data,
            if cmd.selection.amount == 0 then 0 else cmd.selection.amount - 1
          );
      } else {
        return TakeLastBytes(data, cmd.selection.amount);
      }
    } else {
      var delimiter := TailRecordSpec.RecordDelimiter(cmd.zeroTerminated);
      if cmd.selection.fromStart {
        return TailRecordCore.DropFirstRecords(
            data,
            if cmd.selection.amount == 0 then 0 else cmd.selection.amount - 1,
            delimiter
          );
      } else {
        return TailRecordCore.TakeLastRecords(data, cmd.selection.amount, delimiter);
      }
    }
  }

  function OutputPiece(
    cmd: TailSchema.TailCmd,
    input: TailSchema.Input,
    result: BenchWorld.IOResult<BenchWorld.Bytes>,
                                printedHeaders: int
  ): BenchWorld.Bytes
  {
    match result
    case Ok(data) =>
      if Spec.SuppressZeroTrailingSelection(cmd) then
        []
      else
        Spec.HeaderForInput(cmd, input, printedHeaders) + RenderData(cmd, data)
    case Err(err) =>
      if (err.StreamFailure? || (err.ReadFailure? && err.readStage == BenchWorld.CloseFailed)) && !Spec.SuppressZeroTrailingSelection(cmd) then
        Spec.HeaderForInput(cmd, input, printedHeaders) + RenderData(cmd, err.partial)
      else if IOContract.IOErrorIsDirectory(err) then Spec.HeaderForInput(cmd, input, printedHeaders) else []
  } by method {
    match result
    case Ok(data) =>
      if Spec.SuppressZeroTrailingSelection(cmd) {
        return [];
      } else {
        return Spec.HeaderForInput(cmd, input, printedHeaders) + RenderData(cmd, data);
      }
    case Err(err) =>
      if (err.StreamFailure? || (err.ReadFailure? && err.readStage == BenchWorld.CloseFailed)) && !Spec.SuppressZeroTrailingSelection(cmd) {
        return Spec.HeaderForInput(cmd, input, printedHeaders) + RenderData(cmd, err.partial);
      } else if IOContract.IOErrorIsDirectory(err) {
        return Spec.HeaderForInput(cmd, input, printedHeaders);
      } else {
        return [];
      }
  }

  ghost function PrefixHeaderCountCore(
    cmd: TailSchema.TailCmd,
    preFs: BenchWorld.FileSystem,
    preStdin: BenchWorld.Bytes,
    i: nat,
    preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult
  ): nat
    requires i <= |cmd.inputs|
    decreases i
  {
    if i == 0 then
      0
    else
      PrefixHeaderCountCore(cmd, preFs, preStdin, i - 1, preStreams) +
      (if Spec.ResultHasHeader(cmd, ReadResultCore(cmd, preFs, preStdin, i - 1, preStreams)) then 1 else 0)
  }

  ghost function PrefixOutputCore(
    cmd: TailSchema.TailCmd,
    preFs: BenchWorld.FileSystem,
    preStdin: BenchWorld.Bytes,
    i: nat,
    preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult
  ): BenchWorld.Bytes
    requires i <= |cmd.inputs|
    decreases i
  {
    if i == 0 then
      []
    else
      PrefixOutputCore(cmd, preFs, preStdin, i - 1, preStreams) +
      OutputPiece(
        cmd,
        cmd.inputs[i - 1],
        ReadResultCore(cmd, preFs, preStdin, i - 1, preStreams),
        PrefixHeaderCountCore(cmd, preFs, preStdin, i - 1, preStreams)
      )
  }

  ghost function PrefixErrorOutputCore(
    cmd: TailSchema.TailCmd,
    preFs: BenchWorld.FileSystem,
    preStdin: BenchWorld.Bytes,
    i: nat,
    preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult
  ): BenchWorld.Bytes
    requires i <= |cmd.inputs|
    decreases i
  {
    if i == 0 then
      []
    else
      PrefixErrorOutputCore(cmd, preFs, preStdin, i - 1, preStreams) +
      Spec.ErrorPiece(cmd.inputs[i - 1], ReadResultCore(cmd, preFs, preStdin, i - 1, preStreams))
  }

  ghost function PrefixHadErrorCore(
    cmd: TailSchema.TailCmd,
    preFs: BenchWorld.FileSystem,
    preStdin: BenchWorld.Bytes,
    i: nat,
    preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult
  ): bool
    requires i <= |cmd.inputs|
    decreases i
  {
    if i == 0 then
      false
    else
      PrefixHadErrorCore(cmd, preFs, preStdin, i - 1, preStreams) ||
      Spec.HadErrorPiece(cmd.inputs[i - 1], ReadResultCore(cmd, preFs, preStdin, i - 1, preStreams))
  }

  ghost function RunOutputCore(
    cmd: TailSchema.TailCmd,
    preFs: BenchWorld.FileSystem,
    preStdin: BenchWorld.Bytes,
    preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult
  ): BenchWorld.Bytes
  {
    PrefixOutputCore(cmd, preFs, preStdin, |cmd.inputs|, preStreams)
  }

  twostate predicate PreparedSummary(raw: TailSchema.TailCmdRaw, io: BenchIO.IO, exit: int, plannedStdout: BenchWorld.Bytes, plannedStderr: BenchWorld.Bytes)
    reads io.stdinRegion
  {
    var cmd := Spec.Command(raw);
    if cmd.mode == TailSchema.ModeHelp then
      io.stdin() == old(io.stdin()) &&
      plannedStdout == old(io.stdout()) + Spec.HelpText() &&
      plannedStderr == old(io.stderr()) &&
      exit == 0
    else if cmd.mode == TailSchema.ModeVersion then
      io.stdin() == old(io.stdin()) &&
      plannedStdout == old(io.stdout()) + Spec.VersionText() &&
      plannedStderr == old(io.stderr()) &&
      exit == 0
    else if cmd.mode == TailSchema.ModeInvalidCount then
      io.stdin() == old(io.stdin()) &&
      plannedStdout == old(io.stdout()) &&
      plannedStderr == old(io.stderr()) + Spec.InvalidCountMessage(cmd.invalidCountUnit, cmd.invalidCountValue) &&
      exit == 1
    else if Spec.SuppressZeroTrailingSelection(cmd) then
      io.stdin() == old(io.stdin()) &&
      plannedStdout == old(io.stdout()) &&
      plannedStderr == old(io.stderr()) &&
      exit == 0
    else
      io.stdin() == PrefixStdinCore(cmd, old(io.stdin()), |cmd.inputs|, old(io.trustedStreams())) &&
      plannedStdout == old(io.stdout()) + RunOutputCore(cmd, old(io.fs()), old(io.stdin()), old(io.trustedStreams())) &&
      plannedStderr == old(io.stderr()) + PrefixErrorOutputCore(cmd, old(io.fs()), old(io.stdin()), |cmd.inputs|, old(io.trustedStreams())) &&
      exit == (if PrefixHadErrorCore(cmd, old(io.fs()), old(io.stdin()), |cmd.inputs|, old(io.trustedStreams())) then 1 else 0)
  }

  lemma PrefixStdinCoreStep(cmd: TailSchema.TailCmd, preStdin: BenchWorld.Bytes, i: nat, preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult)
    requires i < |cmd.inputs|
    ensures PrefixStdinCore(cmd, preStdin, i + 1, preStreams) ==
            match cmd.inputs[i]
            case Stdin(_) => IOContract.ObservedReadStdinRemainingFields(PrefixStdinCore(cmd, preStdin, i, preStreams), preStreams)
            case File(_) => PrefixStdinCore(cmd, preStdin, i, preStreams)
  {
  }

  lemma PrefixHeaderCountCoreStep(
    cmd: TailSchema.TailCmd,
    preFs: BenchWorld.FileSystem,
    preStdin: BenchWorld.Bytes,
    i: nat,
    preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult
  )
    requires i < |cmd.inputs|
    ensures PrefixHeaderCountCore(cmd, preFs, preStdin, i + 1, preStreams) ==
            PrefixHeaderCountCore(cmd, preFs, preStdin, i, preStreams) +
            (if Spec.ResultHasHeader(cmd, ReadResultCore(cmd, preFs, preStdin, i, preStreams)) then 1 else 0)
  {
  }

  lemma PrefixOutputCoreStep(
    cmd: TailSchema.TailCmd,
    preFs: BenchWorld.FileSystem,
    preStdin: BenchWorld.Bytes,
    i: nat,
    preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult
  )
    requires i < |cmd.inputs|
    ensures PrefixOutputCore(cmd, preFs, preStdin, i + 1, preStreams) ==
            PrefixOutputCore(cmd, preFs, preStdin, i, preStreams) +
            OutputPiece(
              cmd,
              cmd.inputs[i],
              ReadResultCore(cmd, preFs, preStdin, i, preStreams),
              PrefixHeaderCountCore(cmd, preFs, preStdin, i, preStreams)
            )
  {
  }

  lemma PrefixErrorOutputCoreStep(
    cmd: TailSchema.TailCmd,
    preFs: BenchWorld.FileSystem,
    preStdin: BenchWorld.Bytes,
    i: nat,
    preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult
  )
    requires i < |cmd.inputs|
    ensures PrefixErrorOutputCore(cmd, preFs, preStdin, i + 1, preStreams) ==
            PrefixErrorOutputCore(cmd, preFs, preStdin, i, preStreams) +
            Spec.ErrorPiece(cmd.inputs[i], ReadResultCore(cmd, preFs, preStdin, i, preStreams))
  {
  }

  lemma PrefixHadErrorCoreStep(
    cmd: TailSchema.TailCmd,
    preFs: BenchWorld.FileSystem,
    preStdin: BenchWorld.Bytes,
    i: nat,
    preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult
  )
    requires i < |cmd.inputs|
    ensures PrefixHadErrorCore(cmd, preFs, preStdin, i + 1, preStreams) ==
            (PrefixHadErrorCore(cmd, preFs, preStdin, i, preStreams) ||
             Spec.HadErrorPiece(cmd.inputs[i], ReadResultCore(cmd, preFs, preStdin, i, preStreams)))
  {
  }

  method GetHelpText() returns (out: BenchWorld.Bytes)
    ensures out == Spec.HelpText()
  {
    out := Spec.HelpText();
  }

  method GetVersionText() returns (out: BenchWorld.Bytes)
    ensures out == Spec.VersionText()
  {
    out := Spec.VersionText();
  }

  method {:isolate_assertions} Prepare(raw: TailSchema.TailCmdRaw, io: BenchIO.IO) returns (exit: int, plannedOut: BenchWorld.Bytes, plannedErr: BenchWorld.Bytes)
    modifies io.stdinRegion
    ensures PreparedSummary(raw, io, exit, old(io.stdout()) + plannedOut, old(io.stderr()) + plannedErr)
    decreases *
  {
    hide *;
    reveal PreparedSummary(), PrefixStdinCore(), PrefixOutputCore(), PrefixErrorOutputCore();
    reveal PrefixHadErrorCore(), PrefixHeaderCountCore(), RunOutputCore(), ReadResultCore();
    reveal Spec.SuppressZeroTrailingSelection();
    plannedOut := [];
    plannedErr := [];
    ghost var initialStdout := io.stdout();
    ghost var initialStderr := io.stderr();

    ghost var preFs := io.fs();
    ghost var preStreams := io.trustedStreams();
    ghost var preStdin := io.stdin();
    ghost var preStdout := (initialStdout + plannedOut);
    ghost var preStderr := (initialStderr + plannedErr);
    var cmd := Spec.Command(raw);

    if cmd.mode == TailSchema.ModeHelp {
      var help := GetHelpText();
      plannedOut := plannedOut + help;
      exit := 0;
      assert io.stdin() == preStdin;
      assert (initialStderr + plannedErr) == preStderr;
      assert (initialStdout + plannedOut) == preStdout + Spec.HelpText();
      return;
    }

    if cmd.mode == TailSchema.ModeVersion {
      var version := GetVersionText();
      plannedOut := plannedOut + version;
      exit := 0;
      assert io.stdin() == preStdin;
      assert (initialStderr + plannedErr) == preStderr;
      assert (initialStdout + plannedOut) == preStdout + Spec.VersionText();
      return;
    }

    if cmd.mode == TailSchema.ModeInvalidCount {
      var invalid := Spec.InvalidCountMessage(cmd.invalidCountUnit, cmd.invalidCountValue);
      plannedErr := plannedErr + invalid;
      exit := 1;
      assert io.stdin() == preStdin;
      assert (initialStdout + plannedOut) == preStdout;
      assert (initialStderr + plannedErr) == preStderr + Spec.InvalidCountMessage(cmd.invalidCountUnit, cmd.invalidCountValue);
      return;
    }

    var suppressZero := Spec.SuppressZeroTrailingSelection(cmd);
    if suppressZero {
      exit := 0;
      assert io.stdin() == preStdin;
      assert (initialStdout + plannedOut) == preStdout;
      assert (initialStderr + plannedErr) == preStderr;
      return;
    }

    var out: BenchWorld.Bytes := [];
    var err: BenchWorld.Bytes := [];
    var hadError := false;
    var headers := 0;

    var i := 0;
    while i < |cmd.inputs|
      invariant 0 <= i <= |cmd.inputs|
      invariant io.stdin() == PrefixStdinCore(cmd, preStdin, i, preStreams)
      invariant (initialStdout + plannedOut) == preStdout
      invariant (initialStderr + plannedErr) == preStderr
      invariant out == PrefixOutputCore(cmd, preFs, preStdin, i, old(io.trustedStreams()))
      invariant err == PrefixErrorOutputCore(cmd, preFs, preStdin, i, old(io.trustedStreams()))
      invariant hadError == PrefixHadErrorCore(cmd, preFs, preStdin, i, old(io.trustedStreams()))
      invariant headers == PrefixHeaderCountCore(cmd, preFs, preStdin, i, old(io.trustedStreams()))
      decreases |cmd.inputs| - i
    {
      var input := cmd.inputs[i];
      var readResult: BenchWorld.IOResult<BenchWorld.Bytes>;
      match input {
        case Stdin(_) =>
          ghost var beforeStdin := io.stdin();
          readResult := io.ReadStdin();
          PrefixStdinCoreStep(cmd, preStdin, i, preStreams);
          PrefixHeaderCountCoreStep(cmd, preFs, preStdin, i, old(io.trustedStreams()));
          PrefixOutputCoreStep(cmd, preFs, preStdin, i, old(io.trustedStreams()));
          PrefixErrorOutputCoreStep(cmd, preFs, preStdin, i, old(io.trustedStreams()));
          PrefixHadErrorCoreStep(cmd, preFs, preStdin, i, old(io.trustedStreams()));
          assert beforeStdin == PrefixStdinCore(cmd, preStdin, i, preStreams);
          assert readResult == IOContract.ObservedReadStdinResultFields(beforeStdin, preStreams);
        case File(path) =>
          readResult := io.ReadFile(path);
      }
      if input.File? {
        PrefixStdinCoreStep(cmd, preStdin, i, preStreams);
        PrefixHeaderCountCoreStep(cmd, preFs, preStdin, i, old(io.trustedStreams()));
        PrefixOutputCoreStep(cmd, preFs, preStdin, i, old(io.trustedStreams()));
        PrefixErrorOutputCoreStep(cmd, preFs, preStdin, i, old(io.trustedStreams()));
        PrefixHadErrorCoreStep(cmd, preFs, preStdin, i, old(io.trustedStreams()));
      }
      assert readResult == ReadResultCore(cmd, preFs, preStdin, i, old(io.trustedStreams()));

      var piece := OutputPiece(cmd, input, readResult, headers);
      var errorPiece := Spec.ErrorPiece(input, readResult);
      var inputHadError := Spec.HadErrorPiece(input, readResult);
      var inputHadHeader := Spec.ResultHasHeader(cmd, readResult);

      out := out + piece;
      err := err + errorPiece;
      hadError := hadError || inputHadError;
      headers := headers + (if inputHadHeader then 1 else 0);
      i := i + 1;
    }

    if |out| > 0 {
      plannedOut := plannedOut + out;
    } else {
      assert out == [];
      assert (initialStdout + plannedOut) == preStdout + out;
    }
    if |err| > 0 {
      plannedErr := plannedErr + err;
    } else {
      assert err == [];
      assert (initialStderr + plannedErr) == preStderr + err;
    }
    exit := if hadError then 1 else 0;

    assert out == RunOutputCore(cmd, preFs, preStdin, old(io.trustedStreams()));
    assert err == PrefixErrorOutputCore(cmd, preFs, preStdin, |cmd.inputs|, old(io.trustedStreams()));
    assert hadError == PrefixHadErrorCore(cmd, preFs, preStdin, |cmd.inputs|, old(io.trustedStreams()));
    assert io.stdin() == PrefixStdinCore(cmd, preStdin, |cmd.inputs|, preStreams);
    assert (initialStdout + plannedOut) == preStdout + RunOutputCore(cmd, preFs, preStdin, old(io.trustedStreams()));
    assert (initialStderr + plannedErr) == preStderr + PrefixErrorOutputCore(cmd, preFs, preStdin, |cmd.inputs|, old(io.trustedStreams()));
  }

  twostate predicate CoreSummary(raw: TailSchema.TailCmdRaw, io: BenchIO.IO, exit: int)
    reads io.stdinRegion, io.stdoutRegion, io.stderrRegion
  {
    exists out: BenchWorld.Bytes, diagnostics: BenchWorld.Bytes, normalExit: int ::
      PreparedSummary(raw, io, normalExit,
                      old(io.stdout()) + out, old(io.stderr()) + diagnostics) &&
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
      errors := errors + Spec.StreamWriteErrorMessage(message);
    }
    assert errors == diagnostics + (if outErr == 0 then [] else
                                    Spec.StreamWriteErrorMessage(StreamContract.CLocaleErrnoTextResult(outErr)));
    var errErr := 0;
    if errors != [] {
      var diagnosed := io.WriteStderr(errors);
      errErr := StreamContract.ResultErrno(diagnosed);
      assert StreamContract.WriteStderrSpec(old(io.stderr()), io.trustedStreams(), io.stderr(),
                                            errors, StreamContract.WriteResultCommitted(diagnosed), errErr);
    }
    exit := if outErr != 0 || errErr != 0 then 1 else normalExit;
  }

  method RunCore(raw: TailSchema.TailCmdRaw, io: BenchIO.IO) returns (exit: int)
    modifies io.stdinRegion, io.stdoutRegion, io.stderrRegion
    ensures CoreSummary(raw, io, exit)
    decreases *
  {
    var normalExit, out, diagnostics := Prepare(raw, io);

    assert PreparedSummary(raw, io, normalExit, old(io.stdout()) + out, old(io.stderr()) + diagnostics);
    if Spec.Emits(raw) {
      exit := Flush(io, out, diagnostics, normalExit);
    } else {
      exit := normalExit;
    }
    assert PreparedSummary(raw, io, normalExit, old(io.stdout()) + out, old(io.stderr()) + diagnostics);
    assert Spec.Emission(raw, io, out, diagnostics, normalExit, exit);
  }
}
