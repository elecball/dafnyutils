include "TruncateSpec.dfy"
include "TruncateProof.dfy"

module TruncateCore {
  import S = TruncateSchema
  import Spec = TruncateSpec
  import Proof = TruncateProof
  import BenchIO
  import W = BenchWorld
  import C = IOContract
  import Utf8 = Utf8Semantics

  method SkipSpaces(text: string, start: nat) returns (end: nat)
    requires start <= |text|
    ensures Spec.SpaceBoundary(text, start, end)
  {
    end := start;
    while end < |text| && Spec.IsSpace(text[end])
      invariant start <= end <= |text|
      invariant forall i :: start <= i < end ==> Spec.IsSpace(text[i])
      decreases |text| - end
    { end := end + 1; }
  }

  method ParseSize(text: string, io: BenchIO.IO) returns (parsed: S.ParsedSize)
    ensures Spec.SizeRelation(text, parsed)
  {
    reveal Spec.SizeRelation();
    var a := SkipSpaces(text, 0);
    var prefix := Spec.PrefixModifier(text, a);
    var b := SkipSpaces(text, a + (if prefix == S.Absolute then 0 else 1));
    var signed := b < |text| && text[b] in {'+', '-'};
    var c := b + (if signed then 1 else 0);
    var end := c;
    var magnitude: nat := 0;
    while end < |text| && Spec.IsDigit(text[end])
      invariant c <= end <= |text|
      invariant Spec.Digits(text[c..end])
      invariant magnitude == Spec.Decimal(text[c..end])
      decreases |text| - end
    {
      magnitude := magnitude * 10 + Spec.Digit(text[end]);
      end := end + 1;
      assert text[c..end][..|text[c..end]| - 1] == text[c..end - 1];
    }
    assert Spec.NumberLayout(text, a, b, c, end);
    if c == end { magnitude := 1; }
    var scale := Spec.Scale(text[end..]);
    var value := (if b < |text| && text[b] == '-' then -1 else 1) * magnitude * scale;
    var modifier := if prefix != S.Absolute then prefix else if signed then S.Relative else S.Absolute;
    var error: W.Bytes := [];
    if prefix != S.Absolute && signed {
      error := Spec.MultipleModifiers();
    } else if scale == 0 || (c == end && (signed || text[end..] == "")) {
      var quote := io.QuoteArgument(Utf8.Encode(text[b..]));
      error := Spec.InvalidNumberText(quote, false);
    } else if value < Spec.MinSize || value > Spec.MaxSize {
      var quote := io.QuoteArgument(Utf8.Encode(text[b..]));
      error := Spec.InvalidNumberText(quote, true);
    }
    parsed := S.ParsedSize(modifier, signed, value, error);
  }

  method Resolve(raw: S.TruncateCmdRaw, io: BenchIO.IO)
    returns (mode: S.Modifier, value: int, error: W.Bytes)
    ensures Spec.Resolved(raw, mode, value, error)
  {
    reveal Spec.Resolved();
    var parsed: seq<S.ParsedSize> := [];
    var i := 0;
    while i < |raw.sizes|
      invariant 0 <= i <= |raw.sizes|
      invariant |parsed| == i
      invariant forall j :: 0 <= j < i ==> Spec.SizeRelation(raw.sizes[j], parsed[j])
      decreases |raw.sizes| - i
    {
      var next := ParseSize(raw.sizes[i], io);
      parsed := parsed + [next];
      i := i + 1;
    }
    mode, value, error := S.Absolute, 0, [];
    i := 0;
    while i < |parsed|
      invariant 0 <= i <= |parsed|
      invariant Spec.ModeAt(parsed, i, mode)
      invariant value == (if i == 0 then 0 else parsed[i - 1].value)
      invariant error == [] ==> forall j :: 0 <= j < i ==> Spec.ErrorAt(parsed, j, [])
      invariant error != [] ==>
        (exists j: nat :: j < i && Spec.ErrorAt(parsed, j, error) &&
          (forall k :: 0 <= k < j ==> Spec.ErrorAt(parsed, k, [])))
      decreases |parsed| - i
    {
      var prior := mode;
      Proof.ModeAppend(parsed, i, prior);
      if parsed[i].modifier != S.Absolute { mode := parsed[i].modifier; }
      var step :=
        if parsed[i].signed && prior != S.Absolute then Spec.MultipleModifiers()
        else if parsed[i].error != [] then parsed[i].error
        else if mode in {S.RoundDown, S.RoundUp} && parsed[i].value == 0 then Spec.DivisionByZero()
        else [];
      assert (prior != S.Absolute) <==>
        (exists j: nat :: j < i && parsed[j].modifier != S.Absolute);
      assert Spec.ErrorAt(parsed, i, step);
      if error == [] { error := step; }
      value := parsed[i].value;
      i := i + 1;
    }
  }

  method OpenMessage(io: BenchIO.IO, path: string, err: int) returns (message: W.Bytes)
    ensures message == Spec.CannotOpen(path, err)
  {
    var quote := io.QuoteafPath(path);
    var reason := io.GetCLocaleErrnoText(err);
    message := Spec.OpenText(quote, reason);
  }
  method StatMessage(io: BenchIO.IO, path: string, err: int, reference: bool) returns (message: W.Bytes)
    ensures message == Spec.CannotStat(path, err, reference)
  {
    var quote := io.QuoteafPath(path);
    var reason := io.GetCLocaleErrnoText(err);
    message := Spec.StatText(quote, reason, reference);
  }
  method ResizeMessage(io: BenchIO.IO, path: string, size: nat, err: int) returns (message: W.Bytes)
    ensures message == Spec.TruncateError(path, size, err)
  {
    var quote := io.QuoteafPath(path);
    var reason := io.GetCLocaleErrnoText(err);
    message := Spec.ResizeText(quote, size, reason);
  }

  method OpenOne(io: BenchIO.IO, path: string, noCreate: bool) returns (isOpen: bool, err: int)
    modifies io.fsRegion
    ensures Spec.OpenRelation(old(io.trustedFilesystem()), old(io.now()), path, noCreate,
      old(io.fs()), io.fs(), isOpen, err)
  {
    reveal Spec.OpenRelation();
    if noCreate {
      var query := io.PathExists(path, true);
      if query.Err? {
        isOpen := false;
        err := if C.ResultErrno(query) == 2 then 0 else C.ResultErrno(query);
        return;
      }
    }
    var created := io.CreateFile(path);
    isOpen, err := created.Ok?, C.ResultErrno(created);
  }

  method Status(io: BenchIO.IO, path: string) returns (result: W.IOResult<W.FileStatus>)
    modifies io.statusObservationsRegion
    ensures Spec.StatusRelation(Spec.StatusObservations(io.statusObservations(),io.trustedNativeFailures()), old(io.statusCursor()), io.statusCursor(),
      old(io.fs()), path, result.Ok?, C.ResultValue(result, W.DEFAULT_FILE_STATUS), C.ResultErrno(result))
  {
    reveal Spec.StatusRelation();
    result := io.GetFileStatus(path, true);
  }

  method TruncateOne(io: BenchIO.IO, path: string, size: nat) returns (error: W.Bytes)
    modifies io.fsRegion
    ensures Spec.Truncation(old(io.trustedFilesystem()), old(io.now()), path, size,
      old(io.fs()), io.fs(), error)
  {
    reveal Spec.Truncation();
    var result := io.TruncateFile(path, size);
    if result.Ok? { error := []; }
    else { error := ResizeMessage(io, path, size, C.ResultErrno(result)); }
  }

  method {:vcs_split_on_every_assert} ResizeOne(io: BenchIO.IO, path: string, mode: S.Modifier, delta: int, blocks: bool, reference: int)
    returns (error: W.Bytes)
    modifies io.fsRegion, io.statusObservationsRegion
    ensures Spec.ResizeRelation(old(io.trustedFilesystem()), Spec.StatusObservations(io.statusObservations(),io.trustedNativeFailures()), old(io.now()),
      path, mode, delta, blocks, reference, old(io.fs()), old(io.statusCursor()),
      io.fs(), io.statusCursor(), error)
  {
    ghost var observations: (W.TrustedFilesystemRequest) -> W.TrustedFilesystemResult := io.trustedFilesystem();
    ghost var timeSamples := Spec.StatusObservations(io.statusObservations(),io.trustedNativeFailures());
    ghost var instant := io.now();
    ghost var before := io.fs();
    ghost var cursor := io.statusCursor();
    var status := W.DEFAULT_FILE_STATUS;
    var statOk, statErr := true, 0;
    if blocks || (mode != S.Absolute && reference < 0) {
      var result := Status(io, path);
      statOk, statErr := result.Ok?, C.ResultErrno(result);
      status := C.ResultValue(result, W.DEFAULT_FILE_STATUS);
      if result.Err? {
        error := StatMessage(io, path, statErr, false);
        assert Spec.ResizeOutcome(observations, timeSamples, instant,
          path, mode, delta, blocks, reference, before, cursor, io.fs(), io.statusCursor(),
          error, status, statOk, statErr) by { hide *; reveal Spec.ResizeOutcome(); }
        assert Spec.ResizeRelation(observations, timeSamples, instant, path,
          mode, delta, blocks, reference, before, cursor, io.fs(), io.statusCursor(), error) by {
          hide *;
          Proof.ResizeWitness(observations, timeSamples, instant, path,
          mode, delta, blocks, reference, before, cursor, io.fs(), io.statusCursor(),
          error, status, statOk, statErr);
        }
        return;
      }
    }
    ghost var afterCursor := io.statusCursor();
    assert (if blocks || (mode != S.Absolute && reference < 0) then
      Spec.StatusRelation(timeSamples, cursor, afterCursor, before,
        path, statOk, status, statErr)
      else afterCursor == cursor && statOk && status == W.DEFAULT_FILE_STATUS && statErr == 0);
    var scaled := delta * (if blocks then Spec.BlockSize(status) else 1);
    var base := if reference >= 0 then reference as nat else status.storage.size;
    var requested := Spec.AdjustedSize(mode, base, scaled);
    if scaled < Spec.MinSize || scaled > Spec.MaxSize {
      var quote := io.QuoteafPath(path);
      error := Spec.BlockOverflowText(quote, delta, Spec.BlockSize(status));
      assert error == Spec.BlockOverflow(path, delta, Spec.BlockSize(status));
      assert Spec.ResizeOutcome(observations, timeSamples, instant,
        path, mode, delta, blocks, reference, before, cursor, io.fs(), io.statusCursor(),
        error, status, statOk, statErr) by { hide *; reveal Spec.ResizeOutcome(); }
      assert Spec.ResizeRelation(observations, timeSamples, instant, path,
        mode, delta, blocks, reference, before, cursor, io.fs(), io.statusCursor(), error) by {
        hide *;
        Proof.ResizeWitness(observations, timeSamples, instant, path,
        mode, delta, blocks, reference, before, cursor, io.fs(), io.statusCursor(),
        error, status, statOk, statErr);
      }
    } else if requested > Spec.MaxSize {
      var quote := io.QuoteafPath(path);
      error := Spec.ExtendOverflowText(quote);
      assert error == Spec.ExtendOverflow(path);
      assert Spec.ResizeOutcome(observations, timeSamples, instant,
        path, mode, delta, blocks, reference, before, cursor, io.fs(), io.statusCursor(),
        error, status, statOk, statErr) by { hide *; reveal Spec.ResizeOutcome(); }
      assert Spec.ResizeRelation(observations, timeSamples, instant, path,
        mode, delta, blocks, reference, before, cursor, io.fs(), io.statusCursor(), error) by {
        hide *;
        Proof.ResizeWitness(observations, timeSamples, instant, path,
        mode, delta, blocks, reference, before, cursor, io.fs(), io.statusCursor(),
        error, status, statOk, statErr);
      }
    } else {
      error := TruncateOne(io, path, Spec.Clamped(requested));
      assert Spec.ResizeOutcome(observations, timeSamples, instant,
        path, mode, delta, blocks, reference, before, cursor, io.fs(), io.statusCursor(),
        error, status, statOk, statErr) by { hide *; reveal Spec.ResizeOutcome(); }
      assert Spec.ResizeRelation(observations, timeSamples, instant, path,
        mode, delta, blocks, reference, before, cursor, io.fs(), io.statusCursor(), error) by {
        hide *;
        Proof.ResizeWitness(observations, timeSamples, instant, path,
        mode, delta, blocks, reference, before, cursor, io.fs(), io.statusCursor(),
        error, status, statOk, statErr);
      }
    }
  }

  method {:vcs_split_on_every_assert} File(io: BenchIO.IO, path: string, noCreate: bool, mode: S.Modifier,
      delta: int, blocks: bool, reference: int) returns (error: W.Bytes)
    modifies io.fsRegion, io.statusObservationsRegion
    ensures Spec.FileStep(old(io.trustedFilesystem()), Spec.StatusObservations(io.statusObservations(),io.trustedNativeFailures()), old(io.now()),
      path, noCreate, mode, delta, blocks, reference, old(io.fs()), old(io.statusCursor()),
      io.fs(), io.statusCursor(), error)
  {
    hide *;
    ghost var observations: (W.TrustedFilesystemRequest) -> W.TrustedFilesystemResult := io.trustedFilesystem();
    ghost var timeSamples := Spec.StatusObservations(io.statusObservations(),io.trustedNativeFailures());
    ghost var instant := io.now();
    ghost var before := io.fs();
    ghost var cursor := io.statusCursor();
    var isOpen, err := OpenOne(io, path, noCreate);
    ghost var openedFs := io.fs();
    if !isOpen {
      if err == 0 { error := []; }
      else { error := OpenMessage(io, path, err); }
      assert Spec.FileStep(observations, timeSamples, instant, path,
        noCreate, mode, delta, blocks, reference, before, cursor, io.fs(), io.statusCursor(), error) by {
        hide *;
        Proof.FileWitness(observations, timeSamples, instant, path,
        noCreate, mode, delta, blocks, reference, before, cursor, io.fs(), io.statusCursor(), error,
        openedFs, isOpen, err);
      }
    } else {
      error := ResizeOne(io, path, mode, delta, blocks, reference);
      assert Spec.FileStep(observations, timeSamples, instant, path,
        noCreate, mode, delta, blocks, reference, before, cursor, io.fs(), io.statusCursor(), error) by {
        hide *;
        Proof.FileWitness(observations, timeSamples, instant, path,
        noCreate, mode, delta, blocks, reference, before, cursor, io.fs(), io.statusCursor(), error,
        openedFs, isOpen, err);
      }
    }
  }

  method {:vcs_split_on_every_assert} Files(raw: S.TruncateCmdRaw, mode: S.Modifier, delta: int, reference: int, io: BenchIO.IO)
    returns (errors: W.Bytes, exit: int)
    modifies io.fsRegion, io.statusObservationsRegion
    ensures Spec.FilesRelation(raw, mode, delta, reference, old(io.trustedFilesystem()),
      Spec.StatusObservations(io.statusObservations(),io.trustedNativeFailures()), old(io.now()), old(io.fs()), old(io.statusCursor()),
      io.fs(), io.statusCursor(), errors, exit)
  {
    ghost var before := io.fs();
    ghost var cursor := io.statusCursor();
    ghost var states := [Spec.FileState(before, cursor, [], false)];
    errors := [];
    var failed := false;
    var i := 0;
    while i < |raw.files|
      invariant 0 <= i <= |raw.files|
      invariant |states| == i + 1
      invariant states[0] == Spec.FileState(before, cursor, [], false)
      invariant states[i] == Spec.FileState(io.fs(), io.statusCursor(), errors, failed)
      invariant forall j :: 0 <= j < i ==>
        Spec.FileRelation(io.trustedFilesystem(), Spec.StatusObservations(io.statusObservations(),io.trustedNativeFailures()), io.now(), raw.files[j],
          raw.noCreate, mode, delta, raw.blocks, reference, states[j], states[j + 1])
      decreases |raw.files| - i
    {
      ghost var previous := states[i];
      var error := File(io, raw.files[i], raw.noCreate, mode, delta, raw.blocks, reference);
      errors := errors + error;
      failed := failed || error != [];
      ghost var next := Spec.FileState(io.fs(), io.statusCursor(), errors, failed);
      Proof.FileStepImpliesRelation(io.trustedFilesystem(), Spec.StatusObservations(io.statusObservations(),io.trustedNativeFailures()), io.now(),
        raw.files[i], raw.noCreate, mode, delta, raw.blocks, reference, previous, next, error);
      ghost var priorStates := states;
      states := states + [next];
      forall j | 0 <= j < i + 1
        ensures Spec.FileRelation(io.trustedFilesystem(), Spec.StatusObservations(io.statusObservations(),io.trustedNativeFailures()), io.now(),
          raw.files[j], raw.noCreate, mode, delta, raw.blocks, reference, states[j], states[j + 1])
      {
        if j == i { assert states[j] == previous && states[j + 1] == next; }
        else { assert states[j] == priorStates[j] && states[j + 1] == priorStates[j + 1]; }
      }
      i := i + 1;
    }
    exit := if failed then 1 else 0;
    Proof.FilesWitness(raw, mode, delta, reference, io.trustedFilesystem(), Spec.StatusObservations(io.statusObservations(),io.trustedNativeFailures()),
      io.now(), before, cursor, io.fs(), io.statusCursor(), errors, exit, states);
  }

  method {:vcs_split_on_every_assert} Run(raw: S.TruncateCmdRaw, mode: S.Modifier, value: int, io: BenchIO.IO)
    returns (errors: W.Bytes, exit: int)
    modifies io.fsRegion, io.statusObservationsRegion
    ensures Spec.RunRelation(raw, mode, value, old(io.trustedFilesystem()), Spec.StatusObservations(io.statusObservations(),io.trustedNativeFailures()),
      old(io.now()), old(io.fs()), old(io.statusCursor()), io.fs(), io.statusCursor(), errors, exit)
  {
    ghost var observations: (W.TrustedFilesystemRequest) -> W.TrustedFilesystemResult := io.trustedFilesystem();
    ghost var timeSamples := Spec.StatusObservations(io.statusObservations(),io.trustedNativeFailures());
    ghost var instant := io.now();
    ghost var before := io.fs();
    ghost var cursor := io.statusCursor();
    if raw.hasReference {
      var result := Status(io, raw.reference);
      ghost var next := io.statusCursor();
      if result.Err? {
        errors := StatMessage(io, raw.reference, C.ResultErrno(result), true);
        exit := 1;
      } else {
        var size := result.v.storage.size;
        errors, exit := Files(raw, mode, if |raw.sizes| == 0 then size else value,
          if |raw.sizes| == 0 then -1 else size, io);
      }
      Proof.ReferenceRunWitness(raw, mode, value, observations, timeSamples, instant,
        before, cursor, io.fs(), io.statusCursor(), errors, exit,
        result.Ok?, C.ResultValue(result, W.DEFAULT_FILE_STATUS), C.ResultErrno(result), next);
    } else {
      errors, exit := Files(raw, mode, value, -1, io);
      Proof.NoReferenceRunWitness(raw, mode, value, observations, timeSamples, instant,
        before, cursor, io.fs(), io.statusCursor(), errors, exit);
    }
  }

  method Diagnostic(message: W.Bytes, io: BenchIO.IO) returns (err: int)
    modifies io.stderrRegion
    ensures Spec.DiagnosticResult(old(io.stderr()), io.stderr(), io.trustedStreams(), message, err)
  {
    reveal Spec.DiagnosticResult();
    err := 0;
    if message != [] {
      var result := io.WriteStderr(message);
      err := C.ResultErrno(result);
    }
  }

  method Information(mode: S.Mode, io: BenchIO.IO) returns (exit: int)
    modifies io.stdoutRegion, io.stderrRegion
    ensures Spec.HelpResult(mode, old(io.stdout()), io.stdout(), old(io.stderr()), io.stderr(),
      io.trustedStreams(), exit)
  {
    reveal Spec.DiagnosticResult();
    var payload := if mode == S.Help then Spec.HelpText() else Spec.VersionText();
    var write := io.WriteStdout(payload);
    ghost var committed := C.WriteResultCommitted(write);
    var writeErr := C.ResultErrno(write);
    var diagnosticErr := 0;
    if writeErr == 0 { exit := 0; }
    else {
      var reason := io.GetCLocaleErrnoText(writeErr);
      diagnosticErr := Diagnostic(Spec.WriteErrorText(reason), io);
      exit := 1;
    }
    Proof.HelpOutputWitness(old(io.stdout()), io.trustedStreams(), io.stdout(), mode,
      old(io.stderr()), io.stderr(), exit, committed, writeErr, diagnosticErr);
  }

  method {:vcs_split_on_every_assert} RunCore(raw: S.TruncateCmdRaw, io: BenchIO.IO) returns (exit: int)
    modifies io.fsRegion, io.statusObservationsRegion, io.stdoutRegion, io.stderrRegion
    ensures Spec.Spec(raw, io, exit)
  {
    hide *;
    var mode, value, error := Resolve(raw, io);
    if error != [] {
      var diagnosticErr := Diagnostic(error, io);
      exit := 1;
      assert Spec.ExecutionRelation(raw, mode, value, error, io, exit) by {
        reveal Spec.ExecutionRelation();
      }
    } else if raw.mode != S.Run {
      exit := Information(raw.mode, io);
      assert Spec.ExecutionRelation(raw, mode, value, error, io, exit) by {
        reveal Spec.ExecutionRelation();
      }
    } else if raw.parseError != [] {
      var diagnosticErr := Diagnostic(raw.parseError, io);
      exit := 1;
      assert Spec.ExecutionRelation(raw, mode, value, error, io, exit) by {
        reveal Spec.ExecutionRelation();
      }
    } else if Spec.ConfigurationError(raw, mode) != [] {
      var diagnosticErr := Diagnostic(Spec.ConfigurationError(raw, mode), io);
      exit := 1;
      assert Spec.ExecutionRelation(raw, mode, value, error, io, exit) by {
        reveal Spec.ExecutionRelation();
      }
    } else {
      var errors: W.Bytes;
      var normalExit: int;
      errors, normalExit := Run(raw, mode, value, io);
      var diagnosticErr := Diagnostic(errors, io);
      exit := if diagnosticErr == 0 then normalExit else 1;
      assert Spec.RunRelation(raw, mode, value, old(io.trustedFilesystem()), Spec.StatusObservations(io.statusObservations(),io.trustedNativeFailures()),
        old(io.now()), old(io.fs()), old(io.statusCursor()), io.fs(), io.statusCursor(), errors, normalExit);
      assert Spec.DiagnosticResult(old(io.stderr()), io.stderr(), old(io.trustedStreams()), errors, diagnosticErr);
      assert Spec.ExecutionRelation(raw, mode, value, error, io, exit) by {
        reveal Spec.ExecutionRelation();
        assert exists emitted: W.Bytes, runExit: int, err: int ::
          Spec.RunRelation(raw, mode, value, old(io.trustedFilesystem()), Spec.StatusObservations(io.statusObservations(),io.trustedNativeFailures()),
            old(io.now()), old(io.fs()), old(io.statusCursor()), io.fs(), io.statusCursor(), emitted, runExit) &&
          Spec.DiagnosticResult(old(io.stderr()), io.stderr(), old(io.trustedStreams()), emitted, err) &&
          exit == (if err == 0 then runExit else 1);
      }
    }
    Proof.RunWitness(raw, mode, value, error, io, exit);
  }
}
