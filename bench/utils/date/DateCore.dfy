include "DateSpec.dfy"
include "DateCalendar.dfy"
include "DateFormat.dfy"

module DateCore {
  import IO = BenchIO
  import W = BenchWorld
  import C = IOContract
  import U = Utf8Semantics
  import S = DateSchema
  import Spec = DateSpec
  import Calendar = DateCalendar
  import Format = DateFormat
  import SE = StringEscaping

  method ArgumentError(kind: Spec.ErrorKind, value: string, io: IO.IO) returns (diagnostic: W.Bytes)
    ensures diagnostic == Spec.ErrorText(kind, C.QuoteArgumentResult(U.Encode(value)))
  {
    var quote := io.QuoteArgument(U.Encode(value));
    diagnostic := Spec.ErrorText(kind, quote);
  }

  method FileError(path: string, errno: int, io: IO.IO) returns (diagnostic: W.Bytes)
    ensures diagnostic == Spec.ErrorText(Spec.FileFailure, SE.SpecQuoteFBytes(U.Encode(path)), C.CLocaleErrnoTextResult(errno))
  {
    var quote := SE.SpecQuoteFBytes(U.Encode(path));
    var reason := io.GetCLocaleErrnoText(errno);
    diagnostic := Spec.ErrorText(Spec.FileFailure, quote, reason);
  }

  method EarlyPlan(raw: S.DateCmdRaw, io: IO.IO) returns (stdout: W.Bytes, stderr: W.Bytes, code: int)
    requires Spec.Early(raw)
    ensures Spec.EarlyPlan(raw, stdout, stderr, code)
  {
    stdout := [];
    stderr := [];
    code := 1;
    if raw.mode == S.Help { stdout := Spec.HelpText(); code := 0; }
    else if raw.mode == S.Version { stdout := Spec.VersionText(); code := 0; }
    else if raw.mode == S.InvalidIso || raw.mode == S.InvalidRfc {
      var quote := io.QuoteArgument(U.Encode(raw.invalidValue));
      stderr := Spec.InvalidFormatText(raw.mode == S.InvalidIso, quote, raw.invalidValue == "");
    } else if raw.date.Some? && raw.reference.Some? { stderr := Spec.ErrorText(Spec.Exclusive); }
    else if |raw.operands| > 1 { stderr := ArgumentError(Spec.ExtraOperand, raw.operands[1], io); }
    else if |raw.operands| == 1 && (|raw.operands[0]| == 0 || raw.operands[0][0] != '+') {
      stderr := ArgumentError(if raw.date.Some? || raw.reference.Some? then Spec.LeadingPlus else Spec.InvalidDate, raw.operands[0], io);
    } else { stderr := Spec.ErrorText(Spec.MultipleFormats); }
  }

  method Select(raw: S.DateCmdRaw, io: IO.IO) returns (selection: Spec.Selection)
    ensures Spec.Selected(raw, io.fs(), io.now(), io.trustedTimeParses(), io.trustedFilesystem(), selection)
  {
    if raw.reference.Some? {
      var result := io.GetFileTimes(raw.reference.value, true);
      if result.Ok? {
        selection := Spec.Instant(result.v.mtimeSec, result.v.mtimeNsec);
      } else {
        var diagnostic := FileError(raw.reference.value, C.ResultErrno(result), io);
        selection := Spec.SelectionError(diagnostic);
      }
      assert Spec.Times(result) == C.ResultValue(result, W.FileTimeStatus(0, 0, 0, 0, false, false, 0, 0, 0));
    } else {
      var now := io.Now();
      if raw.date.Some? {
        var result := io.ParseDate(raw.date.value, now, 0);
        if result.Ok? { selection := Spec.Instant(result.v.sec, result.v.nsec); }
        else {
          var diagnostic := ArgumentError(Spec.InvalidDate, raw.date.value, io);
          selection := Spec.SelectionError(diagnostic);
        }
      } else { selection := Spec.Instant(now, 0); }
    }
  }

  method TimeOutput(format: string, seconds: int, nanos: int, io: IO.IO)
    returns (stdout: W.Bytes, stderr: W.Bytes, code: int)
    ensures Spec.TimeOutput(format, seconds, nanos, stdout, stderr, code)
  {
    var civil := Calendar.Convert(seconds);
    var iso := Calendar.Convert(Spec.IsoThursday(seconds));
    if -2147481748 <= civil.year <= 2147485547 {
      var text := Format.Render(format, seconds, nanos, civil, iso);
      stdout := U.Encode(text + "\n");
      stderr := [];
      code := 0;
    } else {
      var text := Calendar.Number(seconds, 1);
      stderr := ArgumentError(Spec.Range, text, io);
      stdout := "\n";
      code := 1;
    }
  }

  method Prepare(raw: S.DateCmdRaw, io: IO.IO) returns (stdout: W.Bytes, stderr: W.Bytes, code: int)
    ensures Spec.Plan(raw, io.fs(), io.now(), io.trustedTimeParses(), io.trustedFilesystem(), stdout, stderr, code)
  {
    if Spec.Early(raw) { stdout, stderr, code := EarlyPlan(raw, io); }
    else {
      var selection := Select(raw, io);
      match selection
      case SelectionError(diagnostic) => stdout, stderr, code := [], diagnostic, 1;
      case Instant(seconds, nanos) => stdout, stderr, code := TimeOutput(Spec.OutputFormat(raw), seconds, nanos, io);
    }
  }

  method Emit(io: IO.IO, stdout: W.Bytes, stderr: W.Bytes, code: int) returns (exit: int)
    modifies io.stdoutRegion, io.stderrRegion
    ensures Spec.Emitted(old(io.stdout()), old(io.stderr()), io.stdout(), io.stderr(), io.trustedStreams(), stdout, stderr, code, exit)
  {
    var outResult := io.WriteStdout(stdout);
    assert io.trustedStreams()(W.StreamWriteStdout(old(io.stdout()), stdout)) ==
           W.StreamWriteResult(C.WriteResultCommitted(outResult), io.stdout(), C.ResultErrno(outResult)) by {
      reveal C.WriteStdoutSpec(), C.TrustedWriteStdoutWithOutcomeContractFields(), C.TrustedWriteWithOutcomeFields();
    }
    var diagnostic := stderr;
    if outResult.Err? {
      var reason := io.GetCLocaleErrnoText(C.ResultErrno(outResult));
      diagnostic := diagnostic + Spec.ErrorText(Spec.WriteFailure, [], reason);
    }
    assert diagnostic == stderr + (if C.ResultErrno(outResult) == 0 then []
                                   else Spec.ErrorText(Spec.WriteFailure, [], C.CLocaleErrnoTextResult(C.ResultErrno(outResult))));
    var errResult := io.WriteStderr(diagnostic);
    assert io.trustedStreams()(W.StreamWriteStderr(old(io.stderr()), diagnostic)) ==
           W.StreamWriteResult(C.WriteResultCommitted(errResult), io.stderr(), C.ResultErrno(errResult)) by {
      reveal C.WriteStderrSpec(), C.TrustedWriteStderrWithOutcomeContractFields(), C.TrustedWriteWithOutcomeFields();
    }
    exit := if outResult.Ok? && errResult.Ok? then code else 1;
    assert io.trustedStreams()(W.StreamWriteStdout(old(io.stdout()), stdout)).StreamWriteResult?;
    assert io.trustedStreams()(W.StreamWriteStderr(old(io.stderr()), diagnostic)).StreamWriteResult?;
  }

  twostate predicate CoreSummary(raw: S.DateCmdRaw, io: IO.IO, exit: int)
    reads io.fsRegion, io.nowRegion, io.trustedTimeParsesRegion, io.trustedFilesystemRegion,
          io.trustedStreamsRegion, io.stdoutRegion, io.stderrRegion
  {
    exists stdout: W.Bytes, stderr: W.Bytes, code: int ::
      Spec.Plan(raw, io.fs(), io.now(), io.trustedTimeParses(), io.trustedFilesystem(), stdout, stderr, code) &&
      Spec.Emitted(old(io.stdout()), old(io.stderr()), io.stdout(), io.stderr(), io.trustedStreams(), stdout, stderr, code, exit)
  }

  method RunCore(raw: S.DateCmdRaw, io: IO.IO) returns (exit: int)
    modifies io.stdoutRegion, io.stderrRegion
    ensures CoreSummary(raw, io, exit)
  {
    var stdout, stderr, code := Prepare(raw, io);
    exit := Emit(io, stdout, stderr, code);
  }
}
