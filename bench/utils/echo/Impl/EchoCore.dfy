include "../../../core/Utf8.dfy"
include "../Spec/EchoSpec.dfy"
include "../../../core/World.dfy"
include "../../../core/IO.dfy"
include "../../../core/IOContract.dfy"
include "../Spec/EchoSchema.dfy"

module EchoCore {
  import StreamContract = IOContract

  import BenchIO
  import Utf8 = Utf8Semantics
  import BenchWorld
  import IOContract
  import EchoSchema
  import Spec = EchoSpec

  datatype EchoMode = ModeRun | ModeHelp | ModeVersion
  datatype EchoPlan = EchoPlan(mode: EchoMode, noNewline: bool, escapes: bool, operands: seq<string>)
  datatype EchoOptions = EchoOptions(noNewline: bool, doV9: bool, next: nat)
  datatype RenderResult = RenderResult(out: BenchWorld.Bytes, stopped: bool)
  datatype EscapeParse = EscapeParse(value: int, next: nat)

  function ApplyEchoOptionChars(token: string, i: nat, noNewline: bool, doV9: bool): (bool, bool)
    requires i <= |token|
    decreases |token| - i
  {
    if i >= |token| then
      (noNewline, doV9)
    else if token[i] == 'n' then
      ApplyEchoOptionChars(token, i + 1, true, doV9)
    else if token[i] == 'e' then
      ApplyEchoOptionChars(token, i + 1, noNewline, true)
    else if token[i] == 'E' then
      ApplyEchoOptionChars(token, i + 1, noNewline, false)
    else
      ApplyEchoOptionChars(token, i + 1, noNewline, doV9)
  }

  function ScanOptions(args: seq<string>, i: nat, noNewline: bool, doV9: bool): EchoOptions
    requires i <= |args|
    decreases |args| - i
  {
    if i >= |args| || !Spec.OptionToken(args[i]) then
      EchoOptions(noNewline, doV9, i)
    else
      var next := ApplyEchoOptionChars(args[i], 1, noNewline, doV9);
      ScanOptions(args, i + 1, next.0, next.1)
  }

  function Command(raw: EchoSchema.EchoCmdRaw, posixlyCorrect: bool): EchoPlan
  {
    var args := raw.args;
    var allowOptions := !posixlyCorrect || (|args| > 0 && args[0] == "-n");
    if allowOptions && |args| == 1 && args[0] == "--help" then
      EchoPlan(ModeHelp, false, false, [])
    else if allowOptions && |args| == 1 && args[0] == "--version" then
      EchoPlan(ModeVersion, false, false, [])
    else if allowOptions then
      var scanned := ScanOptions(args, 0, false, false);
      var operands := if scanned.next <= |args| then args[scanned.next..] else [];
      EchoPlan(ModeRun, scanned.noNewline, scanned.doV9 || posixlyCorrect, operands)
    else
      EchoPlan(ModeRun, false, posixlyCorrect, args)
  }

  function ParseHex(text: string, i: nat): EscapeParse
    requires i <= |text|
    requires i < |text| && Spec.IsHexDigit(text[i])
    ensures 0 <= ParseHex(text, i).value < 256
    ensures i < ParseHex(text, i).next <= |text|
  {
    if i + 1 < |text| && Spec.IsHexDigit(text[i + 1]) then
      EscapeParse(Spec.HexValue(text[i]) * 16 + Spec.HexValue(text[i + 1]), i + 2)
    else
      EscapeParse(Spec.HexValue(text[i]), i + 1)
  }

  function ParseOctalAfterZero(text: string, i: nat): EscapeParse
    requires i <= |text|
    ensures 0 <= ParseOctalAfterZero(text, i).value < 512
    ensures i <= ParseOctalAfterZero(text, i).next <= |text|
  {
    if i < |text| && BenchWorld.IsOctalDigit(text[i]) then
      ParseOctalDigits(text, i + 1, BenchWorld.CharToDigit(text[i]), 1)
    else
      EscapeParse(0, i)
  }

  function ParseOctalDigits(text: string, i: nat, acc: int, digits: nat): EscapeParse
    requires i <= |text|
    requires 1 <= digits <= 3
    requires 0 <= acc
    requires digits == 1 ==> acc < 8
    requires digits == 2 ==> acc < 64
    requires digits == 3 ==> acc < 512
    ensures 0 <= ParseOctalDigits(text, i, acc, digits).value < 512
    ensures i <= ParseOctalDigits(text, i, acc, digits).next <= |text|
    decreases 3 - digits
  {
    if digits >= 3 || i >= |text| || !BenchWorld.IsOctalDigit(text[i]) then
      EscapeParse(acc, i)
    else
      ParseOctalDigits(text, i + 1, acc * 8 + BenchWorld.CharToDigit(text[i]), digits + 1)
  }

  function RenderEscaped(text: string, i: nat): RenderResult
    requires i <= |text|
    decreases |text| - i
  {
    if i >= |text| then
      RenderResult([], false)
    else if text[i] != '\\' || i + 1 >= |text| then
      var rest := RenderEscaped(text, i + 1);
      RenderResult(Utf8.EncodeChar(text[i]) + rest.out, rest.stopped)
    else
      var e := text[i + 1];
      if e == 'c' then
        RenderResult([], true)
      else if e == 'a' then
        var rest := RenderEscaped(text, i + 2);
        RenderResult([(7 as char)] + rest.out, rest.stopped)
      else if e == 'b' then
        var rest := RenderEscaped(text, i + 2);
        RenderResult([(8 as char)] + rest.out, rest.stopped)
      else if e == 'e' then
        var rest := RenderEscaped(text, i + 2);
        RenderResult([(27 as char)] + rest.out, rest.stopped)
      else if e == 'f' then
        var rest := RenderEscaped(text, i + 2);
        RenderResult([(12 as char)] + rest.out, rest.stopped)
      else if e == 'n' then
        var rest := RenderEscaped(text, i + 2);
        RenderResult([(10 as char)] + rest.out, rest.stopped)
      else if e == 'r' then
        var rest := RenderEscaped(text, i + 2);
        RenderResult([(13 as char)] + rest.out, rest.stopped)
      else if e == 't' then
        var rest := RenderEscaped(text, i + 2);
        RenderResult([(9 as char)] + rest.out, rest.stopped)
      else if e == 'v' then
        var rest := RenderEscaped(text, i + 2);
        RenderResult([(11 as char)] + rest.out, rest.stopped)
      else if e == '\\' then
        var rest := RenderEscaped(text, i + 2);
        RenderResult(['\\'] + rest.out, rest.stopped)
      else if e == 'x' then
        if i + 2 < |text| && Spec.IsHexDigit(text[i + 2]) then
          var p := ParseHex(text, i + 2);
          var rest := RenderEscaped(text, p.next);
          RenderResult([(p.value % 256) as char] + rest.out, rest.stopped)
        else
          var rest := RenderEscaped(text, i + 2);
          RenderResult(['\\', 'x'] + rest.out, rest.stopped)
      else if e == '0' then
        var p := ParseOctalAfterZero(text, i + 2);
        var rest := RenderEscaped(text, p.next);
        RenderResult([(p.value % 256) as char] + rest.out, rest.stopped)
      else if BenchWorld.IsOctalDigit(e) then
        var p := ParseOctalDigits(text, i + 2, BenchWorld.CharToDigit(e), 1);
        var rest := RenderEscaped(text, p.next);
        RenderResult([(p.value % 256) as char] + rest.out, rest.stopped)
      else
        var rest := RenderEscaped(text, i + 2);
        RenderResult(['\\'] + Utf8.EncodeChar(e) + rest.out, rest.stopped)
  }

  function RenderArg(text: string, escapes: bool): RenderResult
  {
    if escapes then
      RenderEscaped(text, 0)
    else
      RenderResult(Utf8.Encode(text), false)
  }

  function RenderOperands(args: seq<string>, escapes: bool): RenderResult
    decreases |args|
  {
    if |args| == 0 then
      RenderResult([], false)
    else
      var first := RenderArg(args[0], escapes);
      if first.stopped then
        first
      else
        var rest := RenderOperands(args[1..], escapes);
        if |args| == 1 then
          RenderResult(first.out, rest.stopped)
        else if rest.stopped then
          RenderResult(first.out + [' '] + rest.out, true)
        else
          RenderResult(first.out + [' '] + rest.out, false)
  }

  function OutputFromCommand(cmd: EchoPlan): BenchWorld.Bytes
  {
    if cmd.mode == ModeHelp then
      Spec.HelpText()
    else if cmd.mode == ModeVersion then
      Spec.VersionText()
    else
      var rendered := RenderOperands(cmd.operands, cmd.escapes);
      rendered.out + (if rendered.stopped || cmd.noNewline then [] else "\n")
  }

  function Output(raw: EchoSchema.EchoCmdRaw, posixlyCorrect: bool): BenchWorld.Bytes
  {
    OutputFromCommand(Command(raw, posixlyCorrect))
  }

  twostate predicate PreparedSummary(raw: EchoSchema.EchoCmdRaw, io: BenchIO.IO, exit: int, plannedStdout: BenchWorld.Bytes, plannedStderr: BenchWorld.Bytes)

  {
    plannedStderr == old(io.stderr()) &&
    (    plannedStdout == old(io.stdout()) + Output(raw, Spec.PosixlyCorrect(old(io.env()))) &&
         exit == 0)
  }

  method Prepare(raw: EchoSchema.EchoCmdRaw, io: BenchIO.IO) returns (exit: int, plannedOut: BenchWorld.Bytes, plannedErr: BenchWorld.Bytes)

    ensures PreparedSummary(raw, io, exit, old(io.stdout()) + plannedOut, old(io.stderr()) + plannedErr)
    decreases *
  {
    plannedOut := [];
    plannedErr := [];
    ghost var initialStdout := io.stdout();
    ghost var initialStderr := io.stderr();

    ghost var preEnv := io.env();
    ghost var preStdout := (initialStdout + plannedOut);
    exit := 0;
    var envResult := io.GetEnv("POSIXLY_CORRECT");
    assert IOContract.GetEnvContractFields(preEnv, "POSIXLY_CORRECT", envResult);
    match envResult
    case Ok(_) =>
      assert "POSIXLY_CORRECT" in preEnv;
      var out := Output(raw, true);
      assert out == Output(raw, Spec.PosixlyCorrect(preEnv));
      plannedOut := plannedOut + out;
    case Err(_) =>
      assert !("POSIXLY_CORRECT" in preEnv);
      var out := Output(raw, false);
      assert out == Output(raw, Spec.PosixlyCorrect(preEnv));
      plannedOut := plannedOut + out;
      assert (initialStdout + plannedOut) == preStdout + Output(raw, Spec.PosixlyCorrect(preEnv));
  }

  twostate predicate CoreSummary(raw: EchoSchema.EchoCmdRaw, io: BenchIO.IO, exit: int)
    reads io.stdoutRegion, io.stderrRegion
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

  method RunCore(raw: EchoSchema.EchoCmdRaw, io: BenchIO.IO) returns (exit: int)
    modifies io.stdoutRegion, io.stderrRegion
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
