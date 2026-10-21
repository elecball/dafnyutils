include "PrintfTextCore.dfy"
include "../../core/IOContract.dfy"
include "../../core/World.dfy"
include "../../core/IO.dfy"
include "PrintfSchema.dfy"
include "PrintfSpec.dfy"

module PrintfCore {
  import StreamContract = IOContract

  import BenchIO
  import Utf8 = PrintfUtf8Core
  import Text = PrintfTextCore
  import BenchWorld
  import Schema = PrintfSchema
  import Spec = PrintfSpec

  function ClassifyFragment(
    format: string,
    args: seq<string>,
    start: nat,
    nextArg: nat
  ): Spec.FragmentPlan
    requires start < |format|
    requires nextArg <= |args|
  {
    if format[start] == '\\' then
      if start + 1 >= |format| then
        Spec.OneFragment(Spec.FormatFragment(start + 1, nextArg, ['\\']))
      else if format[start + 1] == 'a' then
        Spec.OneFragment(Spec.FormatFragment(start + 2, nextArg, [7 as char]))
      else if format[start + 1] == 'b' then
        Spec.OneFragment(Spec.FormatFragment(start + 2, nextArg, [8 as char]))
      else if format[start + 1] == 'c' then
        Spec.StopFragment(1, [])
      else if format[start + 1] == 'e' then
        Spec.OneFragment(Spec.FormatFragment(start + 2, nextArg, [27 as char]))
      else if format[start + 1] == 'f' then
        Spec.OneFragment(Spec.FormatFragment(start + 2, nextArg, [12 as char]))
      else if format[start + 1] == 'n' then
        Spec.OneFragment(Spec.FormatFragment(start + 2, nextArg, ['\n']))
      else if format[start + 1] == 'r' then
        Spec.OneFragment(Spec.FormatFragment(start + 2, nextArg, ['\r']))
      else if format[start + 1] == 't' then
        Spec.OneFragment(Spec.FormatFragment(start + 2, nextArg, ['\t']))
      else if format[start + 1] == 'v' then
        Spec.OneFragment(Spec.FormatFragment(start + 2, nextArg, [11 as char]))
      else if format[start + 1] == '\\' then
        Spec.OneFragment(Spec.FormatFragment(start + 2, nextArg, ['\\']))
      else if format[start + 1] == '"' then
        Spec.OneFragment(Spec.FormatFragment(start + 2, nextArg, ['"']))
      else if BenchWorld.IsOctalDigit(format[start + 1]) then
        var digitStart := start + 1;
        var digits := Spec.OctalCount(format, digitStart);
        Spec.OneFragment(Spec.FormatFragment(
                           digitStart + digits, nextArg,
                           [(Spec.OctalValue(format, digitStart, digits) % 256) as char]))
      else if format[start + 1] == 'x' then
        var digits := Spec.HexCount(format, start + 2);
        if digits == 0 then Spec.StopFragment(2, Spec.MissingHexMessage())
        else Spec.OneFragment(Spec.FormatFragment(
                                start + 2 + digits, nextArg,
                                [(Spec.HexValue(format, start + 2, digits) % 256) as char]))
      else if format[start + 1] == 'u' || format[start + 1] == 'U' then
        var upper := format[start + 1] == 'U';
        var width := if upper then 8 else 4;
        if !Spec.HexSpan(format, start + 2, width) then
          Spec.StopFragment(2, Spec.MissingHexMessage())
        else
          var value := Spec.HexValue(format, start + 2, width);
          if 0xd800 <= value <= 0xdfff then
            Spec.StopFragment(2, Spec.InvalidUnicodeMessage(value, upper))
          else
            Spec.OneFragment(Spec.FormatFragment(
                               start + 2 + width, nextArg, Spec.UnicodeBytes(value)))
      else
        Spec.OneFragment(Spec.FormatFragment(
                           start + 2, nextArg, ['\\'] + Utf8.EncodeChar(format[start + 1])))
    else if format[start] == '%' then
      if start + 1 >= |format| then
        Spec.NoFragment
      else if format[start + 1] == '%' then
        Spec.OneFragment(Spec.FormatFragment(start + 2, nextArg, ['%']))
      else if format[start + 1] == 's' then
        Spec.OneFragment(Spec.FormatFragment(
                           start + 2,
                           if nextArg < |args| then nextArg + 1 else nextArg,
                           if nextArg < |args| then Utf8.Encode(args[nextArg]) else []))
      else
        Spec.NoFragment
    else
      Spec.OneFragment(Spec.FormatFragment(start + 1, nextArg, Utf8.EncodeChar(format[start])))
  }

  function RenderPass(format: string, args: seq<string>, i: nat, nextArg: nat):
    (int, BenchWorld.Bytes, nat, BenchWorld.Bytes)
    requires i <= |format|
    requires nextArg <= |args|
    ensures 0 <= RenderPass(format, args, i, nextArg).0 <= 2
    ensures RenderPass(format, args, i, nextArg).0 == 0 ==>
              RenderPass(format, args, i, nextArg).3 == []
    ensures nextArg <= RenderPass(format, args, i, nextArg).2 <= |args|
    decreases |format| - i
  {
    if i >= |format| then
      (0, [], nextArg, [])
    else
      match ClassifyFragment(format, args, i, nextArg)
      case NoFragment => (2, [], nextArg, Spec.UnsupportedFormatMessage())
      case StopFragment(status, error) => (status, [], nextArg, error)
      case OneFragment(fragment) =>
        var rest := RenderPass(format, args, fragment.end, fragment.afterArg);
        (rest.0, fragment.output + rest.1, rest.2, rest.3)
  } by method {
    if i >= |format| {
      return (0, [], nextArg, []);
    } else {
      match ClassifyFragment(format, args, i, nextArg)
      case NoFragment =>
        return (2, [], nextArg, Spec.UnsupportedFormatMessage());
      case StopFragment(status, error) =>
        return (status, [], nextArg, error);
      case OneFragment(fragment) =>
        var rest := RenderPass(format, args, fragment.end, fragment.afterArg);
        return (rest.0, fragment.output + rest.1, rest.2, rest.3);
    }
  }

  function RenderRepeatedFrom(format: string, args: seq<string>, startArg: nat):
    (int, BenchWorld.Bytes, BenchWorld.Bytes)
    requires startArg <= |args|
    ensures 0 <= RenderRepeatedFrom(format, args, startArg).0 <= 2
    decreases |args| - startArg
  {
    var pass := RenderPass(format, args, 0, startArg);
    if pass.0 != 0 then
      (pass.0, pass.1, pass.3)
    else if pass.2 == startArg then
      if startArg == |args| then
        (0, pass.1, [])
      else
        (0, pass.1, Text.ExcessArgumentsWarning(args[startArg]))
    else if pass.2 >= |args| then
      (0, pass.1, [])
    else
      var rest := RenderRepeatedFrom(format, args, pass.2);
      (rest.0, pass.1 + rest.1, rest.2)
  } by method {
    var pass := RenderPass(format, args, 0, startArg);
    if pass.0 != 0 {
      return (pass.0, pass.1, pass.3);
    } else if pass.2 == startArg {
      if startArg == |args| {
        return (0, pass.1, []);
      } else {
        return (0, pass.1, Text.ExcessArgumentsWarning(args[startArg]));
      }
    } else if pass.2 >= |args| {
      return (0, pass.1, []);
    } else {
      assert startArg < pass.2 < |args|;
      var rest := RenderRepeatedFrom(format, args, pass.2);
      return (rest.0, pass.1 + rest.1, rest.2);
    }
  }

  function RenderRepeated(format: string, args: seq<string>):
    (int, BenchWorld.Bytes, BenchWorld.Bytes)
  {
    RenderRepeatedFrom(format, args, 0)
  } by method {
    return RenderRepeatedFrom(format, args, 0);
  }

  function Evaluate(raw: Schema.PrintfCmdRaw): (BenchWorld.Bytes, BenchWorld.Bytes, int)
  {
    if Schema.HelpSelected(raw) then
      (Spec.HelpText(), Text.RequestExcessWarning(raw), 0)
    else if Schema.VersionSelected(raw) then
      (Spec.VersionText(), Text.RequestExcessWarning(raw), 0)
    else if |raw.operands| == 0 then
      ([], Spec.MissingOperandMessage(), 1)
    else
      var rendered := RenderRepeated(raw.operands[0], raw.operands[1..]);
      (rendered.1, rendered.2, if rendered.0 == 2 then 1 else 0)
  } by method {
    if Schema.HelpSelected(raw) {
      return (Spec.HelpText(), Text.RequestExcessWarning(raw), 0);
    } else if Schema.VersionSelected(raw) {
      return (Spec.VersionText(), Text.RequestExcessWarning(raw), 0);
    } else if |raw.operands| == 0 {
      return ([], Spec.MissingOperandMessage(), 1);
    } else {
      var rendered := RenderRepeated(raw.operands[0], raw.operands[1..]);
      return (rendered.1, rendered.2, if rendered.0 == 2 then 1 else 0);
    }
  }

  twostate predicate PreparedSummary(raw: Schema.PrintfCmdRaw, io: BenchIO.IO, exit: int, plannedStdout: BenchWorld.Bytes, plannedStderr: BenchWorld.Bytes)

  {
    var result := Evaluate(raw);
    plannedStdout == old(io.stdout()) + result.0 &&
    plannedStderr == old(io.stderr()) + result.1 &&
    exit == result.2
  }

  method Prepare(raw: Schema.PrintfCmdRaw, io: BenchIO.IO) returns (exit: int, plannedOut: BenchWorld.Bytes, plannedErr: BenchWorld.Bytes)

    ensures PreparedSummary(raw, io, exit, old(io.stdout()) + plannedOut, old(io.stderr()) + plannedErr)
    decreases *
  {
    plannedOut := [];
    plannedErr := [];
    ghost var initialStdout := io.stdout();
    ghost var initialStderr := io.stderr();

    ghost var preStdout := (initialStdout + plannedOut);
    ghost var preStderr := (initialStderr + plannedErr);
    var result := Evaluate(raw);
    plannedOut := plannedOut + result.0;
    assert (initialStdout + plannedOut) == preStdout + result.0;
    plannedErr := plannedErr + result.1;
    assert (initialStderr + plannedErr) == preStderr + result.1;
    exit := result.2;
    assert PreparedSummary(raw, io, exit, old(io.stdout()) + plannedOut, old(io.stderr()) + plannedErr);
  }

  twostate predicate CoreSummary(raw: Schema.PrintfCmdRaw, io: BenchIO.IO, exit: int)
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
      errors := errors + Text.StreamWriteErrorMessage(message);
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

  method RunCore(raw: Schema.PrintfCmdRaw, io: BenchIO.IO) returns (exit: int)
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
