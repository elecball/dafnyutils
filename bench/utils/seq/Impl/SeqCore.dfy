include "../Spec/SeqSpec.dfy"
include "../../../core/IOContract.dfy"
include "../../../core/World.dfy"
include "../../../core/IO.dfy"
include "../Spec/SeqSchema.dfy"

module SeqCore {
  import StreamContract = IOContract

  import Result = Results
  import BenchIO
  import BenchWorld
  import SeqSchema
  import Spec = SeqSpec

  datatype Decimal = Decimal(raw: string, value: int, scale: nat, negativeZero: bool)
  type DecimalParse = Result.Result<Decimal, string>
  datatype Scan = Scan(ok: bool, sawDigit: bool, sawDot: bool, mantissa: int, scale: nat)
  datatype NatScan = NatScan(ok: bool, sawDigit: bool, value: nat)
  datatype ExponentParse = ExponentOk(value: int) | ExponentErr
  datatype NumberPlan =
    | NumbersOk(first: Decimal, step: Decimal, last: Decimal)
    | NumbersErr(stderr: BenchWorld.Bytes)
  datatype RunResult = RunResult(stdout: BenchWorld.Bytes, stderr: BenchWorld.Bytes, exit: int)

  function ScanDecimal(text: string, i: nat, sawDot: bool, sawDigit: bool, mantissa: int, scale: nat): Scan
    requires i <= |text|
    requires 0 <= mantissa
    decreases |text| - i
  {
    if i >= |text| then
      Scan(true, sawDigit, sawDot, mantissa, scale)
    else if Spec.IsDigit(text[i]) then
      ScanDecimal(
        text,
        i + 1,
        sawDot,
        true,
        mantissa * 10 + Spec.DigitAt(text[i]),
        if sawDot then scale + 1 else scale
      )
    else if text[i] == '.' && !sawDot then
      ScanDecimal(text, i + 1, true, sawDigit, mantissa, scale)
    else
      Scan(false, sawDigit, sawDot, mantissa, scale)
  } by method
  {
    if i >= |text| {
      return Scan(true, sawDigit, sawDot, mantissa, scale);
    } else if '0' <= text[i] <= '9' {
      return ScanDecimal(
          text,
          i + 1,
          sawDot,
          true,
          mantissa * 10 + ((text[i] as int) - ('0' as int)),
          if sawDot then scale + 1 else scale
        );
    } else if text[i] == '.' && !sawDot {
      return ScanDecimal(text, i + 1, true, sawDigit, mantissa, scale);
    } else {
      return Scan(false, sawDigit, sawDot, mantissa, scale);
    }
  }


  function ExponentIndex(text: string, i: nat): int
    requires i <= |text|
    ensures ExponentIndex(text, i) == -1 || i <= ExponentIndex(text, i) < |text|
    decreases |text| - i
  {
    if i >= |text| then
      -1
    else if text[i] == 'e' || text[i] == 'E' then
      i
    else
      ExponentIndex(text, i + 1)
  } by method
  {
    if i >= |text| {
      return -1;
    } else if text[i] == 'e' || text[i] == 'E' {
      return i;
    } else {
      return ExponentIndex(text, i + 1);
    }
  }

  function ScanNat(text: string, i: nat, sawDigit: bool, value: nat): NatScan
    requires i <= |text|
    decreases |text| - i
  {
    if i >= |text| then
      NatScan(true, sawDigit, value)
    else if Spec.IsDigit(text[i]) then
      ScanNat(text, i + 1, true, (value * 10 + Spec.DigitAt(text[i])) as nat)
    else
      NatScan(false, sawDigit, value)
  } by method
  {
    if i >= |text| {
      return NatScan(true, sawDigit, value);
    } else if '0' <= text[i] <= '9' {
      var digit := (text[i] as int) - ('0' as int);
      return ScanNat(text, i + 1, true, (value * 10 + digit) as nat);
    } else {
      return NatScan(false, sawDigit, value);
    }
  }

  function ParseExponent(text: string): ExponentParse
  {
    if |text| == 0 then
      ExponentErr
    else
      var negative := text[0] == '-';
      var start := if text[0] == '-' || text[0] == '+' then 1 else 0;
      if start >= |text| then
        ExponentErr
      else
        var scanned := ScanNat(text, start, false, 0);
        if scanned.ok && scanned.sawDigit then
          ExponentOk(if negative then -(scanned.value as int) else scanned.value as int)
        else
          ExponentErr
  } by method
  {
    if |text| == 0 {
      return ExponentErr;
    }
    var negative := text[0] == '-';
    var start := if text[0] == '-' || text[0] == '+' then 1 else 0;
    if start >= |text| {
      return ExponentErr;
    }
    var scanned := ScanNat(text, start, false, 0);
    if scanned.ok && scanned.sawDigit {
      return ExponentOk(if negative then -(scanned.value as int) else scanned.value as int);
    }
    return ExponentErr;
  }

  function ApplyExponent(token: string, value: int, scale: nat, negativeZero: bool, exponent: int): Decimal
  {
    if exponent >= 0 then
      var positiveExponent := exponent as nat;
      if positiveExponent <= scale then
        Decimal(token, value, scale - positiveExponent, negativeZero)
      else
        Decimal(token, value * Spec.Pow10(positiveExponent - scale), 0, negativeZero)
    else
      Decimal(token, value, scale + ((-exponent) as nat), negativeZero)
  } by method
  {
    if exponent >= 0 {
      var positiveExponent := exponent as nat;
      if positiveExponent <= scale {
        return Decimal(token, value, scale - positiveExponent, negativeZero);
      }
      var factor := Spec.Pow10(positiveExponent - scale);
      return Decimal(token, value * factor, 0, negativeZero);
    }
    return Decimal(token, value, scale + ((-exponent) as nat), negativeZero);
  }

  function ParseDecimal(token: string): DecimalParse
  {
    if |token| == 0 then
      Result.Err(token)
    else
      var negative := token[0] == '-';
      var start := if token[0] == '-' || token[0] == '+' then 1 else 0;
      if start >= |token| then
        Result.Err(token)
      else
        var exponentIndex := ExponentIndex(token, start);
        var mantissaText := if exponentIndex < 0 then token else token[..exponentIndex];
        var scanned := ScanDecimal(mantissaText, start, false, false, 0, 0);
        if scanned.ok && scanned.sawDigit then
          var value := if negative then -scanned.mantissa else scanned.mantissa;
          var negativeZero := negative && scanned.mantissa == 0;
          if exponentIndex < 0 then
            Result.Ok(Decimal(token, value, scanned.scale, negativeZero))
          else
            var exponentText := token[exponentIndex + 1..];
            var exponentParse := ParseExponent(exponentText);
            match exponentParse
            case ExponentErr =>
              Result.Err(token)
            case ExponentOk(exponent) =>
              Result.Ok(ApplyExponent(token, value, scanned.scale, negativeZero, exponent))
        else
          Result.Err(token)
  } by method
  {
    if |token| == 0 {
      return Result.Err(token);
    }
    var negative := token[0] == '-';
    var start := if token[0] == '-' || token[0] == '+' then 1 else 0;
    if start >= |token| {
      return Result.Err(token);
    }
    var exponentIndex := ExponentIndex(token, start);
    var mantissaText := if exponentIndex < 0 then token else token[..exponentIndex];
    var scanned := ScanDecimal(mantissaText, start, false, false, 0, 0);
    if !scanned.ok || !scanned.sawDigit {
      return Result.Err(token);
    }
    var value := if negative then -scanned.mantissa else scanned.mantissa;
    var negativeZero := negative && scanned.mantissa == 0;
    if exponentIndex < 0 {
      return Result.Ok(Decimal(token, value, scanned.scale, negativeZero));
    }
    var exponentText := token[exponentIndex + 1..];
    match ParseExponent(exponentText)
    case ExponentErr =>
      return Result.Err(token);
    case ExponentOk(exponent) =>
      return Result.Ok(ApplyExponent(token, value, scanned.scale, negativeZero, exponent));
  }

  function ParseNumbers(args: seq<string>): NumberPlan
  {
    if |args| == 0 then
      NumbersErr(Spec.MissingOperandMessage())
    else if |args| > 3 then
      NumbersErr(Spec.ExtraOperandMessage(args[3]))
    else
      var firstText := if |args| == 1 then "1" else args[0];
      var stepText := if |args| == 3 then args[1] else "1";
      var lastText := if |args| == 1 then args[0] else if |args| == 2 then args[1] else args[2];
      var firstParse := ParseDecimal(firstText);
      match firstParse
      case Err(token) =>
        NumbersErr(Spec.InvalidNumberMessage(token))
      case Ok(first) =>
        var stepParse := ParseDecimal(stepText);
        match stepParse
        case Err(token) =>
          NumbersErr(Spec.InvalidNumberMessage(token))
        case Ok(step) =>
          if step.value == 0 then
            NumbersErr(Spec.ZeroIncrementMessage(step.raw))
          else
            var lastParse := ParseDecimal(lastText);
            match lastParse
            case Err(token) =>
              NumbersErr(Spec.InvalidNumberMessage(token))
            case Ok(last) =>
              NumbersOk(first, step, last)
  } by method
  {
    if |args| == 0 {
      var message := MissingOperandMessageRuntime();
      return NumbersErr(message);
    }
    if |args| > 3 {
      var message := ExtraOperandMessageRuntime(args[3]);
      return NumbersErr(message);
    }
    var firstText := if |args| == 1 then "1" else args[0];
    var stepText := if |args| == 3 then args[1] else "1";
    var lastText := if |args| == 1 then args[0] else if |args| == 2 then args[1] else args[2];
    match ParseDecimal(firstText)
    case Err(token) =>
      var message := InvalidNumberMessageRuntime(token);
      return NumbersErr(message);
    case Ok(first) =>
      match ParseDecimal(stepText)
      case Err(token) =>
        var message := InvalidNumberMessageRuntime(token);
        return NumbersErr(message);
      case Ok(step) =>
        if step.value == 0 {
          var message := ZeroIncrementMessageRuntime(step.raw);
          return NumbersErr(message);
        }
        match ParseDecimal(lastText)
        case Err(token) =>
          var message := InvalidNumberMessageRuntime(token);
          return NumbersErr(message);
        case Ok(last) =>
          return NumbersOk(first, step, last);
  }

  function MaxScale(first: Decimal, step: Decimal, last: Decimal): nat
  {
    Spec.MaxNat(first.scale, Spec.MaxNat(step.scale, last.scale))
  } by method
  {
    var stepLast := Spec.MaxNat(step.scale, last.scale);
    return Spec.MaxNat(first.scale, stepLast);
  }

  function Rescale(d: Decimal, scale: nat): int
    requires d.scale <= scale
  {
    d.value * Spec.Pow10(scale - d.scale)
  } by method
  {
    return d.value * Spec.Pow10(scale - d.scale);
  }

  function GenerateValues(current: int, step: int, count: nat): seq<int>
    decreases count
  {
    if count == 0 then
      []
    else
      [current] + GenerateValues(current + step, step, count - 1)
  } by method
  {
    var i := count;
    var values: seq<int> := [];
    while i > 0
      invariant 0 <= i <= count
      invariant values == GenerateValues(current + step * i, step, count - i)
      decreases i
    {
      i := i - 1;
      values := [current + step * i] + values;
    }
    return values;
  }

  function RenderValues(values: seq<int>, scale: nat, firstNegativeZero: bool): seq<BenchWorld.Bytes>
    decreases |values|
  {
    if |values| == 0 then
      []
    else
      [Spec.RenderFixed(values[0], scale, firstNegativeZero)] + RenderValues(values[1..], scale, false)
  } by method
  {
    var i := |values|;
    var rendered: seq<BenchWorld.Bytes> := [];
    while i > 0
      invariant 0 <= i <= |values|
      invariant rendered == RenderValues(values[i..], scale, if i == 0 then firstNegativeZero else false)
      decreases i
    {
      i := i - 1;
      rendered := [Spec.RenderFixed(values[i], scale, if i == 0 then firstNegativeZero else false)] + rendered;
    }
    return rendered;
  }

  function MaxWidth(items: seq<BenchWorld.Bytes>): nat
    decreases |items|
  {
    if |items| == 0 then
      0
    else
      Spec.MaxNat(|items[0]|, MaxWidth(items[1..]))
  } by method
  {
    var i := |items|;
    var width: nat := 0;
    while i > 0
      invariant 0 <= i <= |items|
      invariant width == MaxWidth(items[i..])
      decreases i
    {
      i := i - 1;
      width := Spec.MaxNat(|items[i]|, width);
    }
    return width;
  }

  function PadValues(items: seq<BenchWorld.Bytes>, width: nat): seq<BenchWorld.Bytes>
    decreases |items|
  {
    if |items| == 0 then
      []
    else
      [Spec.PadNumber(items[0], width)] + PadValues(items[1..], width)
  } by method
  {
    var i := |items|;
    var padded: seq<BenchWorld.Bytes> := [];
    while i > 0
      invariant 0 <= i <= |items|
      invariant padded == PadValues(items[i..], width)
      decreases i
    {
      i := i - 1;
      padded := [Spec.PadNumber(items[i], width)] + padded;
    }
    return padded;
  }

  function JoinItems(items: seq<BenchWorld.Bytes>, separator: BenchWorld.Bytes): BenchWorld.Bytes
    decreases |items|
  {
    if |items| == 0 then
      []
    else if |items| == 1 then
      items[0] + ['\n']
    else
      items[0] + separator + JoinItems(items[1..], separator)
  } by method
  {
    var i := |items|;
    var out: BenchWorld.Bytes := [];
    while i > 0
      invariant 0 <= i <= |items|
      invariant out == JoinItems(items[i..], separator)
      decreases i
    {
      i := i - 1;
      if i == |items| - 1 {
        out := items[i] + ['\n'];
      } else {
        out := items[i] + separator + out;
      }
    }
    return out;
  }

  function RenderSequence(first: Decimal, step: Decimal, last: Decimal, equalWidth: bool, separator: BenchWorld.Bytes): BenchWorld.Bytes
    requires step.value != 0
  {
    var scale := MaxScale(first, step, last);
    var firstValue := Rescale(first, scale);
    var stepValue := Rescale(step, scale);
    var lastValue := Rescale(last, scale);
    var values := GenerateValues(firstValue, stepValue, Spec.TermCount(firstValue, stepValue, lastValue));
    var rendered := RenderValues(values, scale, first.negativeZero && first.value == 0);
    var padded := if equalWidth then PadValues(rendered, MaxWidth(rendered)) else rendered;
    JoinItems(padded, separator)
  } by method
  {
    var scale := MaxScale(first, step, last);
    var firstValue := Rescale(first, scale);
    var stepValue := Rescale(step, scale);
    var lastValue := Rescale(last, scale);
    var count := Spec.TermCount(firstValue, stepValue, lastValue);
    var values := GenerateValues(firstValue, stepValue, count);
    var rendered := RenderValues(values, scale, first.negativeZero && first.value == 0);
    var padded := if equalWidth then PadValues(rendered, MaxWidth(rendered)) else rendered;
    return JoinItems(padded, separator);
  }

  function Evaluate(raw: SeqSchema.SeqCmdRaw): RunResult
  {
    if Spec.HelpSelected(raw) then
      RunResult(Spec.HelpText(), [], 0)
    else if Spec.VersionSelected(raw) then
      RunResult(Spec.VersionText(), [], 0)
    else
      var plan := ParseNumbers(raw.operands);
      match plan
      case NumbersErr(stderr) =>
        RunResult([], stderr, 1)
      case NumbersOk(first, step, last) =>
        RunResult(RenderSequence(first, step, last, raw.equalWidth, Spec.Separator(raw)), [], 0)
  } by method
  {
    if Spec.HelpSelected(raw) {
      var out := GetHelpText();
      return RunResult(out, [], 0);
    }
    if Spec.VersionSelected(raw) {
      var out := GetVersionText();
      return RunResult(out, [], 0);
    }
    match ParseNumbers(raw.operands)
    case NumbersErr(stderr) =>
      return RunResult([], stderr, 1);
    case NumbersOk(first, step, last) =>
      var separator := Spec.Separator(raw);
      return RunResult(
          RenderSequence(first, step, last, raw.equalWidth, separator),
          [],
          0
        );
  }

  twostate predicate PreparedSummary(raw: SeqSchema.SeqCmdRaw, io: BenchIO.IO, exit: int, plannedStdout: BenchWorld.Bytes, plannedStderr: BenchWorld.Bytes)

  {
    var result := Evaluate(raw);
    plannedStdout == old(io.stdout()) + result.stdout &&
    plannedStderr == old(io.stderr()) + result.stderr &&
    exit == result.exit
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

  method MissingOperandMessageRuntime() returns (message: BenchWorld.Bytes)
    ensures message == Spec.MissingOperandMessage()
  {
    message := Spec.MissingOperandMessage();
  }

  method ExtraOperandMessageRuntime(token: string) returns (message: BenchWorld.Bytes)
    ensures message == Spec.ExtraOperandMessage(token)
  {
    message := Spec.ExtraOperandMessage(token);
  }

  method InvalidNumberMessageRuntime(token: string) returns (message: BenchWorld.Bytes)
    ensures message == Spec.InvalidNumberMessage(token)
  {
    message := Spec.InvalidNumberMessage(token);
  }

  method ZeroIncrementMessageRuntime(token: string) returns (message: BenchWorld.Bytes)
    ensures message == Spec.ZeroIncrementMessage(token)
  {
    message := Spec.ZeroIncrementMessage(token);
  }

  method Prepare(raw: SeqSchema.SeqCmdRaw, io: BenchIO.IO) returns (exit: int, plannedOut: BenchWorld.Bytes, plannedErr: BenchWorld.Bytes)

    ensures PreparedSummary(raw, io, exit, old(io.stdout()) + plannedOut, old(io.stderr()) + plannedErr)
    decreases *
  {
    plannedOut := [];
    plannedErr := [];
    ghost var initialStdout := io.stdout();
    ghost var initialStderr := io.stderr();

    var result := Evaluate(raw);
    plannedOut := plannedOut + result.stdout;
    plannedErr := plannedErr + result.stderr;
    exit := result.exit;
    assert PreparedSummary(raw, io, exit, old(io.stdout()) + plannedOut, old(io.stderr()) + plannedErr);
  }

  twostate predicate CoreSummary(raw: SeqSchema.SeqCmdRaw, io: BenchIO.IO, exit: int)
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

  method RunCore(raw: SeqSchema.SeqCmdRaw, io: BenchIO.IO) returns (exit: int)
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
