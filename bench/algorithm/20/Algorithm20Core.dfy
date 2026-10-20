include "Algorithm20TextCore.dfy"
include "Algorithm20Schema.dfy"
include "../../core/IO.dfy"
include "Algorithm20Spec.dfy"

module Algorithm20Core {
  import BenchIO
  import BenchWorld
  import Schema = Algorithm20Schema
  import CliSpec = Algorithm20Spec
  import Text = Algorithm20TextCore

  twostate predicate CoreSummary(raw: Schema.Algorithm20CmdRaw, io: BenchIO.IO, exit: int)
    reads io.stdoutRegion, io.stderrRegion, io.trustedStreamsRegion
  {
    if CliSpec.Valid(raw) then
      io.stderr() == old(io.stderr()) &&
      exists result: int ::
        AnswerSummary(raw.time, result) && CliSpec.Output(io, CliSpec.OutputText(result), exit)
    else
      io.stdout() == old(io.stdout()) && CliSpec.InvalidInput(io, exit)
  }

  method RunCore(raw: Schema.Algorithm20CmdRaw, io: BenchIO.IO) returns (exit: int)
    modifies io.stdoutRegion, io.stderrRegion
    ensures CoreSummary(raw, io, exit)
    decreases *
  {
    if !CliSpec.Valid(raw) {
      var written := io.WriteStderr(CliSpec.InvalidInputText());
      exit := if written.Err? then 1 else 2;
      return;
    }
    var result := Solve(raw.time);
    var text := Text.OutputText(result);
    var written := io.WriteStdout(text);
    exit := if written.Err? then 1 else 0;
  }

  import Spec = Algorithm20Spec

  function CharToNat(c: char): int
  {
    (c as int) - ('0' as int)
  }

  function NatToChar(n: int): char
  {
    if 0 <= n <= 9 then (n + ('0' as int)) as char else '0'
  }

  function TimeToMinutes(time: string): int
    requires |time| == 5
  {
    var h0 := CharToNat(time[0]);
    var h1 := CharToNat(time[1]);
    var m0 := CharToNat(time[3]);
    var m1 := CharToNat(time[4]);
    (h0 * 10 + h1) * 60 + (m0 * 10 + m1)
  }

  function TwoDigitStr(n: int): string
  {
    var t := NatToChar(n / 10);
    var u := NatToChar(n % 10);
    [t] + [u]
  }

  function MinutesToTime(m: int): string
  {
    var hours := m / 60;
    var minutes := m % 60;
    TwoDigitStr(hours) + [Spec.TimeSeparator()] + TwoDigitStr(minutes)
  }

  function IsPalindromeTime(t: string): bool
  {
    |t| == 5 &&
    t[2] == Spec.TimeSeparator() &&
    t[0] == t[4] &&
    t[1] == t[3]
  }

  function PalindromeAfter(time: string, result: int): bool
    requires |time| == 5
  {
    var totalMinutes := TimeToMinutes(time);
    IsPalindromeTime(MinutesToTime((totalMinutes + result) % 1440))
  }

  method Solve(time: string) returns (result: int)
    requires |time| == 5
    ensures AnswerSummary(time, result)
    decreases *
  {
    result := 0;
    while !PalindromeAfter(time, result)
      invariant 0 <= result
      invariant forall k: int :: 0 <= k < result ==> !PalindromeAfter(time, k)
      decreases *
    {
      result := result + 1;
    }
  }

  ghost predicate AnswerSummary(time: string, result: int)
  {
    |time| == 5 &&
    0 <= result &&
    PalindromeAfter(time, result) &&
    forall k: int :: 0 <= k < result ==> !PalindromeAfter(time, k)
  }
}
