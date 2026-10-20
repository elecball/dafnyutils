include "Algorithm59TextCore.dfy"
include "Algorithm59Schema.dfy"
include "../../core/IO.dfy"
include "Algorithm59Spec.dfy"

module Algorithm59Core {
  import BenchIO
  import BenchWorld
  import Schema = Algorithm59Schema
  import CliSpec = Algorithm59Spec
  import Text = Algorithm59TextCore

  twostate predicate CoreSummary(raw: Schema.Algorithm59CmdRaw, io: BenchIO.IO, exit: int)
    reads io.stdoutRegion, io.stderrRegion, io.trustedStreamsRegion
  {
    if CliSpec.Valid(raw) then
      io.stderr() == old(io.stderr()) &&
      exists output: string ::
        AnswerSummary(raw.n, raw.a, raw.s, output) && CliSpec.Output(io, CliSpec.OutputText(output), exit)
    else
      io.stdout() == old(io.stdout()) && CliSpec.InvalidInput(io, exit)
  }

  method RunCore(raw: Schema.Algorithm59CmdRaw, io: BenchIO.IO) returns (exit: int)
    requires CliSpec.Valid(raw) ==> ValidInput(raw.n, raw.a, raw.s)
    modifies io.stdoutRegion, io.stderrRegion
    ensures CoreSummary(raw, io, exit)
    decreases *
  {
    if !CliSpec.Valid(raw) {
      var written := io.WriteStderr(CliSpec.InvalidInputText());
      exit := if written.Err? then 1 else 2;
      return;
    }
    var output := Solve(raw.n, raw.a, raw.s);
    var text := Text.OutputText(output);
    var written := io.WriteStdout(text);
    exit := if written.Err? then 1 else 0;
  }

  import Spec = Algorithm59Spec

  predicate IsPermutation<T(==)>(a: seq<T>, b: seq<T>)
  {
    multiset(a) == multiset(b)
  }

  function Range(lo: int, hi: int): seq<int>
    decreases hi - lo
  {
    if lo >= hi then [] else [lo] + Range(lo + 1, hi)
  }

  predicate ValidInput(n: int, a: seq<int>, s: string)
  {
    1 <= n && n <= 200000 &&
    |a| == n &&
    |s| == n - 1 &&
    IsPermutation(a, Range(1, n + 1))
  }

  predicate IsAllowedSwap(s: string, i: int)
  {
    0 <= i < |s| && s[i] == '1'
  }

  function MaxR(s: string, n: int, start: int): int
    requires 1 <= start <= n
    requires |s| == n - 1
    ensures start <= MaxR(s, n, start) <= n
    decreases n - start
  {
    if start < n && IsAllowedSwap(s, start - 1) then MaxR(s, n, start + 1)
    else start
  }

  function Segments(s: string, n: int): seq<(int, int)>
    requires 1 <= n
    requires |s| == n - 1
  {
    SegmentsFrom(s, n, 1)
  }

  function SegmentsFrom(s: string, n: int, start: int): seq<(int,int)>
    requires 1 <= start
    requires 1 <= n
    requires |s| == n - 1
    decreases n - start + 1
  {
    if start > n then []
    else
      var r := MaxR(s, n, start);
      [(start, r)] + SegmentsFrom(s, n, r + 1)
  }

  predicate SegmentGood(a: seq<int>, seg: (int, int))
  {
    1 <= seg.0 <= seg.1 <= |a| &&
    IsPermutation(a[seg.0 - 1 .. seg.1], Range(seg.0, seg.1 + 1))
  }

  predicate AllSegmentsGood(n: int, a: seq<int>, s: string)
    requires ValidInput(n, a, s)
  {
    forall seg :: seg in Segments(s, n) ==> SegmentGood(a, seg)
  }

  predicate AnswerSummary(n: int, a: seq<int>, s: string, output: string)
  {
    ValidInput(n, a, s) &&
    (
      (AllSegmentsGood(n, a, s) && output == Spec.PositiveResult()) ||
      (!AllSegmentsGood(n, a, s) && output == Spec.NegativeResult())
    )
  }

  method Solve(n: int, a: seq<int>, s: string) returns (output: string)
    requires ValidInput(n, a, s)
    ensures AnswerSummary(n, a, s, output)
  {
    if AllSegmentsGood(n, a, s) {
      output := Spec.PositiveResult();
    } else {
      output := Spec.NegativeResult();
    }
  }
}
