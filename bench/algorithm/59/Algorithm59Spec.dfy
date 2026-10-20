include "../../core/Utf8.dfy"
include "Algorithm59Schema.dfy"
include "../../core/IO.dfy"
include "../../core/IOContract.dfy"

module Algorithm59Spec
{
  import BenchIO
  import BenchWorld
  import Utf8 = Utf8Semantics
  import C = IOContract
  import Schema = Algorithm59Schema

  predicate Valid(raw: Schema.Algorithm59CmdRaw)
  {
    raw.parsed && ValidInput(raw.n, raw.a, raw.s)
  }

  function InvalidInputText(): BenchWorld.Bytes { "algorithm59: invalid input\n" }


  ghost function OutputText(output: string): BenchWorld.Bytes
  {
    Utf8.Encode(output + "\n")
  }

  twostate predicate Output(io: BenchIO.IO, text: BenchWorld.Bytes, exit: int)
    reads io.stdoutRegion, io.trustedStreamsRegion
  {
    exists committed: nat, err: int ::
      C.TrustedWriteStdoutWithOutcomeContractFields(
        old(io.trustedStreams()), old(io.stdout()), io.stdout(), text, committed, err) &&
      exit == (if err == 0 then 0 else 1)
  }

  twostate predicate InvalidInput(io: BenchIO.IO, exit: int)
    reads io.stderrRegion, io.trustedStreamsRegion
  {
    exists committed: nat, err: int ::
      C.TrustedWriteStderrWithOutcomeContractFields(
        old(io.trustedStreams()), old(io.stderr()), io.stderr(), InvalidInputText(), committed, err) &&
      exit == (if err == 0 then 2 else 1)
  }

  twostate predicate Spec(raw: Schema.Algorithm59CmdRaw, io: BenchIO.IO, exit: int)
    reads io.stdoutRegion, io.stderrRegion, io.trustedStreamsRegion
  {
    if Valid(raw) then
      io.stderr() == old(io.stderr()) &&
      exists output: string ::
        Answer(raw.n, raw.a, raw.s, output) && Output(io, OutputText(output), exit)
    else
      io.stdout() == old(io.stdout()) && InvalidInput(io, exit)
  }

  function PositiveResult(): string
  {
    "YES"
  }

  function NegativeResult(): string
  {
    "NO"
  }

  predicate {:fuel 100} IsPermutation<T(==)>(a: seq<T>, b: seq<T>)
  {
    multiset(a) == multiset(b)
  }

  function {:fuel 100} Range(lo: int, hi: int): seq<int>
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

  ghost predicate Answer(n: int, a: seq<int>, s: string, output: string)
  {
    ValidInput(n, a, s) &&
    (
      (Sortable(n, a, s) && output == PositiveResult()) ||
      (!Sortable(n, a, s) && output == NegativeResult())
    )
  }

  ghost predicate Sortable(n: int, a: seq<int>, s: string)
    requires |a| == n
  {
    forall lo, hi ::
      IsSwapSegment(s, n, lo, hi) ==>
        IsPermutation(a[lo - 1 .. hi], Range(lo, hi + 1))
  }

  predicate IsSwapSegment(s: string, n: int, lo: int, hi: int)
  {
    1 <= lo <= hi <= n &&
    (lo == 1 || !IsAllowedSwap(s, lo - 2)) &&
    (hi == n || !IsAllowedSwap(s, hi - 1)) &&
    forall i :: lo - 1 <= i < hi - 1 ==> IsAllowedSwap(s, i)
  }

  /**
    * Returns true iff the character at index i in the swap string s is '1',
    * indicating that a swap between positions i+1 and i+2 is allowed.
    * @param s The swap indicator string of length n-1.
    * @param i The zero-based index in s to check (0 ≤ i < |s|).
    */
  predicate IsAllowedSwap(s: string, i: int)
  {
    0 <= i < |s| && s[i] == '1'
  }
}
