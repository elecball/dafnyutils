include "../../core/Utf8.dfy"
include "Algorithm63Schema.dfy"
include "../../core/IO.dfy"
include "../../core/IOContract.dfy"

module Algorithm63Spec
{
  import BenchIO
  import BenchWorld
  import Utf8 = Utf8Semantics
  import C = IOContract
  import Schema = Algorithm63Schema

  predicate Valid(raw: Schema.Algorithm63CmdRaw)
  {
    raw.parsed && 0 <= raw.n && |raw.a| == raw.n
  }

  function InvalidInputText(): BenchWorld.Bytes { "algorithm63: invalid input\n" }


  ghost function IntegerText(value: int): string
    decreases if value < 0 then 1 else 0, if value < 0 then -value else value
  {
    if value < 0 then "-" + IntegerText(-value)
    else if value < 10 then [(('0' as int) + value) as char]
    else IntegerText(value / 10) + IntegerText(value % 10)
  }

  ghost function OutputText(result: int): BenchWorld.Bytes
  {
    Utf8.Encode(IntegerText(result) + "\n")
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

  twostate predicate Spec(raw: Schema.Algorithm63CmdRaw, io: BenchIO.IO, exit: int)
    reads io.stdoutRegion, io.stderrRegion, io.trustedStreamsRegion
  {
    if Valid(raw) then
      io.stderr() == old(io.stderr()) &&
      exists result: int ::
        Answer(raw.n, raw.k, raw.a, result) && Output(io, OutputText(result), exit)
    else
      io.stdout() == old(io.stdout()) && InvalidInput(io, exit)
  }

  function {:fuel 100} Product(s: seq<int>): int
  {
    if |s| == 0 then 1 else s[0] * Product(s[1..])
  }

  ghost function ValidSubdecks(a: seq<int>, k: int): set<(int, int)>
  {
    set x: int, y: int |
      0 <= x < |a| && 0 <= y < |a| && x + y < |a| &&
      IsValidSubdeck(a, x, y, k)
      :: (x, y)
  }

  ghost predicate Answer(n: int, k: int, a: seq<int>, result: int) {
    0 <= n &&
    |a| == n &&
    result == |ValidSubdecks(a, k)|
  }

  predicate IsValidSubdeck(a: seq<int>, x: int, y: int, k: int)
  {
    // The subdeck must be non-empty: x + y < |a|
    0 <= x && 0 <= y && x + y < |a| &&
    // The product of the subdeck elements is divisible by k
    SubdeckProductDivisible(a, x, y, k)
  }

  predicate SubdeckProductDivisible(a: seq<int>, x: int, y: int, k: int)
  {
    0 <= x && 0 <= y && x + y < |a| &&
    // Define the subdeck by slicing the sequence
    var subdeck := a[x .. |a| - y];

    // Divisibility condition: k divides the product of subdeck's elements
    k != 0 && Product(subdeck) % k == 0
  }
}
