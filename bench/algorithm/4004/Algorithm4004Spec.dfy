include "../../core/Utf8.dfy"
include "Algorithm4004Schema.dfy"
include "../../core/IO.dfy"
include "../../core/IOContract.dfy"

module Algorithm4004Spec
{
  import BenchIO
  import BenchWorld
  import Utf8 = Utf8Semantics
  import C = IOContract
  import Schema = Algorithm4004Schema

  predicate Valid(raw: Schema.Algorithm4004CmdRaw)
  {
    raw.parsed && true
  }

  function InvalidInputText(): BenchWorld.Bytes { "algorithm4004: invalid input\n" }


  function IntegerText(value: int): string
    decreases if value < 0 then 1 else 0, if value < 0 then -value else value
  {
    if value < 0 then "-" + IntegerText(-value)
    else if value < 10 then [(('0' as int) + value) as char]
    else IntegerText(value / 10) + IntegerText(value % 10)
  }

  function LinesText(lines: seq<string>): string
    decreases |lines|
  {
    if |lines| == 0 then "" else lines[0] + "\n" + LinesText(lines[1..])
  }

  function OutputText(out: int): BenchWorld.Bytes
  {
    Utf8.Encode(IntegerText(out) + "\n")
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

  twostate predicate Spec(raw: Schema.Algorithm4004CmdRaw, io: BenchIO.IO, exit: int)
    reads io.stdoutRegion, io.stderrRegion, io.trustedStreamsRegion
  {
    if Valid(raw) then
      io.stderr() == old(io.stderr()) &&
      exists out: int ::
        Answer(raw.n, raw.a, out) && Output(io, OutputText(out), exit)
    else
      io.stdout() == old(io.stdout()) && InvalidInput(io, exit)
  }

  ghost predicate Answer(n: int, a: seq<int>, out: int)
  {
    if out == -1 then
      forall D: int :: D >= 0 ==> !IsFeasible(a, D)
    else
      out >= 0 &&
      IsFeasible(a, out) &&
      forall D: int :: 0 <= D < out ==> !IsFeasible(a, D)
  }

  /**
    * Determines whether for the given sequence a and non-negative integer D,
    * there exists a common target integer T and an assignment of operations (add D, subtract D, or do nothing)
    * applied to each element a[i], resulting in all elements equal to T.
    * Formally, there exists T such that for all i in [0..|a|),
    * a[i] + op_i = T where op_i ∈ { -D, 0, D }.
    * Returns false if no such assignment exists.
    *
    * @param a sequence of integers
    * @param D non-negative integer to add or subtract
    */
  ghost predicate IsFeasible(a: seq<int>, D: int)
  {
    exists T {:trigger AllCanAdjustTo(a, D, T)} :: AllCanAdjustTo(a, D, T)
  }

  ghost predicate AllCanAdjustTo(a: seq<int>, D: int, T: int)
  {
    forall i :: 0 <= i < |a| ==> CanAdjustTo(a[i], D, T)
  }

  /**
    * Returns true iff the element 'a_i' can be adjusted by adding -D, 0, or D to obtain 'T'.
    * Formally, there exists an op in {-D, 0, D} such that a_i + op = T.
    * @param a_i an integer element from the sequence
    * @param D a non-negative integer adjustment magnitude
    * @param T the target integer value to check adjustment feasibility
    */
  predicate CanAdjustTo(a_i: int, D: int, T: int)
  {
    T == a_i - D || T == a_i || T == a_i + D
  }
}
