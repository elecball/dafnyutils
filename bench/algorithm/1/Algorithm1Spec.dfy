include "../../core/Utf8.dfy"
include "Algorithm1Schema.dfy"
include "../../core/IO.dfy"
include "../../core/IOContract.dfy"

module Algorithm1Spec
{
  import BenchIO
  import BenchWorld
  import Utf8 = Utf8Semantics
  import C = IOContract
  import Schema = Algorithm1Schema

  predicate Valid(raw: Schema.Algorithm1CmdRaw)
  {
    raw.parsed && raw.x >= 1
  }

  function InvalidInputText(): BenchWorld.Bytes { "algorithm1: invalid input\n" }


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

  function OutputText(result: int): BenchWorld.Bytes
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

  twostate predicate Spec(raw: Schema.Algorithm1CmdRaw, io: BenchIO.IO, exit: int)
    reads io.stdoutRegion, io.stderrRegion, io.trustedStreamsRegion
  {
    if Valid(raw) then
      io.stderr() == old(io.stderr()) &&
      exists result: int ::
        Answer(raw.x, result) && Output(io, OutputText(result), exit)
    else
      io.stdout() == old(io.stdout()) && InvalidInput(io, exit)
  }

  predicate Answer(x: int, result: int)
  {
    1 <= result <= x
    &&
    (forall t :: 1 <= t <= x ==> SumOfDigits(result) >= SumOfDigits(t))
    &&
    (forall t :: 1 <= t <= x && SumOfDigits(t) == SumOfDigits(result) ==> t <= result)
  }

  /**
    * Returns the sum of decimal digits of the positive integer n.
    * For example, SumOfDigits(521) == 5 + 2 + 1 == 8.
    * It holds that SumOfDigits(n) >= 0 for all n >= 0.
    * Precondition: n >= 0.
    * Note: Leading zeros do not affect the sum.
    * @param n the integer whose decimal digits are summed
    * @return the sum of digits of n
    */
  function SumOfDigits(n: int): int
    decreases n
  {
    if n <= 0 then 0 else (n % 10) + SumOfDigits(n / 10)
  }
}
