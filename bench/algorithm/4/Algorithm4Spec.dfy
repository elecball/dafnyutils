include "../../core/Utf8.dfy"
include "Algorithm4Schema.dfy"
include "../../core/IO.dfy"
include "../../core/IOContract.dfy"

module Algorithm4Spec
{
  import BenchIO
  import BenchWorld
  import Utf8 = Utf8Semantics
  import C = IOContract
  import Schema = Algorithm4Schema

  predicate Valid(raw: Schema.Algorithm4CmdRaw)
  {
    raw.parsed && true
  }

  function InvalidInputText(): BenchWorld.Bytes { "algorithm4: invalid input\n" }


  ghost function IntegerText(value: int): string
    decreases if value < 0 then 1 else 0, if value < 0 then -value else value
  {
    if value < 0 then "-" + IntegerText(-value)
    else if value < 10 then [(('0' as int) + value) as char]
    else IntegerText(value / 10) + IntegerText(value % 10)
  }

  ghost function OutputText(y: int): BenchWorld.Bytes
  {
    Utf8.Encode(IntegerText(y) + "\n")
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

  twostate predicate Spec(raw: Schema.Algorithm4CmdRaw, io: BenchIO.IO, exit: int)
    reads io.stdoutRegion, io.stderrRegion, io.trustedStreamsRegion
  {
    if Valid(raw) then
      io.stderr() == old(io.stderr()) &&
      exists y: int ::
        Answer(raw.x, raw.hh, raw.mm, y) && Output(io, OutputText(y), exit)
    else
      io.stdout() == old(io.stdout()) && InvalidInput(io, exit)
  }

  predicate Answer(x: int, hh: int, mm: int, y: int)
  {
    var total := hh * 60 + mm;
    0 <= y &&
    IsLuckyTime(((total - x * y) % 1440 + 1440) % 1440 / 60, ((total - x * y) % 1440 + 1440) % 1440 % 60) &&
    forall z :: 0 <= z < y ==>
                  !IsLuckyTime(((total - x * z) % 1440 + 1440) % 1440 / 60, ((total - x * z) % 1440 + 1440) % 1440 % 60)
  }

  predicate IsLuckyTime(h: int, m: int)
  {
    ContainsDigit7(h) || ContainsDigit7(m)
  }

  predicate ContainsDigit7(x: int)
  {
    x >= 0 &&
    (
      (x % 10 == 7) ||
      (x >= 10 && ContainsDigit7(x / 10))
    )
  }
}
