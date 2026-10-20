include "../../core/Utf8.dfy"
include "Algorithm38Schema.dfy"
include "../../core/IO.dfy"
include "../../core/IOContract.dfy"

module Algorithm38Spec
{
  import BenchIO
  import BenchWorld
  import Utf8 = Utf8Semantics
  import C = IOContract
  import Schema = Algorithm38Schema

  predicate Valid(raw: Schema.Algorithm38CmdRaw)
  {
    raw.parsed && ValidInput(raw.n, raw.L, raw.kefa, raw.sasha)
  }

  function InvalidInputText(): BenchWorld.Bytes { "algorithm38: invalid input\n" }


  ghost function OutputText(result: string): BenchWorld.Bytes
  {
    Utf8.Encode(result + "\n")
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

  twostate predicate Spec(raw: Schema.Algorithm38CmdRaw, io: BenchIO.IO, exit: int)
    reads io.stdoutRegion, io.stderrRegion, io.trustedStreamsRegion
  {
    if Valid(raw) then
      io.stderr() == old(io.stderr()) &&
      exists result: string ::
        Answer(raw.n, raw.L, raw.kefa, raw.sasha, result) && Output(io, OutputText(result), exit)
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

  predicate {:fuel 100} IsSorted(s: seq<int>)
  {
    forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
  }

  predicate ValidInput(n: int, L: int, kefa: seq<int>, sasha: seq<int>)
  {
    n >= 1 && n <= 50 &&
    L >= n && L <= 100 &&
    |kefa| == n && |sasha| == n &&
    IsSorted(kefa) && IsSorted(sasha) &&
    (forall x :: x in kefa ==> 0 <= x < L) &&
    (forall x :: x in sasha ==> 0 <= x < L)
  }

  predicate Answer(n: int, L: int, kefa: seq<int>, sasha: seq<int>, result: string) {
    // Preconditions on inputs: sizes and domain
    ValidInput(n, L, kefa, sasha) &&
    (
      (HasRotation(n, L, kefa, sasha) && result == PositiveResult()) ||
      (!HasRotation(n, L, kefa, sasha) && result == NegativeResult())
    )
  }

  predicate HasRotation(n: int, L: int, kefa: seq<int>, sasha: seq<int>)
  {
    exists offset ::
      0 <= offset < n &&
      IsRotation(DistSeq(kefa, L), DistSeq(sasha, L), offset)
  }

  function DistSeq(p: seq<int>, L: int): seq<int>
  {
    if |p| == 0 then
      []
    else
      // Differences between consecutive barriers
      seq(|p|, i =>
        if 0 <= i && i + 1 < |p| then
          p[i + 1] - p[i]
        else // wrap-around distance from last to first barrier modulo L
          L - p[|p| - 1] + p[0]
          )
  }

  predicate IsRotation(s1: seq<int>, s2: seq<int>, offset: int)
  {
    |s1| == |s2| &&
    0 <= offset < |s1| &&
    forall i :: 0 <= i < |s1| ==> s2[i] == s1[(i + offset) % |s1|]
  }
}
