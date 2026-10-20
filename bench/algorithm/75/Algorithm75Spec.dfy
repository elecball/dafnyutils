include "../../core/Utf8.dfy"
include "Algorithm75Schema.dfy"
include "../../core/IO.dfy"
include "../../core/IOContract.dfy"

module Algorithm75Spec
{
  import BenchIO
  import BenchWorld
  import Utf8 = Utf8Semantics
  import C = IOContract
  import Schema = Algorithm75Schema

  predicate Valid(raw: Schema.Algorithm75CmdRaw)
  {
    raw.parsed && ValidGrid(raw.n, raw.m, raw.grid)
  }

  function InvalidInputText(): BenchWorld.Bytes { "algorithm75: invalid input\n" }


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

  function OutputText(out_status: string, out_x: int, out_y: int): BenchWorld.Bytes
  {
    Utf8.Encode(out_status + "\n" + (if out_status == PositiveResult() then IntegerText(out_x) + " " + IntegerText(out_y) + "\n" else ""))
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

  twostate predicate Spec(raw: Schema.Algorithm75CmdRaw, io: BenchIO.IO, exit: int)
    reads io.stdoutRegion, io.stderrRegion, io.trustedStreamsRegion
  {
    if Valid(raw) then
      io.stderr() == old(io.stderr()) &&
      exists out_status: string, out_x: int, out_y: int ::
        Answer(raw.n, raw.m, raw.grid, out_status, out_x, out_y) && Output(io, OutputText(out_status, out_x, out_y), exit)
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

  predicate ValidGrid(n: int, m: int, grid: seq<string>)
  {
    1 <= n <= 1000 &&
    1 <= m <= 1000 &&
    |grid| == n &&
    forall r | 0 <= r < n ::
      |grid[r]| == m &&
      forall c | 0 <= c < m :: grid[r][c] == '.' || grid[r][c] == '*'
  }

  predicate BombCoversAllWalls(n: int, m: int, grid: seq<string>, x: int, y: int)
  {
    ValidGrid(n, m, grid) &&
    1 <= x <= n &&
    1 <= y <= m &&
    forall r, c | 0 <= r < n && 0 <= c < m && grid[r][c] == '*' ::
      r + 1 == x || c + 1 == y
  }

  predicate Answer(n: int, m: int, grid: seq<string>, out_status: string, out_x: int, out_y: int)
  {
    ValidGrid(n, m, grid) &&
    (
      (out_status == PositiveResult() && BombCoversAllWalls(n, m, grid, out_x, out_y)) ||
      (
        out_status == NegativeResult() &&
        out_x == 0 &&
        out_y == 0 &&
        !(exists x, y | 1 <= x <= n && 1 <= y <= m :: BombCoversAllWalls(n, m, grid, x, y))
      )
    )
  }
}
