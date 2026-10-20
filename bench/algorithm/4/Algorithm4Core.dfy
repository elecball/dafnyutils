include "Algorithm4TextCore.dfy"
include "Algorithm4Spec.dfy"
include "Algorithm4Schema.dfy"
include "../../core/IO.dfy"
module Algorithm4Core {
  import BenchIO
  import BenchWorld
  import Schema = Algorithm4Schema
  import CliSpec = Algorithm4Spec
  import Text = Algorithm4TextCore

  twostate predicate CoreSummary(raw: Schema.Algorithm4CmdRaw, io: BenchIO.IO, exit: int)
    reads io.stdoutRegion, io.stderrRegion, io.trustedStreamsRegion
  {
    if CliSpec.Valid(raw) then
      io.stderr() == old(io.stderr()) &&
      exists y: int ::
        AnswerSummary(raw.x, raw.hh, raw.mm, y) && CliSpec.Output(io, CliSpec.OutputText(y), exit)
    else
      io.stdout() == old(io.stdout()) && CliSpec.InvalidInput(io, exit)
  }

  method RunCore(raw: Schema.Algorithm4CmdRaw, io: BenchIO.IO) returns (exit: int)
    modifies io.stdoutRegion, io.stderrRegion
    ensures CoreSummary(raw, io, exit)
    decreases *
  {
    if !CliSpec.Valid(raw) {
      var written := io.WriteStderr(CliSpec.InvalidInputText());
      exit := if written.Err? then 1 else 2;
      return;
    }
    var y := Solve(raw.x, raw.hh, raw.mm);
    var text := Text.OutputText(y);
    var written := io.WriteStdout(text);
    exit := if written.Err? then 1 else 0;
  }

  function ContainsDigit7(x: int): bool
    decreases if x < 10 then 0 else x
  {
    x >= 0 &&
    (x % 10 == 7 || (x >= 10 && ContainsDigit7(x / 10)))
  }

  function IsLuckyTime(h: int, m: int): bool
  {
    ContainsDigit7(h) || ContainsDigit7(m)
  }

  function TimeAt(x: int, hh: int, mm: int, y: int): int
  {
    var total := hh * 60 + mm;
    ((total - x * y) % 1440 + 1440) % 1440
  }

  function LuckyAt(x: int, hh: int, mm: int, y: int): bool
  {
    IsLuckyTime(TimeAt(x, hh, mm, y) / 60, TimeAt(x, hh, mm, y) % 60)
  }

  method Solve(x: int, hh: int, mm: int) returns (y: int)
    ensures AnswerSummary(x, hh, mm, y)
    decreases *
  {
    y := 0;
    while !LuckyAt(x, hh, mm, y)
      invariant 0 <= y
      invariant forall z :: 0 <= z < y ==> !LuckyAt(x, hh, mm, z)
      decreases *
    {
      y := y + 1;
    }
  }

  ghost predicate AnswerSummary(x: int, hh: int, mm: int, y: int)
  {
    0 <= y &&
    LuckyAt(x, hh, mm, y) &&
    forall z :: 0 <= z < y ==> !LuckyAt(x, hh, mm, z)
  }
}
