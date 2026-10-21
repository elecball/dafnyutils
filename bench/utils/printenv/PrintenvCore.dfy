include "../../core/Utf8.dfy"
include "PrintenvSpec.dfy"
include "../../core/World.dfy"
include "../../core/IO.dfy"
include "../../core/IOContract.dfy"
include "PrintenvSchema.dfy"

module PrintenvCore {
  import StreamContract = IOContract

  import BenchIO
  import Schema = PrintenvSchema
  import BenchWorld
  import IOContract
  import Spec = PrintenvSpec
  import Utf8 = Utf8Semantics

  function RenderEnvEntries(entries: seq<string>, terminator: BenchWorld.Bytes): BenchWorld.Bytes
    decreases |entries|
  {
    if |entries| == 0 then
      []
    else
      Utf8.Encode(entries[0]) + terminator + RenderEnvEntries(entries[1..], terminator)
  } by method {
    if |entries| == 0 {
      return [];
    } else {
      var rest := RenderEnvEntries(entries[1..], terminator);
      return Utf8.Encode(entries[0]) + terminator + rest;
    }
  }

  datatype EnvLookup = Missing | Found(value: string)

  function FindEquals(text: string, i: nat): nat
    requires i <= |text|
    ensures i <= FindEquals(text, i) <= |text|
    decreases |text| - i
  {
    if i >= |text| || text[i] == '=' then
      i
    else
      FindEquals(text, i + 1)
  } by method {
    if i >= |text| || text[i] == '=' {
      return i;
    } else {
      return FindEquals(text, i + 1);
    }
  }

  function EntryName(entry: string): string
  {
    var eq := FindEquals(entry, 0);
    entry[..eq]
  } by method {
    var eq := FindEquals(entry, 0);
    return entry[..eq];
  }

  function EntryValue(entry: string): string
  {
    var eq := FindEquals(entry, 0);
    if eq < |entry| then entry[eq + 1..] else ""
  } by method {
    var eq := FindEquals(entry, 0);
    if eq < |entry| {
      return entry[eq + 1..];
    } else {
      return "";
    }
  }

  function LookupEntry(name: string, entries: seq<string>): EnvLookup
    decreases |entries|
  {
    if |entries| == 0 then
      Missing
    else if EntryName(entries[0]) == name then
      Found(EntryValue(entries[0]))
    else
      LookupEntry(name, entries[1..])
  } by method {
    if |entries| == 0 {
      return Missing;
    } else {
      var entryName := EntryName(entries[0]);
      if entryName == name {
        var entryValue := EntryValue(entries[0]);
        return Found(entryValue);
      } else {
        return LookupEntry(name, entries[1..]);
      }
    }
  }

  function LookupOutput(operands: seq<string>, entries: seq<string>, terminator: BenchWorld.Bytes): BenchWorld.Bytes
    decreases |operands|
  {
    if |operands| == 0 then
      []
    else
      match LookupEntry(operands[0], entries)
      case Missing => LookupOutput(operands[1..], entries, terminator)
      case Found(value) => Utf8.Encode(value) + terminator + LookupOutput(operands[1..], entries, terminator)
  } by method {
    if |operands| == 0 {
      return [];
    } else {
      var rest := LookupOutput(operands[1..], entries, terminator);
      var lookup := LookupEntry(operands[0], entries);
      match lookup
      case Missing =>
        return rest;
      case Found(value) =>
        return Utf8.Encode(value) + terminator + rest;
    }
  }

  function AnyMissing(operands: seq<string>, entries: seq<string>): bool
    decreases |operands|
  {
    |operands| > 0 &&
    (LookupEntry(operands[0], entries) == Missing || AnyMissing(operands[1..], entries))
  } by method {
    if |operands| == 0 {
      return false;
    } else {
      var lookup := LookupEntry(operands[0], entries);
      if lookup == Missing {
        return true;
      } else {
        return AnyMissing(operands[1..], entries);
      }
    }
  }

  function Output(cmd: Schema.PrintenvCmd, entries: seq<string>): BenchWorld.Bytes
  {
    if |cmd.operands| == 0 then
      RenderEnvEntries(entries, Spec.Terminator(cmd.nullTerminated))
    else
      LookupOutput(cmd.operands, entries, Spec.Terminator(cmd.nullTerminated))
  } by method {
    var terminator := Spec.Terminator(cmd.nullTerminated);
    if |cmd.operands| == 0 {
      return RenderEnvEntries(entries, terminator);
    } else {
      return LookupOutput(cmd.operands, entries, terminator);
    }
  }

  function ExitStatus(cmd: Schema.PrintenvCmd, entries: seq<string>): int
  {
    if |cmd.operands| > 0 && AnyMissing(cmd.operands, entries) then 1 else 0
  } by method {
    return
      if |cmd.operands| > 0 && AnyMissing(cmd.operands, entries)
      then 1
      else 0;
  }

  twostate predicate PreparedSummary(raw: Schema.PrintenvCmdRaw, io: BenchIO.IO, exit: int, plannedStdout: BenchWorld.Bytes, plannedStderr: BenchWorld.Bytes)

  {
    var cmd := Schema.Command(raw);
    if cmd.mode == Schema.ModeHelp then
      plannedStdout == old(io.stdout()) + Spec.HelpTextSpec() &&
      plannedStderr == old(io.stderr()) &&
      exit == 0
    else if cmd.mode == Schema.ModeVersion then
      plannedStdout == old(io.stdout()) + Spec.VersionTextSpec() &&
      plannedStderr == old(io.stderr()) &&
      exit == 0
    else
      exists entries: seq<string> ::
        IOContract.GetEnvironmentContractFields(old(io.env()), entries) &&
        plannedStdout == old(io.stdout()) + Output(cmd, entries) &&
        plannedStderr == old(io.stderr()) &&
        exit == ExitStatus(cmd, entries)
  }

  method Prepare(raw: Schema.PrintenvCmdRaw, io: BenchIO.IO) returns (exit: int, plannedOut: BenchWorld.Bytes, plannedErr: BenchWorld.Bytes)

    ensures PreparedSummary(raw, io, exit, old(io.stdout()) + plannedOut, old(io.stderr()) + plannedErr)
    decreases *
  {
    plannedOut := [];
    plannedErr := [];
    ghost var initialStdout := io.stdout();
    ghost var initialStderr := io.stderr();

    ghost var preEnv := io.env();
    ghost var preStdout := (initialStdout + plannedOut);
    var cmd := Schema.Command(raw);

    if cmd.mode == Schema.ModeHelp {
      var out := Spec.HelpTextSpec();
      plannedOut := plannedOut + out;
      exit := 0;
      assert PreparedSummary(raw, io, exit, old(io.stdout()) + plannedOut, old(io.stderr()) + plannedErr);
      return;
    }

    if cmd.mode == Schema.ModeVersion {
      var out := Spec.VersionTextSpec();
      plannedOut := plannedOut + out;
      exit := 0;
      assert PreparedSummary(raw, io, exit, old(io.stdout()) + plannedOut, old(io.stderr()) + plannedErr);
      return;
    }

    var entries := io.GetEnvironment();
    assert IOContract.GetEnvironmentContractFields(preEnv, entries);
    var out := Output(cmd, entries);
    var status := ExitStatus(cmd, entries);
    plannedOut := plannedOut + out;
    exit := status;
    assert (initialStdout + plannedOut) == preStdout + out;
    assert PreparedSummary(raw, io, exit, old(io.stdout()) + plannedOut, old(io.stderr()) + plannedErr);
  }

  twostate predicate CoreSummary(raw: Schema.PrintenvCmdRaw, io: BenchIO.IO, exit: int)
    reads io.stdoutRegion, io.stderrRegion
  {
    exists out: BenchWorld.Bytes, diagnostics: BenchWorld.Bytes, normalExit: int ::
      PreparedSummary(raw, io, normalExit,
                      old(io.stdout()) + out, old(io.stderr()) + diagnostics) &&
      Spec.Emission(raw, io, out, diagnostics, normalExit, exit)
  }

  method Flush(io: BenchIO.IO, out: BenchWorld.Bytes,
               diagnostics: BenchWorld.Bytes, normalExit: int) returns (exit: int)
    modifies io.stdoutRegion, io.stderrRegion
    ensures Spec.EmitFields(old(io.trustedStreams()), old(io.stdout()), old(io.stderr()),
                            io.stdout(), io.stderr(), out, diagnostics, normalExit, exit)
  {
    var outErr := 0;
    if out != [] {
      var written := io.WriteStdout(out);
      outErr := StreamContract.ResultErrno(written);
    }
    var errors := diagnostics;
    if outErr != 0 {
      var message := io.GetCLocaleErrnoText(outErr);
      errors := errors + Spec.StreamWriteErrorMessage(message);
    }
    assert errors == diagnostics + (if outErr == 0 then [] else
                                    Spec.StreamWriteErrorMessage(StreamContract.CLocaleErrnoTextResult(outErr)));
    var errErr := 0;
    if errors != [] {
      var diagnosed := io.WriteStderr(errors);
      errErr := StreamContract.ResultErrno(diagnosed);
      assert StreamContract.WriteStderrSpec(old(io.stderr()), io.trustedStreams(), io.stderr(),
                                            errors, StreamContract.WriteResultCommitted(diagnosed), errErr);
    }
    exit := if outErr != 0 || errErr != 0 then Spec.StreamFailureExit() else normalExit;
  }

  method RunCore(raw: Schema.PrintenvCmdRaw, io: BenchIO.IO) returns (exit: int)
    modifies io.stdoutRegion, io.stderrRegion
    ensures CoreSummary(raw, io, exit)
    decreases *
  {
    var normalExit, out, diagnostics := Prepare(raw, io);

    assert PreparedSummary(raw, io, normalExit, old(io.stdout()) + out, old(io.stderr()) + diagnostics);
    if Spec.Emits(raw) {
      exit := Flush(io, out, diagnostics, normalExit);
    } else {
      exit := normalExit;
    }
    assert PreparedSummary(raw, io, normalExit, old(io.stdout()) + out, old(io.stderr()) + diagnostics);
    assert Spec.Emission(raw, io, out, diagnostics, normalExit, exit);
  }
}
