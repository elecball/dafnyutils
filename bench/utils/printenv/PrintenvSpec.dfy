include "../../core/World.dfy"
include "../../core/IO.dfy"
include "../../core/IOContract.dfy"
include "PrintenvSchema.dfy"

module PrintenvSpec {
  import StreamContract = IOContract
  import StreamUtf8 = Utf8Semantics

  import BenchIO
  import Schema = PrintenvSchema
  import BenchWorld
  import IOContract
  import Utf8 = Utf8Semantics




  function HelpTextSpec(): BenchWorld.Bytes
  {
    "Usage: printenv [OPTION] [VARIABLE]...\n"
    + "Print the values of the specified environment VARIABLE(s).\n"
    + "If no VARIABLE is specified, print name and value pairs for them all.\n"
    + "\n"
    + "  -0, --null\n"
    + "         end each output line with NUL, not newline\n"
    + "      --help\n"
    + "         display this help and exit\n"
    + "      --version\n"
    + "         output version information and exit\n"
    + "\n"
    + "Your shell may have its own version of printenv, which usually supersedes\n"
    + "the version described here.  Please refer to your shell's documentation\n"
    + "for details about the options it supports.\n"
    + "\n"
    + "Report bugs to: bug-coreutils@gnu.org\n"
    + "GNU coreutils home page: <https://www.gnu.org/software/coreutils/>\n"
    + "General help using GNU software: <https://www.gnu.org/gethelp/>\n"
    + "Report any translation bugs to <https://translationproject.org/team/>\n"
    + "Full documentation <https://www.gnu.org/software/coreutils/printenv>\n"
    + "or available locally via: info '(coreutils) printenv invocation'\n"
  }

  function VersionTextSpec(): BenchWorld.Bytes
  {
    "printenv (GNU coreutils) 9.10.13-2cf49\n"
    + "Copyright (C) 2026 Free Software Foundation, Inc.\n"
    + "License GPLv3+: GNU GPL version 3 or later <https://gnu.org/licenses/gpl.html>.\n"
    + "This is free software: you are free to change and redistribute it.\n"
    + "There is NO WARRANTY, to the extent permitted by law.\n"
    + "\n"
    + "Written by David MacKenzie and Richard Mlynarik.\n"
  }

  function Terminator(nullTerminated: bool): BenchWorld.Bytes
  {
    if nullTerminated then [(0 as char)] else "\n"
  }

  ghost predicate EnvironmentOutputRelation(
    entries: seq<string>,
    terminator: BenchWorld.Bytes,
    out: BenchWorld.Bytes
  )
    decreases |entries|
  {
    if |entries| == 0 then
      out == []
    else
      exists rest: BenchWorld.Bytes ::
        EnvironmentOutputRelation(entries[1..], terminator, rest) &&
        out == Utf8.Encode(entries[0]) + terminator + rest
  }

  ghost predicate OperandResultRelation(
    env: map<string, string>,
    operands: seq<string>,
    terminator: BenchWorld.Bytes,
    out: BenchWorld.Bytes,
    exit: int
  )
    decreases |operands|
  {
    if |operands| == 0 then
      out == [] && exit == 0
    else
      exists rest: BenchWorld.Bytes, restExit: int ::
        OperandResultRelation(
          env, operands[1..], terminator, rest, restExit
        ) &&
        if operands[0] in env then
          out == Utf8.Encode(env[operands[0]]) + terminator + rest &&
          exit == restExit
        else
          out == rest &&
          exit == 1
  }

  twostate predicate PreparedSpec(raw: Schema.PrintenvCmdRaw, io: BenchIO.IO, exit: int, plannedStdout: BenchWorld.Bytes, plannedStderr: BenchWorld.Bytes)

  {
    var cmd := Schema.Command(raw);
    if cmd.mode == Schema.ModeHelp then
      plannedStdout == old(io.stdout()) + HelpTextSpec() &&
      plannedStderr == old(io.stderr()) &&
      exit == 0
    else if cmd.mode == Schema.ModeVersion then
      plannedStdout == old(io.stdout()) + VersionTextSpec() &&
      plannedStderr == old(io.stderr()) &&
      exit == 0
    else if |cmd.operands| == 0 then
      exists entries: seq<string>, out: BenchWorld.Bytes ::
        IOContract.GetEnvironmentContractFields(old(io.env()), entries) &&
        EnvironmentOutputRelation(
          entries, Terminator(cmd.nullTerminated), out) &&
        plannedStdout == old(io.stdout()) + out &&
        plannedStderr == old(io.stderr()) &&
        exit == 0
    else
      exists out: BenchWorld.Bytes ::
        OperandResultRelation(
          old(io.env()),
          cmd.operands,
          Terminator(cmd.nullTerminated),
          out,
          exit
        ) &&
        plannedStdout == old(io.stdout()) + out &&
        plannedStderr == old(io.stderr())
  }

  function Emits(raw: Schema.PrintenvCmdRaw): bool
  {
    true
  }

  function StreamWriteErrorText(message: string): string
  {
    "printenv: write error: " + message + "\n"
  }

  ghost function StreamWriteErrorMessage(message: string): BenchWorld.Bytes
  {
    StreamUtf8.Encode(StreamWriteErrorText(message))
  }

  function StreamFailureExit(): int
  {
    2
  }

  ghost predicate EmitFields(
    observations: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult,
    beforeStdout: BenchWorld.Bytes, beforeStderr: BenchWorld.Bytes,
    afterStdout: BenchWorld.Bytes, afterStderr: BenchWorld.Bytes,
    out: BenchWorld.Bytes, diagnostics: BenchWorld.Bytes,
    normalExit: int, exit: int
  )
  {
    var stdoutResult := if out == [] then BenchWorld.StreamWriteResult(0, beforeStdout, 0)
                        else observations(BenchWorld.StreamWriteStdout(beforeStdout, out));
    stdoutResult.StreamWriteResult? &&
    var errors := diagnostics + (if stdoutResult.err == 0 then [] else
                                 StreamWriteErrorMessage(StreamContract.CLocaleErrnoTextResult(stdoutResult.err)));
    var stderrResult := if errors == [] then BenchWorld.StreamWriteResult(0, beforeStderr, 0)
                        else observations(BenchWorld.StreamWriteStderr(beforeStderr, errors));
    stderrResult.StreamWriteResult? &&
    (if out == [] then afterStdout == beforeStdout else StreamContract.WriteStdoutSpec(
       beforeStdout, observations, afterStdout, out, stdoutResult.committed, stdoutResult.err)) &&
    (if errors == [] then afterStderr == beforeStderr else StreamContract.WriteStderrSpec(
       beforeStderr, observations, afterStderr, errors, stderrResult.committed, stderrResult.err)) &&
    exit == (if stdoutResult.err != 0 || stderrResult.err != 0 then StreamFailureExit() else normalExit)
  }

  twostate predicate Emission(raw: Schema.PrintenvCmdRaw, io: BenchIO.IO,
                              out: BenchWorld.Bytes, diagnostics: BenchWorld.Bytes,
                              normalExit: int, exit: int)
    reads io.stdoutRegion, io.stderrRegion
  {
    if Emits(raw) then
      EmitFields(old(io.trustedStreams()), old(io.stdout()), old(io.stderr()),
                 io.stdout(), io.stderr(), out, diagnostics, normalExit, exit)
    else
      io.stdout() == old(io.stdout()) && io.stderr() == old(io.stderr()) &&
      exit == normalExit
  }

  twostate predicate Spec(raw: Schema.PrintenvCmdRaw, io: BenchIO.IO, exit: int)
    reads io.stdoutRegion, io.stderrRegion
  {
    exists out: BenchWorld.Bytes, diagnostics: BenchWorld.Bytes, normalExit: int ::
      PreparedSpec(raw, io, normalExit,
                   old(io.stdout()) + out, old(io.stderr()) + diagnostics) &&
      Emission(raw, io, out, diagnostics, normalExit, exit)
  }
}
