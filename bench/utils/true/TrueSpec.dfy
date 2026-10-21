include "../../core/IOContract.dfy"
include "../../core/World.dfy"
include "../../core/IO.dfy"
include "TrueSchema.dfy"

module TrueSpec {
  import StreamContract = IOContract
  import StreamUtf8 = Utf8Semantics

  import BenchIO
  import BenchWorld
  import Schema = TrueSchema




  function HelpTextSpec(): BenchWorld.Bytes
  {
    "Usage: true [ignored command line arguments]\n"
    + "  or:  true OPTION\n"
    + "Exit with a status code indicating success.\n"
    + "\n"
    + "      --help\n"
    + "         display this help and exit\n"
    + "      --version\n"
    + "         output version information and exit\n"
    + "\n"
    + "Your shell may have its own version of true, which usually supersedes\n"
    + "the version described here.  Please refer to your shell's documentation\n"
    + "for details about the options it supports.\n"
    + "\n"
    + "Report bugs to: bug-coreutils@gnu.org\n"
    + "GNU coreutils home page: <https://www.gnu.org/software/coreutils/>\n"
    + "General help using GNU software: <https://www.gnu.org/gethelp/>\n"
    + "Report any translation bugs to <https://translationproject.org/team/>\n"
    + "Full documentation <https://www.gnu.org/software/coreutils/true>\n"
    + "or available locally via: info '(coreutils) true invocation'\n"
  }

  function VersionTextSpec(): BenchWorld.Bytes
  {
    "true (GNU coreutils) 9.10.13-2cf49\n"
    + "Copyright (C) 2026 Free Software Foundation, Inc.\n"
    + "License GPLv3+: GNU GPL version 3 or later <https://gnu.org/licenses/gpl.html>.\n"
    + "This is free software: you are free to change and redistribute it.\n"
    + "There is NO WARRANTY, to the extent permitted by law.\n"
    + "\n"
    + "Written by Jim Meyering.\n"
  }

  twostate predicate PreparedSpec(raw: Schema.TrueCmdRaw, io: BenchIO.IO, exit: int, plannedStdout: BenchWorld.Bytes, plannedStderr: BenchWorld.Bytes)

  {
    plannedStderr == old(io.stderr()) &&
    (    var cmd := Schema.Command(raw);
         if cmd.mode == Schema.ModeHelp then
           plannedStdout == old(io.stdout()) + HelpTextSpec() &&
           exit == 0
         else if cmd.mode == Schema.ModeVersion then
           plannedStdout == old(io.stdout()) + VersionTextSpec() &&
           exit == 0
         else
           plannedStdout == old(io.stdout()) &&
           exit == 0)
  }

  function Emits(raw: Schema.TrueCmdRaw): bool
  {
    Schema.Command(raw).mode == Schema.ModeHelp || Schema.Command(raw).mode == Schema.ModeVersion
  }

  function StreamWriteErrorText(message: string): string
  {
    "true: write error: " + message + "\n"
  }

  ghost function StreamWriteErrorMessage(message: string): BenchWorld.Bytes
  {
    StreamUtf8.Encode(StreamWriteErrorText(message))
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
    exit == (if stdoutResult.err != 0 || stderrResult.err != 0 then 1 else normalExit)
  }

  twostate predicate Emission(raw: Schema.TrueCmdRaw, io: BenchIO.IO,
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

  twostate predicate Spec(raw: Schema.TrueCmdRaw, io: BenchIO.IO, exit: int)
    reads io.stdoutRegion, io.stderrRegion
  {
    exists out: BenchWorld.Bytes, diagnostics: BenchWorld.Bytes, normalExit: int ::
      PreparedSpec(raw, io, normalExit,
                   old(io.stdout()) + out, old(io.stderr()) + diagnostics) &&
      Emission(raw, io, out, diagnostics, normalExit, exit)
  }
}
