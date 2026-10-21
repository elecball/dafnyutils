include "../../core/IOContract.dfy"
include "../../core/IO.dfy"
include "../../core/StringEscaping.dfy"
include "LognameSchema.dfy"

module LognameSpec {
  import StreamContract = IOContract
  import StreamUtf8 = Utf8Semantics

  import BenchIO
  import Utf8 = Utf8Semantics
  import BenchWorld
  import Schema = LognameSchema
  import SE = StringEscaping

  function HelpTextSpec(): BenchWorld.Bytes
  {
    "Usage: logname [OPTION]\n"
    + "Print the user's login name.\n"
    + "\n"
    + "      --help\n"
    + "         display this help and exit\n"
    + "      --version\n"
    + "         output version information and exit\n"
    + "\n"
    + "Report bugs to: bug-coreutils@gnu.org\n"
    + "GNU coreutils home page: <https://www.gnu.org/software/coreutils/>\n"
    + "General help using GNU software: <https://www.gnu.org/gethelp/>\n"
    + "Report any translation bugs to <https://translationproject.org/team/>\n"
    + "Full documentation <https://www.gnu.org/software/coreutils/logname>\n"
    + "or available locally via: info '(coreutils) logname invocation'\n"
  }

  function VersionTextSpec(): BenchWorld.Bytes
  {
    "logname (GNU coreutils) 9.10.13-2cf49\n"
    + "Copyright (C) 2026 Free Software Foundation, Inc.\n"
    + "License GPLv3+: GNU GPL version 3 or later <https://gnu.org/licenses/gpl.html>.\n"
    + "This is free software: you are free to change and redistribute it.\n"
    + "There is NO WARRANTY, to the extent permitted by law.\n"
    + "\n"
    + "Written by David MacKenzie.\n"
  }

  function ExtraOperandPrefix(): BenchWorld.Bytes
  {
    "logname: extra operand "
  }

  function ExtraOperandSuffix(): BenchWorld.Bytes
  {
    "\n"
    + "Try 'logname --help' for more information.\n"
  }

  function ExtraOperandMessageSpec(op: string): BenchWorld.Bytes
  {
    ExtraOperandPrefix() + SE.SpecLocaleQuoteBytes(Utf8.Encode(op)) + ExtraOperandSuffix()
  }

  function NoLoginNameMessageSpec(): BenchWorld.Bytes
  {
    "logname: no login name\n"
  }

  function HasLoginNameProps(props: map<string, string>): bool
  {
    "loginName" in props
  }

  function LoginNameTerminator(): BenchWorld.Bytes
  {
    "\n"
  }

  function LoginNameOutput(name: string): BenchWorld.Bytes
  {
    Utf8.Encode(name) + LoginNameTerminator()
  }

  twostate predicate PreparedSpec(raw: Schema.LognameCmdRaw, io: BenchIO.IO, exit: int, plannedStdout: BenchWorld.Bytes, plannedStderr: BenchWorld.Bytes)

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
    else if |cmd.operands| > 0 then
      plannedStdout == old(io.stdout()) &&
      plannedStderr == old(io.stderr()) + ExtraOperandMessageSpec(cmd.operands[0]) &&
      exit == 1
    else if HasLoginNameProps(old(io.props())) then
      plannedStdout == old(io.stdout()) + LoginNameOutput(old(io.props())["loginName"]) &&
      plannedStderr == old(io.stderr()) &&
      exit == 0
    else
      plannedStdout == old(io.stdout()) &&
      plannedStderr == old(io.stderr()) + NoLoginNameMessageSpec() &&
      exit == 1
  }

  function Emits(raw: Schema.LognameCmdRaw): bool
  {
    true
  }

  function StreamWriteErrorText(message: string): string
  {
    "logname: write error: " + message + "\n"
  }

  function StreamWriteErrorMessage(message: string): BenchWorld.Bytes
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

  twostate predicate Emission(raw: Schema.LognameCmdRaw, io: BenchIO.IO,
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

  twostate predicate Spec(raw: Schema.LognameCmdRaw, io: BenchIO.IO, exit: int)
    reads io.stdoutRegion, io.stderrRegion
  {
    exists out: BenchWorld.Bytes, diagnostics: BenchWorld.Bytes, normalExit: int ::
      PreparedSpec(raw, io, normalExit,
                   old(io.stdout()) + out, old(io.stderr()) + diagnostics) &&
      Emission(raw, io, out, diagnostics, normalExit, exit)
  }
}
