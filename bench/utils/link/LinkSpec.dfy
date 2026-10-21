include "LinkSchema.dfy"
include "../../core/IO.dfy"
include "../../core/Utf8.dfy"
include "CliSupport.dfy"

module LinkSpec {
  import StreamWorld = BenchWorld
  import StreamContract = IOContract

  import BenchIO
  import BenchWorld
  import CliTypes
  import Schema = LinkSchema
  import Utf8 = Utf8Semantics
  import CliModel
  import C = IOContract

  function HelpTextSpec(): BenchWorld.Bytes
  {
    "Usage: link FILE1 FILE2\n"
    + "  or:  link OPTION\n"
    + "Call the link function to create a link named FILE2 to an existing FILE1.\n"
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
    + "Full documentation <https://www.gnu.org/software/coreutils/link>\n"
    + "or available locally via: info '(coreutils) link invocation'\n"
  }

  function VersionTextSpec(): BenchWorld.Bytes
  {
    "link (GNU coreutils) 9.10.13-2cf49\n"
    + "Copyright (C) 2026 Free Software Foundation, Inc.\n"
    + "License GPLv3+: GNU GPL version 3 or later <https://gnu.org/licenses/gpl.html>.\n"
    + "This is free software: you are free to change and redistribute it.\n"
    + "There is NO WARRANTY, to the extent permitted by law.\n"
    + "\n"
    + "Written by Michael Stone.\n"
  }

  function LongOptionName(token: string): string
  {
    var eq := CliModel.FindChar(token, '=');
    var name := if eq >= 0 then token[..eq] else token;
    if |name| > 2 && CliModel.HasPrefix(name, "--") then
      var abbreviation := name[2..];
      if CliModel.HasPrefix("help", abbreviation) then "--help"
      else if CliModel.HasPrefix("version", abbreviation) then "--version"
      else name
    else name
  }

  function UnknownShortTemplate(): BenchWorld.Bytes
  {
    ['l', 'i', 'n', 'k', ':', ' ', 'i', 'n', 'v', 'a', 'l', 'i', 'd',
     ' ', 'o', 'p', 't', 'i', 'o', 'n', ' ', '-', '-', ' ', '\'', '\0',
     '\'', '\n', 'T', 'r', 'y', ' ', '\'', 'l', 'i', 'n', 'k', ' ', '-',
     '-', 'h', 'e', 'l', 'p', '\'', ' ', 'f', 'o', 'r', ' ', 'm', 'o', 'r',
     'e', ' ', 'i', 'n', 'f', 'o', 'r', 'm', 'a', 't', 'i', 'o', 'n', '.',
     '\n']
  }

  function UnknownShortText(byte: BenchWorld.RawByte): BenchWorld.Bytes
  {
    UnknownShortTemplate()[25 := byte]
  }

  function ParseErrorTextPart1(): StreamWorld.Bytes
  {
    "link: unrecognized option '"
  }

  function ParseErrorTextPart2(): StreamWorld.Bytes
  {
    "'\n"
  }

  function ParseErrorTextPart3(): StreamWorld.Bytes
  {
    "Try 'link --help' for more information.\n"
  }

  function ParseErrorTextPart4(): StreamWorld.Bytes
  {
    "link: invalid option\nTry 'link --help' for more information.\n"
  }

  function ParseErrorTextPart5(): StreamWorld.Bytes
  {
    "link: option '"
  }

  function ParseErrorTextPart6(): StreamWorld.Bytes
  {
    "' doesn't allow an argument\n"
  }

  function ParseErrorTextPart7(): StreamWorld.Bytes
  {
    "' is ambiguous; possibilities: '--help' '--version'\n"
  }

  function ParseErrorTextPart8(): StreamWorld.Bytes
  {
    "link: "
  }

  function ParseErrorTextPart9(): StreamWorld.Bytes
  {
    "missing option value"
  }

  function ParseErrorTextPart10(): StreamWorld.Bytes
  {
    "parse error"
  }

  function ParseErrorTextPart11(): StreamWorld.Bytes
  {
    " at token '"
  }

  ghost function ParseErrorText(err: CliTypes.ParseError): BenchWorld.Bytes
  {
    if err.kind == CliTypes.UnknownOption then
      if |err.rawToken| > 2 && err.rawToken[0] == '-' && err.rawToken[1] == '-' then
        ParseErrorTextPart1() + Utf8.Encode(err.rawToken) + ParseErrorTextPart2() +
        ParseErrorTextPart3()
      else if |err.rawToken| > 1 && err.rawToken[0] == '-' then
        UnknownShortText(Utf8.EncodeChar(err.rawToken[1])[0])
      else
        ParseErrorTextPart4()
    else if err.kind == CliTypes.UnexpectedValue then
      ParseErrorTextPart5() + Utf8.Encode(LongOptionName(err.rawToken)) +
      ParseErrorTextPart6() +
      ParseErrorTextPart3()
    else if err.kind == CliTypes.Ambiguous then
      ParseErrorTextPart5() + Utf8.Encode(err.rawToken) +
      ParseErrorTextPart7() +
      ParseErrorTextPart3()
    else
      ParseErrorTextPart8() + Utf8.Encode(
        (if err.kind == CliTypes.MissingValue
         then ParseErrorTextPart9()
         else ParseErrorTextPart10())) +
      ParseErrorTextPart11() + Utf8.Encode(err.rawToken) + ParseErrorTextPart2()
  }

  twostate predicate LinkResult(
    io: BenchIO.IO,
    source: BenchWorld.Path,
    target: BenchWorld.Path,
    ok: bool,
    err: int
  )
    reads io.fsRegion, io.nowRegion, io.trustedFilesystemRegion
  {
    C.CreateHardLinkSpec(
      old(io.fs()),
      old(io.now()),
      old(io.trustedFilesystem()),
      io.fs(),
      source,
      target,
      ok,
      err
    )
  }

  function MissingOperandText(): BenchWorld.Bytes
  {
    "link: missing operand\n"
    + "Try 'link --help' for more information.\n"
  }

  function MissingOperandAfterText(
    quotedSource: BenchWorld.Bytes
  ): BenchWorld.Bytes
  {
    "link: missing operand after " + quotedSource + "\n"
    + "Try 'link --help' for more information.\n"
  }

  function ExtraOperandText(quotedOperand: BenchWorld.Bytes): BenchWorld.Bytes
  {
    "link: extra operand " + quotedOperand + "\n"
    + "Try 'link --help' for more information.\n"
  }

  function CannotCreateLinkTextPart1(): StreamWorld.Bytes
  {
    "link: cannot create link "
  }

  function CannotCreateLinkTextPart2(): StreamWorld.Bytes
  {
    " to "
  }

  function CannotCreateLinkTextPart3(): StreamWorld.Bytes
  {
    ": "
  }

  function CannotCreateLinkTextPart4(): StreamWorld.Bytes
  {
    "\n"
  }

  ghost function CannotCreateLinkText(
    quotedTarget: BenchWorld.Bytes,
    quotedSource: BenchWorld.Bytes,
    reason: string
  ): BenchWorld.Bytes
  {
    CannotCreateLinkTextPart1() + quotedTarget + CannotCreateLinkTextPart2() + quotedSource + CannotCreateLinkTextPart3()
    + Utf8.Encode(reason) + CannotCreateLinkTextPart4()
  }


  function WriteErrorTextPart1(): StreamWorld.Bytes
  {
    "link: write error: "
  }

  function WriteErrorTextPart2(): StreamWorld.Bytes
  {
    "\n"
  }

  ghost function WriteErrorText(reason: string): StreamWorld.Bytes
  {
    WriteErrorTextPart1() + Utf8.Encode(reason) + WriteErrorTextPart2()
  }

  ghost predicate EmissionOutcomeFields(
    beforeOut: StreamWorld.Bytes, beforeErr: StreamWorld.Bytes,
    afterOut: StreamWorld.Bytes, afterErr: StreamWorld.Bytes,
    observations: (StreamWorld.TrustedStreamRequest) -> StreamWorld.TrustedStreamResult,
    output: StreamWorld.Bytes, diagnostics: StreamWorld.Bytes,
    normalExit: int, exit: int,
    committed: nat, outErr: int, errCommitted: nat, errErr: int
  )
  {
    (if |output| == 0 then afterOut == beforeOut && committed == 0 && outErr == 0
     else StreamContract.WriteStdoutSpec(beforeOut, observations, afterOut, output, committed, outErr)) &&
    var finalDiagnostics := diagnostics +
                            (if outErr == 0 then [] else WriteErrorText(StreamContract.CLocaleErrnoTextResult(outErr)));
    (if |finalDiagnostics| == 0 then afterErr == beforeErr && errCommitted == 0 && errErr == 0
     else StreamContract.WriteStderrSpec(beforeErr, observations, afterErr, finalDiagnostics, errCommitted, errErr)) &&
    exit == (if outErr != 0 || errErr != 0 then 1 else normalExit)
  }

  ghost predicate EmissionFields(
    beforeOut: StreamWorld.Bytes, beforeErr: StreamWorld.Bytes,
    afterOut: StreamWorld.Bytes, afterErr: StreamWorld.Bytes,
    observations: (StreamWorld.TrustedStreamRequest) -> StreamWorld.TrustedStreamResult,
    output: StreamWorld.Bytes, diagnostics: StreamWorld.Bytes,
    normalExit: int, exit: int
  )
  {
    exists committed: nat, outErr: int, errCommitted: nat, errErr: int ::
      EmissionOutcomeFields(beforeOut, beforeErr, afterOut, afterErr, observations,
                            output, diagnostics, normalExit, exit,
                            committed, outErr, errCommitted, errErr)
  }
  twostate predicate PreparedSpec(raw: Schema.LinkCmdRaw, io: BenchIO.IO, exit: int, plannedStdout: StreamWorld.Bytes, plannedStderr: StreamWorld.Bytes)
    reads io.fsRegion, io.nowRegion, io.trustedFilesystemRegion
  {
    if raw.mode == Schema.ModeHelp then
      io.fs() == old(io.fs()) &&
      plannedStdout == [] + HelpTextSpec() &&
      plannedStderr == [] &&
      exit == 0
    else if raw.mode == Schema.ModeVersion then
      io.fs() == old(io.fs()) &&
      plannedStdout == [] + VersionTextSpec() &&
      plannedStderr == [] &&
      exit == 0
    else if raw.mode != Schema.ModeRun then
      match raw.mode
      case ModeExtraOperand(operand) =>
        io.fs() == old(io.fs()) &&
        plannedStdout == [] &&
        plannedStderr == [] +
        ExtraOperandText(C.QuoteArgumentResult(Utf8.Encode(operand))) &&
        exit == 1
      case _ => false
    else if |raw.operands| == 0 then
      io.fs() == old(io.fs()) &&
      plannedStdout == [] &&
      plannedStderr == [] + MissingOperandText() &&
      exit == 1
    else if |raw.operands| == 1 then
      io.fs() == old(io.fs()) &&
      plannedStdout == [] &&
      plannedStderr == [] +
      MissingOperandAfterText(
        C.QuoteArgumentResult(Utf8.Encode(raw.operands[0]))
      ) &&
      exit == 1
    else
      exists ok: bool, err: int ::
        LinkResult(io, raw.operands[0], raw.operands[1], ok, err) &&
        plannedStdout == [] &&
        (if ok then
           plannedStderr == [] && exit == 0
         else
           plannedStderr == [] +
           CannotCreateLinkText(C.QuoteafPathResult(raw.operands[1]), C.QuoteafPathResult(raw.operands[0]), C.CLocaleErrnoTextResult(err)) &&
           exit == 1)
  }

  twostate predicate Spec(raw: Schema.LinkCmdRaw, io: BenchIO.IO, exit: int)
    reads io.Footprint()
  {
    exists output: StreamWorld.Bytes, diagnostics: StreamWorld.Bytes, normalExit: int ::
      PreparedSpec(raw, io, normalExit, output, diagnostics) &&
      EmissionFields(old(io.stdout()), old(io.stderr()), io.stdout(), io.stderr(),
                     io.trustedStreams(), output, diagnostics, normalExit, exit)
  }
}
