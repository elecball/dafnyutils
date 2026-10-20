include "MkdirSchema.dfy"
include "../../core/IO.dfy"
include "../../core/Utf8.dfy"
include "CliSupport.dfy"

module MkdirSpec {
  import BenchIO
  import BenchWorld
  import CliTypes
  import Schema = MkdirSchema
  import Utf8 = Utf8Semantics
  import CliModel
  import C = IOContract

  function HelpTextSpec(): BenchWorld.Bytes
  {
    "Usage: mkdir [OPTION]... DIRECTORY...\n"
    + "Create the DIRECTORY(ies), if they do not already exist.\n"
    + "\n"
    + "Mandatory arguments to long options are mandatory for short options too.\n"
    + "  -m, --mode=MODE\n"
    + "         set file mode (as in chmod), not a=rwx - umask\n"
    + "  -p, --parents\n"
    + "         no error if existing, make parent directories as needed,\n"
    + "         with their file modes unaffected by any -m option\n"
    + "  -v, --verbose\n"
    + "         print a message for each created directory\n"
    + "  -Z\n"
    + "         set SELinux security context of each created directory\n"
    + "         to the default type\n"
    + "      --context[=CTX]\n"
    + "         like -Z, or if CTX is specified then set the\n"
    + "         SELinux or SMACK security context to CTX\n"
    + "      --help\n"
    + "         display this help and exit\n"
    + "      --version\n"
    + "         output version information and exit\n"
    + "\n"
    + "Report bugs to: bug-coreutils@gnu.org\n"
    + "GNU coreutils home page: <https://www.gnu.org/software/coreutils/>\n"
    + "General help using GNU software: <https://www.gnu.org/gethelp/>\n"
    + "Report any translation bugs to <https://translationproject.org/team/>\n"
    + "Full documentation <https://www.gnu.org/software/coreutils/mkdir>\n"
    + "or available locally via: info '(coreutils) mkdir invocation'\n"
  }

  function VersionTextSpec(): BenchWorld.Bytes
  {
    "mkdir (GNU coreutils) 9.10.13-2cf49\n"
    + "Copyright (C) 2026 Free Software Foundation, Inc.\n"
    + "License GPLv3+: GNU GPL version 3 or later <https://gnu.org/licenses/gpl.html>.\n"
    + "This is free software: you are free to change and redistribute it.\n"
    + "There is NO WARRANTY, to the extent permitted by law.\n"
    + "\n"
    + "Written by David MacKenzie.\n"
  }

  function LongOptionName(token: string): string
  {
    var eq := CliModel.FindChar(token, '=');
    var name := if eq >= 0 then token[..eq] else token;
    if |name| > 2 && CliModel.HasPrefix(name, "--") then
      var abbreviation := name[2..];
      if CliModel.HasPrefix("help", abbreviation) then "--help"
      else if CliModel.HasPrefix("version", abbreviation) then "--version"
      else if CliModel.HasPrefix("verbose", abbreviation) then "--verbose"
      else name
    else name
  }

  function UnknownShortText(byte: BenchWorld.RawByte): BenchWorld.Bytes
  {
    "mkdir: invalid option -- '" + [byte] + "'\n"
    + "Try 'mkdir --help' for more information.\n"
  }

  function ParseErrorTextPart1(): BenchWorld.Bytes
  {
    "mkdir: unrecognized option '"
  }

  function ParseErrorTextPart2(): BenchWorld.Bytes
  {
    "'\n"
  }

  function ParseErrorTextPart3(): BenchWorld.Bytes
  {
    "Try 'mkdir --help' for more information.\n"
  }

  function ParseErrorTextPart4(): BenchWorld.Bytes
  {
    "mkdir: invalid option\nTry 'mkdir --help' for more information.\n"
  }

  function ParseErrorTextPart5(): BenchWorld.Bytes
  {
    "mkdir: option '"
  }

  function ParseErrorTextPart6(): BenchWorld.Bytes
  {
    "' doesn't allow an argument\n"
  }

  function ParseErrorTextPart7(): BenchWorld.Bytes
  {
    "' is ambiguous; possibilities: "
  }

  function ParseErrorTextPart8(): BenchWorld.Bytes
  {
    "'--context' '--mode' '--parents' '--verbose' '--help' '--version'\n"
  }

  function ParseErrorTextPart9(): BenchWorld.Bytes
  {
    "'--verbose' '--version'\n"
  }

  function ParseErrorTextPart10(): BenchWorld.Bytes
  {
    "mkdir: "
  }

  function ParseErrorTextPart11(): BenchWorld.Bytes
  {
    "missing option value"
  }

  function ParseErrorTextPart12(): BenchWorld.Bytes
  {
    "parse error"
  }

  function ParseErrorTextPart13(): BenchWorld.Bytes
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
        (if |err.rawToken| > 2 && err.rawToken[2] == '=' then
          ParseErrorTextPart8()
         else ParseErrorTextPart9()) +
        ParseErrorTextPart3()
      else
        ParseErrorTextPart10() + Utf8.Encode(
        (if err.kind == CliTypes.MissingValue
        then ParseErrorTextPart11()
        else ParseErrorTextPart12())) +
        ParseErrorTextPart13() + Utf8.Encode(err.rawToken) + ParseErrorTextPart2()
  }

  function MissingOperandText(): BenchWorld.Bytes {
    "mkdir: missing operand\nTry 'mkdir --help' for more information.\n"
  }

  function AnnouncementText(quoted: BenchWorld.Bytes): BenchWorld.Bytes {
    "mkdir: created directory " + quoted + "\n"
  }

  ghost function Announcement(path: string): BenchWorld.Bytes {
    AnnouncementText(C.QuoteafPathResult(path))
  }

  function DiagnosticTextPart1(): BenchWorld.Bytes
  {
    "mkdir: cannot create directory "
  }

  function DiagnosticTextPart2(): BenchWorld.Bytes
  {
    ": "
  }

  function DiagnosticTextPart3(): BenchWorld.Bytes
  {
    "\n"
  }

  ghost function DiagnosticText(quoted: BenchWorld.Bytes, reason: string): BenchWorld.Bytes
  {
    DiagnosticTextPart1() + quoted + DiagnosticTextPart2() + Utf8.Encode(reason) + DiagnosticTextPart3()
  }

  ghost function Diagnostic(path: string, err: int): BenchWorld.Bytes
  {
    DiagnosticText(C.QuoteArgumentResult(Utf8.Encode(path)), C.CLocaleErrnoTextResult(err))
  }

  ghost function OutputPiece(verbose: bool, path: string, ok: bool): BenchWorld.Bytes {
    if verbose && ok then Announcement(path) else []
  }

  ghost function ErrorPiece(path: string, ok: bool, err: int): BenchWorld.Bytes
  {
    if ok then [] else Diagnostic(path, err)
  }

  // Cuts partition the observable bytes in operand order, including empty pieces.
  ghost predicate OrderedPieces(
    paths: seq<string>, verbose: bool, successes: seq<bool>, errors: seq<int>,
    output: BenchWorld.Bytes, diagnostics: BenchWorld.Bytes,
    outCuts: seq<nat>, errCuts: seq<nat>)
  {
    |successes| == |paths| && |errors| == |paths| &&
    |outCuts| == |paths| + 1 && |errCuts| == |paths| + 1 &&
    outCuts[0] == 0 && errCuts[0] == 0 &&
    outCuts[|paths|] == |output| && errCuts[|paths|] == |diagnostics| &&
    (forall i {:trigger outCuts[i]} {:trigger errCuts[i]} | 0 <= i < |paths| ::
      outCuts[i] <= outCuts[i + 1] <= |output| &&
      errCuts[i] <= errCuts[i + 1] <= |diagnostics| &&
      output[outCuts[i]..outCuts[i + 1]] == OutputPiece(verbose, paths[i], successes[i]) &&
      diagnostics[errCuts[i]..errCuts[i + 1]] == ErrorPiece(paths[i], successes[i], errors[i]))
  }

  ghost predicate CreationResults(
    paths: seq<string>, states: seq<BenchWorld.FileSystem>, successes: seq<bool>, errors: seq<int>,
    now: int, mask: bv32, observations: C.ValidFilesystemObservations)
  {
    |states| == |paths| + 1 && |successes| == |paths| && |errors| == |paths| &&
    (forall i | 0 <= i < |paths| ::
      C.CreateDirectorySpec(states[i], now, observations, mask, states[i + 1],
        paths[i], 511 as bv32, successes[i], errors[i]))
  }

  ghost predicate RunRelation(
    raw: Schema.MkdirCmdRaw,
    before: BenchWorld.FileSystem, after: BenchWorld.FileSystem,
    now: int, mask: bv32, observations: C.ValidFilesystemObservations,
    output: BenchWorld.Bytes, diagnostics: BenchWorld.Bytes, exit: int)
  {
    var paths := Schema.Operands(raw);
    exists states: seq<BenchWorld.FileSystem>, successes: seq<bool>, errors: seq<int>,
           outCuts: seq<nat>, errCuts: seq<nat> ::
      CreationResults(paths, states, successes, errors, now, mask, observations) &&
      states[0] == before && states[|paths|] == after &&
      OrderedPieces(paths, raw.verbose, successes, errors, output, diagnostics, outCuts, errCuts) &&
      exit == (if forall i | 0 <= i < |paths| :: successes[i] then 0 else 1)
  }

  function WriteErrorTextPart1(): BenchWorld.Bytes
  {
    "mkdir: write error: "
  }

  function WriteErrorTextPart2(): BenchWorld.Bytes
  {
    "\n"
  }

  ghost function WriteErrorText(reason: string): BenchWorld.Bytes
  {
    WriteErrorTextPart1() + Utf8.Encode(reason) + WriteErrorTextPart2()
  }

  ghost predicate StreamResults(
    beforeOut: BenchWorld.Bytes, afterOut: BenchWorld.Bytes,
    beforeErr: BenchWorld.Bytes, afterErr: BenchWorld.Bytes,
    observations: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult,
    output: BenchWorld.Bytes, diagnostics: BenchWorld.Bytes, creationExit: int, exit: int)
  {
    var outObservation := observations(BenchWorld.StreamWriteStdout(beforeOut, output));
    outObservation.StreamWriteResult? &&
    var outErr := outObservation.err;
    var finalDiagnostic := diagnostics +
      (if outErr == 0 then [] else WriteErrorText(C.CLocaleErrnoTextResult(outErr)));
    var errObservation := observations(BenchWorld.StreamWriteStderr(beforeErr, finalDiagnostic));
    errObservation.StreamWriteResult? &&
    C.WriteStdoutSpec(beforeOut, observations, afterOut, output, outObservation.committed, outErr) &&
    C.WriteStderrSpec(beforeErr, observations, afterErr, finalDiagnostic, errObservation.committed, errObservation.err) &&
    exit == (if creationExit == 0 && outErr == 0 && errObservation.err == 0 then 0 else 1)
  }

  twostate predicate Spec(raw: Schema.MkdirCmdRaw, io: BenchIO.IO, exit: int)
    reads io.fsRegion, io.stdoutRegion, io.stderrRegion,
          io.nowRegion, io.umaskRegion, io.trustedFilesystemRegion, io.trustedStreamsRegion
  {
    exists output: BenchWorld.Bytes, diagnostics: BenchWorld.Bytes, creationExit: int ::
      RunRelation(raw, old(io.fs()), io.fs(), io.now(), io.umask(),
        io.trustedFilesystem(), output, diagnostics, creationExit) &&
      StreamResults(old(io.stdout()), io.stdout(), old(io.stderr()), io.stderr(),
        io.trustedStreams(), output, diagnostics, creationExit, exit)
  }
}
