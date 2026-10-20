include "../../core/Errno.dfy"
include "../../core/World.dfy"
include "../../core/IO.dfy"
include "../../core/IOContract.dfy"
include "../../core/StringEscaping.dfy"
include "ReadlinkSchema.dfy"

module ReadlinkSpec {
  import StreamWorld = BenchWorld
  import StreamContract = IOContract

  import Errno = Errnos
  import Result = Results
  import BenchIO
  import Utf8 = Utf8Semantics
  import IOContract
  import BenchWorld
  import Schema = ReadlinkSchema
  import SE = StringEscaping




  function ErrnoTextSpec(err: BenchWorld.IOError): string
  {
    match err
    case NoSuchFile => "No such file or directory"
    case IsDirectory => "Is a directory"
    case NotDirectory => "Not a directory"
    case PermissionDenied => "Permission denied"
    case InvalidPath => "Invalid argument"
    case Other(msg) => msg
    case ReadFailure(_, message, _, _) => message
    case NativeFailure(_, message) => message
    case WriteFailure(_, message, _, _) => message
    case StreamFailure(_, message, _, _) => message
    case TimeParseFailure(message, _, _) => message
  }



  function HelpTextSpec(): BenchWorld.Bytes
  {
    "Usage: readlink [OPTION]... FILE...\n"
    + "Print value of a symbolic link.\n"
    + "\n"
    + "  -f, --canonicalize\n"
    + "         canonicalize by following symlinks; parsed but unsupported here\n"
    + "  -e, --canonicalize-existing\n"
    + "         canonicalize existing paths; parsed but unsupported here\n"
    + "  -m, --canonicalize-missing\n"
    + "         canonicalize paths with missing components; parsed but unsupported here\n"
    + "  -n, --no-newline\n"
    + "         do not output the trailing delimiter for one FILE\n"
    + "  -q, --quiet\n"
    + "  -s, --silent\n"
    + "         suppress most error messages (on by default)\n"
    + "  -v, --verbose\n"
    + "         report error messages\n"
    + "  -z, --zero\n"
    + "         end each output line with NUL, not newline\n"
    + "      --help\n"
    + "         display this help and exit\n"
    + "      --version\n"
    + "         output version information and exit\n"
    + "\n"
    + "Report bugs to: bug-coreutils@gnu.org\n"
    + "GNU coreutils home page: <https://www.gnu.org/software/coreutils/>\n"
    + "General help using GNU software: <https://www.gnu.org/gethelp/>\n"
    + "Report any translation bugs to <https://translationproject.org/team/>\n"
    + "Full documentation <https://www.gnu.org/software/coreutils/readlink>\n"
    + "or available locally via: info '(coreutils) readlink invocation'\n"
  }

  function VersionTextSpec(): BenchWorld.Bytes
  {
    "readlink (GNU coreutils) 9.10.13-2cf49\n"
    + "Copyright (C) 2026 Free Software Foundation, Inc.\n"
    + "License GPLv3+: GNU GPL version 3 or later <https://gnu.org/licenses/gpl.html>.\n"
    + "This is free software: you are free to change and redistribute it.\n"
    + "There is NO WARRANTY, to the extent permitted by law.\n"
    + "\n"
    + "Written by Dmitry V. Levin.\n"
  }

  function MissingOperandMessageSpec(): BenchWorld.Bytes
  {
    "readlink: missing operand\nTry 'readlink --help' for more information.\n"
  }

  function UnsupportedCanonicalizeMessageSpec(): BenchWorld.Bytes
  {
    "readlink: canonicalize modes are outside this benchmark\n"
  }

  function NoNewlineWarningSpec(): BenchWorld.Bytes
  {
    "readlink: ignoring --no-newline with multiple arguments\n"
  }

  function ErrorMessageSpec(path: BenchWorld.Path, err: BenchWorld.IOError): BenchWorld.Bytes
  {
    "readlink: " + SE.SpecQuoteFBytes(Utf8.Encode(path)) + ": " + ErrnoTextSpec(err) + "\n"
  }

  function NeedsShellQuoteSpec(path: BenchWorld.Path): bool
  {
    |path| == 0 ||
    exists i :: 0 <= i < |path| && ShellQuoteTriggerSpec(path[i])
  }

  function ShellQuoteTriggerSpec(ch: char): bool
  {
    ch == ' ' || ch == ':' || ch == '='
  }

  ghost predicate ErrorMessageMatchesSpec(path: BenchWorld.Path, err: BenchWorld.IOError, errOut: BenchWorld.Bytes)
  {
    errOut == ErrorMessageSpec(path, err) ||
    exists prefix: string ::
      errOut == prefix + "/readlink: " + SE.SpecQuoteFBytes(Utf8.Encode(path)) + ": " + ErrnoTextSpec(err) + "\n"
  }

  function OutputDelimiterSpec(cmd: Schema.ReadlinkCmd): BenchWorld.Bytes
  {
    if cmd.noNewline && |cmd.operands| == 1 then
      ""
    else if cmd.zeroTerminated then
      ['\0']
    else
      "\n"
  }

  function InitialWarningSpec(cmd: Schema.ReadlinkCmd): BenchWorld.Bytes
  {
    if cmd.noNewline && |cmd.operands| > 1 then NoNewlineWarningSpec() else ""
  }

  function MakeAbsoluteSpec(cwd: BenchWorld.Path, path: BenchWorld.Path): BenchWorld.Path
  {
    if BenchWorld.IsAbsolutePath(path) then
      path
    else
      BenchWorld.AppendPath(cwd, path)
  }

  function EndsInSlashSpec(path: BenchWorld.Path): bool
  {
    |path| > 0 && path[|path| - 1] == '/'
  }

  ghost function ReadlinkResultFieldsSpec(
    cmd: Schema.ReadlinkCmd,
    fs: BenchWorld.FileSystem, cwd: BenchWorld.Path, path: BenchWorld.Path
  ): BenchWorld.IOResult<BenchWorld.Path>
  {
    if path == "" then Result.Err(BenchWorld.NoSuchFile)
    else
      var actualPath := MakeAbsoluteSpec(cwd, path);
      match cmd.nativeReads
      case UnboundNativeReads => IOContract.ReadLinkResultFields(fs, actualPath)
      case BoundNativeReads(failures,context) => IOContract.ObservedReadLinkAtCwdResultFields(fs, context, failures, path)
  }

  ghost predicate ReadObservationRelation(
    cmd: Schema.ReadlinkCmd,
    fs: BenchWorld.FileSystem, cwd: BenchWorld.Path, path: BenchWorld.Path,
    result: BenchWorld.IOResult<BenchWorld.Path>
  )
  {
    if path == "" then result == Result.Err(BenchWorld.NoSuchFile)
    else
      var actualPath := MakeAbsoluteSpec(cwd, path);
      match cmd.nativeReads
      case UnboundNativeReads => result == IOContract.ReadLinkResultFields(fs, actualPath)
      case BoundNativeReads(failures,context) => IOContract.ReadLinkAtCwdSpec(fs, context, failures, path, result)
  }

  ghost predicate ReadFragmentRelation(
    cmd: Schema.ReadlinkCmd,
    path: BenchWorld.Path,
    result: BenchWorld.IOResult<BenchWorld.Path>,
                              stdoutFragment: BenchWorld.Bytes,
                              stderrFragment: BenchWorld.Bytes
  )
  {
    match result
    case Ok(target) =>
      stdoutFragment == Utf8.Encode(target) + OutputDelimiterSpec(cmd) &&
      stderrFragment == ""
    case Err(err) =>
      stdoutFragment == "" &&
      (if cmd.verbose then ErrorMessageMatchesSpec(path, err, stderrFragment)
       else stderrFragment == "")
  }

  ghost predicate OutputFragmentCutsRelation(
    fragments: seq<BenchWorld.Bytes>,
    output: BenchWorld.Bytes,
    cuts: seq<nat>
  )
  {
    |cuts| == |fragments| + 1 &&
    cuts[0] == 0 &&
    cuts[|fragments|] == |output| &&
    forall i: nat {:trigger cuts[i]} | i < |fragments| ::
      cuts[i] <= cuts[i + 1] <= |output| &&
      output[cuts[i]..cuts[i + 1]] == fragments[i]
  }

  ghost predicate RunFilesWitnessRelation(
    cmd: Schema.ReadlinkCmd,
    files: seq<BenchWorld.Path>,
    fs: BenchWorld.FileSystem,
    cwd: BenchWorld.Path,
    observations: seq<BenchWorld.IOResult<BenchWorld.Path>>,
    stdoutFragments: seq<BenchWorld.Bytes>,
    stderrFragments: seq<BenchWorld.Bytes>,
    stdoutCuts: seq<nat>,
    stderrCuts: seq<nat>,
    hadError: bool,
    out: BenchWorld.Bytes,
    errOut: BenchWorld.Bytes
  )
  {
    |observations| == |files| &&
    |stdoutFragments| == |files| &&
    |stderrFragments| == |files| &&
    (forall i: nat | i < |files| ::
       ReadObservationRelation(Schema.WithNativeReadOffset(cmd,files[..i]), fs, cwd, files[i], observations[i]) &&
       ReadFragmentRelation(
         Schema.WithNativeReadOffset(cmd,files[..i]),
         files[i],
         observations[i],
         stdoutFragments[i],
         stderrFragments[i]
       )) &&
    hadError == (exists i: nat :: i < |observations| && observations[i].Err?) &&
    OutputFragmentCutsRelation(stdoutFragments, out, stdoutCuts) &&
    OutputFragmentCutsRelation(stderrFragments, errOut, stderrCuts)
  }

  ghost predicate RunFilesRelation(
    cmd: Schema.ReadlinkCmd,
    files: seq<BenchWorld.Path>,
    fs: BenchWorld.FileSystem,
    cwd: BenchWorld.Path,
    hadError: bool,
    out: BenchWorld.Bytes,
    errOut: BenchWorld.Bytes
  )
  {
    exists observations: seq<BenchWorld.IOResult<BenchWorld.Path>>,
      stdoutFragments: seq<BenchWorld.Bytes>,
      stderrFragments: seq<BenchWorld.Bytes>,
      stdoutCuts: seq<nat>,
      stderrCuts: seq<nat> ::
      RunFilesWitnessRelation(
        cmd,
        files,
        fs,
        cwd,
        observations,
        stdoutFragments,
        stderrFragments,
        stdoutCuts,
        stderrCuts,
        hadError,
        out,
        errOut
      )
  }


  function WriteErrorText(reason: string): StreamWorld.Bytes
  {
    "readlink: write error: " + Utf8.Encode(reason) + "\n"
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
  twostate predicate PreparedSpec(raw: Schema.ReadlinkCmdRaw, io: BenchIO.IO, exit: int, plannedStdout: StreamWorld.Bytes, plannedStderr: StreamWorld.Bytes)
    reads io.directoryStateRegion,io.fsRegion,io.cwdRegion
  {
    var cmd := Schema.WithNativeFailures(Schema.Command(raw), old(io.trustedNativeFailures()),old(io.cwdContext()));
    io.directoryModel() == old(io.directoryModel()) &&
    io.cwdContext() == Schema.FinalNativeContext(cmd,old(io.cwdContext())) &&
    if cmd.mode == Schema.ModeHelp then
      plannedStdout == [] + HelpTextSpec() &&
      plannedStderr == [] &&
      exit == 0
    else if cmd.mode == Schema.ModeVersion then
      plannedStdout == [] + VersionTextSpec() &&
      plannedStderr == [] &&
      exit == 0
    else if |cmd.operands| == 0 then
      plannedStdout == [] &&
      plannedStderr == [] + MissingOperandMessageSpec() &&
      exit == 1
    else if cmd.mode == Schema.ModeUnsupportedCanonicalize then
      plannedStdout == [] &&
      plannedStderr == [] + UnsupportedCanonicalizeMessageSpec() &&
      exit == 1
    else
      exists hadError: bool, out: BenchWorld.Bytes, errOut: BenchWorld.Bytes ::
        RunFilesRelation(cmd, cmd.operands, old(io.fs()), old(io.cwd()), hadError, out, errOut) &&
        plannedStdout == [] + out &&
        plannedStderr == [] + InitialWarningSpec(cmd) + errOut &&
        exit == (if hadError then 1 else 0)
  }

  twostate predicate Spec(raw: Schema.ReadlinkCmdRaw, io: BenchIO.IO, exit: int)
    reads io.Footprint()
  {
    exists output: StreamWorld.Bytes, diagnostics: StreamWorld.Bytes, normalExit: int ::
      PreparedSpec(raw, io, normalExit, output, diagnostics) &&
      EmissionFields(old(io.stdout()), old(io.stderr()), io.stdout(), io.stderr(),
                     io.trustedStreams(), output, diagnostics, normalExit, exit)
  }
}
