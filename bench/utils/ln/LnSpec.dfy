include "../../core/Errno.dfy"
include "../../core/World.dfy"
include "../../core/IO.dfy"
include "../../core/IOContract.dfy"
include "../../core/StringEscaping.dfy"
include "LnSchema.dfy"

module LnSpec {
  import StreamWorld = BenchWorld
  import StreamContract = IOContract

  import Errno = Errnos
  import BenchIO
  import IOContract
  import BenchWorld
  import Schema = LnSchema
  import SE = StringEscaping
  import Utf8 = Utf8Semantics

  datatype ObservationContext = ObservationContext(
    filesystem: (BenchWorld.TrustedFilesystemRequest) -> BenchWorld.TrustedFilesystemResult,
    failures: (BenchWorld.NativeFailureRequest) -> int,
    times: BenchWorld.StatusTimeObservations,
    cursor: nat,
    credentials: BenchWorld.ProcessCredentials)

  ghost function Context(io: BenchIO.IO): (context: ObservationContext)
    reads io.trustedFilesystemRegion, io.trustedNativeFailuresRegion,
      io.credentialsRegion, io.statusObservationsRegion
    ensures context == ObservationContext(io.trustedFilesystem(), io.trustedNativeFailures(),
      io.statusObservations(), io.statusCursor(), io.credentials())
  {
    ObservationContext(io.trustedFilesystem(), io.trustedNativeFailures(),
      io.statusObservations(), io.statusCursor(), io.credentials())
  }

  ghost function AtCursor(observations: ObservationContext, cursor: nat): (context: ObservationContext)
    ensures context == ObservationContext(observations.filesystem, observations.failures,
      observations.times, cursor, observations.credentials)
  {
    observations.(cursor := cursor)
  }

  ghost function ObservedDirectory(fs: BenchWorld.FileSystem, observations: ObservationContext,
    path: string, follow: bool): bool
  {
    var result := IOContract.ObservedNativeStatusResultFields(
      observations.times, observations.failures, observations.cursor, fs, path, follow);
    result.Ok? && result.v.kind == BenchWorld.DirectoryKind
  }

  ghost predicate DirectoryObservation(fs: BenchWorld.FileSystem, observations: ObservationContext,
    path: string, follow: bool, ok: bool, isDir: bool, err: int)
  {
    var result := IOContract.ObservedNativeStatusResultFields(
      observations.times, observations.failures, observations.cursor, fs, path, follow);
    ok == result.Ok? && isDir == ObservedDirectory(fs, observations, path, follow) &&
    err == IOContract.ResultErrno(result)
  }

  ghost function DestinationReadCount(operands: seq<string>): nat
    requires 1 <= |operands| <= 2
  {
    if |operands| == 2 && operands[0] != "" then 1 else 0
  }

  ghost function StatusReadCount(cmd: Schema.LnCmd, fs: BenchWorld.FileSystem,
    observations: ObservationContext): nat
  {
    if cmd.mode != Schema.ModeRun || |cmd.operands| == 0 then 0
    else if |cmd.operands| > 2 then
      1 + (if ObservedDirectory(fs, observations, cmd.operands[|cmd.operands| - 1], true)
        then (if cmd.symbolic then 0 else |cmd.operands| - 1) else 0)
    else DestinationReadCount(cmd.operands) + (if cmd.symbolic then 0 else 1)
  }




  function ErrnoTextSpec(err: int): string
  {
    if err == Errno.ENOENT then
      "No such file or directory"
    else if err == Errno.EACCES then
      "Permission denied"
    else if err == Errno.EEXIST then
      "File exists"
    else if err == Errno.ENOTDIR then
      "Not a directory"
    else if err == Errno.EISDIR then
      "Is a directory"
    else if err == Errno.EINVAL then
      "Invalid argument"
    else if err == Errno.ENAMETOOLONG then
      "File name too long"
    else if err == Errno.ELOOP then
      "Too many levels of symbolic links"
    else
      "unknown error"
  }

  function HelpTextSpec(): BenchWorld.Bytes
  {
    "Usage: ln [OPTION]... TARGET LINK_NAME\n"
    + "Create a link named LINK_NAME to TARGET.\n"
    + "\n"
    + "With one TARGET, create a link in the current directory.\n"
    + "\n"
    + "  -s, --symbolic\n"
    + "         make symbolic links instead of hard links\n"
    + "      --help\n"
    + "         display this help and exit\n"
    + "      --version\n"
    + "         output version information and exit\n"
    + "\n"
    + "Report bugs to: bug-coreutils@gnu.org\n"
    + "GNU coreutils home page: <https://www.gnu.org/software/coreutils/>\n"
    + "General help using GNU software: <https://www.gnu.org/gethelp/>\n"
    + "Report any translation bugs to <https://translationproject.org/team/>\n"
    + "Full documentation <https://www.gnu.org/software/coreutils/ln>\n"
    + "or available locally via: info '(coreutils) ln invocation'\n"
  }

  function VersionTextSpec(): BenchWorld.Bytes
  {
    "ln (GNU coreutils) 9.10.13-2cf49\n"
    + "Copyright (C) 2026 Free Software Foundation, Inc.\n"
    + "License GPLv3+: GNU GPL version 3 or later <https://gnu.org/licenses/gpl.html>.\n"
    + "This is free software: you are free to change and redistribute it.\n"
    + "There is NO WARRANTY, to the extent permitted by law.\n"
    + "\n"
    + "Written by Mike Parker and David MacKenzie.\n"
  }

  function MissingOperandMessageSpec(): BenchWorld.Bytes
  {
    "ln: missing file operand\nTry 'ln --help' for more information.\n"
  }

  function UnsupportedHardLinkMessageSpec(): BenchWorld.Bytes
  {
    "ln: hard links are outside this benchmark; use -s/--symbolic\n"
  }

  function FailedAccessMessageTextPart1(): StreamWorld.Bytes
  {
    "ln: failed to access "
  }

  function FailedAccessMessageTextPart2(): StreamWorld.Bytes
  {
    ": "
  }

  function FailedAccessMessageTextPart3(): StreamWorld.Bytes
  {
    "\n"
  }

  ghost function FailedAccessMessageText(source: BenchWorld.Path, err: int, reason: string): BenchWorld.Bytes
  {
    FailedAccessMessageTextPart1() + SE.SpecQuoteAfBytes(Utf8.Encode(source)) +
    FailedAccessMessageTextPart2() + Utf8.Encode(reason) + FailedAccessMessageTextPart3()
  }

  ghost function FailedAccessMessageSpec(source: BenchWorld.Path, err: int): BenchWorld.Bytes
  {
    FailedAccessMessageText(source, err, IOContract.CLocaleErrnoTextResult(err))
  }

  function HardDirectoryMessageSpecPart1(): StreamWorld.Bytes
  {
    "ln: "
  }

  function HardDirectoryMessageSpecPart2(): StreamWorld.Bytes
  {
    ": hard link not allowed for directory\n"
  }

  ghost function HardDirectoryMessageSpec(source: BenchWorld.Path): BenchWorld.Bytes
  {
    HardDirectoryMessageSpecPart1() + SE.SpecQuoteFBytes(Utf8.Encode(source)) +
    HardDirectoryMessageSpecPart2()
  }

  function CreateHardLinkErrorMessageTextPart1(): StreamWorld.Bytes
  {
    "ln: "
  }

  function CreateHardLinkErrorMessageTextPart2(): StreamWorld.Bytes
  {
    "failed to create hard link to "
  }

  function CreateHardLinkErrorMessageTextPart3(): StreamWorld.Bytes
  {
    "failed to create hard link "
  }

  function CreateHardLinkErrorMessageTextPart4(): StreamWorld.Bytes
  {
    " => "
  }

  function CreateHardLinkErrorMessageTextPart5(): StreamWorld.Bytes
  {
    ": "
  }

  function CreateHardLinkErrorMessageTextPart6(): StreamWorld.Bytes
  {
    "\n"
  }

  ghost function CreateHardLinkErrorMessageText(source: BenchWorld.Path, linkName: BenchWorld.Path, err: int, reason: string): BenchWorld.Bytes
  {
    CreateHardLinkErrorMessageTextPart1() +
    (if err == Errno.EMLINK then
       CreateHardLinkErrorMessageTextPart2() + SE.SpecQuoteAfBytes(Utf8.Encode(source))
     else if err == Errno.EEXIST || err == Errno.ENOSPC || err == Errno.EDQUOT || err == Errno.EROFS then
       CreateHardLinkErrorMessageTextPart3() + SE.SpecQuoteAfBytes(Utf8.Encode(linkName))
     else
       CreateHardLinkErrorMessageTextPart3() + SE.SpecQuoteAfBytes(Utf8.Encode(linkName)) +
       CreateHardLinkErrorMessageTextPart4() + SE.SpecQuoteAfBytes(Utf8.Encode(source))) +
    CreateHardLinkErrorMessageTextPart5() + Utf8.Encode(reason) + CreateHardLinkErrorMessageTextPart6()
  }

  ghost function CreateHardLinkErrorMessageSpec(source: BenchWorld.Path, linkName: BenchWorld.Path, err: int): BenchWorld.Bytes
  {
    CreateHardLinkErrorMessageText(source, linkName, err, IOContract.CLocaleErrnoTextResult(err))
  }

  ghost function TrimTrailingSlashes(path: string): string
    decreases |path|
  {
    if |path| > 0 && path[|path| - 1] == '/' then
      TrimTrailingSlashes(path[..|path| - 1])
    else
      path
  }

  ghost function LastSlash(path: string): int
    ensures -1 <= LastSlash(path) < |path|
    decreases |path|
  {
    if |path| == 0 then -1
    else if path[|path| - 1] == '/' then |path| - 1
    else LastSlash(path[..|path| - 1])
  }

  ghost function BaseName(path: string): string
  {
    var trimmed := TrimTrailingSlashes(path);
    if |trimmed| == 0 then (if |path| == 0 then "" else "/")
    else trimmed[LastSlash(trimmed) + 1..]
  }

  ghost function InDirectory(directory: string, source: string): string
  {
    directory + (if |directory| > 0 && directory[|directory| - 1] == '/' then "" else "/") +
    BaseName(source)
  }

  ghost function LinkDestination(
    fs: BenchWorld.FileSystem, observations: ObservationContext, operands: seq<string>
  ): string
    requires 1 <= |operands| <= 2
  {
    if |operands| == 1 then InDirectory(".", operands[0])
    else if operands[0] == "" then operands[1]
    else if ObservedDirectory(fs, observations, operands[1], true) then InDirectory(operands[1], operands[0])
    else operands[1]
  }

  function UnsupportedTargetDirectoryMessageSpec(): BenchWorld.Bytes
  {
    "ln: target-directory link modes are outside this benchmark; use explicit SOURCE LINK_NAME\n"
  }

  function CreateSymlinkErrorMessageTextPart1(): StreamWorld.Bytes
  {
    "ln: failed to create symbolic link "
  }

  function CreateSymlinkErrorMessageTextPart2(): StreamWorld.Bytes
  {
    ""
  }

  function CreateSymlinkErrorMessageTextPart3(): StreamWorld.Bytes
  {
    " -> "
  }

  function CreateSymlinkErrorMessageTextPart4(): StreamWorld.Bytes
  {
    ": "
  }

  function CreateSymlinkErrorMessageTextPart5(): StreamWorld.Bytes
  {
    "\n"
  }

  ghost function CreateSymlinkErrorMessageText(linkName: BenchWorld.Path, source: BenchWorld.Path, err: int, reason: string): BenchWorld.Bytes
  {
    CreateSymlinkErrorMessageTextPart1() + SE.SpecQuoteAfBytes(Utf8.Encode(linkName)) +
    (if source == CreateSymlinkErrorMessageTextPart2() then CreateSymlinkErrorMessageTextPart3() + SE.SpecQuoteAfBytes(Utf8.Encode(source)) else CreateSymlinkErrorMessageTextPart2()) +
    CreateSymlinkErrorMessageTextPart4() + Utf8.Encode(reason) + CreateSymlinkErrorMessageTextPart5()
  }

  ghost function CreateSymlinkErrorMessageSpec(linkName: BenchWorld.Path, source: BenchWorld.Path, err: int): BenchWorld.Bytes
  {
    CreateSymlinkErrorMessageText(linkName, source, err, IOContract.CLocaleErrnoTextResult(err))
  }

  function TargetDirectoryErrorMessageTextPart1(): StreamWorld.Bytes
  {
    "ln: target "
  }

  function TargetDirectoryErrorMessageTextPart2(): StreamWorld.Bytes
  {
    ": "
  }

  function TargetDirectoryErrorMessageTextPart3(): StreamWorld.Bytes
  {
    "\n"
  }

  ghost function TargetDirectoryErrorMessageText(target: BenchWorld.Path, err: int, reason: string): BenchWorld.Bytes
  {
    TargetDirectoryErrorMessageTextPart1() + SE.SpecQuoteAfBytes(Utf8.Encode(target)) +
    TargetDirectoryErrorMessageTextPart2() + Utf8.Encode(reason) + TargetDirectoryErrorMessageTextPart3()
  }

  ghost function TargetDirectoryErrorMessageSpec(target: BenchWorld.Path, err: int): BenchWorld.Bytes
  {
    TargetDirectoryErrorMessageText(target, err, IOContract.CLocaleErrnoTextResult(err))
  }

  opaque ghost predicate LinkStepRelation(
    beforeFs: BenchWorld.FileSystem,
    afterFs: BenchWorld.FileSystem,
    now: int,
    trustedFilesystem: ObservationContext,
    source: BenchWorld.Path,
    destination: BenchWorld.Path,
    symbolic: bool,
    diagnostic: BenchWorld.Bytes,
    success: bool
  )
  {
    if symbolic then
      exists ok: bool, err: int ::
        IOContract.CreateSymlinkSpec(
          beforeFs, now, trustedFilesystem.credentials, trustedFilesystem.failures, afterFs, destination, source, ok, err) &&
        diagnostic == (if ok then [] else CreateSymlinkErrorMessageSpec(destination, source, err)) &&
        success == ok
    else
      exists sourceOk: bool, sourceIsDir: bool, sourceErr: int ::
        DirectoryObservation(
          beforeFs, trustedFilesystem, source, false, sourceOk, sourceIsDir, sourceErr) &&
        (if !sourceOk then
           afterFs == beforeFs &&
           diagnostic == FailedAccessMessageSpec(source, sourceErr) &&
           !success
         else if sourceIsDir then
           afterFs == beforeFs &&
           diagnostic == HardDirectoryMessageSpec(source) &&
           !success
         else
           exists ok: bool, err: int ::
             IOContract.CreateHardLinkSpec(
               beforeFs, now, trustedFilesystem.filesystem, afterFs,
               source, destination, ok, err) &&
             diagnostic == (if ok then [] else
               CreateHardLinkErrorMessageSpec(source, destination, err)) &&
             success == ok)
  }

  opaque ghost predicate LinkBatchRelation(
    beforeFs: BenchWorld.FileSystem,
    afterFs: BenchWorld.FileSystem,
    now: int,
    trustedFilesystem: ObservationContext,
    sources: seq<BenchWorld.Path>,
    directory: BenchWorld.Path,
    symbolic: bool,
    diagnostic: BenchWorld.Bytes,
    success: bool
  )
  {
    exists states: seq<BenchWorld.FileSystem>,
           diagnostics: seq<BenchWorld.Bytes>,
           results: seq<bool>,
           pieces: seq<BenchWorld.Bytes>,
           stepResults: seq<bool> ::
      |states| == |sources| + 1 &&
      |diagnostics| == |sources| + 1 &&
      |results| == |sources| + 1 &&
      |pieces| == |sources| &&
      |stepResults| == |sources| &&
      states[0] == beforeFs &&
      states[|sources|] == afterFs &&
      diagnostics[0] == [] &&
      diagnostics[|sources|] == diagnostic &&
      results[0] &&
      results[|sources|] == success &&
      (forall i: nat :: i < |sources| ==>
          LinkStepRelation(
            states[i], states[i + 1], now, AtCursor(trustedFilesystem, trustedFilesystem.cursor + (if symbolic then 0 else i)),
            sources[i], InDirectory(directory, sources[i]), symbolic,
            pieces[i], stepResults[i]) &&
          diagnostics[i + 1] == diagnostics[i] + pieces[i] &&
          results[i + 1] == (results[i] && stepResults[i]))
  }

  ghost function LinkNameIsDirectoryFs(fs: BenchWorld.FileSystem, linkName: BenchWorld.Path): bool
  {
    match IOContract.ResolvePathForMetadataFields(fs, linkName, true)
    case Ok(resolved) =>
      BenchWorld.FsContainsPath(fs, resolved) &&
      (match BenchWorld.FsNodeAt(fs, resolved)
       case Directory(_, _, _) => true
       case _ => false)
    case Err(_) => false
  }


  function WriteErrorTextPart1(): StreamWorld.Bytes
  {
    "ln: write error: "
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
  twostate predicate PreparedSpec(raw: Schema.LnCmdRaw, io: BenchIO.IO, exit: int, plannedStdout: StreamWorld.Bytes, plannedStderr: StreamWorld.Bytes)
    reads io.fsRegion, io.nowRegion, io.trustedFilesystemRegion, io.statusObservationsRegion, io.trustedNativeFailuresRegion, io.credentialsRegion
  {
    var cmd := Schema.Command(raw);
    io.statusCursor() == old(io.statusCursor()) + StatusReadCount(cmd, old(io.fs()), old(Context(io))) &&
    (if cmd.mode == Schema.ModeHelp then
      io.fs() == old(io.fs()) &&
      plannedStdout == [] + HelpTextSpec() &&
      plannedStderr == [] &&
      exit == 0
    else if cmd.mode == Schema.ModeVersion then
      io.fs() == old(io.fs()) &&
      plannedStdout == [] + VersionTextSpec() &&
      plannedStderr == [] &&
      exit == 0
    else if |cmd.operands| == 0 then
      io.fs() == old(io.fs()) &&
      plannedStdout == [] &&
      plannedStderr == [] + MissingOperandMessageSpec() &&
      exit == 1
    else if |cmd.operands| > 2 then
      var target := cmd.operands[|cmd.operands| - 1];
      plannedStdout == [] &&
      (exists targetOk: bool, targetIsDir: bool, targetErr: int ::
        DirectoryObservation(
          old(io.fs()), old(Context(io)), target, true, targetOk, targetIsDir, targetErr) &&
        (if !(targetOk && targetIsDir) then
           io.fs() == old(io.fs()) &&
           plannedStderr == [] +
             TargetDirectoryErrorMessageSpec(target, if targetOk then 20 else targetErr) &&
           exit == 1
         else
           exists diagnostic: BenchWorld.Bytes, success: bool
             {:trigger LinkBatchRelation(old(io.fs()), io.fs(), old(io.now()), AtCursor(old(Context(io)), old(io.statusCursor()) + 1), cmd.operands[..|cmd.operands| - 1],
               target, cmd.symbolic, diagnostic, success)} ::
             LinkBatchRelation(
               old(io.fs()), io.fs(), old(io.now()), AtCursor(old(Context(io)), old(io.statusCursor()) + 1),
               cmd.operands[..|cmd.operands| - 1], target, cmd.symbolic,
               diagnostic, success) &&
             plannedStderr == [] + diagnostic &&
             exit == (if success then 0 else 1)))
    else
      var source := cmd.operands[0];
      var destination := LinkDestination(old(io.fs()), old(Context(io)), cmd.operands);
      plannedStdout == [] &&
      (exists diagnostic: BenchWorld.Bytes, success: bool
        {:trigger LinkStepRelation(old(io.fs()), io.fs(), old(io.now()),
          AtCursor(old(Context(io)), old(io.statusCursor()) + DestinationReadCount(cmd.operands)),
          source, destination, cmd.symbolic, diagnostic, success)} ::
        LinkStepRelation(old(io.fs()), io.fs(), old(io.now()),
          AtCursor(old(Context(io)), old(io.statusCursor()) + DestinationReadCount(cmd.operands)),
          source, destination, cmd.symbolic, diagnostic, success) &&
        plannedStderr == diagnostic && exit == (if success then 0 else 1)))
  }

  twostate predicate Spec(raw: Schema.LnCmdRaw, io: BenchIO.IO, exit: int)
    reads io.fsRegion, io.nowRegion, io.trustedFilesystemRegion, io.statusObservationsRegion, io.trustedNativeFailuresRegion, io.credentialsRegion, io.stdoutRegion, io.stderrRegion, io.trustedStreamsRegion
  {
    exists output: StreamWorld.Bytes, diagnostics: StreamWorld.Bytes, normalExit: int ::
      PreparedSpec(raw, io, normalExit, output, diagnostics) &&
      EmissionFields(old(io.stdout()), old(io.stderr()), io.stdout(), io.stderr(),
                     io.trustedStreams(), output, diagnostics, normalExit, exit)
  }
}
