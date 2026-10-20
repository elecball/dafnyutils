include "RmSchema.dfy"
include "../../core/IO.dfy"
include "../../core/Utf8.dfy"
include "../../core/CliModel.dfy"
include "../../core/Errno.dfy"
include "../../core/StringEscaping.dfy"
include "../../core/PathSpec.dfy"

module RmSpec {
  import BenchIO
  import R = Results
  import opened BenchWorld
  import CliTypes
  import CliModel
  import Schema = RmSchema
  import Utf8 = Utf8Semantics
  import C = IOContract
  import Errno = Errnos
  import Escaping = StringEscaping
  import Paths = MvPathSpec

  function HelpTextSpec(): Bytes {
    "Usage: rm [OPTION]... [FILE]...\n"
    + "Remove (unlink) the FILE(s).\n"
    + "\n"
    + "  -f, --force\n"
    + "         ignore nonexistent files and arguments, never prompt\n"
    + "  -i\n"
    + "         prompt before every removal\n"
    + "  -I\n"
    + "         prompt once before removing more than three files,\n"
    + "         or when removing recursively; less intrusive than -i,\n"
    + "         while still giving protection against most mistakes\n"
    + "      --interactive[=WHEN]\n"
    + "         prompt according to WHEN: never, once (-I), or always (-i);\n"
    + "         without WHEN, prompt always\n"
    + "      --one-file-system\n"
    + "         when removing a hierarchy recursively,\n"
    + "         skip any directory that is on a file system different\n"
    + "         from that of the corresponding command line argument\n"
    + "      --no-preserve-root\n"
    + "         do not treat '/' specially\n"
    + "      --preserve-root[=all]\n"
    + "         do not remove '/' (default);\n"
    + "         with 'all', reject any command line argument\n"
    + "         on a separate device from its parent\n"
    + "  -r, -R, --recursive\n"
    + "         remove directories and their contents recursively\n"
    + "  -d, --dir\n"
    + "         remove empty directories\n"
    + "  -v, --verbose\n"
    + "         explain what is being done\n"
    + "      --help\n"
    + "         display this help and exit\n"
    + "      --version\n"
    + "         output version information and exit\n"
    + "\n"
    + "By default, rm does not remove directories.  Use the --recursive (-r or -R)\n"
    + "option to remove each listed directory, too, along with all of its contents.\n"
    + "\n"
    + "Any attempt to remove a file whose last file name component is '.' or '..'\n"
    + "is rejected with a diagnostic.\n"
    + "\n"
    + "To remove a file whose name starts with a '-', for example '-foo',\n"
    + "use one of these commands:\n"
    + "  rm -- -foo\n"
    + "\n"
    + "  rm ./-foo\n"
    + "\n"
    + "If you use rm to remove a file, it might be possible to recover\n"
    + "some of its contents, given sufficient expertise and/or time.  For greater\n"
    + "assurance that the contents are unrecoverable, consider using shred(1).\n"
    + "\n"
    + "Report bugs to: bug-coreutils@gnu.org\n"
    + "GNU coreutils home page: <https://www.gnu.org/software/coreutils/>\n"
    + "General help using GNU software: <https://www.gnu.org/gethelp/>\n"
    + "Report any translation bugs to <https://translationproject.org/team/>\n"
    + "Full documentation <https://www.gnu.org/software/coreutils/rm>\n"
    + "or available locally via: info '(coreutils) rm invocation'\n"
  }

  function VersionTextSpec(): Bytes {
    "rm (GNU coreutils) 9.10.13-2cf49\n"
    + "Copyright (C) 2026 Free Software Foundation, Inc.\n"
    + "License GPLv3+: GNU GPL version 3 or later <https://gnu.org/licenses/gpl.html>.\n"
    + "This is free software: you are free to change and redistribute it.\n"
    + "There is NO WARRANTY, to the extent permitted by law.\n"
    + "\n"
    + "Written by Paul Rubin, David MacKenzie, Richard M. Stallman,\n"
    + "and Jim Meyering.\n"
  }

  function UsageText(): Bytes {
    "Try 'rm --help' for more information.\n"
  }

  function MissingOperandText(): Bytes { "rm: missing operand\n" + UsageText() }

  function LongOptionName(token: string): string {
    var eq := CliModel.FindChar(token, '=');
    var name := if eq >= 0 then token[..eq] else token;
    if |name| > 2 && CliModel.HasPrefix(name, "--") then
      var prefix := name[2..];
      if CliModel.HasPrefix("force",prefix) then "--force"
      else if CliModel.HasPrefix("interactive",prefix) then "--interactive"
      else if CliModel.HasPrefix("one-file-system",prefix) then "--one-file-system"
      else if CliModel.HasPrefix("no-preserve-root",prefix) then "--no-preserve-root"
      else if CliModel.HasPrefix("preserve-root",prefix) then "--preserve-root"
      else if CliModel.HasPrefix("-presume-input-tty",prefix) then "---presume-input-tty"
      else if CliModel.HasPrefix("recursive",prefix) then "--recursive"
      else if CliModel.HasPrefix("dir",prefix) then "--dir"
      else if CliModel.HasPrefix("verbose",prefix) then "--verbose"
      else if CliModel.HasPrefix("help",prefix) then "--help"
      else if CliModel.HasPrefix("version",prefix) then "--version"
      else name
    else name
  }

  function ParseDiagnostic(err: CliTypes.ParseError, invalidShort: char): Bytes {
    if err.kind == CliTypes.UnknownOption && !CliModel.HasPrefix(err.rawToken,"--") && |err.rawToken| > 1 then
      "rm: invalid option -- '" + [Utf8.EncodeChar(invalidShort)[0]] + "'\n"
    else Utf8.Encode(
      if err.kind == CliTypes.UnknownOption then
        if CliModel.HasPrefix(err.rawToken, "--") then
          "rm: unrecognized option '" + err.rawToken + "'\n"
        else "rm: invalid option\n"
      else if err.kind == CliTypes.UnexpectedValue then
        "rm: option '" + LongOptionName(err.rawToken) + "' doesn't allow an argument\n"
      else if err.kind == CliTypes.Ambiguous then
        "rm: option '" + err.rawToken + "' is ambiguous; possibilities:" +
        (if CliModel.HasPrefix(err.rawToken,"--=") then
          " '--force' '--interactive' '--one-file-system' '--no-preserve-root'" +
          " '--preserve-root' '---presume-input-tty' '--recursive' '--dir' '--verbose'" +
          " '--help' '--version'\n"
         else " '--verbose' '--version'\n")
      else "rm: option '" + err.rawToken + "' requires an argument\n")
  }

  function ParseErrorText(err: CliTypes.ParseError, invalidShort: char): Bytes {
    ParseDiagnostic(err,invalidShort) + UsageText()
  }

  function HyphenSuggestion(path: Path): Bytes {
    var encoded := Utf8.Encode(path);
    var trigger := exists i: int ::
      0 <= i < |encoded| && encoded[i] != ':' &&
      Escaping.SpecShellQuoteTriggerByte(encoded[i],i == 0,|encoded| == 1);
    var quoted := if trigger then Escaping.SpecQuoteAfBytes(encoded) else encoded;
    "Try 'rm ./" + quoted + "' to remove the file " + Escaping.SpecQuoteAfBytes(encoded) + ".\n"
  }

  function ModeErrorMessage(mode: Schema.RmMode, quoted: Bytes): Bytes {
    match mode
    case ModeInvalidPreserve(value) =>
      "rm: unrecognized --preserve-root argument: " + quoted + "\n"
    case ModeAbbreviatedNoPreserve =>
      "rm: you may not abbreviate the --no-preserve-root option\n"
    case ModeInvalidInteractive(value) =>
      "rm: " + (if value == "" then "ambiguous" else "invalid") + " argument " + quoted +
      " for '--interactive'\nValid arguments are:\n  - 'never', 'no', 'none'\n  - 'once'\n  - 'always', 'yes'\n" + UsageText()
    case _ => "rm: interactive input requires a terminal and incremental input API\n"
  }

  ghost function ModeErrorText(mode: Schema.RmMode): Bytes {
    ModeErrorMessage(mode,match mode
      case ModeInvalidPreserve(value) => C.QuoteafPathResult(value)
      case ModeInvalidInteractive(value) => C.QuoteArgumentResult(Utf8.Encode(value))
      case _ => [])
  }

  function CannotRemoveMessage(quoted: Bytes, reason: string): Bytes {
    "rm: cannot remove " + quoted + ": " + Utf8.Encode(reason) + "\n"
  }

  ghost function CannotRemoveText(path: Path, err: int): Bytes {
    CannotRemoveMessage(C.QuoteafPathResult(path),C.CLocaleErrnoTextResult(err))
  }

  function TraversalMessage(path: Path, reason: string): Bytes {
    "rm: traversal failed: " + Escaping.SpecQuoteFBytes(Utf8.Encode(path)) + ": " + Utf8.Encode(reason) + "\n"
  }

  ghost function TraversalText(path: Path, err: int): Bytes {
    TraversalMessage(path,C.CLocaleErrnoTextResult(err))
  }

  function RemovedMessage(quoted: Bytes, directory: bool): Bytes {
    (if directory then "removed directory " else "removed ") + quoted + "\n"
  }

  ghost function RemovedText(path: Path, directory: bool): Bytes {
    RemovedMessage(C.QuoteafPathResult(path),directory)
  }

  function RootAttributesMessage(reason: string): Bytes {
    "rm: failed to get attributes of '/': " + Utf8.Encode(reason) + "\n"
  }

  ghost function RootAttributesText(err: int): Bytes {
    RootAttributesMessage(C.CLocaleErrnoTextResult(err))
  }

  ghost predicate CommandPath(path: Path, value: Path)
  {
    if |path| == 0 then value == ""
    else if Paths.SlashesOnly(path) then value == "/"
    else exists base: Path, trailing: string ::
      Paths.PathWithoutTrailingSlashes(path,base,trailing) &&
      value == base + (if |trailing| > 0 then "/" else "")
  }

  function ChildPath(parent: Path, name: string): Path {
    parent + (if |parent| > 0 && parent[|parent|-1] == '/' then "" else "/") + name
  }

  function DotOperand(path: Path): bool {
    var parts := C.RawPathSegmentsFields(path);
    |parts| > 0 && parts[|parts|-1] in {".", ".."}
  }

  const LinuxEilseq: int := 84

  function Ignored(raw: Schema.RmCmdRaw, err: int): bool {
    raw.force && err in {Errno.ENOENT, Errno.ENOTDIR, Errno.EINVAL, LinuxEilseq}
  }

  datatype Refusal = NoRefusal | DirectoryRefusal | DotRefusal | RootRefusal |
    CycleRefusal | DeviceRefusal | PreserveDeviceRefusal | ParentRefusal

  function RefusalMessage(path: Path, why: Refusal, quoted: Bytes, quotedParent: Bytes): Bytes {
    match why
    case DirectoryRefusal => CannotRemoveMessage(quoted, "Is a directory")
    case DotRefusal =>
      "rm: refusing to remove '.' or '..' directory: skipping " + quoted + "\n"
    case RootRefusal =>
      (if path == "/" then "rm: it is dangerous to operate recursively on '/'\n"
       else "rm: it is dangerous to operate recursively on " + quoted + " (same as '/')\n") +
      "rm: use --no-preserve-root to override this failsafe\n"
    case CycleRefusal =>
      "rm: WARNING: Circular directory structure.\nThis almost certainly means that you have a corrupted file system.\nNOTIFY YOUR SYSTEM MANAGER.\nThe following directory is part of the cycle:\n  " + Escaping.SpecQuoteFBytes(Utf8.Encode(path)) + "\n\n"
    case DeviceRefusal =>
      "rm: skipping " + quoted + ", since it's on a different device\n"
    case PreserveDeviceRefusal =>
      "rm: skipping " + quoted + ", since it's on a different device\n" +
      "rm: and --preserve-root=all is in effect\n"
    case ParentRefusal =>
      "rm: failed to stat " + quotedParent + ": skipping " +
        quoted + "\n"
    case NoRefusal => []
  }

  ghost function RefusalText(path: Path, why: Refusal): Bytes {
    RefusalMessage(path,why,C.QuoteafPathResult(path),C.QuoteafPathResult(ChildPath(path,"..")))
  }

  function BasicRefusal(raw: Schema.RmCmdRaw, path: Path, top: bool,
    rootKey: HostInodeKey, rootDevice: int, seen: set<HostInodeKey>, status: FileTimeStatus): Refusal
  {
    if !raw.recursive && !raw.directory then DirectoryRefusal
    else if !raw.recursive then NoRefusal
    else if top && DotOperand(path) then DotRefusal
    else if top && raw.preserveRoot && HostInodeKey(status.device,status.inode) == rootKey then RootRefusal
    else if !top && raw.oneFileSystem && status.device != rootDevice then DeviceRefusal
    else if HostInodeKey(status.device,status.inode) in seen then CycleRefusal
    else NoRefusal
  }

  ghost predicate StatusPath(path: Path, value: Path)
  {
    if |path| == 0 then value == ""
    else if Paths.SlashesOnly(path) then value == "/"
    else exists trailing: string :: Paths.PathWithoutTrailingSlashes(path,value,trailing)
  }

  ghost predicate ParentAllowed(raw: Schema.RmCmdRaw, path: Path, top: bool,
    status: FileTimeStatus, fs: FileSystem, trusted: C.ValidFilesystemObservations)
  {
    !raw.recursive || !raw.preserveAll || !top ||
      exists parent: IOResult<FileTimeStatus> ::
        StatusResult(fs,trusted,ChildPath(path,".."),parent) && parent.Ok? && parent.v.device == status.device
  }

  ghost predicate StatusResult(fs: FileSystem, trusted: C.ValidFilesystemObservations,
    path: Path, result: IOResult<FileTimeStatus>)
  {
    var status := C.ResultValue(result, FileTimeStatus(0,0,0,0,false,false,0,0,0));
    exists lookup: Path :: StatusPath(path,lookup) &&
      C.GetFileTimesSpec(fs,trusted,lookup,false,result.Ok?,status.atimeSec,status.atimeNsec,
        status.mtimeSec,status.mtimeNsec,status.isDir,status.isSymlink,
        status.device,status.inode,status.linkCount,C.ResultErrno(result))
  }

  ghost function HostKeys(fs: FileSystem): set<HostInodeKey> {
    set id: InodeId | id in fs.inodes :: fs.inodes[id].hostKey
  }

  ghost function EntryNames(entries: set<DirEntry>): set<string> {
    set entry: DirEntry | entry in entries :: entry.name
  }

  ghost function Names(names: seq<string>): set<string> {
    set i: int | 0 <= i < |names| :: names[i]
  }

  datatype Listing = Listing(order: seq<string>, ghost entries: set<DirEntry>, openError: int, readError: int)

  ghost predicate Listed(fs: FileSystem, path: Path, listing: Listing) {
    if listing.openError != 0 then
      C.OpenDirOutcomeFields(fs,path,false,listing.openError) && listing.order == [] &&
      listing.entries == {} && listing.readError == 0
    else
      0 <= listing.readError && C.OpenDirOutcomeFields(fs,path,true,0) &&
      (exists resolved: Path ::
        C.ResolvePathForMetadataFields(fs,path,true) == R.Ok(resolved) &&
        FsContainsPath(fs,resolved) &&
        listing.entries == C.DirectoryEntriesForPathFields(fs,resolved)) &&
      |Names(listing.order)| == |listing.order| &&
      Names(listing.order) <= EntryNames(listing.entries) &&
      (listing.readError == 0 ==> Names(listing.order) == EntryNames(listing.entries))
  }

  function ReportedErrno(err: int, openError: int): int {
    if openError != 0 && err in {Errno.ENOTEMPTY, Errno.EISDIR, Errno.ENOTDIR, Errno.EEXIST}
      then openError else err
  }

  ghost predicate Attempt(raw: Schema.RmCmdRaw, path: Path, directory: bool,
    now: int, trusted: C.ValidFilesystemObservations, before: FileSystem, after: FileSystem,
    out0: Bytes, out1: Bytes, err0: Bytes, err1: Bytes,
    ok: bool, err: int, earlierError: int, failed: bool)
  {
    (if directory then C.RemoveDirectorySpec(before,now,trusted,after,path,ok,err)
     else C.UnlinkPathSpec(before,now,trusted,after,path,ok,err)) &&
    failed == (!ok && !Ignored(raw,err)) &&
    out1 == out0 + (if ok && raw.verbose then RemovedText(path,directory) else []) &&
    err1 == err0 + (if failed then CannotRemoveText(path,ReportedErrno(err,earlierError)) else [])
  }

  // An inductive removal derivation records atomic filesystem judgments, sibling
  // partitions and the exact hierarchy observed through native directory iteration.
  datatype Removal =
    | Atomic(status: IOResult<FileTimeStatus>, directory: bool, listing: Listing, ok: bool, err: int)
    | Refused(status: IOResult<FileTimeStatus>, why: Refusal, parent: IOResult<FileTimeStatus>)
    | Hierarchy(status: IOResult<FileTimeStatus>, listing: Listing,
        children: seq<Removal>, states: seq<FileSystem>, outputs: seq<Bytes>, errors: seq<Bytes>,
        failures: seq<bool>, ok: bool, err: int)

  ghost predicate HasFailure(failures: seq<bool>) {
    exists i: int :: 0 <= i < |failures| && failures[i]
  }

  ghost predicate RemoveJudgment(raw: Schema.RmCmdRaw, path: Path, top: bool,
    rootKey: HostInodeKey, rootDevice: int, seen: set<HostInodeKey>, now: int,
    trusted: C.ValidFilesystemObservations, before: FileSystem, after: FileSystem,
    out0: Bytes, out1: Bytes, err0: Bytes, err1: Bytes, failed: bool, proof: Removal)
    decreases proof
  {
    StatusResult(before,trusted,path,proof.status) &&
    match proof
    case Atomic(status,directory,listing,ok,err) =>
      (if directory then
        status.Ok? && status.v.isDir &&
        BasicRefusal(raw,path,top,rootKey,rootDevice,seen,status.v) == NoRefusal &&
        ParentAllowed(raw,path,top,status.v,before,trusted) &&
        (!raw.recursive || (Listed(before,path,listing) &&
          (listing.openError != 0 || (listing.readError != 0 && listing.order == []))))
       else status.Err? || !status.v.isDir) &&
      Attempt(raw,path,directory,now,trusted,before,after,out0,out1,err0,err1,
        ok,err,if raw.recursive && directory then
          (if listing.openError != 0 then listing.openError else listing.readError) else 0,failed)
    case Refused(status,why,parent) =>
      status.Ok? && status.v.isDir && why != NoRefusal &&
      (why == BasicRefusal(raw,path,top,rootKey,rootDevice,seen,status.v) ||
        (BasicRefusal(raw,path,top,rootKey,rootDevice,seen,status.v) == NoRefusal &&
        raw.recursive && raw.preserveAll && top &&
        StatusResult(before,trusted,ChildPath(path,".."),parent) &&
        (if parent.Err? then why == ParentRefusal
         else parent.v.device != status.v.device && why == PreserveDeviceRefusal))) &&
      after == before && out1 == out0 && err1 == err0 + RefusalText(path,why) && failed
    case Hierarchy(status,listing,children,states,outputs,errors,failures,ok,err) =>
      status.Ok? && status.v.isDir && raw.recursive &&
      BasicRefusal(raw,path,top,rootKey,rootDevice,seen,status.v) == NoRefusal &&
      ParentAllowed(raw,path,top,status.v,before,trusted) &&
      Listed(before,path,listing) && listing.openError == 0 &&
      (listing.readError == 0 || |listing.order| > 0) &&
      var n := |listing.order|;
      |children| == n && |failures| == n &&
      |states| == n+1 && |outputs| == n+1 && |errors| == n+1 &&
      states[0] == before && outputs[0] == out0 && errors[0] == err0 &&
      (forall i: int :: 0 <= i < n ==>
        RemoveJudgment(raw,ChildPath(path,listing.order[i]),false,rootKey,
          if top then status.v.device else rootDevice,
          seen + {HostInodeKey(status.v.device,status.v.inode)},now,trusted,
          states[i],states[i+1],outputs[i],outputs[i+1],errors[i],errors[i+1],failures[i],children[i])) &&
      (if listing.readError != 0 then
        after == states[n] && out1 == outputs[n] &&
        err1 == errors[n] + TraversalText(path,listing.readError) && failed
       else if HasFailure(failures) then
        after == states[n] && out1 == outputs[n] && err1 == errors[n] && failed
       else Attempt(raw,path,true,now,trusted,states[n],after,outputs[n],out1,errors[n],err1,ok,err,0,failed))
  }

  ghost predicate OperandsJudgment(raw: Schema.RmCmdRaw, now: int,
    trusted: C.ValidFilesystemObservations, rootKey: HostInodeKey,
    before: FileSystem, after: FileSystem, out0: Bytes, out1: Bytes, err0: Bytes, err1: Bytes, exit: int)
  {
    exists states: seq<FileSystem>, outputs: seq<Bytes>, errors: seq<Bytes>,
      failures: seq<bool>, proofs: seq<Removal> ::
      var n := |raw.operands|;
      |states| == n+1 && |outputs| == n+1 && |errors| == n+1 &&
      |failures| == n && |proofs| == n &&
      states[0] == before && states[n] == after &&
      outputs[0] == out0 && outputs[n] == out1 && errors[0] == err0 && errors[n] == err1 &&
      (forall i: int :: 0 <= i < n ==>
        exists path: Path :: CommandPath(raw.operands[i],path) &&
          RemoveJudgment(raw,path,true,rootKey,0,{},now,trusted,
            states[i],states[i+1],outputs[i],outputs[i+1],errors[i],errors[i+1],failures[i],proofs[i])) &&
      exit == (if HasFailure(failures) then 1 else 0)
  }

  function WriteErrorText(reason: string): Bytes {
    "rm: write error: " + Utf8.Encode(reason) + "\n"
  }

  ghost predicate StreamResults(beforeOut: Bytes, afterOut: Bytes,
    beforeErr: Bytes, afterErr: Bytes,
    observations: (TrustedStreamRequest) -> TrustedStreamResult,
    output: Bytes, diagnostics: Bytes, removalExit: int, exit: int)
  {
    var outObservation := observations(StreamWriteStdout(beforeOut,output));
    outObservation.StreamWriteResult? &&
    var finalDiagnostic := diagnostics + (if outObservation.err == 0 then []
      else WriteErrorText(C.CLocaleErrnoTextResult(outObservation.err)));
    var errObservation := observations(StreamWriteStderr(beforeErr,finalDiagnostic));
    errObservation.StreamWriteResult? &&
    C.WriteStdoutSpec(beforeOut,observations,afterOut,output,ReturnError,
      outObservation.committed,outObservation.err) &&
    C.WriteStderrSpec(beforeErr,observations,afterErr,finalDiagnostic,ReturnError,
      errObservation.committed,errObservation.err) &&
    exit == (if removalExit == 0 && outObservation.err == 0 && errObservation.err == 0 then 0 else 1)
  }

  ghost predicate Prepared(raw: Schema.RmCmdRaw, now: int, trusted: C.ValidFilesystemObservations,
    before: FileSystem, after: FileSystem, output: Bytes, diagnostics: Bytes, removalExit: int)
  {
    if raw.mode == Schema.ModeHelp then
      after == before && output == HelpTextSpec() && diagnostics == [] && removalExit == 0
    else if raw.mode == Schema.ModeVersion then
      after == before && output == VersionTextSpec() && diagnostics == [] && removalExit == 0
    else if raw.mode != Schema.ModeRun then
      after == before && output == [] && diagnostics == ModeErrorText(raw.mode) && removalExit == 1
    else if |raw.operands| == 0 then
      after == before && output == [] && diagnostics == (if raw.force then [] else MissingOperandText()) &&
      removalExit == (if raw.force then 0 else 1)
    else if raw.recursive && raw.preserveRoot then
      exists root: IOResult<FileTimeStatus> :: StatusResult(before,trusted,"/",root) &&
        (if root.Err? then
          after == before && output == [] && diagnostics == RootAttributesText(C.ResultErrno(root)) && removalExit == 1
         else OperandsJudgment(raw,now,trusted,HostInodeKey(root.v.device,root.v.inode),
           before,after,[],output,[],diagnostics,removalExit))
    else OperandsJudgment(raw,now,trusted,HostInodeKey(0,0),before,after,[],output,[],diagnostics,removalExit)
  }

  twostate predicate Spec(raw: Schema.RmCmdRaw, io: BenchIO.IO, exit: int)
    reads io.fsRegion, io.stdoutRegion, io.stderrRegion, io.dirHandlesRegion,
      io.nowRegion, io.trustedFilesystemRegion, io.trustedStreamsRegion
  {
    io.dirHandles() == old(io.dirHandles()) &&
    exists output: Bytes, diagnostics: Bytes, removalExit: int ::
      Prepared(raw,io.now(),io.trustedFilesystem(),old(io.fs()),io.fs(),output,diagnostics,removalExit) &&
      StreamResults(old(io.stdout()),io.stdout(),old(io.stderr()),io.stderr(),io.trustedStreams(),
        output,diagnostics,removalExit,exit)
  }
}
