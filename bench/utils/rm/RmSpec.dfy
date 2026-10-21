include "RmSchema.dfy"
include "../../core/IO.dfy"
include "../../core/Utf8.dfy"
include "CliSupport.dfy"
include "../../core/Errno.dfy"
include "../../core/StringEscaping.dfy"
include "RmPathSpec.dfy"

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
  import Paths = RmPathSpec

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

  function ParseDiagnosticPart1(): BenchWorld.Bytes
  {
    "--"
  }

  function ParseDiagnosticPart2(): BenchWorld.Bytes
  {
    "rm: invalid option -- '"
  }

  function ParseDiagnosticPart3(): BenchWorld.Bytes
  {
    "'\n"
  }

  function ParseDiagnosticPart4(): BenchWorld.Bytes
  {
    "rm: unrecognized option '"
  }

  function ParseDiagnosticPart5(): BenchWorld.Bytes
  {
    "rm: invalid option\n"
  }

  function ParseDiagnosticPart6(): BenchWorld.Bytes
  {
    "rm: option '"
  }

  function ParseDiagnosticPart7(): BenchWorld.Bytes
  {
    "' doesn't allow an argument\n"
  }

  function ParseDiagnosticPart8(): BenchWorld.Bytes
  {
    "' is ambiguous; possibilities:"
  }

  function ParseDiagnosticPart9(): BenchWorld.Bytes
  {
    "--="
  }

  function ParseDiagnosticPart10(): BenchWorld.Bytes
  {
    " '--force' '--interactive' '--one-file-system' '--no-preserve-root'"
  }

  function ParseDiagnosticPart11(): BenchWorld.Bytes
  {
    " '--preserve-root' '---presume-input-tty' '--recursive' '--dir' '--verbose'"
  }

  function ParseDiagnosticPart12(): BenchWorld.Bytes
  {
    " '--help' '--version'\n"
  }

  function ParseDiagnosticPart13(): BenchWorld.Bytes
  {
    " '--verbose' '--version'\n"
  }

  function ParseDiagnosticPart14(): BenchWorld.Bytes
  {
    "' requires an argument\n"
  }

  function ParseDiagnostic(err: CliTypes.ParseError, invalidShort: char): Bytes
  {
    if err.kind == CliTypes.UnknownOption && !CliModel.HasPrefix(err.rawToken,ParseDiagnosticPart1()) && |err.rawToken| > 1 then
      ParseDiagnosticPart2() + [Utf8.EncodeChar(invalidShort)[0]] + ParseDiagnosticPart3()
    else Utf8.Encode(
           if err.kind == CliTypes.UnknownOption then
             if CliModel.HasPrefix(err.rawToken, ParseDiagnosticPart1()) then
               ParseDiagnosticPart4() + err.rawToken + ParseDiagnosticPart3()
             else ParseDiagnosticPart5()
           else if err.kind == CliTypes.UnexpectedValue then
             ParseDiagnosticPart6() + LongOptionName(err.rawToken) + ParseDiagnosticPart7()
           else if err.kind == CliTypes.Ambiguous then
             ParseDiagnosticPart6() + err.rawToken + ParseDiagnosticPart8() +
             (if CliModel.HasPrefix(err.rawToken,ParseDiagnosticPart9()) then
                ParseDiagnosticPart10() +
                ParseDiagnosticPart11() +
                ParseDiagnosticPart12()
              else ParseDiagnosticPart13())
           else ParseDiagnosticPart6() + err.rawToken + ParseDiagnosticPart14())
  }

  function ParseErrorText(err: CliTypes.ParseError, invalidShort: char): Bytes
  {
    ParseDiagnostic(err,invalidShort) + UsageText()
  }

  function HyphenSuggestionPart1(): BenchWorld.Bytes
  {
    "Try 'rm ./"
  }

  function HyphenSuggestionPart2(): BenchWorld.Bytes
  {
    "' to remove the file "
  }

  function HyphenSuggestionPart3(): BenchWorld.Bytes
  {
    ".\n"
  }

  function HyphenSuggestion(path: Path): Bytes
  {
    var encoded := Utf8.Encode(path);
    var trigger := exists i: int ::
                     0 <= i < |encoded| && encoded[i] != ':' &&
                     Escaping.SpecShellQuoteTriggerByte(encoded[i],i == 0,|encoded| == 1);
    var quoted := if trigger then Escaping.SpecQuoteAfBytes(encoded) else encoded;
    HyphenSuggestionPart1() + quoted + HyphenSuggestionPart2() + Escaping.SpecQuoteAfBytes(encoded) + HyphenSuggestionPart3()
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

  ghost function ModeErrorText(mode: Schema.RmMode): Bytes
  {
    ModeErrorMessage(mode,match mode
                          case ModeInvalidPreserve(value) => C.QuoteafPathResult(value)
                          case ModeInvalidInteractive(value) => C.QuoteArgumentResult(Utf8.Encode(value))
                          case _ => [])
  }

  function CannotRemoveMessagePart1(): BenchWorld.Bytes
  {
    "rm: cannot remove "
  }

  function CannotRemoveMessagePart2(): BenchWorld.Bytes
  {
    ": "
  }

  function CannotRemoveMessagePart3(): BenchWorld.Bytes
  {
    "\n"
  }

  function CannotRemoveMessage(quoted: Bytes, reason: string): Bytes
  {
    CannotRemoveMessagePart1() + quoted + CannotRemoveMessagePart2() + Utf8.Encode(reason) + CannotRemoveMessagePart3()
  }

  ghost function CannotRemoveText(path: Path, err: int): Bytes
  {
    CannotRemoveMessage(C.QuoteafPathResult(path),C.CLocaleErrnoTextResult(err))
  }

  function TraversalMessagePart1(): BenchWorld.Bytes
  {
    "rm: traversal failed: "
  }

  function TraversalMessagePart2(): BenchWorld.Bytes
  {
    ": "
  }

  function TraversalMessagePart3(): BenchWorld.Bytes
  {
    "\n"
  }

  function TraversalMessage(path: Path, reason: string): Bytes
  {
    TraversalMessagePart1() + Escaping.SpecQuoteFBytes(Utf8.Encode(path)) + TraversalMessagePart2() + Utf8.Encode(reason) + TraversalMessagePart3()
  }

  ghost function TraversalText(path: Path, err: int): Bytes
  {
    TraversalMessage(path,C.CLocaleErrnoTextResult(err))
  }

  function RemovedMessage(quoted: Bytes, directory: bool): Bytes {
    (if directory then "removed directory " else "removed ") + quoted + "\n"
  }

  ghost function RemovedText(path: Path, directory: bool): Bytes {
    RemovedMessage(C.QuoteafPathResult(path),directory)
  }

  function RootAttributesMessagePart1(): BenchWorld.Bytes
  {
    "rm: failed to get attributes of '/': "
  }

  function RootAttributesMessagePart2(): BenchWorld.Bytes
  {
    "\n"
  }

  function RootAttributesMessage(reason: string): Bytes
  {
    RootAttributesMessagePart1() + Utf8.Encode(reason) + RootAttributesMessagePart2()
  }

  ghost function RootAttributesText(err: int): Bytes
  {
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

  function RefusalMessagePart1(): BenchWorld.Bytes
  {
    "Is a directory"
  }

  function RefusalMessagePart2(): BenchWorld.Bytes
  {
    "rm: refusing to remove '.' or '..' directory: skipping "
  }

  function RefusalMessagePart3(): BenchWorld.Bytes
  {
    "\n"
  }

  function RefusalMessagePart4(): BenchWorld.Bytes
  {
    "/"
  }

  function RefusalMessagePart5(): BenchWorld.Bytes
  {
    "rm: it is dangerous to operate recursively on '/'\n"
  }

  function RefusalMessagePart6(): BenchWorld.Bytes
  {
    "rm: it is dangerous to operate recursively on "
  }

  function RefusalMessagePart7(): BenchWorld.Bytes
  {
    " (same as '/')\n"
  }

  function RefusalMessagePart8(): BenchWorld.Bytes
  {
    "rm: use --no-preserve-root to override this failsafe\n"
  }

  function RefusalMessagePart9(): BenchWorld.Bytes
  {
    "rm: WARNING: Circular directory structure.\nThis almost certainly means that you have a corrupted file system.\nNOTIFY YOUR SYSTEM MANAGER.\nThe following directory is part of the cycle:\n  "
  }

  function RefusalMessagePart10(): BenchWorld.Bytes
  {
    "\n\n"
  }

  function RefusalMessagePart11(): BenchWorld.Bytes
  {
    "rm: skipping "
  }

  function RefusalMessagePart12(): BenchWorld.Bytes
  {
    ", since it's on a different device\n"
  }

  function RefusalMessagePart13(): BenchWorld.Bytes
  {
    "rm: and --preserve-root=all is in effect\n"
  }

  function RefusalMessagePart14(): BenchWorld.Bytes
  {
    "rm: failed to stat "
  }

  function RefusalMessagePart15(): BenchWorld.Bytes
  {
    ": skipping "
  }

  function RefusalMessage(path: Path, why: Refusal, quoted: Bytes, quotedParent: Bytes): Bytes
  {
    match why
    case DirectoryRefusal => CannotRemoveMessage(quoted, RefusalMessagePart1())
    case DotRefusal =>
      RefusalMessagePart2() + quoted + RefusalMessagePart3()
    case RootRefusal =>
      (if path == RefusalMessagePart4() then RefusalMessagePart5()
       else RefusalMessagePart6() + quoted + RefusalMessagePart7()) +
      RefusalMessagePart8()
    case CycleRefusal =>
      RefusalMessagePart9() + Escaping.SpecQuoteFBytes(Utf8.Encode(path)) + RefusalMessagePart10()
    case DeviceRefusal =>
      RefusalMessagePart11() + quoted + RefusalMessagePart12()
    case PreserveDeviceRefusal =>
      RefusalMessagePart11() + quoted + RefusalMessagePart12() +
      RefusalMessagePart13()
    case ParentRefusal =>
      RefusalMessagePart14() + quotedParent + RefusalMessagePart15() +
      quoted + RefusalMessagePart3()
    case NoRefusal => []
  }

  function RefusalTextPart1(): BenchWorld.Bytes
  {
    ".."
  }

  ghost function RefusalText(path: Path, why: Refusal): Bytes
  {
    RefusalMessage(path,why,C.QuoteafPathResult(path),C.QuoteafPathResult(ChildPath(path,RefusalTextPart1())))
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

  function EntryNames(entries: set<DirEntry>): set<string> {
    set entry: DirEntry | entry in entries :: entry.name
  }

  function Names(names: seq<string>): set<string> {
    set i: int | 0 <= i < |names| :: names[i]
  }

  datatype Listing = Listing(order: seq<string>, ghost entries: set<DirEntry>, openError: int, readError: int)

  datatype ObservationContext = ObservationContext(
    ghost failures: (NativeFailureRequest) -> int,
    ghost handles: map<int, DirHandleState>)

  ghost function ObservationContextFor(io: BenchIO.IO): ObservationContext
    reads io.trustedNativeFailuresRegion, io.dirHandlesRegion
  {
    ObservationContext(io.trustedNativeFailures(), io.dirHandles())
  }

  datatype DirectoryObservation = DirectoryObservation(
    before: map<int, DirHandleState>, after: map<int, DirHandleState>,
    more: bool, name: string, kind: DirectoryEntryKind, err: int)

  ghost predicate ReadPrefix(fs: FileSystem, context: ObservationContext,
                             handle: int, initialHandles: map<int, DirHandleState>,
                             names: seq<string>, steps: seq<DirectoryObservation>, after: map<int, DirHandleState>)
  {
    |steps| == |names| &&
    (if |steps| == 0 then after == initialHandles else
     steps[0].before == initialHandles && steps[|steps|-1].after == after) &&
    (forall i: nat | i < |steps| ::
       C.ReadDirSpec(fs, steps[i].before, context.failures, steps[i].after,
                     handle, steps[i].more, steps[i].name, steps[i].kind, steps[i].err) &&
       steps[i].more && steps[i].err == 0 && steps[i].name == names[i] &&
       (i > 0 ==> steps[i-1].after == steps[i].before))
  }

  ghost predicate ListingObservation(fs: FileSystem, context: ObservationContext,
                                     path: Path, listing: Listing)
  {
    exists openState: map<int, DirHandleState>, handle: int, openOk: bool
      {:trigger C.OpenDirSpec(fs, context.handles, context.failures, openState,
                              path, false, openOk, handle, listing.openError)} ::
      openOk == (listing.openError == 0) &&
      C.OpenDirSpec(fs, context.handles, context.failures, openState,
                    path, false, openOk, handle, listing.openError) &&
      if listing.openError != 0 then true else
      exists steps: seq<DirectoryObservation>, beforeEnd: map<int, DirHandleState>,
        afterEnd: map<int, DirHandleState>, endKind: DirectoryEntryKind,
        closeOk: bool, closeErr: int
        {:trigger ReadPrefix(fs, context, handle, openState, listing.order, steps, beforeEnd),
        C.ReadDirSpec(fs, beforeEnd, context.failures, afterEnd,
                      handle, false, "", endKind, listing.readError),
        C.CloseDirSpec(afterEnd, context.failures, context.handles, handle, closeOk, closeErr)} ::
        ReadPrefix(fs, context, handle, openState, listing.order, steps, beforeEnd) &&
        C.ReadDirSpec(fs, beforeEnd, context.failures, afterEnd,
                      handle, false, "", endKind, listing.readError) &&
        C.CloseDirSpec(afterEnd, context.failures, context.handles,
                       handle, closeOk, closeErr)
  }

  ghost predicate Listed(context: ObservationContext,
                         fs: FileSystem, path: Path, listing: Listing) {
    ListingObservation(fs, context, path, listing) &&
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

  predicate HasFailure(failures: seq<bool>) {
    exists i: int :: 0 <= i < |failures| && failures[i]
  }

  datatype RemovalScope = RemovalScope(rootKey: HostInodeKey, rootDevice: int, seen: set<HostInodeKey>)

  ghost predicate RemoveJudgment(context: ObservationContext, raw: Schema.RmCmdRaw, path: Path, top: bool,
                                 scope: RemovalScope, now: int,
                                 trusted: C.ValidFilesystemObservations, before: FileSystem, after: FileSystem,
                                 out0: Bytes, out1: Bytes, err0: Bytes, err1: Bytes, failed: bool, proof: Removal)
    decreases proof
  {
    StatusResult(before,trusted,path,proof.status) &&
    match proof
    case Atomic(status,directory,listing,ok,err) =>
      (if directory then
         status.Ok? && status.v.isDir &&
         BasicRefusal(raw,path,top,scope.rootKey,scope.rootDevice,scope.seen,status.v) == NoRefusal &&
         ParentAllowed(raw,path,top,status.v,before,trusted) &&
         (!raw.recursive || (Listed(context, before,path,listing) &&
                             (listing.openError != 0 || (listing.readError != 0 && listing.order == []))))
       else status.Err? || !status.v.isDir) &&
      Attempt(raw,path,directory,now,trusted,before,after,out0,out1,err0,err1,
              ok,err,if raw.recursive && directory then
                (if listing.openError != 0 then listing.openError else listing.readError) else 0,failed)
    case Refused(status,why,parent) =>
      status.Ok? && status.v.isDir && why != NoRefusal &&
      (why == BasicRefusal(raw,path,top,scope.rootKey,scope.rootDevice,scope.seen,status.v) ||
       (BasicRefusal(raw,path,top,scope.rootKey,scope.rootDevice,scope.seen,status.v) == NoRefusal &&
        raw.recursive && raw.preserveAll && top &&
        StatusResult(before,trusted,ChildPath(path,".."),parent) &&
        (if parent.Err? then why == ParentRefusal
         else parent.v.device != status.v.device && why == PreserveDeviceRefusal))) &&
      after == before && out1 == out0 && err1 == err0 + RefusalText(path,why) && failed
    case Hierarchy(status,listing,children,states,outputs,errors,failures,ok,err) =>
      status.Ok? && status.v.isDir && raw.recursive &&
      BasicRefusal(raw,path,top,scope.rootKey,scope.rootDevice,scope.seen,status.v) == NoRefusal &&
      ParentAllowed(raw,path,top,status.v,before,trusted) &&
      Listed(context, before,path,listing) && listing.openError == 0 &&
      (listing.readError == 0 || |listing.order| > 0) &&
      var n := |listing.order|;
      |children| == n && |failures| == n &&
      |states| == n+1 && |outputs| == n+1 && |errors| == n+1 &&
      states[0] == before && outputs[0] == out0 && errors[0] == err0 &&
      (forall i: int :: 0 <= i < n ==>
                          RemoveJudgment(context, raw,ChildPath(path,listing.order[i]),false,RemovalScope(scope.rootKey,
                                                                                                          if top then status.v.device else scope.rootDevice,
                                                                                                          scope.seen + {HostInodeKey(status.v.device,status.v.inode)}),now,trusted,
                                         states[i],states[i+1],outputs[i],outputs[i+1],errors[i],errors[i+1],failures[i],children[i])) &&
      (if listing.readError != 0 then
         after == states[n] && out1 == outputs[n] &&
         err1 == errors[n] + TraversalText(path,listing.readError) && failed
       else if HasFailure(failures) then
         after == states[n] && out1 == outputs[n] && err1 == errors[n] && failed
       else Attempt(raw,path,true,now,trusted,states[n],after,outputs[n],out1,errors[n],err1,ok,err,0,failed))
  }

  ghost predicate OperandsJudgment(context: ObservationContext, raw: Schema.RmCmdRaw, now: int,
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
                                               RemoveJudgment(context, raw,path,true,RemovalScope(rootKey,0,{}),now,trusted,
                                                              states[i],states[i+1],outputs[i],outputs[i+1],errors[i],errors[i+1],failures[i],proofs[i])) &&
      exit == (if HasFailure(failures) then 1 else 0)
  }

  function WriteErrorTextPart1(): BenchWorld.Bytes
  {
    "rm: write error: "
  }

  function WriteErrorTextPart2(): BenchWorld.Bytes
  {
    "\n"
  }

  function WriteErrorText(reason: string): Bytes
  {
    WriteErrorTextPart1() + Utf8.Encode(reason) + WriteErrorTextPart2()
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
    C.WriteStdoutSpec(beforeOut,observations,afterOut,output,
                      outObservation.committed,outObservation.err) &&
    C.WriteStderrSpec(beforeErr,observations,afterErr,finalDiagnostic,
                      errObservation.committed,errObservation.err) &&
    exit == (if removalExit == 0 && outObservation.err == 0 && errObservation.err == 0 then 0 else 1)
  }

  ghost predicate Prepared(context: ObservationContext, raw: Schema.RmCmdRaw, now: int, trusted: C.ValidFilesystemObservations,
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
                                                else OperandsJudgment(context, raw,now,trusted,HostInodeKey(root.v.device,root.v.inode),
                                                                      before,after,[],output,[],diagnostics,removalExit))
    else OperandsJudgment(context, raw,now,trusted,HostInodeKey(0,0),before,after,[],output,[],diagnostics,removalExit)
  }

  twostate predicate Spec(raw: Schema.RmCmdRaw, io: BenchIO.IO, exit: int)
    reads io.fsRegion, io.stdoutRegion, io.stderrRegion, io.dirHandlesRegion,
          io.nowRegion, io.trustedFilesystemRegion, io.trustedStreamsRegion, io.trustedNativeFailuresRegion
  {
    io.dirHandles() == old(io.dirHandles()) &&
    exists output: Bytes, diagnostics: Bytes, removalExit: int ::
      Prepared(old(ObservationContextFor(io)), raw,io.now(),io.trustedFilesystem(),old(io.fs()),io.fs(),output,diagnostics,removalExit) &&
      StreamResults(old(io.stdout()),io.stdout(),old(io.stderr()),io.stderr(),io.trustedStreams(),
                    output,diagnostics,removalExit,exit)
  }
}
