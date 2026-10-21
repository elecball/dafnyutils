include "../../core/Errno.dfy"
include "../../core/World.dfy"
include "../../core/Utf8.dfy"
include "../../core/IO.dfy"
include "../../core/IOContract.dfy"
include "../../core/StringEscaping.dfy"
include "MvPathSpec.dfy"
include "MvQuoteSpec.dfy"
include "MvSchema.dfy"

module MvSpec {
  import Errno = Errnos
  import Result = Results
  import BenchIO
  import IOContract
  import BenchWorld
  import Basename = MvPathSpec
  import Quote = MvQuoteSpec
  import Dirname = MvPathSpec
  import Schema = MvSchema
  import Utf8 = Utf8Semantics
  import SE = StringEscaping





  function ErrnoTextSpec(err: int): string
  {
    if err == Errno.ENOENT then
      "No such file or directory"
    else if err == Errno.EACCES then
      "Permission denied"
    else if err == Errno.EBUSY then
      "Device or resource busy"
    else if err == Errno.EEXIST then
      "File exists"
    else if err == Errno.ENOTDIR then
      "Not a directory"
    else if err == Errno.EISDIR then
      "Is a directory"
    else if err == Errno.EINVAL then
      "Invalid argument"
    else if err == Errno.ENOTEMPTY then
      "Directory not empty"
    else if err == Errno.ELOOP then
      "Too many levels of symbolic links"
    else if err == Errno.EPERM then
      "Operation not permitted"
    else if err == Errno.EIO then
      "Input/output error"
    else if err == Errno.ENOMEM then
      "Cannot allocate memory"
    else if err == Errno.ENAMETOOLONG then
      "File name too long"
    else if err == Errno.EOVERFLOW then
      "Value too large for defined data type"
    else if err == Errno.EXDEV then
      "Invalid cross-device link"
    else if err == Errno.EMLINK then
      "Too many links"
    else if err == Errno.ENOSPC then
      "No space left on device"
    else if err == Errno.EROFS then
      "Read-only file system"
    else if err == Errno.EDQUOT then
      "Disk quota exceeded"
    else
      "unknown error"
  }

  function HelpTextSpec(): BenchWorld.Bytes
  {
    "Usage: mv [OPTION]... [-T] SOURCE DEST\n"
    + "  or:  mv [OPTION]... SOURCE... DIRECTORY\n"
    + "  or:  mv [OPTION]... -t DIRECTORY SOURCE...\n"
    + "Rename SOURCE to DEST, or move SOURCE(s) to DIRECTORY.\n"
    + "\n"
    + "      --backup[=CONTROL]       make a backup of each existing destination file\n"
    + "  -b                           like --backup but does not accept an argument\n"
    + "      --debug                  explain how a file is moved; implies -v\n"
    + "  -f, --force                  do not prompt before overwriting\n"
    + "  -n, --no-clobber             do not overwrite an existing file\n"
    + "      --no-copy                do not copy if a rename cannot be performed\n"
    + "  -S, --suffix=SUFFIX          override the usual backup suffix\n"
    + "      --strip-trailing-slashes remove any trailing slashes from each SOURCE\n"
    + "  -t, --target-directory=DIR   move all SOURCE arguments into DIR\n"
    + "  -T, --no-target-directory    treat DEST as a normal file\n"
    + "      --update[=UPDATE]        control which existing files are updated\n"
    + "  -u                           equivalent to --update=older\n"
    + "  -v, --verbose                explain what is being done\n"
    + "      --help                   display this help and exit\n"
    + "      --version                output version information and exit\n"
    + "\n"
    + "This benchmark models rename-style moves over regular files, directories,\n"
    + "and symlinks already represented in the benchmark IO filesystem.\n"
    + "\n"
    + "Report bugs to: bug-coreutils@gnu.org\n"
    + "GNU coreutils home page: <https://www.gnu.org/software/coreutils/>\n"
    + "Full documentation <https://www.gnu.org/software/coreutils/mv>\n"
    + "or available locally via: info '(coreutils) mv invocation'\n"
  }

  function VersionTextSpec(): BenchWorld.Bytes
  {
    "mv (GNU coreutils) 9.10.13-2cf49\n"
    + "Copyright (C) 2026 Free Software Foundation, Inc.\n"
    + "License GPLv3+: GNU GPL version 3 or later <https://gnu.org/licenses/gpl.html>.\n"
    + "This is free software: you are free to change and redistribute it.\n"
    + "There is NO WARRANTY, to the extent permitted by law.\n"
    + "\n"
    + "Written by Mike Parker, David MacKenzie, and Jim Meyering.\n"
  }

  function MissingFileOperandMessageSpec(): BenchWorld.Bytes
  {
    "mv: missing file operand\nTry 'mv --help' for more information.\n"
  }

  function MissingDestinationMessageSpecPart1(): BenchWorld.Bytes
  {
    "mv: missing destination file operand after "
  }

  function MissingDestinationMessageSpecPart2(): BenchWorld.Bytes
  {
    "\n"
  }

  function MissingDestinationMessageSpecPart3(): BenchWorld.Bytes
  {
    "Try 'mv --help' for more information.\n"
  }

  ghost function MissingDestinationMessageSpec(source: string): BenchWorld.Bytes
  {
    MissingDestinationMessageSpecPart1() + Quote.SpecQuoteAfBytes(Utf8.Encode(source)) + MissingDestinationMessageSpecPart2()
    + MissingDestinationMessageSpecPart3()
  }

  function ExtraOperandMessageSpecPart1(): BenchWorld.Bytes
  {
    "mv: extra operand "
  }

  function ExtraOperandMessageSpecPart2(): BenchWorld.Bytes
  {
    "\nTry 'mv --help' for more information.\n"
  }

  ghost function ExtraOperandMessageSpec(operand: string): BenchWorld.Bytes
  {
    ExtraOperandMessageSpecPart1() + Quote.SpecQuoteAfBytes(Utf8.Encode(operand)) +
    ExtraOperandMessageSpecPart2()
  }

  function TargetDirectoryConflictMessageSpec(): BenchWorld.Bytes
  {
    "mv: cannot combine --target-directory (-t) and --no-target-directory (-T)\n"
  }

  function InvalidBackupArgumentMessageSpecPart1(): BenchWorld.Bytes
  {
    "mv: invalid argument "
  }

  function InvalidBackupArgumentMessageSpecPart2(): BenchWorld.Bytes
  {
    " for 'backup type'\n"
  }

  function InvalidBackupArgumentMessageSpecPart3(): BenchWorld.Bytes
  {
    "Valid arguments are:\n"
  }

  function InvalidBackupArgumentMessageSpecPart4(): BenchWorld.Bytes
  {
    "  - 'none', 'off'\n"
  }

  function InvalidBackupArgumentMessageSpecPart5(): BenchWorld.Bytes
  {
    "  - 'simple', 'never'\n"
  }

  function InvalidBackupArgumentMessageSpecPart6(): BenchWorld.Bytes
  {
    "  - 'existing', 'nil'\n"
  }

  function InvalidBackupArgumentMessageSpecPart7(): BenchWorld.Bytes
  {
    "  - 'numbered', 't'\n"
  }

  function InvalidBackupArgumentMessageSpecPart8(): BenchWorld.Bytes
  {
    "Try 'mv --help' for more information.\n"
  }

  ghost function InvalidBackupArgumentMessageSpec(value: string): BenchWorld.Bytes
  {
    InvalidBackupArgumentMessageSpecPart1() + SE.SpecLocaleQuoteBytes(Utf8.Encode(value)) +
    InvalidBackupArgumentMessageSpecPart2()
    + InvalidBackupArgumentMessageSpecPart3()
    + InvalidBackupArgumentMessageSpecPart4()
    + InvalidBackupArgumentMessageSpecPart5()
    + InvalidBackupArgumentMessageSpecPart6()
    + InvalidBackupArgumentMessageSpecPart7()
    + InvalidBackupArgumentMessageSpecPart8()
  }

  function InvalidUpdateArgumentMessageSpecPart1(): BenchWorld.Bytes
  {
    "mv: invalid argument "
  }

  function InvalidUpdateArgumentMessageSpecPart2(): BenchWorld.Bytes
  {
    " for '--update'\n"
  }

  function InvalidUpdateArgumentMessageSpecPart3(): BenchWorld.Bytes
  {
    "Valid arguments are:\n"
  }

  function InvalidUpdateArgumentMessageSpecPart4(): BenchWorld.Bytes
  {
    "  - 'all'\n"
  }

  function InvalidUpdateArgumentMessageSpecPart5(): BenchWorld.Bytes
  {
    "  - 'none'\n"
  }

  function InvalidUpdateArgumentMessageSpecPart6(): BenchWorld.Bytes
  {
    "  - 'none-fail'\n"
  }

  function InvalidUpdateArgumentMessageSpecPart7(): BenchWorld.Bytes
  {
    "  - 'older'\n"
  }

  function InvalidUpdateArgumentMessageSpecPart8(): BenchWorld.Bytes
  {
    "Try 'mv --help' for more information.\n"
  }

  ghost function InvalidUpdateArgumentMessageSpec(value: string): BenchWorld.Bytes
  {
    InvalidUpdateArgumentMessageSpecPart1() + SE.SpecLocaleQuoteBytes(Utf8.Encode(value)) +
    InvalidUpdateArgumentMessageSpecPart2()
    + InvalidUpdateArgumentMessageSpecPart3()
    + InvalidUpdateArgumentMessageSpecPart4()
    + InvalidUpdateArgumentMessageSpecPart5()
    + InvalidUpdateArgumentMessageSpecPart6()
    + InvalidUpdateArgumentMessageSpecPart7()
    + InvalidUpdateArgumentMessageSpecPart8()
  }

  function TargetFailureMessageSpecPart1(): BenchWorld.Bytes
  {
    "mv: target directory "
  }

  function TargetFailureMessageSpecPart2(): BenchWorld.Bytes
  {
    ": "
  }

  function TargetFailureMessageSpecPart3(): BenchWorld.Bytes
  {
    "\n"
  }

  function TargetFailureMessageSpecPart4(): BenchWorld.Bytes
  {
    "mv: target "
  }

  ghost function TargetFailureMessageSpec(path: string, explicitTargetDirectory: bool, err: int): BenchWorld.Bytes
  {
    if explicitTargetDirectory then
      TargetFailureMessageSpecPart1() + Quote.SpecQuoteAfBytes(Utf8.Encode(path)) +
      TargetFailureMessageSpecPart2() + ErrnoTextSpec(err) + TargetFailureMessageSpecPart3()
    else
      TargetFailureMessageSpecPart4() + Quote.SpecQuoteAfBytes(Utf8.Encode(path)) +
      TargetFailureMessageSpecPart2() + ErrnoTextSpec(err) + TargetFailureMessageSpecPart3()
  }

  function SourceStatFailureMessageSpecPart1(): BenchWorld.Bytes
  {
    "mv: cannot stat "
  }

  function SourceStatFailureMessageSpecPart2(): BenchWorld.Bytes
  {
    ": "
  }

  function SourceStatFailureMessageSpecPart3(): BenchWorld.Bytes
  {
    "\n"
  }

  ghost function SourceStatFailureMessageSpec(source: string, err: int): BenchWorld.Bytes
  {
    SourceStatFailureMessageSpecPart1() + Quote.SpecQuoteAfBytes(Utf8.Encode(source)) +
    SourceStatFailureMessageSpecPart2() + ErrnoTextSpec(err) + SourceStatFailureMessageSpecPart3()
  }

  function ParentStatFailureMessageSpecPart1(): BenchWorld.Bytes
  {
    "mv: "
  }

  function ParentStatFailureMessageSpecPart2(): BenchWorld.Bytes
  {
    ": "
  }

  function ParentStatFailureMessageSpecPart3(): BenchWorld.Bytes
  {
    "\n"
  }

  ghost function ParentStatFailureMessageSpec(path: string, err: int): BenchWorld.Bytes
  {
    ParentStatFailureMessageSpecPart1() + Utf8.Encode(path) + ParentStatFailureMessageSpecPart2() + ErrnoTextSpec(err) + ParentStatFailureMessageSpecPart3()
  }

  function RenameFailureMessageSpecPart1(): BenchWorld.Bytes
  {
    "mv: cannot overwrite directory "
  }

  function RenameFailureMessageSpecPart2(): BenchWorld.Bytes
  {
    " with non-directory "
  }

  function RenameFailureMessageSpecPart3(): BenchWorld.Bytes
  {
    "\n"
  }

  function RenameFailureMessageSpecPart4(): BenchWorld.Bytes
  {
    "mv: cannot overwrite "
  }

  function RenameFailureMessageSpecPart5(): BenchWorld.Bytes
  {
    ": "
  }

  function RenameFailureMessageSpecPart6(): BenchWorld.Bytes
  {
    "mv: cannot move "
  }

  function RenameFailureMessageSpecPart7(): BenchWorld.Bytes
  {
    " to "
  }

  ghost function RenameFailureMessageSpec(source: string, target: string, err: int): BenchWorld.Bytes
  {
    if err == Errno.EISDIR then
      RenameFailureMessageSpecPart1() + Quote.SpecQuoteAfBytes(Utf8.Encode(target)) +
      RenameFailureMessageSpecPart2() + Quote.SpecQuoteAfBytes(Utf8.Encode(source)) + RenameFailureMessageSpecPart3()
    else if err == Errno.ENOTEMPTY then
      RenameFailureMessageSpecPart4() + Quote.SpecQuoteAfBytes(Utf8.Encode(target)) +
      RenameFailureMessageSpecPart5() + ErrnoTextSpec(err) + RenameFailureMessageSpecPart3()
    else
      RenameFailureMessageSpecPart6() + Quote.SpecQuoteAfBytes(Utf8.Encode(source)) +
      RenameFailureMessageSpecPart7() + Quote.SpecQuoteAfBytes(Utf8.Encode(target)) +
      RenameFailureMessageSpecPart5() + ErrnoTextSpec(err) + RenameFailureMessageSpecPart3()
  }

  function SourceRenameFailureMessageSpecPart1(): BenchWorld.Bytes
  {
    "mv: cannot overwrite non-directory "
  }

  function SourceRenameFailureMessageSpecPart2(): BenchWorld.Bytes
  {
    " with directory "
  }

  function SourceRenameFailureMessageSpecPart3(): BenchWorld.Bytes
  {
    "\n"
  }

  function SourceRenameFailureMessageSpecPart4(): BenchWorld.Bytes
  {
    "mv: cannot move "
  }

  function SourceRenameFailureMessageSpecPart5(): BenchWorld.Bytes
  {
    " to a subdirectory of itself, "
  }

  ghost function SourceRenameFailureMessageSpec(
    source: string,
    target: string,
    err: int,
    directorySourceWithExistingTarget: bool
  ): BenchWorld.Bytes
  {
    if directorySourceWithExistingTarget && err == Errno.ENOTDIR then
      SourceRenameFailureMessageSpecPart1() + Quote.SpecQuoteAfBytes(Utf8.Encode(target)) +
      SourceRenameFailureMessageSpecPart2() + Quote.SpecQuoteAfBytes(Utf8.Encode(source)) + SourceRenameFailureMessageSpecPart3()
    else if err == Errno.EINVAL then
      SourceRenameFailureMessageSpecPart4() + Quote.SpecQuoteAfBytes(Utf8.Encode(source)) +
      SourceRenameFailureMessageSpecPart5() + Quote.SpecQuoteAfBytes(Utf8.Encode(target)) + SourceRenameFailureMessageSpecPart3()
    else
      RenameFailureMessageSpec(source, target, err)
  }

  function SourceRenameDiagnosticErrSpec(
    target: string,
    sourceIsDir: bool,
    renameErr: int
  ): int
  {
    if target == "" then
      if sourceIsDir then Errno.EBUSY else Errno.EISDIR
    else
      renameErr
  }

  function SameFileMessageSpecPart1(): BenchWorld.Bytes
  {
    "mv: "
  }

  function SameFileMessageSpecPart2(): BenchWorld.Bytes
  {
    " and "
  }

  function SameFileMessageSpecPart3(): BenchWorld.Bytes
  {
    " are the same file\n"
  }

  ghost function SameFileMessageSpec(source: string, target: string): BenchWorld.Bytes
  {
    SameFileMessageSpecPart1() + Quote.SpecQuoteAfBytes(Utf8.Encode(source)) +
    SameFileMessageSpecPart2() + Quote.SpecQuoteAfBytes(Utf8.Encode(target)) +
    SameFileMessageSpecPart3()
  }

  function BackupWouldDestroySourceMessageSpecPart1(): BenchWorld.Bytes
  {
    "mv: backing up "
  }

  function BackupWouldDestroySourceMessageSpecPart2(): BenchWorld.Bytes
  {
    " might destroy source;  "
  }

  function BackupWouldDestroySourceMessageSpecPart3(): BenchWorld.Bytes
  {
    " not moved\n"
  }

  ghost function BackupWouldDestroySourceMessageSpec(
    source: string,
    target: string
  ): BenchWorld.Bytes
  {
    BackupWouldDestroySourceMessageSpecPart1() +
    Quote.SpecQuoteAfBytes(Utf8.Encode(target)) +
    BackupWouldDestroySourceMessageSpecPart2() +
    Quote.SpecQuoteAfBytes(Utf8.Encode(source)) +
    BackupWouldDestroySourceMessageSpecPart3()
  }

  function VerboseRenameMessageSpecPart1(): BenchWorld.Bytes
  {
    "renamed "
  }

  function VerboseRenameMessageSpecPart2(): BenchWorld.Bytes
  {
    " -> "
  }

  function VerboseRenameMessageSpecPart3(): BenchWorld.Bytes
  {
    "\n"
  }

  ghost function VerboseRenameMessageSpec(source: string, target: string): BenchWorld.Bytes
  {
    VerboseRenameMessageSpecPart1() + Quote.SpecQuoteAfBytes(Utf8.Encode(source)) +
    VerboseRenameMessageSpecPart2() + Quote.SpecQuoteAfBytes(Utf8.Encode(target)) + VerboseRenameMessageSpecPart3()
  }

  function VerboseRenameWithBackupMessageSpecPart1(): BenchWorld.Bytes
  {
    "renamed "
  }

  function VerboseRenameWithBackupMessageSpecPart2(): BenchWorld.Bytes
  {
    " -> "
  }

  function VerboseRenameWithBackupMessageSpecPart3(): BenchWorld.Bytes
  {
    " (backup: "
  }

  function VerboseRenameWithBackupMessageSpecPart4(): BenchWorld.Bytes
  {
    ")\n"
  }

  ghost function VerboseRenameWithBackupMessageSpec(source: string, target: string, backup: string): BenchWorld.Bytes
  {
    VerboseRenameWithBackupMessageSpecPart1() + Quote.SpecQuoteAfBytes(Utf8.Encode(source)) +
    VerboseRenameWithBackupMessageSpecPart2() + Quote.SpecQuoteAfBytes(Utf8.Encode(target)) +
    VerboseRenameWithBackupMessageSpecPart3() + Quote.SpecQuoteAfBytes(Utf8.Encode(backup)) + VerboseRenameWithBackupMessageSpecPart4()
  }

  function DebugSkipMessageSpecPart1(): BenchWorld.Bytes
  {
    "skipped "
  }

  function DebugSkipMessageSpecPart2(): BenchWorld.Bytes
  {
    "\n"
  }

  ghost function DebugSkipMessageSpec(target: string): BenchWorld.Bytes
  {
    DebugSkipMessageSpecPart1() + Quote.SpecQuoteAfBytes(Utf8.Encode(target)) + DebugSkipMessageSpecPart2()
  }

  function NotReplacingMessageSpecPart1(): BenchWorld.Bytes
  {
    "mv: not replacing "
  }

  function NotReplacingMessageSpecPart2(): BenchWorld.Bytes
  {
    "\n"
  }

  ghost function NotReplacingMessageSpec(target: string): BenchWorld.Bytes
  {
    NotReplacingMessageSpecPart1() + Quote.SpecQuoteAfBytes(Utf8.Encode(target)) + NotReplacingMessageSpecPart2()
  }




















  function ShowActionMessageSpec(verbose: bool, debug: bool): bool
  {
    verbose || debug
  }

  ghost function SkipStdoutSpec(target: string, debug: bool): BenchWorld.Bytes
  {
    if debug then DebugSkipMessageSpec(target) else []
  }

  ghost function SourceLeafNameSpec(source: string): string
  {
    var leaf := BenchWorld.LeafName(source);
    if leaf == "" then source else leaf
  }

  // Both stay compilable structural recursions rather than quantifiers: a
  // quantifier is ghost in Dafny, and the non-ghost `NormalizeSourceSpec`
  // below calls these.
  function AllSlashesSpec(text: string): bool
    decreases |text|
  {
    |text| == 0 ||
    (text[0] == '/' && AllSlashesSpec(text[1..]))
  }

  function TrimTrailingSlashesSpec(text: string): string
    decreases |text|
  {
    if |text| == 0 then
      ""
    else if text[|text| - 1] == '/' then
      TrimTrailingSlashesSpec(text[..|text| - 1])
    else
      text
  }

  function NormalizeSourceSpec(source: string, stripTrailingSlashes: bool): string
  {
    if !stripTrailingSlashes then
      source
    else if source == "" then
      source
    else if AllSlashesSpec(source) then
      "/"
    else
      TrimTrailingSlashesSpec(source)
  }

  ghost function TargetInDirectorySpec(directory: string, source: string): string
  {
    BenchWorld.AppendPath(directory, SourceLeafNameSpec(source))
  }

  ghost predicate SameInode(
    fs: BenchWorld.FileSystem,
    left: BenchWorld.Path,
    right: BenchWorld.Path
  )
  {
    exists resolvedLeft: BenchWorld.Path, resolvedRight: BenchWorld.Path ::
      IOContract.ResolvePathForMetadataFields(fs, left, false) ==
      Result.Ok(resolvedLeft) &&
      IOContract.ResolvePathForMetadataFields(fs, right, false) ==
      Result.Ok(resolvedRight) &&
      BenchWorld.InodeSameObject(fs, resolvedLeft, resolvedRight)
  }

  ghost predicate SameDirectoryEntry(
    fs: BenchWorld.FileSystem,
    left: BenchWorld.Path,
    right: BenchWorld.Path
  )
  {
    exists
      leftParent: string,
      rightParent: string,
      leftLeaf: string,
      rightLeaf: string,
      resolvedLeftParent: BenchWorld.Path,
      resolvedRightParent: BenchWorld.Path
      ::
        Dirname.DirnameRelation(left, leftParent) &&
        Dirname.DirnameRelation(right, rightParent) &&
        Basename.BasenameRelation(left, leftLeaf) &&
        Basename.BasenameRelation(right, rightLeaf) &&
        leftLeaf == rightLeaf &&
        IOContract.ResolvePathForMetadataFields(fs, leftParent, false) ==
        Result.Ok(resolvedLeftParent) &&
        IOContract.ResolvePathForMetadataFields(fs, rightParent, false) ==
        Result.Ok(resolvedRightParent) &&
        BenchWorld.InodeSameObject(
          fs, resolvedLeftParent, resolvedRightParent
        )
  }

  ghost predicate SourceSymlinkReferentHasTargetName(
    fs: BenchWorld.FileSystem,
    preCwd: BenchWorld.Path,
    source: BenchWorld.Path,
    target: BenchWorld.Path
  )
  {
    exists
      resolvedSource: BenchWorld.Path,
      resolvedReferent: BenchWorld.Path
      ::
        IOContract.ResolvePathForMetadataFields(fs, source, false) ==
        Result.Ok(resolvedSource) &&
        BenchWorld.FsContainsPath(fs, resolvedSource) &&
        BenchWorld.FsNodeAt(fs, resolvedSource).Symlink? &&
        IOContract.ResolvePathIdentityContractFields(
          fs, preCwd, source, true, resolvedReferent, 0
        ) &&
        SameDirectoryEntry(fs, resolvedReferent, target)
  }

  datatype SameFileDecision =
    | ContinueMove
    | RejectSameFile
    | FailedParentStat(path: string, err: int)

  ghost predicate SameFileMustBeRejected(
    cmd: Schema.MvCmd,
    fs: BenchWorld.FileSystem,
    preCwd: BenchWorld.Path,
    source: BenchWorld.Path,
    target: BenchWorld.Path
  )
  {
    SameDirectoryEntry(fs, source, target) ||
    (cmd.backupMode == Schema.BackupOff &&
     (SameInode(fs, source, target) ||
      SourceSymlinkReferentHasTargetName(
        fs, preCwd, source, target
      )))
  }

  ghost predicate SameFilePolicyRelation(
    cmd: Schema.MvCmd,
    fs: BenchWorld.FileSystem,
    preCwd: BenchWorld.Path,
    source: BenchWorld.Path,
    target: BenchWorld.Path,
    decision: SameFileDecision
  )
  {
    decision ==
    if SameFileMustBeRejected(cmd, fs, preCwd, source, target)
    then RejectSameFile
    else ContinueMove
  }

  lemma SameFilePolicyTotal(
    cmd: Schema.MvCmd,
    fs: BenchWorld.FileSystem,
    preCwd: BenchWorld.Path,
    source: BenchWorld.Path,
    target: BenchWorld.Path
  )
    ensures exists decision: SameFileDecision ::
              SameFilePolicyRelation(
                cmd, fs, preCwd, source, target, decision
              )
  {
    var decision :=
      if SameFileMustBeRejected(cmd, fs, preCwd, source, target)
      then RejectSameFile
      else ContinueMove;
    assert SameFilePolicyRelation(
        cmd, fs, preCwd, source, target, decision
      );
  }

  lemma SameFilePolicyFunctional(
    cmd: Schema.MvCmd,
    fs: BenchWorld.FileSystem,
    preCwd: BenchWorld.Path,
    source: BenchWorld.Path,
    target: BenchWorld.Path,
    left: SameFileDecision,
    right: SameFileDecision
  )
    requires SameFilePolicyRelation(
               cmd, fs, preCwd, source, target, left
             )
    requires SameFilePolicyRelation(
               cmd, fs, preCwd, source, target, right
             )
    ensures left == right
  {
  }

  ghost function DigitCharSpec(d: nat): char
    requires d < 10
  { Basename.DigitCharSpec(d) }

  ghost function DecimalNatSpec(n: nat): string
  { Basename.DecimalNatSpec(n) }

  ghost function NumberedBackupPathSpec(target: string, index: nat): string
    requires index >= 1
  { Basename.NumberedBackupPathSpec(target,index) }

  ghost function SimpleBackupPathSpec(target: string, suffix: string): string
  { Basename.SimpleBackupPathSpec(target,suffix) }

  function SourceNewerSpec(srcSec: int, srcNsec: int, dstSec: int, dstNsec: int): bool
  {
    srcSec > dstSec || (srcSec == dstSec && srcNsec > dstNsec)
  }

  function TargetDirectoryErrSpec(statOk: bool, isDir: bool, statErr: int): int
  {
    if statOk then
      if !isDir then Errno.ENOTDIR else statErr
    else
      statErr
  }

  function StepSuccessStdoutSpecPart1(): BenchWorld.Bytes
  {
    ""
  }

  ghost function StepSuccessStdoutSpec(source: string, target: string, backupPath: string, verbose: bool, debug: bool): BenchWorld.Bytes
  {
    if !ShowActionMessageSpec(verbose, debug) then
      []
    else if backupPath == StepSuccessStdoutSpecPart1() then
      VerboseRenameMessageSpec(source, target)
    else
      VerboseRenameWithBackupMessageSpec(source, target, backupPath)
  }

  datatype MoveOutcome = MoveOutcome(
    stdoutFragment: BenchWorld.Bytes,
    stderrFragment: BenchWorld.Bytes,
    failed: bool
  )

  datatype StatusCallEvidence = StatusCallEvidence(
    fs: BenchWorld.FileSystem,
    path: string,
    followSymlink: bool,
    ok: bool,
    status: BenchWorld.FileStatus,
    err: int
  )

  datatype NativeStatusInputs = NativeStatusInputs(
    times: BenchWorld.StatusTimeObservations,
    failures: (BenchWorld.NativeFailureRequest) -> int,
    now: int
  )

  ghost predicate StatusExistsOutcomeFields(fs: BenchWorld.FileSystem, path: string,
                                            followSymlink: bool, found: bool, err: int)
  {
    if found then IOContract.PathExistsContractFields(fs, path, followSymlink, true, err)
    else err > 0 && err in IOContract.NativeStatusFailureErrnosFields(fs, path, followSymlink)
  }

  ghost predicate StatusCallsFor(
    observations: NativeStatusInputs,
    first: nat,
    calls: seq<StatusCallEvidence>
  )
  {
    forall i: nat | i < |calls| ::
      IOContract.ObservedNativeFileStatusContractFields(
        observations.times, observations.failures, first + i, calls[i].fs, calls[i].path,
        calls[i].followSymlink, calls[i].ok, calls[i].status, calls[i].err
      )
  }

  ghost predicate StatusRequest(
    call: StatusCallEvidence,
    fs: BenchWorld.FileSystem,
    path: string,
    followSymlink: bool
  )
  {
    call.fs == fs && call.path == path && call.followSymlink == followSymlink
  }

  ghost predicate BackupStatusSuffix(
    backupMode: Schema.BackupMode,
    fs: BenchWorld.FileSystem,
    target: string,
    calls: seq<StatusCallEvidence>
  )
  {
    if backupMode == Schema.BackupOff || backupMode == Schema.BackupSimple then
      |calls| == 0
    else if backupMode == Schema.BackupExisting then
      |calls| >= 1 &&
      StatusRequest(calls[0], fs, NumberedBackupPathSpec(target, 1), false) &&
      (if !calls[0].ok then
         |calls| == 1
       else
         |calls| >= 2 &&
         (forall i: nat | 1 <= i < |calls| ::
            StatusRequest(calls[i], fs, NumberedBackupPathSpec(target, i), false)) &&
         (forall i: nat | 1 <= i + 1 < |calls| :: calls[i].ok) &&
         !calls[|calls| - 1].ok)
    else
      |calls| >= 1 &&
      (forall i: nat | i < |calls| ::
         StatusRequest(calls[i], fs, NumberedBackupPathSpec(target, i + 1), false)) &&
      (forall i: nat | i + 1 < |calls| :: calls[i].ok) &&
      !calls[|calls| - 1].ok
  }

  ghost predicate ObservedUpdateDecision(
    cmd: Schema.MvCmd,
    fs: BenchWorld.FileSystem,
    cwd: BenchWorld.Path,
    source: string,
    target: string,
    afterFs: BenchWorld.FileSystem,
    outcome: MoveOutcome,
    calls: seq<StatusCallEvidence>
  )
  {
    if cmd.updateMode == Schema.UpdateOlder &&
       cmd.overwriteMode != Schema.OverwriteSkip &&
       |calls| >= 2 && calls[0].ok && calls[1].ok &&
       !(|calls| >= 4 && (!calls[2].ok || !calls[3].ok) &&
         (exists leaf: string :: Basename.BasenameRelation(source, leaf) &&
                                 Basename.BasenameRelation(target, leaf))) &&
       !SameFileMustBeRejected(cmd, fs, cwd, source, target) then
      |calls| >= 2 &&
      StatusRequest(calls[0], fs, source, false) &&
      StatusRequest(calls[1], fs, target, false) &&
      calls[0].ok && calls[1].ok &&
      (if !SourceNewerSpec(
            calls[0].status.times.mtimeSec,
            calls[0].status.times.mtimeNsec,
            calls[1].status.times.mtimeSec,
            calls[1].status.times.mtimeNsec
          ) then
         afterFs == fs &&
         outcome == MoveOutcome(SkipStdoutSpec(target, cmd.debug), [], false)
       else
         ExistingTargetRenameEffectRelation(
           source, target, cmd, fs, cwd, afterFs, outcome
         ))
    else
      true
  }

  ghost predicate ObservedSameFileRejection(
    cmd: Schema.MvCmd, calls: seq<StatusCallEvidence>, sourceLeaf: string,
    targetLeaf: string, resolveOk: bool, resolvedSource: string
  )
  {
    |calls| >= 4 &&
    ((sourceLeaf == targetLeaf && calls[2].ok && calls[3].ok &&
      calls[2].status.hostKey == calls[3].status.hostKey) ||
     (cmd.backupMode == Schema.BackupOff &&
      (calls[0].status.hostKey == calls[1].status.hostKey ||
       (resolveOk && |calls| >= 6 && calls[3].ok && calls[5].ok &&
        calls[3].status.hostKey == calls[5].status.hostKey &&
        (exists referentLeaf: string ::
           Basename.BasenameRelation(resolvedSource, referentLeaf) && referentLeaf == targetLeaf)))))
  }

  ghost predicate ObservedReferentParentFailure(
    calls: seq<StatusCallEvidence>, targetLeaf: string,
    resolveOk: bool, resolvedSource: string
  )
  {
    resolveOk && |calls| >= 6 && (!calls[5].ok || !calls[3].ok) &&
    exists leaf: string :: Basename.BasenameRelation(resolvedSource, leaf) && leaf == targetLeaf
  }

  ghost predicate MoveComparisonObservations(
    cmd: Schema.MvCmd,
    fs: BenchWorld.FileSystem,
    cwd: BenchWorld.Path,
    source: string,
    target: string,
    calls: seq<StatusCallEvidence>,
    sourceParent: string,
    targetParent: string,
    sourceLeaf: string,
    targetLeaf: string,
    resolveOk: bool,
    resolvedSource: string,
    resolveErr: int,
    afterEntries: nat,
    inputs: NativeStatusInputs
  )
  {
    |calls| >= 4 &&
    calls[0].ok && calls[1].ok &&
    StatusRequest(calls[0], fs, source, false) &&
    StatusRequest(calls[1], fs, target, false) &&
    Dirname.DirnameRelation(source, sourceParent) &&
    Dirname.DirnameRelation(target, targetParent) &&
    Basename.BasenameRelation(source, sourceLeaf) &&
    Basename.BasenameRelation(target, targetLeaf) &&
    StatusRequest(calls[2], fs, sourceParent, false) &&
    StatusRequest(calls[3], fs, targetParent, false) &&
    (if sourceLeaf == targetLeaf && (!calls[2].ok || !calls[3].ok) then
       afterEntries == 4 && |calls| == 4 &&
       !resolveOk && resolvedSource == "" && resolveErr == 0
     else (if calls[0].status.kind == BenchWorld.SymlinkKind then
             IOContract.ResolvePathIdentitySpec(
               fs, cwd, inputs.failures, source, resolveOk, resolvedSource, resolveErr
             ) &&
             |calls| >= 5 &&
             StatusRequest(calls[4], fs, source, true) &&
             (if resolveOk then
                exists referentParent: string ::
                  afterEntries == 6 && |calls| >= 6 &&
                  Dirname.DirnameRelation(resolvedSource, referentParent) &&
                  StatusRequest(calls[5], fs, referentParent, false)
              else
                afterEntries == 5)
           else
             afterEntries == 4 && !resolveOk && resolvedSource == "" && resolveErr == 0))
  }

  ghost predicate MoveContinuationObservations(
    cmd: Schema.MvCmd,
    fs: BenchWorld.FileSystem,
    cwd: BenchWorld.Path,
    source: string,
    target: string,
    calls: seq<StatusCallEvidence>,
    sourceParent: string,
    targetParent: string,
    sourceLeaf: string,
    targetLeaf: string,
    resolveOk: bool,
    resolvedSource: string,
    resolveErr: int,
    afterEntries: nat,
    inputs: NativeStatusInputs
  )
  {
    |calls| >= 4 &&
    (if sourceLeaf == targetLeaf && (!calls[2].ok || !calls[3].ok) then true
     else
       (if ObservedReferentParentFailure(calls, targetLeaf, resolveOk, resolvedSource) ||
           ObservedSameFileRejection(cmd, calls, sourceLeaf, targetLeaf, resolveOk, resolvedSource) ||
           (cmd.updateMode == Schema.UpdateOlder &&
            !SourceNewerSpec(
              calls[0].status.times.mtimeSec,
              calls[0].status.times.mtimeNsec,
              calls[1].status.times.mtimeSec,
              calls[1].status.times.mtimeNsec
            )) then
          |calls| == afterEntries
        else
          var collisionNeeded :=
            (cmd.backupMode == Schema.BackupSimple ||
             cmd.backupMode == Schema.BackupExisting) &&
            sourceLeaf == targetLeaf + cmd.backupSuffix;
          var afterCollision := afterEntries +
                                (if collisionNeeded then 1 else 0);
          afterCollision <= |calls| &&
          (collisionNeeded ==>
             StatusRequest(
               calls[afterEntries], fs,
               SimpleBackupPathSpec(target, cmd.backupSuffix), true
             )) &&
          (if collisionNeeded && calls[afterEntries].ok &&
              calls[afterEntries].status.hostKey == calls[0].status.hostKey then
             |calls| == afterCollision
           else
             BackupStatusSuffix(cmd.backupMode, fs, target, calls[afterCollision..]))))
  }

  ghost opaque predicate MoveStatusShapeWitness(
    cmd: Schema.MvCmd,
    fs: BenchWorld.FileSystem,
    cwd: BenchWorld.Path,
    source: string,
    target: string,
    calls: seq<StatusCallEvidence>,
    sourceParent: string,
    targetParent: string,
    sourceLeaf: string,
    targetLeaf: string,
    resolveOk: bool,
    resolvedSource: string,
    resolveErr: int,
    afterEntries: nat,
    inputs: NativeStatusInputs
  )
  {
    MoveComparisonObservations(cmd, fs, cwd, source, target, calls, sourceParent, targetParent,
                               sourceLeaf, targetLeaf, resolveOk, resolvedSource, resolveErr, afterEntries, inputs) &&
    MoveContinuationObservations(cmd, fs, cwd, source, target, calls, sourceParent, targetParent,
                                 sourceLeaf, targetLeaf, resolveOk, resolvedSource, resolveErr, afterEntries, inputs)
  }

  ghost opaque predicate MoveStatusShape(
    cmd: Schema.MvCmd,
    fs: BenchWorld.FileSystem,
    cwd: BenchWorld.Path,
    source: string,
    target: string,
    calls: seq<StatusCallEvidence>,
    inputs: NativeStatusInputs
  )
  {
    |calls| >= 1 &&
    StatusRequest(calls[0], fs, source, false) &&
    (if !calls[0].ok then
       |calls| == 1
     else
       |calls| >= 2 &&
       StatusRequest(calls[1], fs, target, false) &&
       (if !calls[1].ok || cmd.overwriteMode == Schema.OverwriteSkip ||
           cmd.updateMode == Schema.UpdateNone ||
           cmd.updateMode == Schema.UpdateNoneFail then
          |calls| == 2
        else
          exists sourceParent: string, targetParent: string,
            sourceLeaf: string, targetLeaf: string,
            resolveOk: bool, resolvedSource: string, resolveErr: int,
            afterEntries: nat ::
            MoveStatusShapeWitness(
              cmd, fs, cwd, source, target, calls,
              sourceParent, targetParent, sourceLeaf, targetLeaf,
              resolveOk, resolvedSource, resolveErr, afterEntries, inputs
            )))
  }

  ghost function ConcatenateFragments(fragments: seq<BenchWorld.Bytes>): BenchWorld.Bytes
    decreases |fragments|
  {
    if |fragments| == 0 then
      []
    else
      fragments[0] + ConcatenateFragments(fragments[1..])
  }

  ghost predicate NumberedBackupTargetSpecFromFields(preFs: BenchWorld.FileSystem, target: string, start: nat, backupPath: string)
  {
    start >= 1 &&
    exists index: nat, missErr: int ::
      index >= start &&
      backupPath == NumberedBackupPathSpec(target, index) &&
      StatusExistsOutcomeFields(preFs, backupPath, false, false, missErr) &&
      forall j: nat | start <= j < index ::
        StatusExistsOutcomeFields(preFs, NumberedBackupPathSpec(target, j), false, true, 0)
  }

  ghost predicate NumberedBackupTargetSpecFields(preFs: BenchWorld.FileSystem, target: string, backupPath: string)
  {
    NumberedBackupTargetSpecFromFields(preFs, target, 1, backupPath)
  }

  ghost predicate BackupTargetSpecFields(preFs: BenchWorld.FileSystem, target: string, backupMode: Schema.BackupMode, suffix: string, backupPath: string)
  {
    if backupMode == Schema.BackupOff then
      backupPath == ""
    else if backupMode == Schema.BackupSimple then
      backupPath == SimpleBackupPathSpec(target, suffix)
    else if backupMode == Schema.BackupExisting then
      ((exists hitErr: int ::
          StatusExistsOutcomeFields(preFs, NumberedBackupPathSpec(target, 1), false, true, hitErr) &&
          NumberedBackupTargetSpecFields(preFs, target, backupPath)) ||
       (exists missErr: int ::
          StatusExistsOutcomeFields(preFs, NumberedBackupPathSpec(target, 1), false, false, missErr) &&
          backupPath == SimpleBackupPathSpec(target, suffix)))
    else
      NumberedBackupTargetSpecFields(preFs, target, backupPath)
  }

  ghost predicate BackupWouldDestroySource(
    cmd: Schema.MvCmd,
    fs: BenchWorld.FileSystem,
    source: string,
    target: string
  )
  {
    (cmd.backupMode == Schema.BackupSimple ||
     cmd.backupMode == Schema.BackupExisting) &&
    (exists sourceLeaf: string, targetLeaf: string ::
       Basename.BasenameRelation(source, sourceLeaf) &&
       Basename.BasenameRelation(target, targetLeaf) &&
       sourceLeaf == targetLeaf + cmd.backupSuffix) &&
    exists
      resolvedSource: BenchWorld.Path,
      resolvedBackup: BenchWorld.Path
      ::
        IOContract.ResolvePathForMetadataFields(
          fs, source, false
        ) == Result.Ok(resolvedSource) &&
        IOContract.ResolvePathForMetadataFields(
          fs, SimpleBackupPathSpec(target, cmd.backupSuffix), true
        ) == Result.Ok(resolvedBackup) &&
        BenchWorld.InodeSameObject(
          fs, resolvedSource, resolvedBackup
        )
  }

  ghost predicate RenameEffectRelation(
    source: string,
    target: string,
    backupPath: string,
    verbose: bool,
    debug: bool,
    beforeFs: BenchWorld.FileSystem,
    preCwd: BenchWorld.Path,
    afterFs: BenchWorld.FileSystem,
    outcome: MoveOutcome
  )
  {
    (backupPath == "" &&
     IOContract.RenamePathContractFields(beforeFs, source, target, true, 0, afterFs) &&
     outcome == MoveOutcome(StepSuccessStdoutSpec(source, target, "", verbose, debug), [], false)) ||
    (backupPath == "" &&
     exists
       renameErr: int,
       sourceIsDir: bool,
       sourceStatErr: int
       ::
         IOContract.IsDirectoryStrictContractFields(
           beforeFs,
           source,
           false,
           true,
           sourceIsDir,
           sourceStatErr
         ) &&
         IOContract.RenamePathContractFields(beforeFs, source, target, false, renameErr, afterFs) &&
         outcome == MoveOutcome(
           [],
           SourceRenameFailureMessageSpec(
             source,
             target,
             SourceRenameDiagnosticErrSpec(
               target, sourceIsDir, renameErr
             ),
             sourceIsDir && StatusExistsOutcomeFields(
               beforeFs, target, false, true, 0)
           ),
           true
         )) ||
    (backupPath != "" &&
     exists backupErr: int ::
       IOContract.RenamePathContractFields(beforeFs, target, backupPath, false, backupErr, afterFs) &&
       outcome == MoveOutcome([], RenameFailureMessageSpec(source, target, backupErr), true)) ||
    (backupPath != "" &&
     exists backupFs: BenchWorld.FileSystem ::
       IOContract.RenamePathContractFields(beforeFs, target, backupPath, true, 0, backupFs) &&
       IOContract.RenamePathContractFields(backupFs, source, target, true, 0, afterFs) &&
       outcome == MoveOutcome(StepSuccessStdoutSpec(source, target, backupPath, verbose, debug), [], false)) ||
    (backupPath != "" &&
     exists
       backupFs: BenchWorld.FileSystem,
       renameErr: int,
       sourceIsDir: bool,
       sourceStatErr: int
       ::
         IOContract.IsDirectoryStrictContractFields(
           beforeFs,
           source,
           false,
           true,
           sourceIsDir,
           sourceStatErr
         ) &&
         IOContract.RenamePathContractFields(beforeFs, target, backupPath, true, 0, backupFs) &&
         IOContract.RenamePathContractFields(backupFs, source, target, false, renameErr, afterFs) &&
         outcome == MoveOutcome(
           [],
           SourceRenameFailureMessageSpec(
             source,
             target,
             SourceRenameDiagnosticErrSpec(
               target, sourceIsDir, renameErr
             ),
             false
           ),
           true
         ))
  }

  ghost predicate ObservedRenameEffectRelation(
    source: string, target: string, backupPath: string, cmd: Schema.MvCmd,
    sourceIsDir: bool, targetWasFound: bool, inputs: NativeStatusInputs,
    beforeFs: BenchWorld.FileSystem, afterFs: BenchWorld.FileSystem, outcome: MoveOutcome
  )
  {
    (backupPath == "" &&
     IOContract.RenamePathSpec(beforeFs, inputs.now, inputs.failures,
                               afterFs, source, target, true, 0) &&
     outcome == MoveOutcome(StepSuccessStdoutSpec(source, target, "", cmd.verbose, cmd.debug), [], false)) ||
    (backupPath == "" &&
     exists err: int ::
       IOContract.RenamePathSpec(beforeFs, inputs.now, inputs.failures,
                                 afterFs, source, target, false, err) &&
       outcome == MoveOutcome([], SourceRenameFailureMessageSpec(source, target,
                                                                 SourceRenameDiagnosticErrSpec(target, sourceIsDir, err), sourceIsDir && targetWasFound), true)) ||
    (backupPath != "" &&
     exists err: int ::
       IOContract.RenamePathSpec(beforeFs, inputs.now, inputs.failures,
                                 afterFs, target, backupPath, false, err) &&
       outcome == MoveOutcome([], RenameFailureMessageSpec(source, target, err), true)) ||
    (backupPath != "" &&
     exists backupFs: BenchWorld.FileSystem ::
       IOContract.RenamePathSpec(beforeFs, inputs.now, inputs.failures,
                                 backupFs, target, backupPath, true, 0) &&
       IOContract.RenamePathSpec(backupFs, inputs.now, inputs.failures,
                                 afterFs, source, target, true, 0) &&
       outcome == MoveOutcome(StepSuccessStdoutSpec(source, target, backupPath, cmd.verbose, cmd.debug), [], false)) ||
    (backupPath != "" &&
     exists backupFs: BenchWorld.FileSystem, err: int ::
       IOContract.RenamePathSpec(beforeFs, inputs.now, inputs.failures,
                                 backupFs, target, backupPath, true, 0) &&
       IOContract.RenamePathSpec(backupFs, inputs.now, inputs.failures,
                                 afterFs, source, target, false, err) &&
       outcome == MoveOutcome([], SourceRenameFailureMessageSpec(source, target,
                                                                 SourceRenameDiagnosticErrSpec(target, sourceIsDir, err), false), true))
  }

  ghost predicate BackupPathFromObservations(
    cmd: Schema.MvCmd, fs: BenchWorld.FileSystem, target: string,
    calls: seq<StatusCallEvidence>, path: string
  )
  {
    BackupStatusSuffix(cmd.backupMode, fs, target, calls) &&
    (if cmd.backupMode == Schema.BackupOff then path == ""
     else if cmd.backupMode == Schema.BackupSimple then
       path == SimpleBackupPathSpec(target, cmd.backupSuffix)
     else if cmd.backupMode == Schema.BackupExisting && !calls[0].ok then
       path == SimpleBackupPathSpec(target, cmd.backupSuffix)
     else if cmd.backupMode == Schema.BackupExisting then
       |calls| >= 2 && path == NumberedBackupPathSpec(target, |calls| - 1)
     else |calls| >= 1 && path == NumberedBackupPathSpec(target, |calls|))
  }

  ghost predicate ExistingTargetRenameEffectRelation(
    source: string,
    target: string,
    cmd: Schema.MvCmd,
    beforeFs: BenchWorld.FileSystem,
    preCwd: BenchWorld.Path,
    afterFs: BenchWorld.FileSystem,
    outcome: MoveOutcome
  )
  {
    if BackupWouldDestroySource(cmd, beforeFs, source, target) then
      afterFs == beforeFs &&
      outcome == MoveOutcome(
        [],
        BackupWouldDestroySourceMessageSpec(source, target),
        true
      )
    else if cmd.backupMode == Schema.BackupOff then
      RenameEffectRelation(
        source, target, "", cmd.verbose, cmd.debug,
        beforeFs, preCwd, afterFs, outcome
      )
    else
      exists backupPath: string ::
        BackupTargetSpecFields(
          beforeFs, target, cmd.backupMode, cmd.backupSuffix, backupPath
        ) &&
        RenameEffectRelation(
          source, target, backupPath, cmd.verbose, cmd.debug,
          beforeFs, preCwd, afterFs, outcome
        )
  }

  ghost predicate ParentMetadataFailureEffect(
    source: string, target: string, cmd: Schema.MvCmd,
    fs: BenchWorld.FileSystem, afterFs: BenchWorld.FileSystem, outcome: MoveOutcome
  )
  {
    cmd.overwriteMode != Schema.OverwriteSkip &&
    cmd.updateMode != Schema.UpdateNone && cmd.updateMode != Schema.UpdateNoneFail &&
    exists sourceParent: string, targetParent: string, failedPath: string,
      failedStatus: BenchWorld.FileStatus, err: int, leaf: string ::
      Dirname.DirnameRelation(source, sourceParent) &&
      Dirname.DirnameRelation(target, targetParent) &&
      Basename.BasenameRelation(source, leaf) && Basename.BasenameRelation(target, leaf) &&
      failedPath in {sourceParent, targetParent} &&
      IOContract.FileStatusStructureContractFields(fs, failedPath, false, false, failedStatus, err) &&
      err > 0 && afterFs == fs &&
      outcome == MoveOutcome([], ParentStatFailureMessageSpec(failedPath, err), true)
  }

  ghost predicate OriginalMoveEffectRelation(
    source: string,
    target: string,
    cmd: Schema.MvCmd,
    beforeFs: BenchWorld.FileSystem,
    preCwd: BenchWorld.Path,
    afterFs: BenchWorld.FileSystem,
    outcome: MoveOutcome
  )
  {
    exists sourceOk: bool, sourceIsDir: bool, sourceErr: int ::
      IOContract.IsDirectoryStrictContractFields(
        beforeFs, source, false, sourceOk, sourceIsDir, sourceErr
      ) &&
      if !sourceOk then
        afterFs == beforeFs &&
        outcome == MoveOutcome(
          [], SourceStatFailureMessageSpec(source, sourceErr), true
        )
      else
        exists found: bool, existsErr: int ::
          StatusExistsOutcomeFields(
            beforeFs, target, false, found, existsErr
          ) &&
          if !found then
            RenameEffectRelation(
              source, target, "", cmd.verbose, cmd.debug,
              beforeFs, preCwd, afterFs, outcome
            )
          else if cmd.overwriteMode == Schema.OverwriteSkip then
            afterFs == beforeFs &&
            outcome == MoveOutcome(SkipStdoutSpec(target, cmd.debug), [], false)
          else if cmd.updateMode == Schema.UpdateNone then
            afterFs == beforeFs &&
            outcome == MoveOutcome(SkipStdoutSpec(target, cmd.debug), [], false)
          else if cmd.updateMode == Schema.UpdateNoneFail then
            afterFs == beforeFs &&
            outcome == MoveOutcome([], NotReplacingMessageSpec(target), true)
          else
            exists decision: SameFileDecision ::
              SameFilePolicyRelation(
                cmd, beforeFs, preCwd, source, target, decision
              ) &&
              if decision == RejectSameFile then
                afterFs == beforeFs &&
                outcome == MoveOutcome(
                  [], SameFileMessageSpec(source, target), true
                )
              else if cmd.updateMode == Schema.UpdateOlder then
                exists sourceMtimeSec: int, sourceMtimeNsec: int,
                  targetMtimeSec: int, targetMtimeNsec: int ::
                  if !SourceNewerSpec(
                       sourceMtimeSec, sourceMtimeNsec,
                       targetMtimeSec, targetMtimeNsec
                     ) then
                    afterFs == beforeFs &&
                    outcome == MoveOutcome(
                      SkipStdoutSpec(target, cmd.debug), [], false
                    )
                  else
                    ExistingTargetRenameEffectRelation(
                      source, target, cmd, beforeFs, preCwd, afterFs, outcome
                    )
              else
                ExistingTargetRenameEffectRelation(
                  source, target, cmd, beforeFs, preCwd, afterFs, outcome
                )
  }

  ghost predicate ObservedMetadataFault(
    source: string, fs: BenchWorld.FileSystem, cwd: BenchWorld.Path,
    calls: seq<StatusCallEvidence>, inputs: NativeStatusInputs
  )
  {
    (exists i: nat :: i < |calls| && !calls[i].ok &&
                      StatusExistsOutcomeFields(calls[i].fs, calls[i].path, calls[i].followSymlink, true, 0)) ||
    (|calls| >= 4 && calls[0].ok && calls[1].ok &&
     (!calls[2].ok || !calls[3].ok) &&
     (exists leaf: string :: Basename.BasenameRelation(source, leaf) && Basename.BasenameRelation(calls[1].path, leaf))) ||
    (|calls| >= 6 && calls[0].ok && calls[0].status.kind == BenchWorld.SymlinkKind &&
     (!calls[3].ok || !calls[5].ok)) ||
    (|calls| >= 5 && calls[0].ok && calls[0].status.kind == BenchWorld.SymlinkKind &&
     inputs.failures(BenchWorld.ResolveIdentityRequest(fs, cwd, source)) != 0)
  }

  ghost predicate MoveEffectRelation(
    source: string, target: string, cmd: Schema.MvCmd,
    beforeFs: BenchWorld.FileSystem, cwd: BenchWorld.Path,
    afterFs: BenchWorld.FileSystem, outcome: MoveOutcome
  )
  {
    OriginalMoveEffectRelation(source, target, cmd, beforeFs, cwd, afterFs, outcome) ||
    ParentMetadataFailureEffect(source, target, cmd, beforeFs, afterFs, outcome) ||
    (exists inputs: NativeStatusInputs, first: nat, calls: seq<StatusCallEvidence> ::
       StatusCallsFor(inputs, first, calls) &&
       MoveStatusShape(cmd, beforeFs, cwd, source, target, calls, inputs) &&
       ObservedMoveOutcome(source, target, cmd, beforeFs, cwd, afterFs, outcome, calls, inputs) &&
       ObservedMetadataFault(source, beforeFs, cwd, calls, inputs))
  }

  ghost predicate BatchMoveWitnessRelation(
    sources: seq<string>,
    directory: string,
    cmd: Schema.MvCmd,
    beforeFs: BenchWorld.FileSystem,
    preCwd: BenchWorld.Path,
    afterFs: BenchWorld.FileSystem,
    hadError: bool,
    out: BenchWorld.Bytes,
    err: BenchWorld.Bytes,
    fsBounds: seq<BenchWorld.FileSystem>,
    outcomes: seq<MoveOutcome>,
    stdoutFragments: seq<BenchWorld.Bytes>,
    stderrFragments: seq<BenchWorld.Bytes>
  )
  {
    |fsBounds| == |sources| + 1 &&
    |outcomes| == |sources| &&
    |stdoutFragments| == |sources| &&
    |stderrFragments| == |sources| &&
    fsBounds[0] == beforeFs &&
    fsBounds[|fsBounds| - 1] == afterFs &&
    (forall i: nat | i < |sources| ::
       var normalizedSource :=
         NormalizeSourceSpec(sources[i], cmd.stripTrailingSlashes);
       MoveEffectRelation(
         normalizedSource,
         TargetInDirectorySpec(directory, normalizedSource),
         cmd,
         fsBounds[i],
         preCwd,
         fsBounds[i + 1],
         outcomes[i]
       ) &&
       stdoutFragments[i] == outcomes[i].stdoutFragment &&
       stderrFragments[i] == outcomes[i].stderrFragment) &&
    ConcatenateFragments(stdoutFragments) == out &&
    ConcatenateFragments(stderrFragments) == err &&
    (hadError <==>
     exists i: nat :: i < |outcomes| && outcomes[i].failed)
  }

  ghost predicate BatchMoveRelation(
    sources: seq<string>,
    directory: string,
    cmd: Schema.MvCmd,
    beforeFs: BenchWorld.FileSystem,
    preCwd: BenchWorld.Path,
    afterFs: BenchWorld.FileSystem,
    hadError: bool,
    out: BenchWorld.Bytes,
    err: BenchWorld.Bytes
  )
  {
    exists
      fsBounds: seq<BenchWorld.FileSystem>,
      outcomes: seq<MoveOutcome>,
      stdoutFragments: seq<BenchWorld.Bytes>,
      stderrFragments: seq<BenchWorld.Bytes>
      ::
        BatchMoveWitnessRelation(
          sources, directory, cmd, beforeFs, preCwd, afterFs,
          hadError, out, err,
          fsBounds, outcomes, stdoutFragments, stderrFragments
        )
  }

  ghost predicate TargetDirectoryCheckSpecFields(directory: string, preFs: BenchWorld.FileSystem, ok: bool, err: int)
  {
    exists statOk: bool, isDir: bool, statErr: int ::
      IOContract.IsDirectoryContractFields(
        preFs, directory, true, statOk, isDir, statErr
      ) &&
      ok == (statOk && isDir) &&
      err == TargetDirectoryErrSpec(statOk, isDir, statErr)
  }

  ghost predicate CandidateRunIntoDirectoryFields(
    sources: seq<string>,
    directory: string,
    explicitTargetDirectory: bool,
    cmd: Schema.MvCmd,
    beforeFs: BenchWorld.FileSystem,
    preCwd: BenchWorld.Path,
    afterFs: BenchWorld.FileSystem,
    preStdout: BenchWorld.Bytes,
    preStderr: BenchWorld.Bytes,
    stdout2: BenchWorld.Bytes,
    stderr2: BenchWorld.Bytes,
    exit: int
  )
  {
    (exists hadError: bool, out: BenchWorld.Bytes, err: BenchWorld.Bytes ::
       TargetDirectoryCheckSpecFields(directory, beforeFs, true, 0) &&
       BatchMoveRelation(
         sources, directory, cmd,
         beforeFs, preCwd, afterFs, hadError, out, err
       ) &&
       exit == (if hadError then 1 else 0) &&
       stdout2 == preStdout + out &&
       stderr2 == preStderr + err) ||
    (exists directoryErr: int ::
       TargetDirectoryCheckSpecFields(
         directory, beforeFs, false, directoryErr
       ) &&
       afterFs == beforeFs &&
       exit == 1 &&
       stdout2 == preStdout &&
       stderr2 == preStderr +
       TargetFailureMessageSpec(
         directory, explicitTargetDirectory, directoryErr
       ))
  }

  ghost predicate CandidateRunTwoOperandFields(
    cmd: Schema.MvCmd,
    beforeFs: BenchWorld.FileSystem,
    preCwd: BenchWorld.Path,
    afterFs: BenchWorld.FileSystem,
    preStdout: BenchWorld.Bytes,
    preStderr: BenchWorld.Bytes,
    stdout2: BenchWorld.Bytes,
    stderr2: BenchWorld.Bytes,
    exit: int
  )
    requires |cmd.operands| == 2
  {
    var source :=
      NormalizeSourceSpec(cmd.operands[0], cmd.stripTrailingSlashes);
    var destination := cmd.operands[1];
    if cmd.noTargetDirectory then
      exists outcome: MoveOutcome ::
        MoveEffectRelation(
          source, destination, cmd,
          beforeFs, preCwd, afterFs, outcome
        ) &&
        exit == (if outcome.failed then 1 else 0) &&
        stdout2 == preStdout + outcome.stdoutFragment &&
        stderr2 == preStderr + outcome.stderrFragment
    else
      (exists directoryErr: int, outcome: MoveOutcome ::
         IOContract.IsDirectoryContractFields(
           beforeFs, destination, true, true, true, directoryErr
         ) &&
         BatchMoveRelation(
           [cmd.operands[0]], destination, cmd,
           beforeFs, preCwd, afterFs, outcome.failed,
           outcome.stdoutFragment, outcome.stderrFragment
         ) &&
         exit == (if outcome.failed then 1 else 0) &&
         stdout2 == preStdout + outcome.stdoutFragment &&
         stderr2 == preStderr + outcome.stderrFragment) ||
      (exists directoryErr: int, outcome: MoveOutcome ::
         IOContract.IsDirectoryContractFields(
           beforeFs, destination, true, true, false, directoryErr
         ) &&
         MoveEffectRelation(
           source, destination, cmd,
           beforeFs, preCwd, afterFs, outcome
         ) &&
         exit == (if outcome.failed then 1 else 0) &&
         stdout2 == preStdout + outcome.stdoutFragment &&
         stderr2 == preStderr + outcome.stderrFragment) ||
      (exists directoryErr: int, outcome: MoveOutcome ::
         IOContract.IsDirectoryContractFields(
           beforeFs, destination, true, false, false, directoryErr
         ) &&
         MoveEffectRelation(
           source, destination, cmd,
           beforeFs, preCwd, afterFs, outcome
         ) &&
         exit == (if outcome.failed then 1 else 0) &&
         stdout2 == preStdout + outcome.stdoutFragment &&
         stderr2 == preStderr + outcome.stderrFragment) ||
      (exists directoryErr: int, outcome: MoveOutcome ::
         IOContract.IsDirectoryContractFields(
           beforeFs, destination, true, false, true, directoryErr
         ) &&
         MoveEffectRelation(
           source, destination, cmd,
           beforeFs, preCwd, afterFs, outcome
         ) &&
         exit == (if outcome.failed then 1 else 0) &&
         stdout2 == preStdout + outcome.stdoutFragment &&
         stderr2 == preStderr + outcome.stderrFragment)
  }

  ghost predicate CandidateSpecFields(
    raw: Schema.MvCmdRaw,
    preFs: BenchWorld.FileSystem,
    preCwd: BenchWorld.Path,
    preStdout: BenchWorld.Bytes,
    preStderr: BenchWorld.Bytes,
    afterFs: BenchWorld.FileSystem,
    plannedStdout: BenchWorld.Bytes,
    plannedStderr: BenchWorld.Bytes,
    exit: int
  )
  {
    var cmd := Schema.Command(raw);
    if cmd.mode == Schema.ModeInvalidBackup then
      afterFs == preFs &&
      exit == 1 &&
      plannedStdout == preStdout &&
      plannedStderr ==
      preStderr + InvalidBackupArgumentMessageSpec(cmd.invalidBackupArg)
    else if cmd.mode == Schema.ModeInvalidUpdate then
      afterFs == preFs &&
      exit == 1 &&
      plannedStdout == preStdout &&
      plannedStderr ==
      preStderr + InvalidUpdateArgumentMessageSpec(cmd.invalidUpdateArg)
    else if cmd.mode == Schema.ModeHelp then
      afterFs == preFs &&
      exit == 0 &&
      plannedStdout == preStdout + HelpTextSpec() &&
      plannedStderr == preStderr
    else if cmd.mode == Schema.ModeVersion then
      afterFs == preFs &&
      exit == 0 &&
      plannedStdout == preStdout + VersionTextSpec() &&
      plannedStderr == preStderr
    else if cmd.targetDirectory != "" && cmd.noTargetDirectory then
      afterFs == preFs &&
      exit == 1 &&
      plannedStdout == preStdout &&
      plannedStderr == preStderr + TargetDirectoryConflictMessageSpec()
    else if |cmd.operands| == 0 then
      afterFs == preFs &&
      exit == 1 &&
      plannedStdout == preStdout &&
      plannedStderr == preStderr + MissingFileOperandMessageSpec()
    else if cmd.targetDirectory != "" then
      CandidateRunIntoDirectoryFields(
        cmd.operands, cmd.targetDirectory, true, cmd,
        preFs, preCwd, afterFs,
        preStdout, preStderr, plannedStdout, plannedStderr, exit
      )
    else if |cmd.operands| == 1 then
      afterFs == preFs &&
      exit == 1 &&
      plannedStdout == preStdout &&
      plannedStderr ==
      preStderr + MissingDestinationMessageSpec(cmd.operands[0])
    else if cmd.noTargetDirectory && |cmd.operands| > 2 then
      afterFs == preFs &&
      exit == 1 &&
      plannedStdout == preStdout &&
      plannedStderr == preStderr + ExtraOperandMessageSpec(cmd.operands[2])
    else if |cmd.operands| == 2 then
      CandidateRunTwoOperandFields(
        cmd, preFs, preCwd, afterFs,
        preStdout, preStderr, plannedStdout, plannedStderr, exit
      )
    else
      CandidateRunIntoDirectoryFields(
        cmd.operands[..|cmd.operands| - 1],
        cmd.operands[|cmd.operands| - 1],
        false,
        cmd,
        preFs,
        preCwd,
        afterFs,
        preStdout,
        preStderr,
        plannedStdout,
        plannedStderr,
        exit
      )
  }

  ghost predicate ObservedParentFailureOutcome(
    source: string, target: string, cmd: Schema.MvCmd, fs: BenchWorld.FileSystem, cwd: BenchWorld.Path,
    afterFs: BenchWorld.FileSystem, outcome: MoveOutcome,
    calls: seq<StatusCallEvidence>
  )
  {
    if |calls| >= 4 && calls[0].ok && calls[1].ok &&
       (!calls[2].ok || !calls[3].ok) &&
       (exists leaf: string :: Basename.BasenameRelation(source, leaf) &&
                               Basename.BasenameRelation(target, leaf)) then
      |calls| == 4 && afterFs == fs &&
      (exists sourceParent: string, targetParent: string ::
         Dirname.DirnameRelation(source, sourceParent) &&
         Dirname.DirnameRelation(target, targetParent) &&
         StatusRequest(calls[2], fs, sourceParent, false) &&
         StatusRequest(calls[3], fs, targetParent, false) &&
         outcome == MoveOutcome([], ParentStatFailureMessageSpec(
                                  if !calls[2].ok then sourceParent else targetParent,
                                  if !calls[2].ok then calls[2].err else calls[3].err), true))
    else OriginalMoveEffectRelation(source, target, cmd, fs, cwd, afterFs, outcome)
  }

  ghost predicate ObservedClassificationOutcome(
    source: string, target: string, cmd: Schema.MvCmd,
    fs: BenchWorld.FileSystem, cwd: BenchWorld.Path,
    afterFs: BenchWorld.FileSystem, outcome: MoveOutcome,
    calls: seq<StatusCallEvidence>, inputs: NativeStatusInputs,
    names: (string, string, string, string),
    resolveOk: bool, resolvedSource: string, resolveErr: int, afterEntries: nat
  )
  {
    var sourceParent := names.0;
    var targetParent := names.1;
    var sourceLeaf := names.2;
    var targetLeaf := names.3;
    |calls| >= 4 &&
    MoveStatusShapeWitness(cmd, fs, cwd, source, target, calls,
                           sourceParent, targetParent, sourceLeaf, targetLeaf,
                           resolveOk, resolvedSource, resolveErr, afterEntries, inputs) &&
    (if sourceLeaf == targetLeaf && (!calls[2].ok || !calls[3].ok) then
       afterFs == fs && outcome == MoveOutcome([], ParentStatFailureMessageSpec(
                                                 if !calls[2].ok then sourceParent else targetParent,
                                                 if !calls[2].ok then calls[2].err else calls[3].err), true)
     else if ObservedReferentParentFailure(calls, targetLeaf, resolveOk, resolvedSource) then
       afterFs == fs &&
       (exists referentParent: string :: Dirname.DirnameRelation(resolvedSource, referentParent) &&
                                         outcome == MoveOutcome([], ParentStatFailureMessageSpec(
                                                                  if !calls[5].ok then referentParent else targetParent,
                                                                  if !calls[5].ok then calls[5].err else calls[3].err), true))
     else if ObservedSameFileRejection(cmd, calls, sourceLeaf, targetLeaf, resolveOk, resolvedSource) then
       afterFs == fs && outcome == MoveOutcome([], SameFileMessageSpec(source, target), true)
     else if cmd.updateMode == Schema.UpdateOlder &&
             !SourceNewerSpec(calls[0].status.times.mtimeSec, calls[0].status.times.mtimeNsec,
                              calls[1].status.times.mtimeSec, calls[1].status.times.mtimeNsec) then
       afterFs == fs && outcome == MoveOutcome(SkipStdoutSpec(target, cmd.debug), [], false)
     else
       var collisionNeeded :=
         (cmd.backupMode == Schema.BackupSimple || cmd.backupMode == Schema.BackupExisting) &&
         sourceLeaf == targetLeaf + cmd.backupSuffix;
       var afterCollision := afterEntries + (if collisionNeeded then 1 else 0);
       afterCollision <= |calls| &&
       (if collisionNeeded && calls[afterEntries].ok &&
           calls[afterEntries].status.hostKey == calls[0].status.hostKey then
          afterFs == fs && outcome == MoveOutcome([], BackupWouldDestroySourceMessageSpec(source, target), true)
        else
          exists backupPath: string ::
            BackupPathFromObservations(cmd, fs, target, calls[afterCollision..], backupPath) &&
            ObservedRenameEffectRelation(source, target, backupPath, cmd,
                                         calls[0].status.kind == BenchWorld.DirectoryKind, true, inputs,
                                         fs, afterFs, outcome)))
  }

  ghost predicate ObservedMoveOutcome(
    source: string, target: string, cmd: Schema.MvCmd,
    fs: BenchWorld.FileSystem, cwd: BenchWorld.Path,
    afterFs: BenchWorld.FileSystem, outcome: MoveOutcome,
    calls: seq<StatusCallEvidence>, inputs: NativeStatusInputs
  )
  {
    |calls| >= 1 &&
    (if !calls[0].ok then
       afterFs == fs && outcome == MoveOutcome([], SourceStatFailureMessageSpec(source, calls[0].err), true)
     else
       |calls| >= 2 &&
       (if !calls[1].ok then
          ObservedRenameEffectRelation(source, target, "", cmd,
                                       calls[0].status.kind == BenchWorld.DirectoryKind, false, inputs,
                                       fs, afterFs, outcome)
        else if cmd.overwriteMode == Schema.OverwriteSkip || cmd.updateMode == Schema.UpdateNone then
          afterFs == fs && outcome == MoveOutcome(SkipStdoutSpec(target, cmd.debug), [], false)
        else if cmd.updateMode == Schema.UpdateNoneFail then
          afterFs == fs && outcome == MoveOutcome([], NotReplacingMessageSpec(target), true)
        else
          exists sourceParent: string, targetParent: string, sourceLeaf: string, targetLeaf: string,
            resolveOk: bool, resolvedSource: string, resolveErr: int, afterEntries: nat ::
            ObservedClassificationOutcome(source, target, cmd, fs, cwd, afterFs, outcome,
                                          calls, inputs, (sourceParent, targetParent, sourceLeaf, targetLeaf),
                                          resolveOk, resolvedSource, resolveErr, afterEntries)))
  }

  ghost predicate ObservedStepRelation(
    source: string,
    target: string,
    cmd: Schema.MvCmd,
    beforeFs: BenchWorld.FileSystem,
    cwd: BenchWorld.Path,
    afterFs: BenchWorld.FileSystem,
    outcome: MoveOutcome,
    observations: NativeStatusInputs,
    firstStatus: nat,
    afterStatus: nat,
    calls: seq<StatusCallEvidence>
  )
  {
    afterStatus == firstStatus + |calls| &&
    StatusCallsFor(observations, firstStatus, calls) &&
    MoveEffectRelation(source, target, cmd, beforeFs, cwd, afterFs, outcome) &&
    MoveStatusShape(cmd, beforeFs, cwd, source, target, calls, observations) &&
    ObservedMoveOutcome(source, target, cmd, beforeFs, cwd, afterFs, outcome, calls, observations) &&
    (!ObservedMetadataFault(source, beforeFs, cwd, calls, observations) ==>
       OriginalMoveEffectRelation(source, target, cmd, beforeFs, cwd, afterFs, outcome))
  }

  ghost predicate ObservedBatchRelation(
    sources: seq<string>,
    directory: string,
    cmd: Schema.MvCmd,
    beforeFs: BenchWorld.FileSystem,
    cwd: BenchWorld.Path,
    afterFs: BenchWorld.FileSystem,
    hadError: bool,
    out: BenchWorld.Bytes,
    err: BenchWorld.Bytes,
    observations: NativeStatusInputs,
    firstStatus: nat,
    afterStatus: nat,
    calls: seq<StatusCallEvidence>
  )
  {
    afterStatus == firstStatus + |calls| &&
    StatusCallsFor(observations, firstStatus, calls) &&
    exists fsBounds: seq<BenchWorld.FileSystem>,
      outcomes: seq<MoveOutcome>,
      stdoutFragments: seq<BenchWorld.Bytes>,
      stderrFragments: seq<BenchWorld.Bytes>,
      statusBounds: seq<nat> ::
      BatchMoveWitnessRelation(
        sources, directory, cmd, beforeFs, cwd, afterFs,
        hadError, out, err,
        fsBounds, outcomes, stdoutFragments, stderrFragments
      ) &&
      |statusBounds| == |sources| + 1 &&
      statusBounds[0] == firstStatus &&
      statusBounds[|sources|] == afterStatus &&
      (forall i: nat {:trigger statusBounds[i]} | i < |sources| ::
         firstStatus <= statusBounds[i] <= statusBounds[i + 1] <= afterStatus &&
         ObservedStepRelation(
           NormalizeSourceSpec(sources[i], cmd.stripTrailingSlashes),
           TargetInDirectorySpec(
             directory,
             NormalizeSourceSpec(sources[i], cmd.stripTrailingSlashes)
           ),
           cmd,
           fsBounds[i], cwd, fsBounds[i + 1], outcomes[i],
           observations, statusBounds[i], statusBounds[i + 1],
           calls[statusBounds[i] - firstStatus ..
           statusBounds[i + 1] - firstStatus]
         ))
  }

  ghost predicate ObservedStatusSpec(
    raw: Schema.MvCmdRaw,
    beforeFs: BenchWorld.FileSystem,
    cwd: BenchWorld.Path,
    afterFs: BenchWorld.FileSystem,
    beforeStdout: BenchWorld.Bytes,
    afterStdout: BenchWorld.Bytes,
    beforeStderr: BenchWorld.Bytes,
    afterStderr: BenchWorld.Bytes,
    exit: int,
    observations: NativeStatusInputs,
    firstStatus: nat,
    afterStatus: nat,
    calls: seq<StatusCallEvidence>
  )
  {
    var cmd := Schema.Command(raw);
    afterStatus == firstStatus + |calls| &&
    StatusCallsFor(observations, firstStatus, calls) &&
    (if cmd.mode != Schema.ModeRun ||
        (cmd.targetDirectory != "" && cmd.noTargetDirectory) ||
        |cmd.operands| == 0 ||
        (cmd.targetDirectory == "" && |cmd.operands| == 1) ||
        (cmd.targetDirectory == "" && cmd.noTargetDirectory &&
         |cmd.operands| > 2) then
       |calls| == 0
     else if cmd.targetDirectory != "" then
       |calls| >= 1 &&
       StatusRequest(calls[0], beforeFs, cmd.targetDirectory, true) &&
       (if calls[0].ok &&
           calls[0].status.kind == BenchWorld.DirectoryKind then
          exists hadError: bool, out: BenchWorld.Bytes, err: BenchWorld.Bytes
            {:trigger ObservedBatchRelation(
              cmd.operands, cmd.targetDirectory, cmd,
              beforeFs, cwd, afterFs, hadError, out, err,
              observations, firstStatus + 1, afterStatus, calls[1..])} ::
            ObservedBatchRelation(
              cmd.operands, cmd.targetDirectory, cmd,
              beforeFs, cwd, afterFs, hadError, out, err,
              observations, firstStatus + 1, afterStatus, calls[1..]
            ) &&
            exit == (if hadError then 1 else 0) &&
            afterStdout == beforeStdout + out &&
            afterStderr == beforeStderr + err
        else
          |calls| == 1)
     else if |cmd.operands| == 2 then
       var source := NormalizeSourceSpec(
                       cmd.operands[0], cmd.stripTrailingSlashes
                     );
       var destination := cmd.operands[1];
       (if cmd.noTargetDirectory then
          exists outcome: MoveOutcome ::
            ObservedStepRelation(
              source, destination, cmd, beforeFs, cwd, afterFs, outcome,
              observations, firstStatus, afterStatus, calls
            ) &&
            exit == (if outcome.failed then 1 else 0) &&
            afterStdout == beforeStdout + outcome.stdoutFragment &&
            afterStderr == beforeStderr + outcome.stderrFragment
        else
          |calls| >= 1 &&
          StatusRequest(calls[0], beforeFs, destination, true) &&
          var target :=
            if calls[0].ok &&
               calls[0].status.kind == BenchWorld.DirectoryKind then
              TargetInDirectorySpec(destination, source)
            else destination;
          exists outcome: MoveOutcome ::
            ObservedStepRelation(
              source, target, cmd, beforeFs, cwd, afterFs, outcome,
              observations, firstStatus + 1, afterStatus, calls[1..]
            ) &&
            exit == (if outcome.failed then 1 else 0) &&
            afterStdout == beforeStdout + outcome.stdoutFragment &&
            afterStderr == beforeStderr + outcome.stderrFragment)
     else
       var directory := cmd.operands[|cmd.operands| - 1];
       var sources := cmd.operands[..|cmd.operands| - 1];
       |calls| >= 1 &&
       StatusRequest(calls[0], beforeFs, directory, true) &&
       (if calls[0].ok &&
           calls[0].status.kind == BenchWorld.DirectoryKind then
          exists hadError: bool, out: BenchWorld.Bytes, err: BenchWorld.Bytes
            {:trigger ObservedBatchRelation(
              sources, directory, cmd,
              beforeFs, cwd, afterFs, hadError, out, err,
              observations, firstStatus + 1, afterStatus, calls[1..])} ::
            ObservedBatchRelation(
              sources, directory, cmd,
              beforeFs, cwd, afterFs, hadError, out, err,
              observations, firstStatus + 1, afterStatus, calls[1..]
            ) &&
            exit == (if hadError then 1 else 0) &&
            afterStdout == beforeStdout + out &&
            afterStderr == beforeStderr + err
        else
          |calls| == 1))
  }

  function WriteErrorTextPart1(): BenchWorld.Bytes
  {
    "mv: write error: "
  }

  function WriteErrorTextPart2(): BenchWorld.Bytes
  {
    "\n"
  }

  ghost function WriteErrorText(reason: string): BenchWorld.Bytes
  {
    WriteErrorTextPart1() + Utf8.Encode(reason) + WriteErrorTextPart2()
  }

  ghost predicate EmissionOutcomeFields(
    beforeOut: BenchWorld.Bytes, beforeErr: BenchWorld.Bytes,
    afterOut: BenchWorld.Bytes, afterErr: BenchWorld.Bytes,
    observations: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult,
    output: BenchWorld.Bytes, diagnostics: BenchWorld.Bytes,
    normalExit: int, exit: int,
    committed: nat, outErr: int, errCommitted: nat, errErr: int
  )
  {
    (if |output| == 0 then afterOut == beforeOut && committed == 0 && outErr == 0
     else IOContract.WriteStdoutSpec(beforeOut, observations, afterOut, output, committed, outErr)) &&
    var finalDiagnostics := diagnostics +
                            (if outErr == 0 then [] else WriteErrorText(IOContract.CLocaleErrnoTextResult(outErr)));
    (if |finalDiagnostics| == 0 then afterErr == beforeErr && errCommitted == 0 && errErr == 0
     else IOContract.WriteStderrSpec(beforeErr, observations, afterErr, finalDiagnostics, errCommitted, errErr)) &&
    exit == (if outErr != 0 || errErr != 0 then 1 else normalExit)
  }

  ghost predicate EmissionFields(
    beforeOut: BenchWorld.Bytes, beforeErr: BenchWorld.Bytes,
    afterOut: BenchWorld.Bytes, afterErr: BenchWorld.Bytes,
    observations: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult,
    output: BenchWorld.Bytes, diagnostics: BenchWorld.Bytes,
    normalExit: int, exit: int
  )
  {
    exists committed: nat, outErr: int, errCommitted: nat, errErr: int ::
      EmissionOutcomeFields(beforeOut, beforeErr, afterOut, afterErr, observations,
                            output, diagnostics, normalExit, exit, committed, outErr, errCommitted, errErr)
  }

  opaque twostate predicate Spec(raw: Schema.MvCmdRaw, io: BenchIO.IO, exit: int)
    reads io.Footprint()
  {
    exists output: BenchWorld.Bytes, diagnostics: BenchWorld.Bytes, normalExit: int ::
      CandidateSpecFields(raw, old(io.fs()), old(io.cwd()), [], [],
                          io.fs(), output, diagnostics, normalExit) &&
      (exists calls: seq<StatusCallEvidence> ::
         ObservedStatusSpec(raw, old(io.fs()), old(io.cwd()), io.fs(),
                            [], output, [], diagnostics, normalExit, NativeStatusInputs(io.statusObservations(), io.trustedNativeFailures(), io.now()),
                            old(io.statusCursor()), io.statusCursor(), calls)) &&
      EmissionFields(old(io.stdout()), old(io.stderr()), io.stdout(), io.stderr(),
                     io.trustedStreams(), output, diagnostics, normalExit, exit)
  }
}
