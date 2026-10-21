include "../../core/StringEscaping.dfy"
include "CpSchema.dfy"
include "../../core/IO.dfy"
include "../../core/Utf8.dfy"
include "CliSupport.dfy"
include "CpPathSpec.dfy"

module CpSpec {
  import BW = BenchWorld
  import Results
  import BenchIO
  import C = IOContract
  import S = CpSchema
  import CliTypes
  import CliModel
  import Utf8 = Utf8Semantics
  import SE = StringEscaping
  import Paths = CpPathSpec

  function HelpText(): BW.Bytes { "Usage: cp [OPTION]... [-T] SOURCE DEST\n  or:  cp [OPTION]... SOURCE... DIRECTORY\n  or:  cp [OPTION]... -t DIRECTORY SOURCE...\nCopy SOURCE to DEST, or multiple SOURCE(s) to DIRECTORY.\n\nMandatory arguments to long options are mandatory for short options too.\n  -a, --archive\n         same as -dR --preserve=all\n      --attributes-only\n         don't copy the file data, just the attributes\n      --backup[=CONTROL]\n         make a backup of each existing destination file\n  -b\n         like --backup but does not accept an argument\n      --copy-contents\n         copy contents of special files when recursive\n  -d\n         same as --no-dereference --preserve=links\n      --debug\n         explain how a file is copied.  Implies -v\n  -f, --force\n         if an existing destination file cannot be opened, remove it and try\n         again (this option is ignored when the -n option is also used)\n  -i, --interactive\n         prompt before overwrite (overrides a previous -n option)\n  -H\n         follow command-line symbolic links in SOURCE\n  -L, --dereference\n         always follow symbolic links in SOURCE\n  -P, --no-dereference\n         never follow symbolic links in SOURCE\n      --keep-directory-symlink\n         follow existing symlinks to directories\n  -l, --link\n         hard link files instead of copying\n  -n, --no-clobber\n         (deprecated) silently skip existing files.  See also --update\n  -p\n         same as --preserve=mode,ownership,timestamps\n      --preserve[=ATTR_LIST]\n         preserve the specified attributes\n      --no-preserve=ATTR_LIST\n         don't preserve the specified attributes\n      --parents\n         use full source file name under DIRECTORY\n  -R, -r, --recursive\n         copy directories recursively\n      --reflink[=WHEN]\n         control clone/CoW copies. See below\n      --remove-destination\n         remove each existing destination file before attempting to open it\n         (contrast with --force)\n      --sparse=WHEN\n         control creation of sparse files. See below\n      --strip-trailing-slashes\n         remove any trailing slashes from each SOURCE argument\n  -s, --symbolic-link\n         make symbolic links instead of copying\n  -S, --suffix=SUFFIX\n         override the usual backup suffix\n  -t, --target-directory=DIRECTORY\n         copy all SOURCE arguments into DIRECTORY\n  -T, --no-target-directory\n         treat DEST as a normal file\n      --update[=UPDATE]\n         control which existing files are updated;\n         UPDATE={all,none,none-fail,older(default)}\n  -u\n         equivalent to --update[=older].  See below\n  -v, --verbose\n         explain what is being done\n  -x, --one-file-system\n         stay on this file system\n  -Z\n         set SELinux security context of destination file to default type\n      --context[=CTX]\n         like -Z, or if CTX is specified then set the\n         SELinux or SMACK security context to CTX\n      --help\n         display this help and exit\n      --version\n         output version information and exit\n\nATTR_LIST is a comma-separated list of attributes. Attributes are 'mode' for\npermissions (including any ACL and xattr permissions), 'ownership' for user\nand group, 'timestamps' for file timestamps, 'links' for hard links, 'context'\nfor security context, 'xattr' for extended attributes, and 'all' for all\nattributes.\n\nBy default, sparse SOURCE files are detected by a crude heuristic and the\ncorresponding DEST file is made sparse as well.  That is the behavior\nselected by --sparse=auto.  Specify --sparse=always to create a sparse DEST\nfile whenever the SOURCE file contains a long enough sequence of zero bytes.\nUse --sparse=never to inhibit creation of sparse files.\n\nUPDATE controls which existing files in the destination are replaced.\n'all' is the default operation when an --update option is not specified,\nand results in all existing files in the destination being replaced.\n'none' is like the --no-clobber option, in that no files in the\ndestination are replaced, and skipped files do not induce a failure.\n'none-fail' also ensures no files are replaced in the destination,\nbut any skipped files are diagnosed and induce a failure.\n'older' is the default operation when --update is specified, and results\nin files being replaced if they're older than the corresponding source file.\n\nBy default or with --reflink=auto, cp will try a lightweight copy, where the\ndata blocks are copied only when modified, falling back to a standard copy\nif this is not possible.  With --reflink[=always] cp will fail if CoW is not\nsupported, while --reflink=never ensures a standard copy is performed.\n\nThe backup suffix is '~', unless set with --suffix or SIMPLE_BACKUP_SUFFIX.\nThe version control method may be selected via the --backup option or through\nthe VERSION_CONTROL environment variable.  Here are the values:\n\n  none, off       never make backups (even if --backup is given)\n  numbered, t     make numbered backups\n  existing, nil   numbered if numbered backups exist, simple otherwise\n  simple, never   always make simple backups\n\nAs a special case, cp makes a backup of SOURCE when the force and backup\noptions are given and SOURCE and DEST are the same name for an existing,\nregular file.\n\nReport bugs to: bug-coreutils@gnu.org\nGNU coreutils home page: <https://www.gnu.org/software/coreutils/>\nGeneral help using GNU software: <https://www.gnu.org/gethelp/>\nReport any translation bugs to <https://translationproject.org/team/>\nFull documentation <https://www.gnu.org/software/coreutils/cp>\nor available locally via: info '(coreutils) cp invocation'\n" }
  function VersionText(): BW.Bytes { "cp (GNU coreutils) 9.10.13-2cf49\nCopyright (C) 2026 Free Software Foundation, Inc.\nLicense GPLv3+: GNU GPL version 3 or later <https://gnu.org/licenses/gpl.html>.\nThis is free software: you are free to change and redistribute it.\nThere is NO WARRANTY, to the extent permitted by law.\n\nWritten by Torbjorn Granlund, David MacKenzie, and Jim Meyering.\n" }

  function Hint(): BW.Bytes { "Try 'cp --help' for more information.\n" }
  function Missing(): BW.Bytes { "cp: missing file operand\n" + Hint() }
  function MissingDestination(source: BW.Bytes): BW.Bytes {
    "cp: missing destination file operand after " + source + "\n" + Hint()
  }
  function Extra(operand: BW.Bytes): BW.Bytes { "cp: extra operand " + operand + "\n" + Hint() }
  function ConfigurationError(error: S.CpError, quoted: BW.Bytes): BW.Bytes {
    match error
    case NoError => []
    case TargetConflict => "cp: cannot combine --target-directory (-t) and --no-target-directory (-T)\n"
    case MultipleTargets => "cp: multiple target directories specified\n"
    case LinkConflict => "cp: cannot make both hard and symbolic links\n" + Hint()
    case BackupConflict => "cp: --backup is mutually exclusive with -n or --update=none-fail\n" + Hint()
    case InvalidUpdate(_, ambiguous) => ("cp: " + (if ambiguous then "ambiguous" else "invalid") + " argument " + quoted + " for '--update'\n" +
                                         "Valid arguments are:\n  - 'all'\n  - 'none'\n  - 'none-fail'\n  - 'older'\n" + Hint())
    case InvalidPreserve(_, enable, ambiguous) => ("cp: " + (if ambiguous then "ambiguous" else "invalid") + " argument " + quoted +
                                                   (if enable then " for '--preserve'\n" else " for '--no-preserve'\n") +
                                                   "Valid arguments are:\n  - 'mode'\n  - 'timestamps'\n  - 'ownership'\n  - 'links'\n  - 'context'\n  - 'xattr'\n  - 'all'\n" + Hint())
    case InvalidBackup(_, ambiguous, environment) => ("cp: " + (if ambiguous then "ambiguous" else "invalid") + " argument " + quoted + (if environment then " for '$VERSION_CONTROL'\n" else " for 'backup type'\n") +
                                                      "Valid arguments are:\n  - 'none', 'off'\n  - 'simple', 'never'\n  - 'existing', 'nil'\n  - 'numbered', 't'\n" + Hint())
  }
  function ErrorArgument(error: S.CpError): string {
    match error
    case InvalidUpdate(value,_) => value
    case InvalidPreserve(value,_,_) => value
    case InvalidBackup(value,_,_) => value
    case _ => ""
  }
  function ConfigurationDiagnostic(error: S.CpError): BW.Bytes
  {
    ConfigurationError(error,SE.SpecLocaleQuoteBytes(Utf8.Encode(ErrorArgument(error))))
  }
  function LongOption(token: string): string {
    var equal := CliModel.FindChar(token,'=');
    var name := if equal >= 0 then token[..equal] else token;
    if |name| > 2 && name[..2] == "--" then
      var suffix := name[2..];
      if CliModel.HasPrefix("help",suffix) then "--help"
      else if CliModel.HasPrefix("version",suffix) then "--version"
      else name
    else name
  }
  function DuplicateDirectory(source: BW.Bytes): BW.Bytes {
    "cp: warning: source directory " + source + " specified more than once\n"
  }
  function Duplicate(source: BW.Bytes): BW.Bytes {
    "cp: warning: source file " + source + " specified more than once\n"
  }

  function ParseErrorTextPart1(): BW.Bytes
  {
    "--"
  }

  function ParseErrorTextPart2(): BW.Bytes
  {
    "cp: unrecognized option '"
  }

  function ParseErrorTextPart3(): BW.Bytes
  {
    "'\n"
  }

  function ParseErrorTextPart4(): BW.Bytes
  {
    "cp: invalid option -- '"
  }

  function ParseErrorTextPart5(): BW.Bytes
  {
    "cp: invalid option\n"
  }

  function ParseErrorTextPart6(): BW.Bytes
  {
    "cp: option '"
  }

  function ParseErrorTextPart7(): BW.Bytes
  {
    "' requires an argument\n"
  }

  function ParseErrorTextPart8(): BW.Bytes
  {
    "cp: option requires an argument -- '"
  }

  function ParseErrorTextPart9(): BW.Bytes
  {
    "cp: missing option argument\n"
  }

  function ParseErrorTextPart10(): BW.Bytes
  {
    "' doesn't allow an argument\n"
  }

  function ParseErrorTextPart11(): BW.Bytes
  {
    "' is ambiguous\n"
  }

  function ParseErrorText(error: CliTypes.ParseError): BW.Bytes
  {
    if error.kind == CliTypes.UnknownOption then
      if |error.rawToken| > 2 && error.rawToken[..2] == ParseErrorTextPart1() then
        ParseErrorTextPart2() + Utf8.Encode(error.rawToken) + ParseErrorTextPart3() + Hint()
      else if |error.rawToken| > 1 then
        ParseErrorTextPart4() + [Utf8.EncodeChar(error.rawToken[1])[0]] + ParseErrorTextPart3() + Hint()
      else ParseErrorTextPart5() + Hint()
    else if error.kind == CliTypes.MissingValue then
      if |error.rawToken| > 2 && error.rawToken[..2] == ParseErrorTextPart1() then
        ParseErrorTextPart6() + Utf8.Encode(error.rawToken) + ParseErrorTextPart7() + Hint()
      else if |error.rawToken| > 1 then
        ParseErrorTextPart8() + [Utf8.EncodeChar(error.rawToken[|error.rawToken|-1])[0]] + ParseErrorTextPart3() + Hint()
      else ParseErrorTextPart9() + Hint()
    else if error.kind == CliTypes.UnexpectedValue then
      ParseErrorTextPart6() + Utf8.Encode(LongOption(error.rawToken)) + ParseErrorTextPart10() + Hint()
    else ParseErrorTextPart6() + Utf8.Encode(error.rawToken) + ParseErrorTextPart11() + Hint()
  }
  function CannotStatPart1(): BW.Bytes
  {
    "cp: cannot stat "
  }

  function CannotStatPart2(): BW.Bytes
  {
    ": "
  }

  function CannotStatPart3(): BW.Bytes
  {
    "\n"
  }

  function CannotStat(path: BW.Bytes, reason: string): BW.Bytes
  {
    CannotStatPart1() + path + CannotStatPart2() + Utf8.Encode(reason) + CannotStatPart3()
  }
  function Omitting(path: BW.Bytes): BW.Bytes { "cp: -r not specified; omitting directory " + path + "\n" }
  function SameFile(source: BW.Bytes, target: BW.Bytes): BW.Bytes {
    "cp: " + source + " and " + target + " are the same file\n"
  }
  function CannotCreatePart1(): BW.Bytes
  {
    "cp: cannot create regular file "
  }

  function CannotCreatePart2(): BW.Bytes
  {
    ": "
  }

  function CannotCreatePart3(): BW.Bytes
  {
    "\n"
  }

  function CannotCreate(target: BW.Bytes, reason: string): BW.Bytes
  {
    CannotCreatePart1() + target + CannotCreatePart2() + Utf8.Encode(reason) + CannotCreatePart3()
  }
  function CannotOpenPart1(): BW.Bytes
  {
    "cp: cannot open "
  }

  function CannotOpenPart2(): BW.Bytes
  {
    " for reading: "
  }

  function CannotOpenPart3(): BW.Bytes
  {
    "\n"
  }

  function CannotOpen(source: BW.Bytes, reason: string): BW.Bytes
  {
    CannotOpenPart1() + source + CannotOpenPart2() + Utf8.Encode(reason) + CannotOpenPart3()
  }
  function ReadErrorPart1(): BW.Bytes
  {
    "cp: error reading "
  }

  function ReadErrorPart2(): BW.Bytes
  {
    ": "
  }

  function ReadErrorPart3(): BW.Bytes
  {
    "\n"
  }

  function ReadError(source: BW.Bytes, reason: string): BW.Bytes
  {
    ReadErrorPart1() + source + ReadErrorPart2() + Utf8.Encode(reason) + ReadErrorPart3()
  }
  function WriteErrorPart1(): BW.Bytes
  {
    "cp: error writing "
  }

  function WriteErrorPart2(): BW.Bytes
  {
    ": "
  }

  function WriteErrorPart3(): BW.Bytes
  {
    "\n"
  }

  function WriteError(target: BW.Bytes, reason: string): BW.Bytes
  {
    WriteErrorPart1() + target + WriteErrorPart2() + Utf8.Encode(reason) + WriteErrorPart3()
  }
  function CloseErrorPart1(): BW.Bytes
  {
    "cp: failed to close "
  }

  function CloseErrorPart2(): BW.Bytes
  {
    ": "
  }

  function CloseErrorPart3(): BW.Bytes
  {
    "\n"
  }

  function CloseError(target: BW.Bytes, reason: string): BW.Bytes
  {
    CloseErrorPart1() + target + CloseErrorPart2() + Utf8.Encode(reason) + CloseErrorPart3()
  }
  function CannotRemovePart1(): BW.Bytes
  {
    "cp: cannot remove "
  }

  function CannotRemovePart2(): BW.Bytes
  {
    ": "
  }

  function CannotRemovePart3(): BW.Bytes
  {
    "\n"
  }

  function CannotRemove(target: BW.Bytes, reason: string): BW.Bytes
  {
    CannotRemovePart1() + target + CannotRemovePart2() + Utf8.Encode(reason) + CannotRemovePart3()
  }
  function Dangling(target: BW.Bytes): BW.Bytes { "cp: not writing through dangling symlink " + target + "\n" }
  function NonDirectory(source: BW.Bytes, target: BW.Bytes): BW.Bytes {
    "cp: cannot overwrite directory " + target + " with non-directory " + source + "\n"
  }
  function DirectoryOverFile(source: BW.Bytes, target: BW.Bytes): BW.Bytes {
    "cp: cannot overwrite non-directory " + target + " with directory " + source + "\n"
  }
  function NotReplaced(target: BW.Bytes): BW.Bytes { "cp: not replacing " + target + "\n" }
  function Verbose(source: BW.Bytes, target: BW.Bytes): BW.Bytes { source + " -> " + target + "\n" }
  function TargetErrorPart1(): BW.Bytes
  {
    "cp: target "
  }

  function TargetErrorPart2(): BW.Bytes
  {
    ": "
  }

  function TargetErrorPart3(): BW.Bytes
  {
    "\n"
  }

  function TargetError(target: BW.Bytes, reason: string): BW.Bytes
  {
    TargetErrorPart1() + target + TargetErrorPart2() + Utf8.Encode(reason) + TargetErrorPart3()
  }
  function DirectoryErrorPart1(): BW.Bytes
  {
    "cp: target directory "
  }

  function DirectoryErrorPart2(): BW.Bytes
  {
    ": "
  }

  function DirectoryErrorPart3(): BW.Bytes
  {
    "\n"
  }

  function DirectoryError(target: BW.Bytes, reason: string): BW.Bytes
  {
    DirectoryErrorPart1() + target + DirectoryErrorPart2() + Utf8.Encode(reason) + DirectoryErrorPart3()
  }
  function Cycle(source: BW.Bytes): BW.Bytes { "cp: cannot copy cyclic symbolic link " + source + "\n" }
  function IntoSelf(source: BW.Bytes, target: BW.Bytes): BW.Bytes {
    "cp: cannot copy a directory, " + source + ", into itself, " + target + "\n"
  }
  function CreateDirectoryErrorPart1(): BW.Bytes
  {
    "cp: cannot create directory "
  }

  function CreateDirectoryErrorPart2(): BW.Bytes
  {
    ": "
  }

  function CreateDirectoryErrorPart3(): BW.Bytes
  {
    "\n"
  }

  function CreateDirectoryError(target: BW.Bytes, reason: string): BW.Bytes
  {
    CreateDirectoryErrorPart1() + target + CreateDirectoryErrorPart2() + Utf8.Encode(reason) + CreateDirectoryErrorPart3()
  }
  function ReadDirectoryErrorPart1(): BW.Bytes
  {
    "cp: cannot access "
  }

  function ReadDirectoryErrorPart2(): BW.Bytes
  {
    ": "
  }

  function ReadDirectoryErrorPart3(): BW.Bytes
  {
    "\n"
  }

  function ReadDirectoryError(source: BW.Bytes, reason: string): BW.Bytes
  {
    ReadDirectoryErrorPart1() + source + ReadDirectoryErrorPart2() + Utf8.Encode(reason) + ReadDirectoryErrorPart3()
  }
  function LinkErrorPart1(): BW.Bytes
  {
    "cp: cannot create symbolic link "
  }

  function LinkErrorPart2(): BW.Bytes
  {
    " to "
  }

  function LinkErrorPart3(): BW.Bytes
  {
    ": "
  }

  function LinkErrorPart4(): BW.Bytes
  {
    "\n"
  }

  function LinkErrorPart5(): BW.Bytes
  {
    "cp: cannot create hard link "
  }

  function LinkError(source: BW.Bytes, target: BW.Bytes, reason: string, symbolic: bool): BW.Bytes
  {
    if symbolic then LinkErrorPart1() + target + LinkErrorPart2() + source + LinkErrorPart3() + Utf8.Encode(reason) + LinkErrorPart4()
    else LinkErrorPart5() + target + LinkErrorPart2() + source + LinkErrorPart3() + Utf8.Encode(reason) + LinkErrorPart4()
  }
  function CopiedSymlinkErrorPart1(): BW.Bytes
  {
    "cp: cannot create symbolic link "
  }

  function CopiedSymlinkErrorPart2(): BW.Bytes
  {
    ": "
  }

  function CopiedSymlinkErrorPart3(): BW.Bytes
  {
    "\n"
  }

  function CopiedSymlinkError(target: BW.Bytes, reason: string): BW.Bytes
  {
    CopiedSymlinkErrorPart1() + target + CopiedSymlinkErrorPart2() + Utf8.Encode(reason) + CopiedSymlinkErrorPart3()
  }
  function ReadSymlinkErrorPart1(): BW.Bytes
  {
    "cp: cannot read symbolic link "
  }

  function ReadSymlinkErrorPart2(): BW.Bytes
  {
    ": "
  }

  function ReadSymlinkErrorPart3(): BW.Bytes
  {
    "\n"
  }

  function ReadSymlinkError(source: BW.Bytes, reason: string): BW.Bytes
  {
    ReadSymlinkErrorPart1() + source + ReadSymlinkErrorPart2() + Utf8.Encode(reason) + ReadSymlinkErrorPart3()
  }
  function RelativeSymlinkErrorPart1(): BW.Bytes
  {
    "cp: "
  }

  function RelativeSymlinkErrorPart2(): BW.Bytes
  {
    ": can make relative symbolic links only in current directory\n"
  }

  function RelativeSymlinkError(target: string): BW.Bytes
  {
    RelativeSymlinkErrorPart1() + SE.SpecQuoteFBytes(Utf8.Encode(target)) + RelativeSymlinkErrorPart2()
  }
  function Removed(target: BW.Bytes): BW.Bytes { "removed " + target + "\n" }

  function ModeErrorPart1(): BW.Bytes
  {
    "cp: preserving permissions for "
  }

  function ModeErrorPart2(): BW.Bytes
  {
    ": "
  }

  function ModeErrorPart3(): BW.Bytes
  {
    "\n"
  }

  function ModeError(target: BW.Bytes, reason: string): BW.Bytes
  {
    ModeErrorPart1() + target + ModeErrorPart2() + Utf8.Encode(reason) + ModeErrorPart3()
  }
  function TimeErrorPart1(): BW.Bytes
  {
    "cp: preserving times for "
  }

  function TimeErrorPart2(): BW.Bytes
  {
    ": "
  }

  function TimeErrorPart3(): BW.Bytes
  {
    "\n"
  }

  function TimeError(target: BW.Bytes, reason: string): BW.Bytes
  {
    TimeErrorPart1() + target + TimeErrorPart2() + Utf8.Encode(reason) + TimeErrorPart3()
  }
  function StdoutErrorPart1(): BW.Bytes
  {
    "cp: write error: "
  }

  function StdoutErrorPart2(): BW.Bytes
  {
    "\n"
  }

  function StdoutError(reason: string): BW.Bytes
  { StdoutErrorPart1() + Utf8.Encode(reason) + StdoutErrorPart2() }

  function EnvironmentValue(env: map<string,string>, key: string): string { if key in env then env[key] else "" }

  function ConfigureBackup(raw: S.CpCmdRaw, version: string, suffix: string): S.CpCmdRaw {
    if raw.mode != S.Run || raw.error != S.NoError || !raw.policy.creation.backup.enabled then raw
    else
      var explicit := raw.policy.creation.backup.control.Some? && raw.policy.creation.backup.control.value != "";
      var value := if explicit then raw.policy.creation.backup.control.value else version;
      var matched := if value == "" then S.Matched("existing") else S.BackupControl(value);
      var suffixValue := if raw.policy.creation.backup.suffix.Some? then raw.policy.creation.backup.suffix.value else suffix;
      var selectedSuffix := if suffixValue != "" && (forall i | 0 <= i < |suffixValue| :: suffixValue[i] != '/') then suffixValue else "~";
      if matched.Unmatched? then raw.(error := S.InvalidBackup(value,matched.ambiguous,!explicit))
      else raw.(policy := raw.policy.(creation := raw.policy.creation.(backup :=
           S.BackupSettings(matched.value != "off",CliTypes.Some(matched.value),CliTypes.Some(selectedSuffix)))))
  }

  function EnvironmentCommand(raw: S.CpCmdRaw, env: map<string,string>): S.CpCmdRaw {
    ConfigureBackup(raw.(policy := raw.policy.(creation := raw.policy.creation.(writeDangling := "POSIXLY_CORRECT" in env))),
                    EnvironmentValue(env,"VERSION_CONTROL"),EnvironmentValue(env,"SIMPLE_BACKUP_SUFFIX"))
  }

  function BackupMode(raw: S.CpCmdRaw): string {
    if raw.policy.creation.backup.enabled && raw.policy.creation.backup.control.Some? then raw.policy.creation.backup.control.value else "off"
  }
  function BackupSuffix(raw: S.CpCmdRaw): string {
    if raw.policy.creation.backup.suffix.Some? then raw.policy.creation.backup.suffix.value else "~"
  }

  type LinkMap = map<(int,int),string>

  function JoinTrimmed(directory: string, base: string): string {
    if |directory| == 0 then base
    else directory +
         (if directory == "/" && |base| > 0 && base[0] == '/' then "."
          else if directory[|directory|-1] == '/' || (|base| > 0 && base[0] == '/') then "" else "/") + base
  }

  ghost predicate TrimmedPath(path: string, trimmed: string) {
    if |path| == 0 then trimmed == ""
    else if Paths.SlashesOnly(path) then trimmed == "/"
    else exists trailing: string :: Paths.PathWithoutTrailingSlashes(path,trimmed,trailing)
  }

  ghost predicate NameConcat(directory: string, base: string, value: string) {
    exists trimmed: string :: TrimmedPath(directory,trimmed) && value == JoinTrimmed(trimmed,base)
  }

  ghost predicate TargetFields(directory: string, source: string, value: string) {
    exists base: string :: Paths.BasenameRelation(source,base) && NameConcat(directory,if base == ".." then "." else base,value)
  }

  ghost predicate ParentsTargetFields(directory: string, source: string, value: string) {
    exists trimmed: string :: TrimmedPath(source,trimmed) && NameConcat(directory,trimmed,value)
  }

  datatype Metadata = Metadata(ok: bool, err: int, value: BW.FileTimeStatus)
  datatype FilesystemProvider = FilesystemProvider(
    filesystem: C.ValidFilesystemObservations, failures: C.ValidNativeFailureObservations)
  type StreamProvider = (BW.TrustedStreamRequest) -> BW.TrustedStreamResult

  ghost predicate MetadataFields(fs: BW.FileSystem, provider: FilesystemProvider,
                                 path: string, follow: bool, result: Metadata) {
    C.GetFileTimesSpec(fs, provider.filesystem, path, follow, result.ok,
                       result.value.atimeSec, result.value.atimeNsec, result.value.mtimeSec, result.value.mtimeNsec,
                       result.value.isDir, result.value.isSymlink, result.value.device, result.value.inode,
                       result.value.linkCount, result.err)
  }
  function Identity(meta: Metadata): (int, int) { (meta.value.device, meta.value.inode) }
  function Skip(raw: S.CpCmdRaw, source: Metadata, target: Metadata): bool {
    target.ok && (raw.policy.skip || raw.policy.update == "none" || raw.policy.update == "none-fail" ||
                  (raw.policy.update == "older" && (source.value.mtimeSec < target.value.mtimeSec ||
                                                    (source.value.mtimeSec == target.value.mtimeSec && source.value.mtimeNsec <= target.value.mtimeNsec))))
  }
  ghost function Q(path: string): BW.Bytes { C.QuoteafPathResult(path) }
  ghost function E(err: int): string { C.CLocaleErrnoTextResult(err) }

  function CreationMode(raw: S.CpCmdRaw, sourceMode: bv32): (result: bv32)
    ensures (result & (511 as bv32)) == result
  {
    if raw.policy.creation.defaultMode then 438 as bv32 else sourceMode & (511 as bv32)
  }
  function DirectoryCreationMode(raw: S.CpCmdRaw, sourceMode: bv32): bv32 {
    sourceMode & ((4095 as bv32) ^ (18 as bv32))
  }
  function DirectoryFinalMode(raw: S.CpCmdRaw, sourceMode: bv32, mask: bv32, createdMode: bv32): bv32 {
    if raw.policy.preserveMode then sourceMode
    else (if raw.policy.creation.defaultMode then (511 as bv32) | (createdMode & (1024 as bv32))
          else (sourceMode & (511 as bv32)) | (createdMode & (3584 as bv32))) & ((4095 as bv32) ^ mask)
  }

  opaque ghost predicate AttributeOutcome(raw: S.CpCmdRaw, source: Metadata, sourceMode: bv32,
                                          target: string, follow: bool, before: BW.FileSystem, after: BW.FileSystem, now: int,
                                          provider: FilesystemProvider, err: BW.Bytes, ok: bool,
                                          observed: (BW.FileSystem,(bool,int),(bool,int))) {
    var middle := observed.0;
    var timeOK, timeErr := observed.1.0,observed.1.1;
    var modeOK, modeErr := observed.2.0,observed.2.1;
    (if raw.policy.preserveTimes then
       C.SetFileTimesSpec(before, now, provider.filesystem, middle, target, follow,
                          source.value.atimeSec, source.value.atimeNsec, source.value.mtimeSec, source.value.mtimeNsec, timeOK, timeErr)
     else middle == before && timeOK && timeErr == 0) &&
    (if raw.policy.preserveMode && follow then
       C.SetFileModeSpec(middle, now,provider.failures, after, target, follow, sourceMode, modeOK, modeErr)
     else after == middle && modeOK && modeErr == 0) &&
    err == (if timeOK then [] else TimeError(Q(target), E(timeErr))) +
    (if modeOK then [] else ModeError(Q(target), E(modeErr))) &&
    ok == (timeOK && modeOK)
  }

  opaque ghost predicate Attributes(raw: S.CpCmdRaw, source: Metadata, sourceMode: bv32,
                                    target: string, follow: bool, before: BW.FileSystem, after: BW.FileSystem, now: int,
                                    provider: FilesystemProvider, err: BW.Bytes, ok: bool) {
    exists observed: (BW.FileSystem,(bool,int),(bool,int)) ::
      AttributeOutcome(raw,source,sourceMode,target,follow,before,after,now,provider,err,ok,observed)
  }

  opaque ghost predicate PayloadOutcome(raw: S.CpCmdRaw, before: BW.FileSystem, after: BW.FileSystem,
                                        props: map<string,string>, now: int, credentials: BW.ProcessCredentials,
                                        provider: FilesystemProvider, target: string, data: BW.Bytes, mode: bv32,
                                        ok: bool, err: int, committed: nat, stage: BW.FileWriteStage, removal: (bool,bool),
                                        observed: (BW.FileSystem,bool,int,nat,BW.FileWriteStage,Metadata)) {
    var first, firstOK, firstErr, firstCommitted, firstStage, targetMeta := observed.0,observed.1,observed.2,observed.3,observed.4,observed.5;
    var removeFailed,didRemove := removal.0,removal.1;
    MetadataFields(before,provider,target,true,targetMeta) &&
    (if raw.policy.attributesOnly && targetMeta.ok then
       C.AppendFileSpec(before,props,now,credentials,provider.filesystem,first,target,[],firstOK,firstErr,firstCommitted,firstStage)
     else C.WriteFileSpec(before,props,now,credentials,provider.filesystem,first,target,data,firstOK,firstErr,firstCommitted,firstStage,CreationMode(raw,mode))) &&
    (if raw.policy.force && targetMeta.ok && firstStage == BW.WriteOpenFailed then
       exists removed: BW.FileSystem, removeOK: bool, removeErr: int ::
         C.UnlinkPathSpec(first,now,provider.filesystem,removed,target,removeOK,removeErr) &&
         (if !removeOK then after == removed && !ok && err == removeErr && committed == 0 && stage == BW.WriteOpenFailed && removeFailed && !didRemove
          else C.WriteFileSpec(removed,props,now,credentials,provider.filesystem,after,target,data,ok,err,committed,stage,CreationMode(raw,mode)) && !removeFailed && didRemove)
     else after == first && ok == firstOK && err == firstErr && committed == firstCommitted && stage == firstStage && !removeFailed && !didRemove)
  }

  opaque ghost predicate PayloadWrite(raw: S.CpCmdRaw, before: BW.FileSystem, after: BW.FileSystem,
                                      props: map<string,string>, now: int, credentials: BW.ProcessCredentials,
                                      provider: FilesystemProvider, target: string, data: BW.Bytes, mode: bv32,
                                      ok: bool, err: int, committed: nat, stage: BW.FileWriteStage, removeFailed: bool, didRemove: bool) {
    exists observed: (BW.FileSystem,bool,int,nat,BW.FileWriteStage,Metadata) ::
      PayloadOutcome(raw,before,after,props,now,credentials,provider,target,data,mode,ok,err,committed,stage,(removeFailed,didRemove),observed)
  }

  opaque ghost predicate DataOutcome(raw: S.CpCmdRaw, source: string, target: string,
                                     metadata: Metadata, mode: bv32, before: BW.FileSystem, after: BW.FileSystem,
                                     props: map<string,string>, now: int, credentials: BW.ProcessCredentials,
                                     provider: FilesystemProvider, streams: StreamProvider,
                                     out: BW.Bytes, err: BW.Bytes, ok: bool, observed: (BW.Bytes,int,BW.FileReadStage,Metadata,Metadata,(BW.FileSystem,bool,int,nat,BW.FileWriteStage,bool,BW.Bytes,bool,Metadata,bool))) {
    var data,readErr,readStage,targetMeta,entryMeta,write := observed.0,observed.1,observed.2,observed.3,observed.4,observed.5;
    var written,writeOK,writeErr,committed,stage,removeFailed,attributesErr,attributesOK,targetMetadata := write.0,write.1,write.2,write.3,write.4,write.5,write.6,write.7,write.8;
    var didRemove := write.9;
    (if raw.policy.attributesOnly then C.OpenReadFileSpec(before,streams,source,data,readErr,readStage)
     else C.ReadFileSpec(before, streams, source, data, readErr, readStage)) &&
    (if readStage == BW.OpenFailed then
       after == before && out == [] && err == CannotOpen(Q(source), E(readErr)) && !ok
     else
       MetadataFields(before,provider,target,true,targetMeta) && MetadataFields(before,provider,target,false,entryMeta) &&
       (if !targetMeta.ok && entryMeta.ok && entryMeta.value.isSymlink && !raw.policy.creation.writeDangling then
          after == before && out == [] && err == Dangling(Q(target)) && !ok
        else
          (if raw.policy.attributesOnly then
             MetadataFields(before, provider, target, true, targetMetadata) &&
             PayloadWrite(raw,before,written,props,now,credentials,provider,target,[],mode,writeOK,writeErr,committed,stage,removeFailed,didRemove)
           else PayloadWrite(raw,before,written,props,now,credentials,provider,target,data,mode,writeOK,writeErr,committed,stage,removeFailed,didRemove)) &&
          (if (writeOK || stage == BW.WriteCloseFailed) && (readErr == 0 || readStage == BW.CloseFailed) then
             Attributes(raw, metadata, mode, target, true, written, after, now, provider, attributesErr, attributesOK)
           else after == written && attributesErr == [] && attributesOK) &&
          out == (if raw.policy.verbose && didRemove then Removed(Q(target)) else []) &&
          err == attributesErr + (if writeOK then [] else
                                  if removeFailed then CannotRemove(Q(target),E(writeErr))
                                  else if stage == BW.WriteOpenFailed then CannotCreate(Q(target), E(writeErr))
                                  else if stage == BW.WriteCloseFailed then CloseError(Q(target), E(writeErr))
                                  else WriteError(Q(target), E(writeErr))) +
          (if readErr == 0 || stage == BW.WriteOpenFailed || stage == BW.WriteFailed then []
           else if readStage == BW.CloseFailed then CloseError(Q(source), E(readErr))
           else ReadError(Q(source), E(readErr))) &&
          ok == (writeOK && readErr == 0 && attributesOK)))
  }

  opaque ghost predicate DataCopy(raw: S.CpCmdRaw, source: string, target: string,
                                  metadata: Metadata, mode: bv32, before: BW.FileSystem, after: BW.FileSystem,
                                  props: map<string,string>, now: int, credentials: BW.ProcessCredentials,
                                  provider: FilesystemProvider, streams: StreamProvider,
                                  out: BW.Bytes, err: BW.Bytes, ok: bool) {
    exists observed: (BW.Bytes,int,BW.FileReadStage,Metadata,Metadata,(BW.FileSystem,bool,int,nat,BW.FileWriteStage,bool,BW.Bytes,bool,Metadata,bool)) ::
      DataOutcome(raw,source,target,metadata,mode,before,after,props,now,credentials,provider,streams,out,err,ok,observed)
  }

  datatype DestinationRecord = NoDestinationRecord | RecordedDestination(metadata: Metadata)
  datatype CopyReceipt = CopyReceipt(record: DestinationRecord, retained: bool, selfCopy: bool)

  opaque ghost predicate DestinationRecordFields(fs: BW.FileSystem, provider: FilesystemProvider, target: string, record: DestinationRecord) {
    exists metadata: Metadata :: MetadataFields(fs,provider,target,false,metadata) &&
                                 record == (if metadata.ok then RecordedDestination(metadata) else NoDestinationRecord)
  }

  function PreUnlink(raw: S.CpCmdRaw, source: Metadata, target: Metadata): bool {
    target.ok && !target.value.isDir && (raw.policy.remove ||
                                         (!raw.policy.attributesOnly && ((raw.policy.creation.preserveLinks && target.value.linkCount > 1) ||
                                                                         (!raw.policy.dereference && (source.value.isSymlink || source.value.isDir)))))
  }

  opaque ghost predicate RelativeLinkAllowed(fs: BW.FileSystem, provider: FilesystemProvider,
                                             source: string, target: string, allowed: bool) {
    if |source| > 0 && source[0] == '/' then allowed
    else exists parent: string :: Paths.DirnameRelation(target,parent) &&
                                  (if parent == "." then allowed
                                   else exists dot: Metadata, destination: Metadata ::
                                          MetadataFields(fs,provider,".",true,dot) && MetadataFields(fs,provider,parent,true,destination) &&
                                          allowed == (!dot.ok || !destination.ok || Identity(dot) == Identity(destination)))
  }

  datatype SameFileObservation = SameFileObservation(sourceEntry: Metadata, targetEntry: Metadata,
                                                     sourceFollow: Metadata, targetFollow: Metadata, sameEntry: bool)

  ghost predicate SameFileDecisionFields(raw: S.CpCmdRaw, source: Metadata, target: Metadata,
                                         observed: SameFileObservation, allowed: bool, returnNow: bool) {
    var sl,tl,sf,tf,sameEntry := observed.sourceEntry,observed.targetEntry,observed.sourceFollow,observed.targetFollow,observed.sameEntry;
    var same := Identity(source) == Identity(target);
    var sameLink := Identity(sl) == Identity(tl);
    var bothLinks := sl.value.isSymlink && tl.value.isSymlink;
    var backup := BackupMode(raw) != "off";
    if same && raw.policy.hard then allowed && returnNow
    else if raw.policy.dereference && (!same || !tl.ok || !sl.ok) then allowed && !returnNow
    else if !raw.policy.dereference && bothLinks then
      allowed == !sameEntry && returnNow == (!sameEntry && !backup && sameLink)
    else if raw.policy.dereference && bothLinks && raw.policy.remove then allowed && !returnNow
    else if backup then
      allowed == (if sameLink then !sameEntry else !(raw.policy.dereference && sl.value.isSymlink && !tl.value.isSymlink)) && !returnNow
    else if raw.policy.remove && (tl.value.isSymlink || (sameLink && tl.value.linkCount > 1 && !sameEntry)) then allowed && !returnNow
    else if !sl.value.isSymlink && !tl.value.isSymlink then
      allowed == (!sameLink || raw.policy.hard) && returnNow == (sameLink && raw.policy.hard)
    else if raw.policy.symbolic && tl.value.isSymlink then allowed && !returnNow
    else if !raw.policy.dereference then
      var different := !sf.ok || !tf.ok || Identity(sf) != Identity(tf);
      allowed == (different || raw.policy.hard) && returnNow == (!different && raw.policy.hard && !tl.value.isSymlink)
    else !allowed && !returnNow
  }

  opaque ghost predicate SameFileObservationFields(raw: S.CpCmdRaw, fs: BW.FileSystem, provider: FilesystemProvider,
                                                   source: string, target: string, sm: Metadata, tm: Metadata,
                                                   observed: SameFileObservation) {
    var sl,tl,sf,tf,sameEntry := observed.sourceEntry,observed.targetEntry,observed.sourceFollow,observed.targetFollow,observed.sameEntry;
    var same := Identity(sm) == Identity(tm);
    var sameLink := Identity(sl) == Identity(tl);
    var bothLinks := sl.value.isSymlink && tl.value.isSymlink;
    var backup := BackupMode(raw) != "off";
    var active := !(same && raw.policy.hard) && !(raw.policy.dereference && (!same || !tl.ok || !sl.ok));
    var askEntry := active && ((!raw.policy.dereference && bothLinks) ||
                               (!(raw.policy.dereference && bothLinks && raw.policy.remove) &&
                                ((backup && sameLink) || (!backup && raw.policy.remove && !tl.value.isSymlink && sameLink && tl.value.linkCount > 1))));
    var askFollow := active && !raw.policy.dereference && !bothLinks && !backup &&
                     !(raw.policy.remove && (tl.value.isSymlink || (sameLink && tl.value.linkCount > 1 && !sameEntry))) &&
                     !(!sl.value.isSymlink && !tl.value.isSymlink) && !(raw.policy.symbolic && tl.value.isSymlink);
    (if raw.policy.dereference && same && !raw.policy.hard then
       MetadataFields(fs,provider,target,false,tl) && (if tl.ok then MetadataFields(fs,provider,source,false,sl) else sl == sm)
     else sl == sm && tl == tm) &&
    (if askEntry then SameEntryFields(fs,provider,source,target,sameEntry) else !sameEntry) &&
    (if askFollow && sl.value.isSymlink then MetadataFields(fs,provider,source,true,sf) else sf == sl) &&
    (if askFollow && sf.ok && tl.value.isSymlink then MetadataFields(fs,provider,target,true,tf) else tf == tl)
  }

  opaque ghost predicate SameFileEligibility(raw: S.CpCmdRaw, source: string, target: string, sm: Metadata, tm: Metadata,
                                             fs: BW.FileSystem, provider: FilesystemProvider, allowed: bool, returnNow: bool) {
    exists observed: SameFileObservation ::
      SameFileObservationFields(raw,fs,provider,source,target,sm,tm,observed) &&
      SameFileDecisionFields(raw,sm,tm,observed,allowed,returnNow)
  }

  opaque ghost predicate LeafOutcome(raw: S.CpCmdRaw, source: string, target: string,
                                     sourceMetadata: Metadata, targetMetadata: Metadata, sourceAttributes: (bv32,string),
                                     before: BW.FileSystem, after: BW.FileSystem, props: map<string,string>, now: int,
                                     credentials: BW.ProcessCredentials, provider: FilesystemProvider, streams: StreamProvider,
                                     reported: (BW.Bytes,BW.Bytes,bool,CopyReceipt), observed: (BW.FileSystem,bool,int,bool,int,bool,BW.FileSystem,BW.Bytes,bool,BW.Bytes)) {
    var out,err,ok,receipt := reported.0,reported.1,reported.2,reported.3;
    var ready,removeOK,removeErr,linkOK,linkErr,relativeOK,linked,attributeErr,attributeOK :=
      observed.0,observed.1,observed.2,observed.3,observed.4,observed.5,observed.6,observed.7,observed.8;
    var dataOut := observed.9;
    var linkTarget := sourceAttributes.1;
    !receipt.selfCopy &&
    (if PreUnlink(raw,sourceMetadata,targetMetadata) then
       C.UnlinkPathSpec(before, now, provider.filesystem, ready, target, removeOK, removeErr)
     else ready == before && removeOK && removeErr == 0) &&
    (if !removeOK && removeErr != 2 then receipt == CopyReceipt(NoDestinationRecord,false,false) && after == ready && out == [] && err == CannotRemove(Q(target), E(removeErr)) && !ok
     else
       out == (if raw.policy.verbose && PreUnlink(raw,sourceMetadata,targetMetadata) then Removed(Q(target)) else []) +
       (if raw.policy.verbose then Verbose(Q(source), Q(target)) else []) + dataOut &&
       (if raw.policy.symbolic || sourceMetadata.value.isSymlink || raw.policy.hard then
          dataOut == [] &&
          (if raw.policy.symbolic then RelativeLinkAllowed(ready,provider,source,target,relativeOK) else relativeOK) &&
          (if !relativeOK then receipt == CopyReceipt(NoDestinationRecord,false,false) && after == ready && !ok && err == RelativeSymlinkError(target)
           else
             (if raw.policy.hard then C.CreateHardLinkSpec(ready, now, provider.filesystem, linked, linkTarget, target, linkOK, linkErr, raw.policy.dereference)
              else C.CreateSymlinkSpec(ready, now, credentials,provider.failures, linked, target, linkTarget, linkOK, linkErr)) &&
             (if linkOK && !raw.policy.hard then Attributes(raw,sourceMetadata,sourceAttributes.0,target,false,linked,after,now,provider,attributeErr,attributeOK)
              else after == linked && attributeErr == [] && attributeOK) &&
             receipt.retained == linkOK &&
             (if linkOK then DestinationRecordFields(linked,provider,target,receipt.record) else receipt.record == NoDestinationRecord) &&
             ok == (linkOK && attributeOK) &&
             err == (if linkOK then attributeErr
                     else if raw.policy.hard || raw.policy.symbolic then LinkError(Q(if raw.policy.hard then linkTarget else source),Q(target),E(linkErr),!raw.policy.hard)
                     else CopiedSymlinkError(Q(target),E(linkErr))))
        else receipt.retained == ok && (if ok then DestinationRecordFields(after,provider,target,receipt.record) else receipt.record == NoDestinationRecord) && DataCopy(raw, source, target, sourceMetadata, sourceAttributes.0, ready, after, props, now, credentials, provider, streams, dataOut, err, ok)))
  }

  opaque ghost predicate LeafCopy(raw: S.CpCmdRaw, source: string, target: string,
                                  sourceMetadata: Metadata, targetMetadata: Metadata, sourceAttributes: (bv32,string),
                                  before: BW.FileSystem, after: BW.FileSystem, props: map<string,string>, now: int,
                                  credentials: BW.ProcessCredentials, provider: FilesystemProvider, streams: StreamProvider,
                                  out: BW.Bytes, err: BW.Bytes, ok: bool) {
    exists receipt: CopyReceipt :: LeafResult(raw,source,target,sourceMetadata,targetMetadata,sourceAttributes,before,after,props,now,credentials,provider,streams,(out,err,ok,receipt))
  }

  opaque ghost predicate LeafResult(raw: S.CpCmdRaw, source: string, target: string,
                                    sm: Metadata, tm: Metadata, attributes: (bv32,string), before: BW.FileSystem, after: BW.FileSystem,
                                    props: map<string,string>, now: int, credentials: BW.ProcessCredentials, provider: FilesystemProvider,
                                    streams: StreamProvider, reported: (BW.Bytes,BW.Bytes,bool,CopyReceipt)) {
    exists observed: (BW.FileSystem,bool,int,bool,int,bool,BW.FileSystem,BW.Bytes,bool,BW.Bytes) ::
      LeafOutcome(raw,source,target,sm,tm,attributes,before,after,props,now,credentials,provider,streams,reported,observed)
  }

  predicate NumberedVersion(base: string, name: string, version: nat) {
    version > 0 && name == base + ".~" + Paths.DecimalNatSpec(version) + "~"
  }

  ghost predicate BackupVersion(base: string, name: string, version: nat) {
    if version == 0 then !(exists positive: nat :: NumberedVersion(base,name,positive))
    else NumberedVersion(base,name,version)
  }

  ghost predicate MaximumBackup(entries: seq<DirectoryName>, base: string, maximum: nat) {
    (forall i: int, version: nat | 0 <= i < |entries| && NumberedVersion(base,entries[i].name,version) :: version <= maximum) &&
    (maximum == 0 || exists i: int :: 0 <= i < |entries| && NumberedVersion(base,entries[i].name,maximum))
  }

  opaque ghost predicate BackupSelectionFields(fs: BW.FileSystem, provider: FilesystemProvider, target: string, mode: string, suffix: string,
                                               path: string, err: int, observed: (string,string,seq<DirectoryName>,int,bool,nat)) {
    var parent,base,entries,scanErr,wasOpened,maximum := observed.0,observed.1,observed.2,observed.3,observed.4,observed.5;
    if mode == "simple" then path == Paths.SimpleBackupPathSpec(target,suffix) && err == 0
    else Paths.DirnameRelation(target,parent) && Paths.BasenameRelation(target,base) &&
         EnumerationWithOpen(fs,provider,parent,entries,scanErr,wasOpened) &&
         (if !wasOpened && scanErr == 12 then path == "" && err == 12
          else MaximumBackup(entries,base,maximum) && err == 0 &&
               path == (if mode == "existing" && maximum == 0 then Paths.SimpleBackupPathSpec(target,suffix)
                        else Paths.NumberedBackupPathSpec(target,maximum+1)))
  }

  opaque ghost predicate BackupSelection(fs: BW.FileSystem, provider: FilesystemProvider, target: string, mode: string, suffix: string, path: string, err: int) {
    exists observed: (string,string,seq<DirectoryName>,int,bool,nat) :: BackupSelectionFields(fs,provider,target,mode,suffix,path,err,observed)
  }

  function CannotBackupPart1(): BW.Bytes
  {
    "cp: cannot backup "
  }

  function CannotBackupPart2(): BW.Bytes
  {
    ": "
  }

  function CannotBackupPart3(): BW.Bytes
  {
    "\n"
  }

  function CannotBackup(target: BW.Bytes, reason: string): BW.Bytes
  { CannotBackupPart1() + target + CannotBackupPart2() + Utf8.Encode(reason) + CannotBackupPart3() }
  function CannotUnbackupPart1(): BW.Bytes
  {
    "cp: cannot un-backup "
  }

  function CannotUnbackupPart2(): BW.Bytes
  {
    ": "
  }

  function CannotUnbackupPart3(): BW.Bytes
  {
    "\n"
  }

  function CannotUnbackup(target: BW.Bytes, reason: string): BW.Bytes
  { CannotUnbackupPart1() + target + CannotUnbackupPart2() + Utf8.Encode(reason) + CannotUnbackupPart3() }
  function BackupDestroysSource(source: BW.Bytes, target: BW.Bytes): BW.Bytes {
    "cp: backing up " + target + " might destroy source;  " + source + " not copied\n"
  }
  function VerboseBackup(source: BW.Bytes, target: BW.Bytes, backup: BW.Bytes): BW.Bytes {
    source + " -> " + target + " (backup: " + backup + ")\n"
  }
  function VerboseUnbackup(backup: BW.Bytes, target: BW.Bytes): BW.Bytes { backup + " -> " + target + " (unbackup)\n" }

  datatype BackupPreparationResult = BackupReady(path: string, renamed: bool) | BackupRejected(error: BW.Bytes)
  datatype BackupPreparationObservation = BackupPreparationObservation(sourceBase: string, targetBase: string, candidate: Metadata,
                                                                       selected: string, selectionErr: int, renamedFs: BW.FileSystem, renameOK: bool, renameErr: int)

  opaque ghost predicate BackupPreparationFields(raw: S.CpCmdRaw, source: string, target: string, sm: Metadata,
                                                 before: BW.FileSystem, after: BW.FileSystem, now: int, provider: FilesystemProvider,
                                                 result: BackupPreparationResult, observed: BackupPreparationObservation) {
    Paths.BasenameRelation(source,observed.sourceBase) && Paths.BasenameRelation(target,observed.targetBase) &&
    (if BackupMode(raw) != "numbered" && observed.sourceBase == observed.targetBase+BackupSuffix(raw) then
       MetadataFields(before,provider,target+BackupSuffix(raw),true,observed.candidate)
     else !observed.candidate.ok) &&
    (if observed.candidate.ok && Identity(observed.candidate) == Identity(sm) then after == before &&
                                                                                   result == BackupRejected(BackupDestroysSource(Q(source),Q(target)))
     else BackupSelection(before,provider,target,BackupMode(raw),BackupSuffix(raw),observed.selected,observed.selectionErr) &&
          (if observed.selectionErr != 0 then after == before && result == BackupRejected(CannotBackup(Q(target),E(observed.selectionErr)))
           else C.RenamePathSpec(before,now,provider.failures,after,target,observed.selected,observed.renameOK,observed.renameErr) &&
                result == (if !observed.renameOK && observed.renameErr != 2 then BackupRejected(CannotBackup(Q(target),E(observed.renameErr)))
                           else BackupReady(observed.selected,observed.renameOK))))
  }

  opaque ghost predicate BackupPreparation(raw: S.CpCmdRaw, source: string, target: string, sm: Metadata,
                                           before: BW.FileSystem, after: BW.FileSystem, now: int, provider: FilesystemProvider,
                                           result: BackupPreparationResult) {
    exists observed: BackupPreparationObservation :: BackupPreparationFields(raw,source,target,sm,before,after,now,provider,result,observed)
  }

  opaque ghost predicate BackupRestorationFields(raw: S.CpCmdRaw, backup: string, target: string, needed: bool,
                                                 before: BW.FileSystem, after: BW.FileSystem, now: int, provider: FilesystemProvider, out: BW.Bytes, err: BW.Bytes,
                                                 observed: (bool,int)) {
    if !needed then after == before && out == [] && err == []
    else C.RenamePathSpec(before,now,provider.failures,after,backup,target,observed.0,observed.1) &&
         out == (if observed.0 && raw.policy.verbose then VerboseUnbackup(Q(backup),Q(target)) else []) &&
         err == (if observed.0 then [] else CannotUnbackup(Q(target),E(observed.1)))
  }

  opaque ghost predicate BackupRestoration(raw: S.CpCmdRaw, backup: string, target: string, needed: bool,
                                           before: BW.FileSystem, after: BW.FileSystem, now: int, provider: FilesystemProvider, out: BW.Bytes, err: BW.Bytes) {
    exists observed: (bool,int) :: BackupRestorationFields(raw,backup,target,needed,before,after,now,provider,out,err,observed)
  }

  datatype BackupObservation = BackupObservation(prepared: BW.FileSystem, preparation: BackupPreparationResult, readyMetadata: Metadata,
                                                 copied: BW.FileSystem, leafOut: BW.Bytes, leafErr: BW.Bytes, leafOK: bool, receipt: CopyReceipt, restoreOut: BW.Bytes, restoreErr: BW.Bytes)

  opaque ghost predicate BackupLeafFields(raw: S.CpCmdRaw, source: string, target: string,
                                          sm: Metadata, tm: Metadata, attributes: (bv32,string), before: BW.FileSystem, after: BW.FileSystem,
                                          props: map<string,string>, now: int, credentials: BW.ProcessCredentials, provider: FilesystemProvider,
                                          streams: StreamProvider, reported: (BW.Bytes,BW.Bytes,bool,CopyReceipt), observed: BackupObservation) {
    var out,err,ok,receipt := reported.0,reported.1,reported.2,reported.3;
    if BackupMode(raw) == "off" || !tm.ok || tm.value.isDir then
      LeafResult(raw,source,target,sm,tm,attributes,before,after,props,now,credentials,provider,streams,reported)
    else BackupPreparation(raw,source,target,sm,before,observed.prepared,now,provider,observed.preparation) &&
         (if observed.preparation.BackupRejected? then after == observed.prepared && out == [] &&
                                                       err == observed.preparation.error && !ok && receipt == CopyReceipt(NoDestinationRecord,false,false)
          else MetadataFields(observed.prepared,provider,target,!raw.policy.remove && !raw.policy.symbolic && !raw.policy.hard && !sm.value.isSymlink,observed.readyMetadata) &&
               LeafResult(raw.(policy := raw.policy.(verbose := false)),source,target,sm,observed.readyMetadata,attributes,
                          observed.prepared,observed.copied,props,now,credentials,provider,streams,
                          (observed.leafOut,observed.leafErr,observed.leafOK,observed.receipt)) && receipt == observed.receipt &&
               BackupRestoration(raw,observed.preparation.path,target,!observed.leafOK && !receipt.retained && observed.preparation.renamed,
                                 observed.copied,after,now,provider,observed.restoreOut,observed.restoreErr) &&
               out == (if raw.policy.verbose then (if observed.preparation.renamed then VerboseBackup(Q(source),Q(target),Q(observed.preparation.path)) else Verbose(Q(source),Q(target))) else []) +
               observed.leafOut+observed.restoreOut && err == observed.leafErr+observed.restoreErr && ok == observed.leafOK)
  }

  opaque ghost predicate BackupLeaf(raw: S.CpCmdRaw, source: string, target: string,
                                    sm: Metadata, tm: Metadata, attributes: (bv32,string), before: BW.FileSystem, after: BW.FileSystem,
                                    props: map<string,string>, now: int, credentials: BW.ProcessCredentials, provider: FilesystemProvider,
                                    streams: StreamProvider, reported: (BW.Bytes,BW.Bytes,bool,CopyReceipt)) {
    exists observed: BackupObservation :: BackupLeafFields(raw,source,target,sm,tm,attributes,before,after,props,now,credentials,provider,streams,reported,observed)
  }

  datatype ParentInfo = ParentInfo(source: string, target: string, metadata: Metadata, mode: bv32, restore: bool)
  datatype ParentStepObservation = ParentStepObservation(
    destination: Metadata, source: Metadata, sourceMode: bv32, sourceModeOK: bool, sourceModeErr: int,
    created: BW.FileSystem, createOK: bool, createErr: int, createdMetadata: Metadata,
    createdMode: bv32, createdModeOK: bool, createdModeErr: int, changed: BW.FileSystem, changeOK: bool, changeErr: int)

  ghost predicate ParentOffsets(path: string, offsets: seq<nat>) {
    (forall i | 0 <= i < |offsets| ::
       0 < offsets[i] < |path| && path[offsets[i]] == '/' && path[offsets[i]-1] != '/') &&
    (forall i,j | 0 <= i < j < |offsets| :: offsets[i] < offsets[j]) &&
    (forall index | 0 < index < |path| && path[index] == '/' && path[index-1] != '/' :: index in offsets)
  }

  function ParentGroups(groups: seq<seq<ParentInfo>>): seq<ParentInfo>
    decreases |groups|
  {
    if |groups| == 0 then [] else ParentGroups(groups[..|groups|-1]) + groups[|groups|-1]
  }

  function ParentVerbosePart1(): BW.Bytes
  {
    " -> "
  }

  function ParentVerbosePart2(): BW.Bytes
  {
    "\n"
  }

  function ParentVerbose(source: string, target: string): BW.Bytes
  {
    Utf8.Encode(source) + ParentVerbosePart1() + Utf8.Encode(target) + ParentVerbosePart2()
  }
  function ParentAttributesErrorPart1(): BW.Bytes
  {
    "cp: failed to get attributes of "
  }

  function ParentAttributesErrorPart2(): BW.Bytes
  {
    ": "
  }

  function ParentAttributesErrorPart3(): BW.Bytes
  {
    "\n"
  }

  function ParentAttributesError(path: BW.Bytes, reason: string): BW.Bytes
  {
    ParentAttributesErrorPart1() + path + ParentAttributesErrorPart2() + Utf8.Encode(reason) + ParentAttributesErrorPart3()
  }
  function ParentCreateErrorPart1(): BW.Bytes
  {
    "cp: cannot make directory "
  }

  function ParentCreateErrorPart2(): BW.Bytes
  {
    ": "
  }

  function ParentCreateErrorPart3(): BW.Bytes
  {
    "\n"
  }

  function ParentCreateError(path: BW.Bytes, reason: string): BW.Bytes
  {
    ParentCreateErrorPart1() + path + ParentCreateErrorPart2() + Utf8.Encode(reason) + ParentCreateErrorPart3()
  }
  function ParentNotDirectory(path: BW.Bytes): BW.Bytes { "cp: " + path + " exists but is not a directory\n" }
  function ParentSetModeErrorPart1(): BW.Bytes
  {
    "cp: setting permissions for "
  }

  function ParentSetModeErrorPart2(): BW.Bytes
  {
    ": "
  }

  function ParentSetModeErrorPart3(): BW.Bytes
  {
    "\n"
  }

  function ParentSetModeError(path: BW.Bytes, reason: string): BW.Bytes
  {
    ParentSetModeErrorPart1() + path + ParentSetModeErrorPart2() + Utf8.Encode(reason) + ParentSetModeErrorPart3()
  }
  function ParentTimeErrorPart1(): BW.Bytes
  {
    "cp: failed to preserve times for "
  }

  function ParentTimeErrorPart2(): BW.Bytes
  {
    ": "
  }

  function ParentTimeErrorPart3(): BW.Bytes
  {
    "\n"
  }

  function ParentTimeError(path: BW.Bytes, reason: string): BW.Bytes
  {
    ParentTimeErrorPart1() + path + ParentTimeErrorPart2() + Utf8.Encode(reason) + ParentTimeErrorPart3()
  }
  function ParentModeErrorPart1(): BW.Bytes
  {
    "cp: failed to preserve permissions for "
  }

  function ParentModeErrorPart2(): BW.Bytes
  {
    ": "
  }

  function ParentModeErrorPart3(): BW.Bytes
  {
    "\n"
  }

  function ParentModeError(path: BW.Bytes, reason: string): BW.Bytes
  {
    ParentModeErrorPart1() + path + ParentModeErrorPart2() + Utf8.Encode(reason) + ParentModeErrorPart3()
  }
  function ParentsRequireDirectory(): BW.Bytes { "cp: with --parents, the destination must be a directory\n" + Hint() }
  function ParentCreationMode(raw: S.CpCmdRaw, sourceMode: bv32): bv32 {
    (if raw.policy.creation.defaultMode then 511 as bv32 else sourceMode & (4095 as bv32)) &
    (if raw.policy.preserveMode then ((4095 as bv32) ^ (18 as bv32)) else 4095 as bv32)
  }

  opaque ghost predicate {:isolate_assertions} ParentStepFields(raw: S.CpCmdRaw, source: string, target: string,
                                                                before: BW.FileSystem, after: BW.FileSystem, now: int, mask: bv32,
                                                                provider: FilesystemProvider, out: BW.Bytes, err: BW.Bytes, ok: bool, records: seq<ParentInfo>,
                                                                observed: ParentStepObservation) {
    var dm,sm := observed.destination,observed.source;
    var need := !dm.ok || raw.policy.preserveMode || raw.policy.preserveTimes;
    MetadataFields(before,provider,target,true,dm) &&
    (if !need then after == before && records == [] && out == [] &&
                   err == (if dm.value.isDir then [] else ParentNotDirectory(Q(target))) && ok == dm.value.isDir
     else MetadataFields(before,provider,source,true,sm) &&
          (if !sm.ok || !sm.value.isDir then after == before && records == [] && out == [] && !ok &&
                                             err == ParentAttributesError(Q(source),E(if sm.ok then 20 else sm.err))
           else C.GetFileModeSpec(before,provider.failures,source,true,observed.sourceModeOK,observed.sourceMode,observed.sourceModeErr) &&
                (if !observed.sourceModeOK then after == before && records == [] && out == [] && !ok &&
                                                err == ParentAttributesError(Q(source),E(observed.sourceModeErr))
                 else if dm.ok then after == before && out == [] &&
                                    records == [ParentInfo(source,target,sm,observed.sourceMode,false)] &&
                                    err == (if dm.value.isDir then [] else ParentNotDirectory(Q(target))) && ok == dm.value.isDir
                 else C.CreateDirectorySpec(before,now,provider.filesystem,mask,observed.created,target,ParentCreationMode(raw,observed.sourceMode),observed.createOK,observed.createErr) &&
                      (if !observed.createOK then after == observed.created && records == [ParentInfo(source,target,sm,observed.sourceMode,false)] && out == [] &&
                                                  err == ParentCreateError(Q(target),E(observed.createErr)) && !ok
                       else out == (if raw.policy.verbose then ParentVerbose(source,target) else []) &&
                            MetadataFields(observed.created,provider,target,false,observed.createdMetadata) &&
                            (if !observed.createdMetadata.ok then after == observed.created && records == [ParentInfo(source,target,sm,observed.sourceMode,false)] &&
                                                                  err == ParentAttributesError(Q(target),E(observed.createdMetadata.err)) && !ok
                             else C.GetFileModeSpec(observed.created,provider.failures,target,false,observed.createdModeOK,observed.createdMode,observed.createdModeErr) &&
                                  (if !observed.createdModeOK then after == observed.created && records == [ParentInfo(source,target,sm,observed.sourceMode,false)] &&
                                                                   err == ParentAttributesError(Q(target),E(observed.createdModeErr)) && !ok
                                   else var restore := !raw.policy.preserveMode && (observed.createdMode & (448 as bv32)) != (448 as bv32);
                                        records == [ParentInfo(source,target,sm,if raw.policy.preserveMode then observed.sourceMode else observed.createdMode,restore)] &&
                                        (if (observed.createdMode | (448 as bv32)) != observed.createdMode then
                                           C.SetFileModeSpec(observed.created,now,provider.failures,after,target,false,observed.createdMode | (448 as bv32),observed.changeOK,observed.changeErr)
                                         else after == observed.created && observed.changeOK && observed.changeErr == 0) &&
                                        ok == observed.changeOK && err == (if ok then [] else ParentSetModeError(Q(target),E(observed.changeErr)))))))))
  }

  opaque ghost predicate ParentStep(raw: S.CpCmdRaw, source: string, target: string,
                                    before: BW.FileSystem, after: BW.FileSystem, now: int, mask: bv32,
                                    provider: FilesystemProvider, out: BW.Bytes, err: BW.Bytes, ok: bool, records: seq<ParentInfo>) {
    exists observed: ParentStepObservation :: ParentStepFields(raw,source,target,before,after,now,mask,provider,out,err,ok,records,observed)
  }

  opaque ghost predicate ParentPreparationFields(raw: S.CpCmdRaw, source: string, directory: string, target: string,
                                                 before: BW.FileSystem, after: BW.FileSystem, now: int, mask: bv32,
                                                 provider: FilesystemProvider, reported: (BW.Bytes,BW.Bytes,bool,seq<ParentInfo>),
                                                 observed: (string,string,Metadata,seq<BW.FileSystem>,seq<BW.Bytes>,seq<BW.Bytes>,seq<bool>,seq<seq<ParentInfo>>,seq<string>,seq<nat>)) {
    var out,err,ok,records := reported.0,reported.1,reported.2,reported.3;
    var trimmed,parent,dm,states,outputs,errors,results,groups,targets := observed.0,observed.1,observed.2,observed.3,observed.4,observed.5,observed.6,observed.7,observed.8;
    var offsets := observed.9;
    if !raw.policy.creation.parents then after == before && out == [] && err == [] && ok && records == []
    else TrimmedPath(source,trimmed) && ParentOffsets(trimmed,offsets) &&
         (if |offsets| == 0 then after == before && out == [] && err == [] && ok && records == []
          else Paths.DirnameRelation(target,parent) && MetadataFields(before,provider,parent,true,dm) &&
               (if dm.ok then after == before && out == [] && records == [] &&
                              err == (if dm.value.isDir then [] else ParentNotDirectory(Q(parent))) && ok == dm.value.isDir
                else var count := |results|;
                     count <= |offsets| && |states| == count+1 && |outputs| == count && |errors| == count && |groups| == count && |targets| == count &&
                     states[0] == before && states[count] == after &&
                     (forall i | 0 <= i < count ::
                        ParentsTargetFields(directory,trimmed[..offsets[i]],targets[i]) &&
                        ParentStep(raw,trimmed[..offsets[i]],targets[i],states[i],states[i+1],now,mask,provider,outputs[i],errors[i],results[i],groups[i])) &&
                     (forall i | 0 <= i < count-1 :: results[i]) &&
                     (count == |offsets| || (count > 0 && !results[count-1])) &&
                     ok == (count == |offsets| && (forall i | 0 <= i < count :: results[i])) &&
                     records == ParentGroups(groups) && Concatenation(outputs,out) && Concatenation(errors,err)))
  }

  opaque ghost predicate ParentPreparation(raw: S.CpCmdRaw, source: string, directory: string, target: string,
                                           before: BW.FileSystem, after: BW.FileSystem, now: int, mask: bv32,
                                           provider: FilesystemProvider, out: BW.Bytes, err: BW.Bytes, ok: bool, records: seq<ParentInfo>) {
    exists observed: (string,string,Metadata,seq<BW.FileSystem>,seq<BW.Bytes>,seq<BW.Bytes>,seq<bool>,seq<seq<ParentInfo>>,seq<string>,seq<nat>) ::
      ParentPreparationFields(raw,source,directory,target,before,after,now,mask,provider,(out,err,ok,records),observed)
  }

  opaque ghost predicate ParentRestoreOneFields(raw: S.CpCmdRaw, parent: ParentInfo, before: BW.FileSystem, after: BW.FileSystem,
                                                now: int, provider: FilesystemProvider, err: BW.Bytes, ok: bool,
                                                observed: (BW.FileSystem,bool,int,bool,int)) {
    var middle,timeOK,timeErr,modeOK,modeErr := observed.0,observed.1,observed.2,observed.3,observed.4;
    (if raw.policy.preserveTimes then
       C.SetFileTimesSpec(before,now,provider.filesystem,middle,parent.target,true,parent.metadata.value.atimeSec,parent.metadata.value.atimeNsec,
                          parent.metadata.value.mtimeSec,parent.metadata.value.mtimeNsec,timeOK,timeErr)
     else middle == before && timeOK && timeErr == 0) &&
    (if !timeOK then after == middle && !ok && err == ParentTimeError(Q(parent.target),E(timeErr))
     else (if raw.policy.preserveMode || parent.restore then C.SetFileModeSpec(middle,now,provider.failures,after,parent.target,true,parent.mode,modeOK,modeErr)
           else after == middle && modeOK && modeErr == 0) &&
          ok == modeOK && err == (if ok then [] else if raw.policy.preserveMode then ModeError(Q(parent.target),E(modeErr)) else ParentModeError(Q(parent.target),E(modeErr))))
  }

  opaque ghost predicate ParentRestoreOne(raw: S.CpCmdRaw, parent: ParentInfo, before: BW.FileSystem, after: BW.FileSystem,
                                          now: int, provider: FilesystemProvider, err: BW.Bytes, ok: bool) {
    exists observed: (BW.FileSystem,bool,int,bool,int) :: ParentRestoreOneFields(raw,parent,before,after,now,provider,err,ok,observed)
  }

  opaque ghost predicate ParentRestorationFields(raw: S.CpCmdRaw, records: seq<ParentInfo>, before: BW.FileSystem, after: BW.FileSystem,
                                                 now: int, provider: FilesystemProvider, err: BW.Bytes, ok: bool,
                                                 observed: (seq<BW.FileSystem>,seq<BW.Bytes>,seq<bool>)) {
    var states,errors,results := observed.0,observed.1,observed.2;
    var count := |results|;
    count <= |records| && |states| == count+1 && |errors| == count && states[0] == before && states[count] == after &&
    (forall i | 0 <= i < count :: ParentRestoreOne(raw,records[|records|-1-i],states[i],states[i+1],now,provider,errors[i],results[i])) &&
    (forall i | 0 <= i < count-1 :: results[i]) &&
    (count == |records| || (count > 0 && !results[count-1])) &&
    ok == (count == |records| && (forall i | 0 <= i < count :: results[i])) && Concatenation(errors,err)
  }

  opaque ghost predicate ParentRestoration(raw: S.CpCmdRaw, records: seq<ParentInfo>, before: BW.FileSystem, after: BW.FileSystem,
                                           now: int, provider: FilesystemProvider, err: BW.Bytes, ok: bool) {
    exists observed: (seq<BW.FileSystem>,seq<BW.Bytes>,seq<bool>) :: ParentRestorationFields(raw,records,before,after,now,provider,err,ok,observed)
  }

  datatype SourceTree =
    MissingSource(path: string, metadata: Metadata) |
    ModeFailureSource(path: string, metadata: Metadata, modeErr: int) |
    LinkFailureSource(path: string, metadata: Metadata, mode: bv32, linkError: BW.IOError) |
    OmittedSource(path: string, metadata: Metadata) |
    CyclicSource(path: string, metadata: Metadata) |
    FileSource(path: string, metadata: Metadata, mode: bv32, linkTarget: string) |
    DirectorySource(path: string, metadata: Metadata, mode: bv32,
                    children: seq<SourceTree>, scanErr: int)

  function TreeHeight(tree: SourceTree): (height: nat)
    ensures tree.DirectorySource? ==> height == 1+ForestHeight(tree.children)
    ensures !tree.DirectorySource? ==> height == 0
    decreases tree
  {
    if tree.DirectorySource? then 1 + ForestHeight(tree.children) else 0
  }

  function ForestHeight(trees: seq<SourceTree>): (height: nat)
    ensures forall i | 0 <= i < |trees| :: TreeHeight(trees[i]) <= height
    decreases trees
  {
    if |trees| == 0 then 0
    else if TreeHeight(trees[0]) > ForestHeight(trees[1..]) then TreeHeight(trees[0]) else ForestHeight(trees[1..])
  }

  ghost predicate OriginalChildIndex(trees: seq<SourceTree>, path: string, index: int) {
    if index == -1 then forall i | 0 <= i < |trees| :: trees[i].path != path
    else 0 <= index < |trees| && trees[index].path == path && (forall i | 0 <= i < index :: trees[i].path != path)
  }

  datatype LiveChildObservation = LiveChildObservation(index: int, metadata: Metadata, mode: bv32, linkTarget: string,
                                                       modeOK: bool, modeErr: int, linkResult: BW.IOResult<string>)

  opaque ghost predicate LiveChildFields(raw: S.CpCmdRaw, fs: BW.FileSystem, provider: FilesystemProvider,
                                         original: seq<SourceTree>, path: string, value: SourceTree, stopped: bool, observed: LiveChildObservation) {
    OriginalChildIndex(original,path,observed.index) && MetadataFields(fs,provider,path,raw.policy.dereference,observed.metadata) &&
    (if !observed.metadata.ok then !stopped && value == MissingSource(path,observed.metadata)
     else C.GetFileModeSpec(fs,provider.failures,path,raw.policy.dereference,observed.modeOK,observed.mode,observed.modeErr) &&
          (if !observed.modeOK then !stopped && value == ModeFailureSource(path,observed.metadata,observed.modeErr)
           else if observed.metadata.value.isDir then
             stopped == (observed.index < 0 || !original[observed.index].DirectorySource? || Identity(original[observed.index].metadata) != Identity(observed.metadata)) &&
             (if stopped then value == UncopiedSource(path)
              else value == DirectorySource(path,observed.metadata,observed.mode,original[observed.index].children,original[observed.index].scanErr))
           else !stopped &&
                (if observed.metadata.value.isSymlink && !raw.policy.hard && !raw.policy.symbolic then
                   C.ReadLinkSpec(fs,provider.failures,path,observed.linkResult) &&
                   (if observed.linkResult.Ok? then observed.linkTarget == observed.linkResult.v &&
                                                    value == FileSource(path,observed.metadata,observed.mode,observed.linkTarget)
                    else value == LinkFailureSource(path,observed.metadata,observed.mode,observed.linkResult.e))
                 else observed.linkTarget == path && value == FileSource(path,observed.metadata,observed.mode,path)))) &&
    (stopped || TreeHeight(value) <= ForestHeight(original))
  }

  opaque ghost predicate LiveChild(raw: S.CpCmdRaw, fs: BW.FileSystem, provider: FilesystemProvider,
                                   original: seq<SourceTree>, path: string, value: SourceTree, stopped: bool) {
    exists observed: LiveChildObservation :: LiveChildFields(raw,fs,provider,original,path,value,stopped,observed)
  }

  opaque ghost predicate LiveSelectionFields(raw: S.CpCmdRaw, tree: SourceTree, enabled: bool,
                                             fs: BW.FileSystem, provider: FilesystemProvider,
                                             selected: seq<SourceTree>, stopped: bool, scanErr: int,
                                             observed: (seq<DirectoryName>,seq<SourceTree>,seq<bool>))
    requires tree.DirectorySource?
    ensures LiveSelectionFields(raw,tree,enabled,fs,provider,selected,stopped,scanErr,observed) ==> ForestHeight(selected) < TreeHeight(tree)
  {
    var entries,processed,flags := observed.0,observed.1,observed.2;
    ForestHeight(selected) < TreeHeight(tree) &&
    (if !enabled then selected == tree.children && !stopped && scanErr == tree.scanErr
     else OrderedEnumeration(fs,provider,tree.path,entries,scanErr) &&
          |processed| == |selected| + (if stopped then 1 else 0) && |flags| == |processed| && |processed| <= |entries| &&
          selected == processed[..|selected|] &&
          (forall i | 0 <= i < |processed| :: NameConcat(tree.path,entries[i].name,processed[i].path) &&
                                              LiveChild(raw,fs,provider,tree.children,processed[i].path,processed[i],flags[i])) &&
          (forall i | 0 <= i < |selected| :: !flags[i]) &&
          (if stopped then flags[|selected|] else |processed| == |entries|))
  }

  opaque ghost predicate LiveSelection(raw: S.CpCmdRaw, tree: SourceTree, enabled: bool,
                                       fs: BW.FileSystem, provider: FilesystemProvider,
                                       selected: seq<SourceTree>, stopped: bool, scanErr: int)
    requires tree.DirectorySource?
    ensures LiveSelection(raw,tree,enabled,fs,provider,selected,stopped,scanErr) ==> ForestHeight(selected) < TreeHeight(tree)
  {
    exists observed: (seq<DirectoryName>,seq<SourceTree>,seq<bool>) :: LiveSelectionFields(raw,tree,enabled,fs,provider,selected,stopped,scanErr,observed)
  }

  ghost function Identities(fs: BW.FileSystem): set<(int,int)> {
    set id | id in fs.inodes :: (fs.inodes[id].hostKey.device, fs.inodes[id].hostKey.inode)
  }

  datatype DirectoryName = DirectoryName(name: string, inode: int)

  ghost predicate SortedEntries(entries: seq<DirectoryName>) {
    forall i,j | 0 <= i < j < |entries| :: entries[i].inode <= entries[j].inode
  }

  opaque ghost predicate EnumerationWithOpen(fs: BW.FileSystem, provider: FilesystemProvider, path: string, entries: seq<DirectoryName>, err: int, wasOpened: bool) {
    exists initial: map<int,BW.DirHandleState>, openedHandles: map<int,BW.DirHandleState>,
      handle: int, openErr: int ::
      var openOK := wasOpened;
      C.OpenDirSpec(fs, initial, provider.failures, openedHandles, path, false, openOK, handle, openErr) &&
      (if !openOK then entries == [] && err == openErr
       else exists states: seq<map<int,BW.DirHandleState>>, kinds: seq<BW.DirectoryEntryKind>,
              readErr: int, closed: map<int,BW.DirHandleState>, closeOK: bool, closeErr: int ::
              |states| == |entries| + 1 && |kinds| == |entries| && states[0] == openedHandles &&
              (forall i | 0 <= i < |entries| ::
                 C.ReadDirSpec(fs, states[i], provider.failures, states[i+1], handle, true, entries[i].name, kinds[i], 0) &&
                 C.ReadDirInodeFields(fs,states[i],handle,entries[i].name,true,entries[i].inode)) &&
              C.ReadDirSpec(fs, states[|entries|], provider.failures, states[|entries|], handle, false, "", BW.UnknownDirentKind, readErr) &&
              C.CloseDirSpec(states[|entries|], provider.failures, closed, handle, closeOK, closeErr) &&
              err == (if readErr != 0 then readErr else closeErr))
  }

  opaque ghost predicate Enumeration(fs: BW.FileSystem, provider: FilesystemProvider, path: string, entries: seq<DirectoryName>, err: int) {
    exists wasOpened: bool :: EnumerationWithOpen(fs,provider,path,entries,err,wasOpened)
  }

  opaque ghost predicate OrderedEnumeration(fs: BW.FileSystem, provider: FilesystemProvider, path: string, entries: seq<DirectoryName>, err: int) {
    exists nativeOrder: seq<DirectoryName> :: Enumeration(fs,provider,path,nativeOrder,err) &&
                                              (if err == 0 then multiset(entries) == multiset(nativeOrder) && SortedEntries(entries)
                                               else entries == [])
  }

  opaque ghost predicate SourceTreeFields(raw: S.CpCmdRaw, fs: BW.FileSystem, provider: FilesystemProvider,
                                          ancestors: set<(int,int)>, parentDevice: int, tree: SourceTree)
    decreases tree
  {
    MetadataFields(fs, provider, tree.path, raw.policy.dereference, tree.metadata) &&
    match tree
    case MissingSource(_, sm) => !sm.ok
    case ModeFailureSource(path, sm, err) => sm.ok &&
                                             !(sm.value.isDir && (!raw.policy.recursive || Identity(sm) in ancestors)) &&
                                             C.GetFileModeSpec(fs, provider.failures, path, raw.policy.dereference, false, 0 as bv32, err)
    case LinkFailureSource(path, sm, mode, err) => sm.ok && !sm.value.isDir &&
                                                   sm.value.isSymlink && !raw.policy.hard && !raw.policy.symbolic &&
                                                   C.GetFileModeSpec(fs, provider.failures, path, raw.policy.dereference, true, mode, 0) &&
                                                   C.ReadLinkSpec(fs, provider.failures, path, Results.Err(err))
    case OmittedSource(_, sm) => sm.ok && sm.value.isDir && !raw.policy.recursive
    case CyclicSource(_, sm) => sm.ok && sm.value.isDir && raw.policy.recursive && Identity(sm) in ancestors
    case FileSource(path, sm, mode, linkTarget) => sm.ok && !sm.value.isDir &&
                                                   C.GetFileModeSpec(fs,provider.failures, path, raw.policy.dereference, true, mode, 0) &&
                                                   (if sm.value.isSymlink && !raw.policy.hard && !raw.policy.symbolic then C.ReadLinkSpec(fs,provider.failures,path,Results.Ok(linkTarget))
                                                    else linkTarget == path)
    case DirectorySource(path, sm, mode, children, scanErr) =>
      sm.ok && sm.value.isDir && raw.policy.recursive && Identity(sm) !in ancestors &&
      C.GetFileModeSpec(fs,provider.failures, path, raw.policy.dereference, true, mode, 0) &&
      (if raw.policy.oneFileSystem && |ancestors| != 0 && sm.value.device != parentDevice then children == [] && scanErr == 0
       else exists entries: seq<DirectoryName> :: |entries| == |children| && OrderedEnumeration(fs,provider, path, entries, scanErr) &&
                                                  forall i | 0 <= i < |children| :: NameConcat(path,entries[i].name,children[i].path) &&
                                                                                    SourceTreeFields(S.ChildCommand(raw), fs, provider, ancestors + {Identity(sm)}, sm.value.device, children[i]))
  }

  opaque ghost predicate SameEntryFields(fs: BW.FileSystem, provider: FilesystemProvider,
                                         source: string, target: string, result: bool) {
    if source == target then result
    else exists sourceParent: string, targetParent: string, sourceBase: string, targetBase: string,
           sm: Metadata, tm: Metadata ::
           Paths.DirnameRelation(source,sourceParent) && Paths.DirnameRelation(target,targetParent) &&
           Paths.BasenameRelation(source,sourceBase) && Paths.BasenameRelation(target,targetBase) &&
           MetadataFields(fs,provider,sourceParent,false,sm) && MetadataFields(fs,provider,targetParent,false,tm) &&
           result == (sm.ok && tm.ok && Identity(sm) == Identity(tm) && sourceBase == targetBase)
  }

  function PreserveEligible(raw: S.CpCmdRaw, tree: SourceTree): bool
    requires tree.FileSource?
  {
    raw.policy.creation.preserveLinks && !raw.policy.hard &&
    (tree.metadata.value.linkCount > 1 || raw.policy.dereference)
  }

  function LinkCommand(raw: S.CpCmdRaw): S.CpCmdRaw {
    raw.(policy := raw.policy.(hard := true,symbolic := false,force := false))
  }

  opaque ghost predicate FileEffect(raw: S.CpCmdRaw, tree: SourceTree, target: string, tm: Metadata,
                                    before: BW.FileSystem, after: BW.FileSystem, props: map<string,string>, now: int,
                                    credentials: BW.ProcessCredentials, provider: FilesystemProvider, streams: StreamProvider,
                                    out: BW.Bytes, err: BW.Bytes, ok: bool, linkState: (LinkMap,LinkMap),record: CopyReceipt)
    requires tree.FileSource?
  {
    exists receipt: CopyReceipt ::
      if PreserveEligible(raw,tree) && Identity(tree.metadata) in linkState.0 then
        BackupLeaf(LinkCommand(raw),tree.path,target,tree.metadata,tm,(tree.mode,linkState.0[Identity(tree.metadata)]),before,after,props,now,credentials,provider,streams,(out,err,ok,receipt)) &&
        linkState.1 == linkState.0 && record == CopyReceipt(NoDestinationRecord,receipt.retained,false)
      else
        BackupLeaf(raw,tree.path,target,tree.metadata,tm,(tree.mode,tree.linkTarget),before,after,props,now,credentials,provider,streams,(out,err,ok,receipt)) &&
        linkState.1 == (if PreserveEligible(raw,tree) && receipt.retained then linkState.0[Identity(tree.metadata) := target] else linkState.0) && record == receipt
  }

  datatype FileTreeObservation = FileTreeObservation(metadata: Metadata, allowed: bool, returnNow: bool)

  ghost predicate FileTreeFields(raw: S.CpCmdRaw, tree: SourceTree, target: string,
                                 before: BW.FileSystem, after: BW.FileSystem, props: map<string,string>, now: int,
                                 credentials: BW.ProcessCredentials, provider: FilesystemProvider, streams: StreamProvider,
                                 out: BW.Bytes, err: BW.Bytes, ok: bool, linkState: (LinkMap,LinkMap,bool), record: CopyReceipt,
                                 observed: FileTreeObservation)
    requires tree.FileSource?
  {
    var tm, allowed, returnNow := observed.metadata, observed.allowed, observed.returnNow;
    MetadataFields(before,provider,target,!raw.policy.remove && !raw.policy.symbolic && !raw.policy.hard && !tree.metadata.value.isSymlink && BackupMode(raw) == "off",tm) &&
    (if tm.ok && !raw.policy.skip && raw.policy.update != "none" && raw.policy.update != "none-fail" then
       SameFileEligibility(raw,tree.path,target,tree.metadata,tm,before,provider,allowed,returnNow)
     else allowed && !returnNow) &&
    (if !allowed then record == CopyReceipt(NoDestinationRecord,false,false) && linkState.1 == linkState.0 && after == before && out == [] && err == SameFile(Q(tree.path),Q(target)) && !ok
     else if Skip(raw,tree.metadata,tm) then record == CopyReceipt(NoDestinationRecord,false,false) && linkState.1 == (if raw.policy.update == "older" && Identity(tree.metadata) !in linkState.0 then linkState.0[Identity(tree.metadata) := target] else linkState.0) && after == before && out == [] && err == (if raw.policy.update == "none-fail" then NotReplaced(Q(target)) else []) && ok == (raw.policy.update != "none-fail")
     else if returnNow then record == CopyReceipt(NoDestinationRecord,false,false) && linkState.1 == linkState.0 && after == before && out == [] && err == [] && ok
     else if tm.ok && tm.value.isDir && BackupMode(raw) == "off" then
       record == CopyReceipt(NoDestinationRecord,false,false) && linkState.1 == linkState.0 && after == before && out == [] && err == NonDirectory(Q(tree.path),Q(target)) && !ok
     else FileEffect(raw,tree,target,tm,before,after,props,now,credentials,provider,streams,out,err,ok,(linkState.0,linkState.1),record))
  }

  opaque ghost predicate CopyTree(raw: S.CpCmdRaw, tree: SourceTree, target: string,
                                  before: BW.FileSystem, after: BW.FileSystem, props: map<string,string>, now: int,
                                  credentials: BW.ProcessCredentials, mask: bv32, provider: FilesystemProvider,
                                  streams: StreamProvider, out: BW.Bytes, err: BW.Bytes, ok: bool,linkState: (LinkMap,LinkMap,bool),record: CopyReceipt)
    decreases TreeHeight(tree), 4
  {
    match tree
    case MissingSource(path, sm) => record == CopyReceipt(NoDestinationRecord,false,false) && linkState.1 == linkState.0 && after == before && out == [] && err == CannotStat(Q(path),E(sm.err)) && !ok
    case ModeFailureSource(path, _, modeErr) => record == CopyReceipt(NoDestinationRecord,false,false) && linkState.1 == linkState.0 && after == before && out == [] && err == CannotStat(Q(path),E(modeErr)) && !ok
    case LinkFailureSource(path, _, _, failure) => record == CopyReceipt(NoDestinationRecord,false,false) && linkState.1 == linkState.0 && after == before && out == [] && err == ReadSymlinkError(Q(path),E(C.IOErrorErrno(failure))) && !ok
    case OmittedSource(path, _) => record == CopyReceipt(NoDestinationRecord,false,false) && linkState.1 == linkState.0 && after == before && out == [] && err == Omitting(Q(path)) && !ok
    case CyclicSource(path, _) => record == CopyReceipt(NoDestinationRecord,false,false) && linkState.1 == linkState.0 && after == before && out == [] && err == Cycle(Q(path)) && !ok
    case FileSource(source, sm, mode, linkTarget) =>
      exists observed: FileTreeObservation ::
        FileTreeFields(raw,tree,target,before,after,props,now,credentials,provider,streams,
                       out,err,ok,linkState,record,observed)
    case DirectorySource(source,sm,mode,children,scanErr) =>
      exists tm: Metadata :: MetadataFields(before,provider,target,raw.policy.keepDirectorySymlink,tm) &&
                             (if tm.ok && Identity(sm) == Identity(tm) then record == CopyReceipt(NoDestinationRecord,false,false) && linkState.1 == linkState.0 && after == before && out == [] && err == SameFile(Q(source),Q(target)) && !ok
                              else if tm.ok && !tm.value.isDir && BackupMode(raw) == "off" then record == CopyReceipt(NoDestinationRecord,false,false) && linkState.1 == linkState.0 && after == before && out == [] && err == DirectoryOverFile(Q(source),Q(target)) && !ok
                              else exists receipt: CopyReceipt ::
                                     BackupDirectory(raw,tree,target,tm,before,after,props,now,credentials,mask,provider,streams,(out,err,ok,receipt),linkState) && record == receipt)
  }

  datatype DirectoryReadyObservation = DirectoryReadyObservation(created: BW.FileSystem, createOK: bool, createErr: int,
                                                                 metadata: Metadata, modeOK: bool, mode: bv32, modeErr: int, changeOK: bool, changeErr: int)

  opaque ghost predicate {:isolate_assertions} DirectoryReadyFields(raw: S.CpCmdRaw, target: string, tm: Metadata, sourceMode: bv32,
                                                                    before: BW.FileSystem, after: BW.FileSystem, now: int, mask: bv32,
                                                                    provider: FilesystemProvider, ok: bool, err: BW.Bytes, observed: DirectoryReadyObservation) {
    if tm.ok && tm.value.isDir then after == before && ok && err == []
    else C.CreateDirectorySpec(before,now,provider.filesystem,mask,observed.created,target,DirectoryCreationMode(raw,sourceMode),observed.createOK,observed.createErr) &&
         (if !observed.createOK then after == observed.created && !ok && err == CreateDirectoryError(Q(target),E(observed.createErr))
          else MetadataFields(observed.created,provider,target,false,observed.metadata) &&
               (if !observed.metadata.ok then after == observed.created && !ok && err == CannotStat(Q(target),E(observed.metadata.err))
                else C.GetFileModeSpec(observed.created,provider.failures,target,false,observed.modeOK,observed.mode,observed.modeErr) &&
                     (if !observed.modeOK then after == observed.created && !ok && err == CannotStat(Q(target),E(observed.modeErr))
                      else (if (observed.mode & (448 as bv32)) != (448 as bv32) then
                              C.SetFileModeSpec(observed.created,now,provider.failures,after,target,false,observed.mode | (448 as bv32),observed.changeOK,observed.changeErr)
                            else after == observed.created && observed.changeOK && observed.changeErr == 0) &&
                           ok == observed.changeOK && err == (if ok then [] else ParentSetModeError(Q(target),E(observed.changeErr))))))
  }

  opaque ghost predicate DirectoryReady(raw: S.CpCmdRaw, target: string, tm: Metadata, sourceMode: bv32,
                                        before: BW.FileSystem, after: BW.FileSystem, now: int, mask: bv32,
                                        provider: FilesystemProvider, ok: bool, err: BW.Bytes, createdMode: bv32) {
    exists observed: DirectoryReadyObservation :: observed.mode == createdMode &&
                                                  DirectoryReadyFields(raw,target,tm,sourceMode,before,after,now,mask,provider,ok,err,observed)
  }

  datatype DirectoryBackupObservation = DirectoryBackupObservation(prepared: BW.FileSystem, preparation: BackupPreparationResult,
                                                                   readyMetadata: Metadata, copied: BW.FileSystem, copyOut: BW.Bytes, copyErr: BW.Bytes, copyOK: bool, receipt: CopyReceipt,
                                                                   restoreOut: BW.Bytes, restoreErr: BW.Bytes, sourceBase: string, removeOK: bool, removeErr: int)

  opaque ghost predicate BackupDirectoryFields(raw: S.CpCmdRaw, tree: SourceTree, target: string, tm: Metadata,
                                               before: BW.FileSystem, after: BW.FileSystem, props: map<string,string>, now: int,
                                               credentials: BW.ProcessCredentials, mask: bv32, provider: FilesystemProvider,
                                               streams: StreamProvider, reported: (BW.Bytes,BW.Bytes,bool,CopyReceipt), linkState: (LinkMap,LinkMap,bool), observed: DirectoryBackupObservation)
    requires tree.DirectorySource?
    decreases TreeHeight(tree),2
  {
    var out,err,ok,receipt := reported.0,reported.1,reported.2,reported.3;
    if BackupMode(raw) == "off" || !tm.ok || tm.value.isDir then
      DirectoryEffect(raw,tree,target,tm,before,after,props,now,credentials,mask,provider,streams,reported,linkState)
    else
      Paths.BasenameRelation(tree.path,observed.sourceBase) &&
      (if observed.sourceBase == "." || observed.sourceBase == ".." then
         (if PreUnlink(raw,tree.metadata,tm) then
            C.UnlinkPathSpec(before,now,provider.filesystem,observed.prepared,target,observed.removeOK,observed.removeErr)
          else observed.prepared == before && observed.removeOK && observed.removeErr == 0) &&
         (if !observed.removeOK && observed.removeErr != 2 then
            after == observed.prepared && out == [] && err == CannotRemove(Q(target),E(observed.removeErr)) && !ok &&
            receipt == CopyReceipt(NoDestinationRecord,false,false) && linkState.1 == linkState.0
          else MetadataFields(observed.prepared,provider,target,raw.policy.keepDirectorySymlink,observed.readyMetadata) &&
               DirectoryEffect(raw,tree,target,observed.readyMetadata,observed.prepared,after,props,now,credentials,mask,provider,streams,
                               (observed.copyOut,err,ok,receipt),linkState) &&
               out == (if raw.policy.verbose && PreUnlink(raw,tree.metadata,tm) then Removed(Q(target)) else []) + observed.copyOut)
       else
         BackupPreparation(raw,tree.path,target,tree.metadata,before,observed.prepared,now,provider,observed.preparation) &&
         (if observed.preparation.BackupRejected? then after == observed.prepared && out == [] && err == observed.preparation.error && !ok &&
                                                       receipt == CopyReceipt(NoDestinationRecord,false,false) && linkState.1 == linkState.0
          else MetadataFields(observed.prepared,provider,target,raw.policy.keepDirectorySymlink,observed.readyMetadata) &&
               DirectoryEffect(raw,tree,target,observed.readyMetadata,observed.prepared,observed.copied,props,now,credentials,mask,provider,streams,
                               (observed.copyOut,observed.copyErr,observed.copyOK,observed.receipt),linkState) && receipt == observed.receipt &&
               BackupRestoration(raw,observed.preparation.path,target,!observed.copyOK && !receipt.retained && observed.preparation.renamed,
                                 observed.copied,after,now,provider,observed.restoreOut,observed.restoreErr) &&
               out == observed.copyOut+observed.restoreOut && err == observed.copyErr+observed.restoreErr && ok == observed.copyOK))
  }

  opaque ghost predicate BackupDirectory(raw: S.CpCmdRaw, tree: SourceTree, target: string, tm: Metadata,
                                         before: BW.FileSystem, after: BW.FileSystem, props: map<string,string>, now: int,
                                         credentials: BW.ProcessCredentials, mask: bv32, provider: FilesystemProvider,
                                         streams: StreamProvider, reported: (BW.Bytes,BW.Bytes,bool,CopyReceipt), linkState: (LinkMap,LinkMap,bool))
    requires tree.DirectorySource?
    decreases TreeHeight(tree),3
  {
    exists observed: DirectoryBackupObservation :: BackupDirectoryFields(raw,tree,target,tm,before,after,props,now,credentials,mask,provider,streams,reported,linkState,observed)
  }

  opaque ghost predicate DirectoryOutcome(raw: S.CpCmdRaw, tree: SourceTree, target: string, tm: Metadata,
                                          before: BW.FileSystem, after: BW.FileSystem, props: map<string,string>, now: int,
                                          credentials: BW.ProcessCredentials, mask: bv32, provider: FilesystemProvider,
                                          streams: StreamProvider, reported: (BW.Bytes,BW.Bytes,bool,CopyReceipt), observed: (BW.FileSystem,bool,BW.Bytes,BW.FileSystem,BW.Bytes,BW.Bytes,bool,BW.Bytes,bool,bv32,seq<SourceTree>,bool,int,bool),linkState: (LinkMap,LinkMap,bool))
    requires tree.DirectorySource?
    decreases TreeHeight(tree), 0
  {
    var out,err,ok,receipt := reported.0,reported.1,reported.2,reported.3;
    var created,createOK,createErr,copied,childOut,childErr,childOK,attributeErr,attributeOK :=
      observed.0,observed.1,observed.2,observed.3,observed.4,observed.5,observed.6,observed.7,observed.8;
    var createdMode := observed.9;
    var selected,stopped,scanErr,childStopped := observed.10,observed.11,observed.12,observed.13;
    DirectoryReady(raw,target,tm,tree.mode,before,created,now,mask,provider,createOK,createErr,createdMode) &&
    (if !createOK then receipt == CopyReceipt(NoDestinationRecord,false,false) && linkState.1 == linkState.0 && after == created && out == [] && err == createErr && !ok
     else
       LiveSelection(S.ChildCommand(raw),tree,linkState.2,created,provider,selected,stopped,scanErr) &&
       Children(S.ChildCommand(raw),selected,target,created,copied,props,now,credentials,mask,provider,streams,childOut,childErr,childOK,(linkState.0,linkState.1,linkState.2,childStopped)) &&
       receipt.selfCopy == (stopped || childStopped) && receipt.retained && DestinationRecordFields(copied,provider,target,receipt.record) &&
       DirectoryAttributes(raw,tree,tm,createdMode,target,copied,after,now,props,provider,attributeErr,attributeOK) &&
       out == (if raw.policy.verbose && !tm.ok then Verbose(Q(tree.path),Q(target)) else []) + childOut &&
       err == childErr + (if scanErr == 0 then [] else ReadDirectoryError(Q(tree.path),E(scanErr))) + attributeErr &&
       ok == (childOK && scanErr == 0 && attributeOK && !stopped))
  }

  opaque ghost predicate DirectoryEffect(raw: S.CpCmdRaw, tree: SourceTree, target: string, tm: Metadata,
                                         before: BW.FileSystem, after: BW.FileSystem, props: map<string,string>, now: int,
                                         credentials: BW.ProcessCredentials, mask: bv32, provider: FilesystemProvider,
                                         streams: StreamProvider, reported: (BW.Bytes,BW.Bytes,bool,CopyReceipt),linkState: (LinkMap,LinkMap,bool))
    requires tree.DirectorySource?
    decreases TreeHeight(tree), 1
  {
    exists observed: (BW.FileSystem,bool,BW.Bytes,BW.FileSystem,BW.Bytes,BW.Bytes,bool,BW.Bytes,bool,bv32,seq<SourceTree>,bool,int,bool) ::
      DirectoryOutcome(raw,tree,target,tm,before,after,props,now,credentials,mask,provider,streams,reported,observed,linkState)
  }

  opaque ghost predicate DirectoryAttributes(raw: S.CpCmdRaw, tree: SourceTree, tm: Metadata, createdMode: bv32,
                                             target: string, before: BW.FileSystem, after: BW.FileSystem, now: int, props: map<string,string>,
                                             provider: FilesystemProvider, err: BW.Bytes, ok: bool)
    requires tree.DirectorySource?
  {
    exists mask: bv32 :: C.GetUmaskSpec(props,mask) &&
                         Attributes(raw.(policy := raw.policy.(preserveMode := raw.policy.preserveMode || !tm.ok)),tree.metadata,
                                    DirectoryFinalMode(raw,tree.mode,mask,createdMode),
                                    target,true,before,after,now,provider,err,ok)
  }

  opaque ghost predicate ChildrenFields(raw: S.CpCmdRaw, trees: seq<SourceTree>, target: string,
                                        before: BW.FileSystem, after: BW.FileSystem, props: map<string,string>, now: int,
                                        credentials: BW.ProcessCredentials, mask: bv32, provider: FilesystemProvider,
                                        streams: StreamProvider, out: BW.Bytes, err: BW.Bytes, ok: bool,linkState: (LinkMap,LinkMap,bool,bool), observed: (seq<BW.FileSystem>,seq<BW.Bytes>,seq<BW.Bytes>,seq<bool>,seq<string>,seq<LinkMap>,seq<CopyReceipt>))
    decreases ForestHeight(trees), 5
  {
    var states,outputs,errors,results,targets,maps,records := observed.0,observed.1,observed.2,observed.3,observed.4,observed.5,observed.6;
    var count := |results|;
    count <= |trees| && |records| == count && |maps| == count+1 && maps[0] == linkState.0 && maps[count] == linkState.1 &&
    |states| == count+1 && |outputs| == count && |errors| == count && |targets| == count &&
    states[0] == before && states[count] == after &&
    (forall i | 0 <= i < count ::
       TargetFields(target,trees[i].path,targets[i]) &&
       CopyTree(raw,trees[i],targets[i],states[i],states[i+1],props,now,credentials,mask,provider,streams,outputs[i],errors[i],results[i],(maps[i],maps[i+1],linkState.2),records[i])) &&
    (forall i | 0 <= i < count-1 :: !records[i].selfCopy) &&
    linkState.3 == (count > 0 && records[count-1].selfCopy) &&
    (count == |trees| || linkState.3) &&
    Concatenation(outputs,out) && Concatenation(errors,err) && ok == (forall i | 0 <= i < |results| :: results[i])
  }

  opaque ghost predicate Children(raw: S.CpCmdRaw, trees: seq<SourceTree>, target: string,
                                  before: BW.FileSystem, after: BW.FileSystem, props: map<string,string>, now: int,
                                  credentials: BW.ProcessCredentials, mask: bv32, provider: FilesystemProvider,
                                  streams: StreamProvider, out: BW.Bytes, err: BW.Bytes, ok: bool,linkState: (LinkMap,LinkMap,bool,bool))
    decreases ForestHeight(trees), 6
  {
    exists observed: (seq<BW.FileSystem>,seq<BW.Bytes>,seq<BW.Bytes>,seq<bool>,seq<string>,seq<LinkMap>,seq<CopyReceipt>) ::
      ChildrenFields(raw,trees,target,before,after,props,now,credentials,mask,provider,streams,out,err,ok,linkState,observed)
  }

  opaque ghost predicate SelfDestination(fs: BW.FileSystem, cwd: string, provider: FilesystemProvider, source: string, target: string, result: bool) {
    exists sourceOK: bool, sourcePath: string, sourceErr: int, parent: string,
      parentOK: bool, parentPath: string, parentErr: int ::
      Paths.DirnameRelation(target,parent) &&
      C.ResolvePathIdentitySpec(fs,cwd,provider.failures,source,sourceOK,sourcePath,sourceErr) &&
      C.ResolvePathIdentitySpec(fs,cwd,provider.failures,parent,parentOK,parentPath,parentErr) &&
      result == (sourceOK && parentOK && (sourcePath == "/" || C.HasPathPrefix(sourcePath,parentPath)))
  }

  opaque ghost predicate RootOutcome(raw: S.CpCmdRaw, tree: SourceTree, target: string, cwd: string,
                                     before: BW.FileSystem, after: BW.FileSystem, props: map<string,string>, now: int,
                                     credentials: BW.ProcessCredentials, mask: bv32, provider: FilesystemProvider,
                                     streams: StreamProvider, reported: (BW.Bytes,BW.Bytes,bool,CopyReceipt), observed: (bool,bool,BW.Bytes,bool,bool,Metadata,Metadata),linkState: (LinkMap,LinkMap)) {
    var out,err,ok,record := reported.0,reported.1,reported.2,reported.3;
    var candidateSelf,self,childErr,childOK,inside,beforeTarget,afterTarget :=
      observed.0,observed.1,observed.2,observed.3,observed.4,observed.5,observed.6;
    (if tree.DirectorySource? && tree.scanErr == 0 then
       SelfDestination(before,cwd,provider,tree.path,target,inside) &&
       (if inside then MetadataFields(before,provider,target,raw.policy.keepDirectorySymlink,beforeTarget) &&
                       candidateSelf == (!beforeTarget.ok || (if beforeTarget.value.isDir then Identity(beforeTarget) != Identity(tree.metadata) else BackupMode(raw) != "off"))
        else !candidateSelf)
     else !candidateSelf) &&
    CopyTree(raw,tree,target,before,after,props,now,credentials,mask,provider,streams,out,childErr,childOK,(linkState.0,linkState.1,candidateSelf),record) &&
    (if candidateSelf then MetadataFields(after,provider,target,true,afterTarget) && self == (record.selfCopy && afterTarget.ok && afterTarget.value.isDir)
     else !self) &&
    err == childErr + (if self then IntoSelf(Q(tree.path),Q(target)) else []) && ok == (childOK && !self)
  }

  opaque ghost predicate RootCopy(raw: S.CpCmdRaw, tree: SourceTree, target: string, cwd: string,
                                  before: BW.FileSystem, after: BW.FileSystem, props: map<string,string>, now: int,
                                  credentials: BW.ProcessCredentials, mask: bv32, provider: FilesystemProvider,
                                  streams: StreamProvider, reported: (BW.Bytes,BW.Bytes,bool,CopyReceipt),linkState: (LinkMap,LinkMap)) {
    exists observed: (bool,bool,BW.Bytes,bool,bool,Metadata,Metadata) ::
      RootOutcome(raw,tree,target,cwd,before,after,props,now,credentials,mask,provider,streams,reported,observed,linkState)
  }

  type SeenDestinations = seq<(string,int,int)>
  datatype DestinationGuardResult = GuardContinue | GuardStop(error: BW.Bytes)
  datatype DestinationGuardObservation = DestinationGuardObservation(target: Metadata, entry: Metadata, mayCopy: bool, same: bool, seen: bool, entrySeen: bool)

  function FollowDestination(raw: S.CpCmdRaw, tree: SourceTree): bool {
    if tree.DirectorySource? then raw.policy.keepDirectorySymlink
    else !raw.policy.remove && !raw.policy.symbolic && !raw.policy.hard && !tree.metadata.value.isSymlink && BackupMode(raw) == "off"
  }
  function RememberDestination(seen: SeenDestinations, target: string, receipt: CopyReceipt): SeenDestinations {
    if receipt.record.RecordedDestination? then
      seen+[(target,receipt.record.metadata.value.device,receipt.record.metadata.value.inode)]
    else seen
  }
  function RememberDirectory(tree: SourceTree, target: string, receipt: CopyReceipt, links: LinkMap): LinkMap {
    if tree.DirectorySource? && receipt.retained then links[Identity(tree.metadata) := target] else links
  }
  function JustCreated(target: BW.Bytes, source: BW.Bytes): BW.Bytes {
    "cp: will not overwrite just-created " + target + " with " + source + "\n"
  }
  function JustCreatedSymlink(target: BW.Bytes, source: BW.Bytes): BW.Bytes {
    "cp: will not copy " + source + " through just-created symlink " + target + "\n"
  }

  opaque ghost predicate SeenDestinationFields(fs: BW.FileSystem, provider: FilesystemProvider, target: string, meta: Metadata,
                                               seen: SeenDestinations, result: bool, matches: seq<bool>) {
    |matches| == |seen| &&
    (forall i | 0 <= i < |seen| ::
       if meta.ok && (meta.value.device,meta.value.inode) == (seen[i].1,seen[i].2) then SameEntryFields(fs,provider,target,seen[i].0,matches[i])
       else !matches[i]) && result == (exists i | 0 <= i < |matches| :: matches[i])
  }
  opaque ghost predicate SeenDestination(fs: BW.FileSystem, provider: FilesystemProvider, target: string, meta: Metadata,
                                         seen: SeenDestinations, result: bool) {
    exists matches: seq<bool> :: SeenDestinationFields(fs,provider,target,meta,seen,result,matches)
  }

  opaque ghost predicate RepeatedSourceFields(raw: S.CpCmdRaw, fs: BW.FileSystem, provider: FilesystemProvider, tree: SourceTree,
                                              target: string, previous: seq<SourceTree>, links: LinkMap, repeated: bool, matches: seq<bool>) {
    if tree.DirectorySource? && Identity(tree.metadata) in links then SameEntryFields(fs,provider,target,links[Identity(tree.metadata)],repeated)
    else if tree.FileSource? && BackupMode(raw) == "off" then
      |matches| == |previous| &&
      (forall i | 0 <= i < |previous| ::
         if previous[i].FileSource? && Identity(tree.metadata) == Identity(previous[i].metadata) then SameEntryFields(fs,provider,tree.path,previous[i].path,matches[i])
         else !matches[i]) && repeated == (exists i | 0 <= i < |matches| :: matches[i])
    else !repeated
  }
  opaque ghost predicate RepeatedSource(raw: S.CpCmdRaw, fs: BW.FileSystem, provider: FilesystemProvider, tree: SourceTree,
                                        target: string, previous: seq<SourceTree>, links: LinkMap, repeated: bool) {
    exists matches: seq<bool> :: RepeatedSourceFields(raw,fs,provider,tree,target,previous,links,repeated,matches)
  }

  opaque ghost predicate MayCopyFields(raw: S.CpCmdRaw, tree: SourceTree, target: string, tm: Metadata,
                                       fs: BW.FileSystem, provider: FilesystemProvider, may: bool, same: bool) {
    if !tree.FileSource? && !tree.DirectorySource? then !may
    else if tree.FileSource? && Skip(raw,tree.metadata,tm) then !may
    else if tm.ok && Identity(tree.metadata) == Identity(tm) then
      if tree.FileSource? && !raw.policy.hard &&
         (raw.policy.remove || BackupMode(raw) != "off" || (tree.metadata.value.isSymlink && tm.value.isSymlink)) then
        SameEntryFields(fs,provider,tree.path,target,same) &&
        may == (!same && !(tree.metadata.value.isSymlink && tm.value.isSymlink && BackupMode(raw) == "off"))
      else !may
    else may == !(tm.ok && tree.FileSource? != !tm.value.isDir && BackupMode(raw) == "off")
  }

  opaque ghost predicate DestinationGuardFields(raw: S.CpCmdRaw, tree: SourceTree, target: string, fs: BW.FileSystem,
                                                provider: FilesystemProvider, seen: SeenDestinations, result: DestinationGuardResult,
                                                observed: DestinationGuardObservation) {
    if !tree.FileSource? && !tree.DirectorySource? then result == GuardContinue
    else MetadataFields(fs,provider,target,FollowDestination(raw,tree),observed.target) &&
         MayCopyFields(raw,tree,target,observed.target,fs,provider,observed.mayCopy,observed.same) &&
         (if !observed.mayCopy then result == GuardContinue
          else (if observed.target.ok && !observed.target.value.isDir && BackupMode(raw) != "numbered" then
                  SeenDestination(fs,provider,target,observed.target,seen,observed.seen)
                else !observed.seen) &&
               (if observed.seen then result == GuardStop(JustCreated(Q(target),Q(tree.path)))
                else if BackupMode(raw) != "off" || PreUnlink(raw,tree.metadata,observed.target) then result == GuardContinue
                else MetadataFields(fs,provider,target,false,observed.entry) &&
                     (if observed.entry.ok && observed.entry.value.isSymlink then SeenDestination(fs,provider,target,observed.entry,seen,observed.entrySeen)
                      else !observed.entrySeen) &&
                     result == (if observed.entrySeen then GuardStop(JustCreatedSymlink(Q(target),Q(tree.path))) else GuardContinue)))
  }

  opaque ghost predicate DestinationGuard(raw: S.CpCmdRaw, tree: SourceTree, target: string, fs: BW.FileSystem,
                                          provider: FilesystemProvider, seen: SeenDestinations, result: DestinationGuardResult) {
    exists observed: DestinationGuardObservation :: DestinationGuardFields(raw,tree,target,fs,provider,seen,result,observed)
  }

  datatype OperandObservation = OperandObservation(destination: string, prepared: BW.FileSystem,
                                                   parentOut: BW.Bytes, parentErr: BW.Bytes, parentOK: bool, parents: seq<ParentInfo>,
                                                   copied: BW.FileSystem, copyOut: BW.Bytes, copyErr: BW.Bytes, copyOK: bool, restoreErr: BW.Bytes, restoreOK: bool,
                                                   record: CopyReceipt, repeated: bool, guard: DestinationGuardResult, rootLinks: LinkMap)

  function UncopiedSource(source: string): SourceTree {
    MissingSource(source,Metadata(false,0,BW.FileTimeStatus(0,0,0,0,false,false,0,0,0)))
  }

  opaque ghost predicate OperandFields(raw: S.CpCmdRaw, source: string, target: string, directory: bool, cwd: string,
                                       filesystem: (BW.FileSystem,BW.FileSystem), props: map<string,string>, now: int,
                                       credentials: BW.ProcessCredentials, mask: bv32, provider: FilesystemProvider, streams: StreamProvider,
                                       reported: (BW.Bytes,BW.Bytes,bool,SourceTree), past: (seq<string>,seq<SourceTree>,LinkMap,LinkMap,SeenDestinations,SeenDestinations), observed: OperandObservation) {
    var out,err,ok,tree := reported.0,reported.1,reported.2,reported.3;
    var before,after := filesystem.0,filesystem.1;
    (if directory then (if raw.policy.creation.parents then ParentsTargetFields(target,source,observed.destination)
                        else TargetFields(target,source,observed.destination))
     else observed.destination == target) &&
    ParentPreparation(raw,source,target,observed.destination,before,observed.prepared,now,mask,provider,
                      observed.parentOut,observed.parentErr,observed.parentOK,observed.parents) &&
    (if !observed.parentOK then tree == UncopiedSource(source) && after == observed.prepared && past.3 == past.2 && past.5 == past.4 &&
                                out == observed.parentOut && err == observed.parentErr && !ok
     else tree.path == source && SourceTreeFields(raw,observed.prepared,provider,{},0,tree) &&
          RepeatedSource(raw,observed.prepared,provider,tree,observed.destination,past.1,past.2,observed.repeated) &&
          (if observed.repeated then observed.copied == observed.prepared && observed.rootLinks == past.2 && observed.record == CopyReceipt(NoDestinationRecord,false,false) &&
                                     observed.copyOut == [] && observed.copyErr == (if tree.DirectorySource? then DuplicateDirectory(Q(source)) else Duplicate(Q(source))) && observed.copyOK
           else DestinationGuard(raw,tree,observed.destination,observed.prepared,provider,past.4,observed.guard) &&
                (if observed.guard.GuardStop? then observed.copied == observed.prepared && observed.rootLinks == past.2 && observed.record == CopyReceipt(NoDestinationRecord,false,false) &&
                                                   observed.copyOut == [] && observed.copyErr == observed.guard.error && !observed.copyOK
                 else RootCopy(raw,tree,observed.destination,cwd,observed.prepared,observed.copied,props,now,credentials,mask,provider,streams,
                               (observed.copyOut,observed.copyErr,observed.copyOK,observed.record),(past.2,observed.rootLinks)))) &&
          past.3 == RememberDirectory(tree,observed.destination,observed.record,observed.rootLinks) &&
          past.5 == RememberDestination(past.4,observed.destination,observed.record) &&
          ParentRestoration(raw,observed.parents,observed.copied,after,now,provider,observed.restoreErr,observed.restoreOK) &&
          out == observed.parentOut+observed.copyOut && err == observed.parentErr+observed.copyErr+observed.restoreErr &&
          ok == (observed.copyOK && observed.restoreOK))
  }

  opaque ghost predicate Operand(raw: S.CpCmdRaw, source: string, target: string, directory: bool, cwd: string,
                                 filesystem: (BW.FileSystem,BW.FileSystem), props: map<string,string>, now: int,
                                 credentials: BW.ProcessCredentials, mask: bv32, provider: FilesystemProvider, streams: StreamProvider,
                                 reported: (BW.Bytes,BW.Bytes,bool,SourceTree), past: (seq<string>,seq<SourceTree>,LinkMap,LinkMap,SeenDestinations,SeenDestinations)) {
    exists observed: OperandObservation :: OperandFields(raw,source,target,directory,cwd,filesystem,props,now,credentials,mask,provider,streams,reported,past,observed)
  }

  opaque ghost predicate BatchOutcome(raw: S.CpCmdRaw, sources: seq<string>, target: string, directory: bool, cwd: string,
                                      before: BW.FileSystem, after: BW.FileSystem, props: map<string,string>, now: int,
                                      credentials: BW.ProcessCredentials, mask: bv32, provider: FilesystemProvider,
                                      streams: StreamProvider, reported: (BW.Bytes,BW.Bytes,bool), observed: (seq<BW.FileSystem>,seq<SourceTree>,seq<BW.Bytes>,seq<BW.Bytes>,seq<bool>,seq<string>,seq<LinkMap>,seq<SeenDestinations>)) {
    var out,err,ok := reported.0,reported.1,reported.2;
    var states,trees,outputs,errors,results,targets,maps,seens := observed.0,observed.1,observed.2,observed.3,observed.4,observed.5,observed.6,observed.7;
    |seens| == |sources|+1 && seens[0] == [] && |maps| == |sources|+1 && maps[0] == map[] &&
    |states| == |sources| + 1 && |trees| == |sources| && |outputs| == |sources| && |errors| == |sources| && |results| == |sources| && |targets| == |sources| &&
    states[0] == before && states[|sources|] == after &&
    (forall i {:trigger trees[i]} | 0 <= i < |sources| ::
       Operand(raw,sources[i],target,directory,cwd,(states[i],states[i+1]),props,now,credentials,mask,provider,streams,
               (outputs[i],errors[i],results[i],trees[i]),(sources[..i],trees[..i],maps[i],maps[i+1],seens[i],seens[i+1]))) &&
    Concatenation(outputs,out) && Concatenation(errors,err) && ok == (forall i | 0 <= i < |results| :: results[i])
  }

  opaque ghost predicate Batch(raw: S.CpCmdRaw, sources: seq<string>, target: string, directory: bool, cwd: string,
                               before: BW.FileSystem, after: BW.FileSystem, props: map<string,string>, now: int,
                               credentials: BW.ProcessCredentials, mask: bv32, provider: FilesystemProvider,
                               streams: StreamProvider, out: BW.Bytes, err: BW.Bytes, ok: bool) {
    exists observed: (seq<BW.FileSystem>,seq<SourceTree>,seq<BW.Bytes>,seq<BW.Bytes>,seq<bool>,seq<string>,seq<LinkMap>,seq<SeenDestinations>) ::
      BatchOutcome(raw,sources,target,directory,cwd,before,after,props,now,credentials,mask,provider,streams,(out,err,ok),observed)
  }

  ghost predicate BlockOffsets(parts: seq<BW.Bytes>, value: BW.Bytes, offsets: seq<nat>) {
    |offsets| == |parts| + 1 && offsets[0] == 0 && offsets[|parts|] == |value| &&
    forall i {:trigger parts[i]} | 0 <= i < |parts| ::
      offsets[i] <= offsets[i+1] <= |value| && value[offsets[i]..offsets[i+1]] == parts[i]
  }

  ghost predicate Concatenation(parts: seq<BW.Bytes>, value: BW.Bytes) {
    exists offsets: seq<nat> :: BlockOffsets(parts,value,offsets)
  }

  opaque ghost predicate PublishedOutcome(beforeOut: BW.Bytes, beforeErr: BW.Bytes,
                                          afterOut: BW.Bytes, afterErr: BW.Bytes, streams: StreamProvider,
                                          out: BW.Bytes, err: BW.Bytes, ok: bool, exit: int, observed: (nat,int,nat,int)) {
    var committed,writeErr,stderrCommitted,stderrErr := observed.0,observed.1,observed.2,observed.3;
    (if |out| == 0 then afterOut == beforeOut && committed == 0 && writeErr == 0
     else C.WriteStdoutSpec(beforeOut, streams, afterOut, out, committed, writeErr)) &&
    (var diagnostic := err + (if writeErr == 0 then [] else StdoutError(E(writeErr)));
     if |diagnostic| == 0 then afterErr == beforeErr && stderrCommitted == 0 && stderrErr == 0
     else C.WriteStderrSpec(beforeErr, streams, afterErr, diagnostic, stderrCommitted, stderrErr)) &&
    exit == (if ok && writeErr == 0 && stderrErr == 0 then 0 else 1)
  }

  opaque ghost predicate Published(beforeOut: BW.Bytes, beforeErr: BW.Bytes,
                                   afterOut: BW.Bytes, afterErr: BW.Bytes, streams: StreamProvider,
                                   out: BW.Bytes, err: BW.Bytes, ok: bool, exit: int) {
    exists observed: (nat,int,nat,int) ::
      PublishedOutcome(beforeOut,beforeErr,afterOut,afterErr,streams,out,err,ok,exit,observed)
  }

  twostate predicate Spec(raw: S.CpCmdRaw, io: BenchIO.IO, exit: int)
    reads io.fsRegion, io.dirHandlesRegion, io.propsRegion, io.nowRegion, io.credentialsRegion,
          io.umaskRegion, io.cwdRegion, io.envRegion, io.trustedFilesystemRegion,io.trustedNativeFailuresRegion, io.trustedStreamsRegion, io.stdoutRegion, io.stderrRegion
  {
    exists out: BW.Bytes, err: BW.Bytes, ok: bool ::
      Command(raw, old(io.fs()), io.fs(), io.cwd(), io.env(), io.props(), io.now(), io.credentials(), io.umask(), FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()), io.trustedStreams(), out, err, ok) &&
      Published(old(io.stdout()), old(io.stderr()), io.stdout(), io.stderr(), io.trustedStreams(), out, err, ok, exit)
  }

  function SpecialSourceBackup(raw: S.CpCmdRaw, source: string, target: string, tm: Metadata): bool {
    raw.policy.force && BackupMode(raw) != "off" && source == target && tm.ok && !tm.value.isDir && !tm.value.isSymlink
  }
  function WithoutBackup(raw: S.CpCmdRaw): S.CpCmdRaw {
    raw.(policy := raw.policy.(creation := raw.policy.creation.(backup := raw.policy.creation.backup.(enabled := false))))
  }
  function MemoryExhausted(): BW.Bytes { "cp: memory exhausted\n" }

  opaque ghost predicate SingleTargetFields(raw: S.CpCmdRaw, source: string, target: string, tm: Metadata, cwd: string,
                                            before: BW.FileSystem, after: BW.FileSystem, props: map<string,string>, now: int,
                                            credentials: BW.ProcessCredentials, mask: bv32, provider: FilesystemProvider, streams: StreamProvider,
                                            reported: (BW.Bytes,BW.Bytes,bool), observed: (string,int)) {
    var out,err,ok := reported.0,reported.1,reported.2;
    if !SpecialSourceBackup(raw,source,target,tm) then
      Batch(raw,[source],target,false,cwd,before,after,props,now,credentials,mask,provider,streams,out,err,ok)
    else BackupSelection(before,provider,target,BackupMode(raw),BackupSuffix(raw),observed.0,observed.1) &&
         (if observed.1 != 0 then after == before && out == [] && err == MemoryExhausted() && !ok
          else Batch(WithoutBackup(raw),[source],observed.0,false,cwd,before,after,props,now,credentials,mask,provider,streams,out,err,ok))
  }

  opaque ghost predicate SingleTarget(raw: S.CpCmdRaw, source: string, target: string, tm: Metadata, cwd: string,
                                      before: BW.FileSystem, after: BW.FileSystem, props: map<string,string>, now: int,
                                      credentials: BW.ProcessCredentials, mask: bv32, provider: FilesystemProvider, streams: StreamProvider,
                                      out: BW.Bytes, err: BW.Bytes, ok: bool) {
    exists observed: (string,int) :: SingleTargetFields(raw,source,target,tm,cwd,before,after,props,now,credentials,mask,provider,streams,(out,err,ok),observed)
  }

  opaque ghost predicate CommandOutcome(raw: S.CpCmdRaw, before: BW.FileSystem, after: BW.FileSystem, cwd: string,
                                        props: map<string,string>, now: int, credentials: BW.ProcessCredentials,
                                        mask: bv32, provider: FilesystemProvider, streams: StreamProvider,
                                        out: BW.Bytes, err: BW.Bytes, ok: bool, tm: Metadata)
    requires |raw.operands| > 0
    requires raw.target.Some? || |raw.operands| > 1
  {
    var target := if raw.target.Some? then raw.target.value else raw.operands[|raw.operands|-1];
    var sources := if raw.target.Some? then raw.operands else raw.operands[..|raw.operands|-1];
    MetadataFields(before, provider, target, true, tm) &&
    (if raw.target.Some? || |sources| > 1 then
       if !tm.ok || !tm.value.isDir then after == before && out == [] &&
                                         err == (if raw.target.Some? then DirectoryError(Q(target), E(if tm.ok then 20 else tm.err))
                                                 else TargetError(Q(target), E(if tm.ok then 20 else tm.err))) && !ok
       else Batch(raw, sources, target, true, cwd, before, after, props, now, credentials, mask, provider, streams, out, err, ok)
     else if raw.policy.creation.parents && (raw.noTarget || !tm.ok || !tm.value.isDir) then
       after == before && out == [] && err == ParentsRequireDirectory() && !ok
     else if !raw.noTarget && tm.ok && tm.value.isDir then Batch(raw,sources,target,true,cwd,before,after,props,now,credentials,mask,provider,streams,out,err,ok)
     else SingleTarget(raw,sources[0],target,tm,cwd,before,after,props,now,credentials,mask,provider,streams,out,err,ok))
  }

  opaque ghost predicate Command(raw: S.CpCmdRaw, before: BW.FileSystem, after: BW.FileSystem, cwd: string,
                                 env: map<string,string>, props: map<string,string>, now: int, credentials: BW.ProcessCredentials,
                                 mask: bv32, provider: FilesystemProvider, streams: StreamProvider,
                                 out: BW.Bytes, err: BW.Bytes, ok: bool) {
    NormalizedCommand(EnvironmentCommand(raw,env),before,after,cwd,props,now,credentials,mask,provider,streams,out,err,ok)
  }

  opaque ghost predicate NormalizedCommand(raw: S.CpCmdRaw, before: BW.FileSystem, after: BW.FileSystem, cwd: string,
                                           props: map<string,string>, now: int, credentials: BW.ProcessCredentials,
                                           mask: bv32, provider: FilesystemProvider, streams: StreamProvider,
                                           out: BW.Bytes, err: BW.Bytes, ok: bool) {
    if raw.mode == S.Help then after == before && out == HelpText() && err == [] && ok
    else if raw.mode == S.Version then after == before && out == VersionText() && err == [] && ok
    else if raw.error != S.NoError then after == before && out == [] && err == ConfigurationDiagnostic(raw.error) && !ok
    else if |raw.operands| == 0 then after == before && out == [] && err == Missing() && !ok
    else if raw.target.None? && |raw.operands| == 1 then after == before && out == [] && err == MissingDestination(Q(raw.operands[0])) && !ok
    else if raw.noTarget && |raw.operands| > 2 then after == before && out == [] && err == Extra(C.QuoteArgumentResult(Utf8.Encode(raw.operands[2]))) && !ok
    else
      exists tm: Metadata :: CommandOutcome(raw,before,after,cwd,props,now,credentials,mask,provider,streams,out,err,ok,tm)
  }
}
