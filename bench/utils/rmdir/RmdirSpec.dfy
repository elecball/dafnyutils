include "RmdirSchema.dfy"
include "../../core/IO.dfy"
include "../../core/Utf8.dfy"
include "../../core/PathSpec.dfy"
include "../../core/CliModel.dfy"

module RmdirSpec {
  import BenchIO
  import opened BenchWorld
  import C = IOContract
  import Errno = Errnos
  import S = RmdirSchema
  import Path = MvPathSpec
  import Utf8 = Utf8Semantics
  import CliTypes
  import CliModel

  function HelpText(): Bytes {
    "Usage: rmdir [OPTION]... DIRECTORY...\n" +
    "Remove the DIRECTORY(ies), if they are empty.\n\n" +
    "      --ignore-fail-on-non-empty\n" +
    "         ignore each failure to remove a non-empty directory\n" +
    "  -p, --parents\n" +
    "         remove DIRECTORY and its ancestors;\n" +
    "         e.g., 'rmdir -p a/b' is similar to 'rmdir a/b a'\n" +
    "  -v, --verbose\n" +
    "         output a diagnostic for every directory processed\n" +
    "      --help\n         display this help and exit\n" +
    "      --version\n         output version information and exit\n\n" +
    "Report bugs to: bug-coreutils@gnu.org\n" +
    "GNU coreutils home page: <https://www.gnu.org/software/coreutils/>\n" +
    "General help using GNU software: <https://www.gnu.org/gethelp/>\n" +
    "Report any translation bugs to <https://translationproject.org/team/>\n" +
    "Full documentation <https://www.gnu.org/software/coreutils/rmdir>\n" +
    "or available locally via: info '(coreutils) rmdir invocation'\n"
  }

  function VersionText(): Bytes {
    "rmdir (GNU coreutils) 9.10.13-2cf49\n" +
    "Copyright (C) 2026 Free Software Foundation, Inc.\n" +
    "License GPLv3+: GNU GPL version 3 or later <https://gnu.org/licenses/gpl.html>.\n" +
    "This is free software: you are free to change and redistribute it.\n" +
    "There is NO WARRANTY, to the extent permitted by law.\n\n" +
    "Written by David MacKenzie.\n"
  }

  function MissingOperandText(): Bytes {
    "rmdir: missing operand\nTry 'rmdir --help' for more information.\n"
  }

  function AttemptText(quoted: Bytes): Bytes {
    "rmdir: removing directory, " + quoted + "\n"
  }

  function FailureText(parent: bool, err: int, custom: bool,
                       quoted: Bytes, reason: string): Bytes {
    "rmdir: failed to remove " +
    (if parent && err != Errno.ENOTDIR then "directory " else "") + quoted +
    ": " + (if custom then "Symbolic link not followed" else Utf8.Encode(reason)) + "\n"
  }

  function ShortOptionText(ch: Bytes): Bytes {
    "rmdir: invalid option -- '" + ch + "'\nTry 'rmdir --help' for more information.\n"
  }

  function ParseErrorText(e: CliTypes.ParseError): Bytes {
    var end := CliModel.FindChar(e.rawToken, '=');
    var name := if end < 0 then e.rawToken else e.rawToken[..end];
    var full := if name in {"--p", "--pa", "--pat", "--path"} then "--path"
      else if CliModel.HasPrefix("--parents", name) then "--parents"
      else if CliModel.HasPrefix("--verbose", name) then "--verbose"
      else if CliModel.HasPrefix("--version", name) then "--version"
      else if CliModel.HasPrefix("--help", name) then "--help"
      else if CliModel.HasPrefix("--ignore-fail-on-non-empty", name) then "--ignore-fail-on-non-empty"
      else name;
    if e.kind == CliTypes.UnexpectedValue then
      "rmdir: option '" + Utf8.Encode(full) + "' doesn't allow an argument\n" +
      "Try 'rmdir --help' for more information.\n"
    else if e.kind == CliTypes.Ambiguous then
      "rmdir: option '" + Utf8.Encode(e.rawToken) +
      "' is ambiguous; possibilities:" +
      (if name == "--" then
        " '--ignore-fail-on-non-empty' '--path' '--parents' '--verbose' '--help' '--version'\n"
       else " '--verbose' '--version'\n") +
      "Try 'rmdir --help' for more information.\n"
    else
      "rmdir: unrecognized option '" + Utf8.Encode(e.rawToken) +
      "'\nTry 'rmdir --help' for more information.\n"
  }

  function MayBeNonempty(err: int): bool {
    err in {Errno.EACCES, Errno.EPERM, Errno.EROFS, Errno.EBUSY}
  }

  function KnownNonempty(err: int): bool {
    err == Errno.ENOTEMPTY || err == Errno.EEXIST
  }

  ghost predicate Trimmed(path: string, trimmed: string) {
    if path == "" then trimmed == ""
    else if Path.SlashesOnly(path) then trimmed == "/"
    else exists trailing: string ::
      Path.PathWithoutTrailingSlashes(path, trimmed, trailing)
  }

  ghost predicate HasParent(path: string) {
    exists i, j :: 0 <= i < j < |path| && path[i] == '/' && path[j] != '/'
  }

  ghost predicate ParentRelation(path: string, parent: string) {
    HasParent(path) && Path.DirnameRelation(path, parent)
  }

  // One dot-free enumeration result, including possible open/read failures.
  ghost predicate NonemptyObservation(fs: FileSystem, path: string, nonempty: bool) {
    exists linkOk: bool, link: bool, linkErr: int ::
      C.IsSymlinkContractFields(fs, path, linkOk, link, linkErr) &&
      if linkOk && link then !nonempty
      else exists before: map<int, DirHandleState>, openState: map<int, DirHandleState>,
                  handle: int, openOk: bool, openErr: int ::
        C.OpenDirContractFields(fs, before, path, false, openOk, handle, openErr, openState) &&
        (if !openOk then !nonempty else
          exists after: map<int, DirHandleState>, more: bool, name: string,
                 kind: DirectoryEntryKind, readErr: int ::
            C.ReadDirContractFields(fs, openState, handle, more, name, kind, readErr, after) &&
            nonempty == (more && readErr == 0))
  }

  ghost predicate IgnoredFailure(raw: S.RmdirCmdRaw, fs: FileSystem,
                                 path: string, err: int, ignored: bool) {
    if !raw.ignoreNonempty then !ignored
    else if KnownNonempty(err) then ignored
    else if MayBeNonempty(err) then NonemptyObservation(fs, path, ignored)
    else !ignored
  }

  // GNU only strips the diagnostic operand after the stat test succeeds.
  ghost predicate FailureDisplay(fs: FileSystem, path: string, parent: bool,
                                 err: int, display: string, custom: bool) {
    if parent || err != Errno.ENOTDIR || !C.HasTrailingSlash(path) then
      display == path && !custom
    else exists statOk: bool, directory: bool, statErr: int ::
      C.IsDirectoryStrictContractFields(fs, path, true, statOk, directory, statErr) &&
      if (!statOk && statErr != Errno.ENOTDIR) || (statOk && directory) then
        exists stripped: string, linkOk: bool, link: bool, linkErr: int ::
          Trimmed(path, stripped) &&
          C.IsSymlinkContractFields(fs, stripped, linkOk, link, linkErr) &&
          custom == (linkOk && link) && display == (if custom then path else stripped)
      else display == path && !custom
  }

  datatype Removal = Removal(path: string, parent: bool, before: FileSystem,
    after: FileSystem, err: int, ignored: bool, display: string, custom: bool)

  ghost predicate RemovalRelation(raw: S.RmdirCmdRaw, now: int,
    trusted: (TrustedFilesystemRequest) -> TrustedFilesystemResult, r: Removal) {
    C.RemoveDirectorySpec(r.before, now, trusted, r.after, r.path, r.err == 0, r.err) &&
    (if r.err == 0 then !r.ignored && !r.custom && r.display == r.path
     else (IgnoredFailure(raw, r.after, r.path, r.err, r.ignored) &&
       (if r.ignored then !r.custom && r.display == r.path
        else FailureDisplay(r.after, r.path, r.parent, r.err, r.display, r.custom))))
  }

  ghost function OutputChunk(raw: S.RmdirCmdRaw, r: Removal): Bytes {
    if raw.verbose then AttemptText(C.QuoteafPathResult(r.path)) else []
  }

  ghost function ErrorChunk(r: Removal): Bytes {
    if r.err == 0 || r.ignored then [] else
      FailureText(r.parent, r.err, r.custom, C.QuoteafPathResult(r.display),
                  C.CLocaleErrnoTextResult(r.err))
  }

  ghost predicate BytePartition(parts: seq<Bytes>, whole: Bytes, cuts: seq<nat>) {
    |cuts| == |parts| + 1 && cuts[0] == 0 && cuts[|parts|] == |whole| &&
    (forall i {:trigger cuts[i]} :: 0 <= i < |parts| ==>
      cuts[i] <= cuts[i + 1] <= |whole| && whole[cuts[i]..cuts[i + 1]] == parts[i])
  }

  ghost predicate ChainPrefix(raw: S.RmdirCmdRaw, path: string, now: int,
    trusted: (TrustedFilesystemRequest) -> TrustedFilesystemResult, rs: seq<Removal>) {
    (forall i :: 0 <= i < |rs| ==> RemovalRelation(raw, now, trusted, rs[i])) &&
    (|rs| > 0 ==> rs[0].path == path && !rs[0].parent) &&
    (forall i {:trigger rs[i]} :: 0 < i < |rs| ==>
      rs[i].parent && rs[i - 1].err == 0 && raw.parents &&
      ParentRelation(rs[i - 1].path, rs[i].path) && rs[i - 1].after == rs[i].before)
  }

  ghost predicate {:isolate_assertions} ChainWitness(raw: S.RmdirCmdRaw, path: string, now: int,
    trusted: (TrustedFilesystemRequest) -> TrustedFilesystemResult,
    before: FileSystem, after: FileSystem, out: Bytes, error: Bytes, good: bool,
    rs: seq<Removal>, outCuts: seq<nat>, errCuts: seq<nat>) {
    |rs| > 0 && ChainPrefix(raw, path, now, trusted, rs) &&
    rs[0].before == before && rs[|rs| - 1].after == after &&
    (rs[|rs| - 1].err != 0 || !raw.parents || !HasParent(rs[|rs| - 1].path)) &&
    good == (forall i :: 0 <= i < |rs| ==> rs[i].err == 0 || rs[i].ignored) &&
    BytePartition(seq(|rs|, i requires 0 <= i < |rs| => OutputChunk(raw, rs[i])), out, outCuts) &&
    BytePartition(seq(|rs|, i requires 0 <= i < |rs| => ErrorChunk(rs[i])), error, errCuts)
  }

  ghost predicate ChainEffect(raw: S.RmdirCmdRaw, path: string, now: int,
    trusted: (TrustedFilesystemRequest) -> TrustedFilesystemResult,
    before: FileSystem, after: FileSystem, out: Bytes, error: Bytes, good: bool) {
    exists rs: seq<Removal>, outCuts: seq<nat>, errCuts: seq<nat> ::
      ChainWitness(raw, path, now, trusted, before, after, out, error, good,
                   rs, outCuts, errCuts)
  }

  ghost predicate BatchWitness(raw: S.RmdirCmdRaw, paths: seq<string>, now: int,
    trusted: (TrustedFilesystemRequest) -> TrustedFilesystemResult,
    before: FileSystem, after: FileSystem, out: Bytes, error: Bytes, good: bool,
    states: seq<FileSystem>, outputs: seq<Bytes>, errors: seq<Bytes>,
    goods: seq<bool>, outCuts: seq<nat>, errCuts: seq<nat>) {
    |states| == |paths| + 1 && |outputs| == |paths| && |errors| == |paths| &&
    |goods| == |paths| && states[0] == before && states[|paths|] == after &&
    (forall i :: 0 <= i < |paths| ==>
      ChainEffect(raw, paths[i], now, trusted, states[i], states[i + 1],
                  outputs[i], errors[i], goods[i])) &&
    good == (forall i :: 0 <= i < |goods| ==> goods[i]) &&
    BytePartition(outputs, out, outCuts) && BytePartition(errors, error, errCuts)
  }

  ghost predicate BatchEffect(raw: S.RmdirCmdRaw, now: int,
    trusted: (TrustedFilesystemRequest) -> TrustedFilesystemResult,
    before: FileSystem, after: FileSystem, out: Bytes, error: Bytes, good: bool) {
    exists states: seq<FileSystem>, outputs: seq<Bytes>, errors: seq<Bytes>,
           goods: seq<bool>, outCuts: seq<nat>, errCuts: seq<nat> ::
      BatchWitness(raw, raw.operands, now, trusted, before, after, out, error,
                    good, states, outputs, errors, goods, outCuts, errCuts)
  }

  function WriteErrorText(reason: string): Bytes {
    "rmdir: write error: " + Utf8.Encode(reason) + "\n"
  }

  ghost predicate StreamResults(beforeOut: Bytes, afterOut: Bytes,
    beforeErr: Bytes, afterErr: Bytes,
    observations: (TrustedStreamRequest) -> TrustedStreamResult,
    output: Bytes, diagnostics: Bytes, removalExit: int, exit: int) {
    var outObservation := observations(StreamWriteStdout(beforeOut, output));
    outObservation.StreamWriteResult? &&
    var finalDiagnostic := diagnostics + (if outObservation.err == 0 then []
      else WriteErrorText(C.CLocaleErrnoTextResult(outObservation.err)));
    var errObservation := observations(StreamWriteStderr(beforeErr, finalDiagnostic));
    errObservation.StreamWriteResult? &&
    C.WriteStdoutSpec(beforeOut, observations, afterOut, output, ReturnError,
                      outObservation.committed, outObservation.err) &&
    C.WriteStderrSpec(beforeErr, observations, afterErr, finalDiagnostic, ReturnError,
                      errObservation.committed, errObservation.err) &&
    exit == (if removalExit == 0 && outObservation.err == 0 && errObservation.err == 0 then 0 else 1)
  }

  twostate predicate Spec(raw: S.RmdirCmdRaw, io: BenchIO.IO, exit: int)
    reads io.fsRegion, io.stdoutRegion, io.stderrRegion, io.nowRegion,
          io.trustedFilesystemRegion, io.trustedStreamsRegion
  {
    if raw.mode == S.ModeHelp then
      StreamResults(old(io.stdout()), io.stdout(), old(io.stderr()), io.stderr(),
                    io.trustedStreams(), HelpText(), [], 0, exit)
    else if raw.mode == S.ModeVersion then
      StreamResults(old(io.stdout()), io.stdout(), old(io.stderr()), io.stderr(),
                    io.trustedStreams(), VersionText(), [], 0, exit)
    else if |raw.operands| == 0 then
      StreamResults(old(io.stdout()), io.stdout(), old(io.stderr()), io.stderr(),
                    io.trustedStreams(), [], MissingOperandText(), 1, exit)
    else exists out: Bytes, error: Bytes, good: bool ::
      BatchEffect(raw, io.now(), io.trustedFilesystem(), old(io.fs()), io.fs(),
                  out, error, good) &&
      StreamResults(old(io.stdout()), io.stdout(), old(io.stderr()), io.stderr(),
                    io.trustedStreams(), out, error, if good then 0 else 1, exit)
  }
}
