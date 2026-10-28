include "RmdirSchema.dfy"
include "../../../core/IO.dfy"
include "../../../core/Utf8.dfy"
include "RmdirPathSpec.dfy"
include "../Impl/CliSupport.dfy"

module RmdirSpec {
  import BenchIO
  import opened BenchWorld
  import C = IOContract
  import Errno = Errnos
  import S = RmdirSchema
  import Path = RmdirPathSpec
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

  function FailureTextPart1(): BenchWorld.Bytes
  {
    "rmdir: failed to remove "
  }

  function FailureTextPart2(): BenchWorld.Bytes
  {
    "directory "
  }

  function FailureTextPart3(): BenchWorld.Bytes
  {
    ""
  }

  function FailureTextPart4(): BenchWorld.Bytes
  {
    ": "
  }

  function FailureTextPart5(): BenchWorld.Bytes
  {
    "Symbolic link not followed"
  }

  function FailureTextPart6(): BenchWorld.Bytes
  {
    "\n"
  }

  function FailureText(parent: bool, err: int, custom: bool,
                       quoted: Bytes, reason: string): Bytes
  {
    FailureTextPart1() +
    (if parent && err != Errno.ENOTDIR then FailureTextPart2() else FailureTextPart3()) + quoted +
    FailureTextPart4() + (if custom then FailureTextPart5() else Utf8.Encode(reason)) + FailureTextPart6()
  }

  function ShortOptionText(ch: Bytes): Bytes {
    "rmdir: invalid option -- '" + ch + "'\nTry 'rmdir --help' for more information.\n"
  }

  function ParseErrorTextPart1(): BenchWorld.Bytes
  {
    "--p"
  }

  function ParseErrorTextPart2(): BenchWorld.Bytes
  {
    "--pa"
  }

  function ParseErrorTextPart3(): BenchWorld.Bytes
  {
    "--pat"
  }

  function ParseErrorTextPart4(): BenchWorld.Bytes
  {
    "--path"
  }

  function ParseErrorTextPart5(): BenchWorld.Bytes
  {
    "--parents"
  }

  function ParseErrorTextPart6(): BenchWorld.Bytes
  {
    "--verbose"
  }

  function ParseErrorTextPart7(): BenchWorld.Bytes
  {
    "--version"
  }

  function ParseErrorTextPart8(): BenchWorld.Bytes
  {
    "--help"
  }

  function ParseErrorTextPart9(): BenchWorld.Bytes
  {
    "--ignore-fail-on-non-empty"
  }

  function ParseErrorTextPart10(): BenchWorld.Bytes
  {
    "rmdir: option '"
  }

  function ParseErrorTextPart11(): BenchWorld.Bytes
  {
    "' doesn't allow an argument\n"
  }

  function ParseErrorTextPart12(): BenchWorld.Bytes
  {
    "Try 'rmdir --help' for more information.\n"
  }

  function ParseErrorTextPart13(): BenchWorld.Bytes
  {
    "' is ambiguous; possibilities:"
  }

  function ParseErrorTextPart14(): BenchWorld.Bytes
  {
    "--"
  }

  function ParseErrorTextPart15(): BenchWorld.Bytes
  {
    " '--ignore-fail-on-non-empty' '--path' '--parents' '--verbose' '--help' '--version'\n"
  }

  function ParseErrorTextPart16(): BenchWorld.Bytes
  {
    " '--verbose' '--version'\n"
  }

  function ParseErrorTextPart17(): BenchWorld.Bytes
  {
    "rmdir: unrecognized option '"
  }

  function ParseErrorTextPart18(): BenchWorld.Bytes
  {
    "'\nTry 'rmdir --help' for more information.\n"
  }

  function ParseErrorText(e: CliTypes.ParseError): Bytes
  {
    var end := CliModel.FindChar(e.rawToken, '=');
    var name := if end < 0 then e.rawToken else e.rawToken[..end];
    var full := if name in {ParseErrorTextPart1(), ParseErrorTextPart2(), ParseErrorTextPart3(), ParseErrorTextPart4()} then ParseErrorTextPart4()
                else if CliModel.HasPrefix(ParseErrorTextPart5(), name) then ParseErrorTextPart5()
                else if CliModel.HasPrefix(ParseErrorTextPart6(), name) then ParseErrorTextPart6()
                else if CliModel.HasPrefix(ParseErrorTextPart7(), name) then ParseErrorTextPart7()
                else if CliModel.HasPrefix(ParseErrorTextPart8(), name) then ParseErrorTextPart8()
                else if CliModel.HasPrefix(ParseErrorTextPart9(), name) then ParseErrorTextPart9()
                else name;
    if e.kind == CliTypes.UnexpectedValue then
      ParseErrorTextPart10() + Utf8.Encode(full) + ParseErrorTextPart11() +
      ParseErrorTextPart12()
    else if e.kind == CliTypes.Ambiguous then
      ParseErrorTextPart10() + Utf8.Encode(e.rawToken) +
      ParseErrorTextPart13() +
      (if name == ParseErrorTextPart14() then
         ParseErrorTextPart15()
       else ParseErrorTextPart16()) +
      ParseErrorTextPart12()
    else
      ParseErrorTextPart17() + Utf8.Encode(e.rawToken) +
      ParseErrorTextPart18()
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

  predicate HasParent(path: string) {
    exists i, j :: 0 <= i < j < |path| && path[i] == '/' && path[j] != '/'
  }

  ghost predicate ParentRelation(path: string, parent: string) {
    HasParent(path) && Path.DirnameRelation(path, parent)
  }

  datatype ObservationContext = ObservationContext(
    ghost failures: (NativeFailureRequest) -> int,
    ghost handles: map<int, DirHandleState>)

  ghost function ObservationContextFor(io: BenchIO.IO): ObservationContext
    reads io.trustedNativeFailuresRegion, io.dirHandlesRegion
  {
    ObservationContext(io.trustedNativeFailures(), io.dirHandles())
  }

  // GNU directory_status preserves the read result across cleanup-close errors.
  ghost predicate NonemptyObservation(context: ObservationContext,
                                      fs: FileSystem, path: string, nonempty: bool) {
    exists linkOk: bool, link: bool, linkErr: int ::
      C.IsSymlinkSpec(fs, context.failures, path, linkOk, link, linkErr) &&
      if linkOk && link then !nonempty
      else exists openState: map<int, DirHandleState>,
             handle: int, openOk: bool, openErr: int ::
             C.OpenDirSpec(fs, context.handles, context.failures, openState,
                           path, false, openOk, handle, openErr) &&
             (if !openOk then !nonempty else
              exists afterRead: map<int, DirHandleState>, more: bool, name: string,
                kind: DirectoryEntryKind, readErr: int,
                closeOk: bool, closeErr: int ::
                C.ReadDirSpec(fs, openState, context.failures, afterRead,
                              handle, more, name, kind, readErr) &&
                C.CloseDirSpec(afterRead, context.failures, context.handles,
                               handle, closeOk, closeErr) &&
                nonempty == (more && readErr == 0))
  }

  ghost predicate IgnoredFailure(context: ObservationContext, raw: S.RmdirCmdRaw, fs: FileSystem,
                                 path: string, err: int, ignored: bool) {
    if !raw.ignoreNonempty then !ignored
    else if KnownNonempty(err) then ignored
    else if MayBeNonempty(err) then NonemptyObservation(context, fs, path, ignored)
    else !ignored
  }

  // GNU only strips the diagnostic operand after the stat test succeeds.
  ghost predicate FailureDisplay(context: ObservationContext, fs: FileSystem, path: string, parent: bool,
                                 err: int, display: string, custom: bool) {
    if parent || err != Errno.ENOTDIR || !C.HasTrailingSlash(path) then
      display == path && !custom
    else exists statOk: bool, directory: bool, statErr: int ::
           C.IsDirectorySpec(fs, context.failures, path, true, statOk, directory, statErr) &&
           if (!statOk && statErr != Errno.ENOTDIR) || (statOk && directory) then
             exists stripped: string, linkOk: bool, link: bool, linkErr: int ::
               Trimmed(path, stripped) &&
               C.IsSymlinkSpec(fs, context.failures, stripped, linkOk, link, linkErr) &&
               custom == (linkOk && link) && display == (if custom then path else stripped)
           else display == path && !custom
  }

  datatype Removal = Removal(path: string, parent: bool, before: FileSystem,
                             after: FileSystem, err: int, ignored: bool, display: string, custom: bool)

  ghost predicate RemovalRelation(context: ObservationContext, raw: S.RmdirCmdRaw, now: int,
                                  trusted: (TrustedFilesystemRequest) -> TrustedFilesystemResult, r: Removal) {
    C.RemoveDirectorySpec(r.before, now, trusted, r.after, r.path, r.err == 0, r.err) &&
    (if r.err == 0 then !r.ignored && !r.custom && r.display == r.path
     else (IgnoredFailure(context, raw, r.after, r.path, r.err, r.ignored) &&
           (if r.ignored then !r.custom && r.display == r.path
            else FailureDisplay(context, r.after, r.path, r.parent, r.err, r.display, r.custom))))
  }

  ghost function OutputChunk(raw: S.RmdirCmdRaw, r: Removal): Bytes {
    if raw.verbose then AttemptText(C.QuoteafPathResult(r.path)) else []
  }

  ghost function ErrorChunk(r: Removal): Bytes
  {
    if r.err == 0 || r.ignored then [] else
    FailureText(r.parent, r.err, r.custom, C.QuoteafPathResult(r.display),
                C.CLocaleErrnoTextResult(r.err))
  }

  ghost predicate BytePartition(parts: seq<Bytes>, whole: Bytes, cuts: seq<nat>) {
    |cuts| == |parts| + 1 && cuts[0] == 0 && cuts[|parts|] == |whole| &&
    (forall i {:trigger cuts[i]} :: 0 <= i < |parts| ==>
                                      cuts[i] <= cuts[i + 1] <= |whole| && whole[cuts[i]..cuts[i + 1]] == parts[i])
  }

  ghost predicate ChainPrefix(context: ObservationContext, raw: S.RmdirCmdRaw, path: string, now: int,
                              trusted: (TrustedFilesystemRequest) -> TrustedFilesystemResult, rs: seq<Removal>) {
    (forall i :: 0 <= i < |rs| ==> RemovalRelation(context, raw, now, trusted, rs[i])) &&
    (|rs| > 0 ==> rs[0].path == path && !rs[0].parent) &&
    (forall i {:trigger rs[i]} :: 0 < i < |rs| ==>
                                    rs[i].parent && rs[i - 1].err == 0 && raw.parents &&
                                    ParentRelation(rs[i - 1].path, rs[i].path) && rs[i - 1].after == rs[i].before)
  }

  ghost predicate {:isolate_assertions} ChainWitness(context: ObservationContext, raw: S.RmdirCmdRaw, path: string, now: int,
                                                     trusted: (TrustedFilesystemRequest) -> TrustedFilesystemResult,
                                                     before: FileSystem, after: FileSystem, out: Bytes, error: Bytes, good: bool,
                                                     rs: seq<Removal>, outCuts: seq<nat>, errCuts: seq<nat>) {
    |rs| > 0 && ChainPrefix(context, raw, path, now, trusted, rs) &&
    rs[0].before == before && rs[|rs| - 1].after == after &&
    (rs[|rs| - 1].err != 0 || !raw.parents || !HasParent(rs[|rs| - 1].path)) &&
    good == (forall i :: 0 <= i < |rs| ==> rs[i].err == 0 || rs[i].ignored) &&
    BytePartition(seq(|rs|, i requires 0 <= i < |rs| => OutputChunk(raw, rs[i])), out, outCuts) &&
    BytePartition(seq(|rs|, i requires 0 <= i < |rs| => ErrorChunk(rs[i])), error, errCuts)
  }

  ghost predicate ChainEffect(context: ObservationContext, raw: S.RmdirCmdRaw, path: string, now: int,
                              trusted: (TrustedFilesystemRequest) -> TrustedFilesystemResult,
                              before: FileSystem, after: FileSystem, out: Bytes, error: Bytes, good: bool) {
    exists rs: seq<Removal>, outCuts: seq<nat>, errCuts: seq<nat> ::
      ChainWitness(context, raw, path, now, trusted, before, after, out, error, good,
                   rs, outCuts, errCuts)
  }

  ghost predicate BatchWitness(context: ObservationContext, raw: S.RmdirCmdRaw, paths: seq<string>, now: int,
                               trusted: (TrustedFilesystemRequest) -> TrustedFilesystemResult,
                               before: FileSystem, after: FileSystem, out: Bytes, error: Bytes, good: bool,
                               states: seq<FileSystem>, outputs: seq<Bytes>, errors: seq<Bytes>,
                               goods: seq<bool>, outCuts: seq<nat>, errCuts: seq<nat>) {
    |states| == |paths| + 1 && |outputs| == |paths| && |errors| == |paths| &&
    |goods| == |paths| && states[0] == before && states[|paths|] == after &&
    (forall i :: 0 <= i < |paths| ==>
                   ChainEffect(context, raw, paths[i], now, trusted, states[i], states[i + 1],
                               outputs[i], errors[i], goods[i])) &&
    good == (forall i :: 0 <= i < |goods| ==> goods[i]) &&
    BytePartition(outputs, out, outCuts) && BytePartition(errors, error, errCuts)
  }

  ghost predicate BatchEffect(context: ObservationContext, raw: S.RmdirCmdRaw, now: int,
                              trusted: (TrustedFilesystemRequest) -> TrustedFilesystemResult,
                              before: FileSystem, after: FileSystem, out: Bytes, error: Bytes, good: bool) {
    exists states: seq<FileSystem>, outputs: seq<Bytes>, errors: seq<Bytes>,
      goods: seq<bool>, outCuts: seq<nat>, errCuts: seq<nat> ::
      BatchWitness(context, raw, raw.operands, now, trusted, before, after, out, error,
                   good, states, outputs, errors, goods, outCuts, errCuts)
  }

  function WriteErrorTextPart1(): BenchWorld.Bytes
  {
    "rmdir: write error: "
  }

  function WriteErrorTextPart2(): BenchWorld.Bytes
  {
    "\n"
  }

  function WriteErrorText(reason: string): Bytes
  {
    WriteErrorTextPart1() + Utf8.Encode(reason) + WriteErrorTextPart2()
  }

  function PriorWriteErrorText(): Bytes {
    "rmdir: write error\n"
  }

  ghost predicate StreamResults(beforeOut: Bytes, afterOut: Bytes,
                                beforeErr: Bytes, afterErr: Bytes,
                                observations: (TrustedStreamRequest) -> TrustedStreamResult,
                                output: Bytes, diagnostics: Bytes, removalExit: int, exit: int) {
    var outObservation := observations(StreamWriteStdout(beforeOut, output));
    outObservation.StreamWriteResult? &&
    var finalDiagnostic := diagnostics + (if outObservation.err == 0 then []
                                          else if |diagnostics| != 0 then PriorWriteErrorText()
                                          else WriteErrorText(C.CLocaleErrnoTextResult(outObservation.err)));
    var errObservation := observations(StreamWriteStderr(beforeErr, finalDiagnostic));
    errObservation.StreamWriteResult? &&
    C.WriteStdoutSpec(beforeOut, observations, afterOut, output,
                      outObservation.committed, outObservation.err) &&
    C.WriteStderrSpec(beforeErr, observations, afterErr, finalDiagnostic,
                      errObservation.committed, errObservation.err) &&
    exit == (if removalExit == 0 && outObservation.err == 0 && errObservation.err == 0 then 0 else 1)
  }

  twostate predicate Spec(raw: S.RmdirCmdRaw, io: BenchIO.IO, exit: int)
    reads io.fsRegion, io.stdoutRegion, io.stderrRegion, io.nowRegion,
          io.trustedFilesystemRegion, io.trustedStreamsRegion, io.trustedNativeFailuresRegion, io.dirHandlesRegion
  {
    io.dirHandles() == old(io.dirHandles()) &&
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
           BatchEffect(old(ObservationContextFor(io)), raw, io.now(), io.trustedFilesystem(), old(io.fs()), io.fs(),
                       out, error, good) &&
           StreamResults(old(io.stdout()), io.stdout(), old(io.stderr()), io.stderr(),
                         io.trustedStreams(), out, error, if good then 0 else 1, exit)
  }
}
