include "../../core/Errno.dfy"
include "../../core/World.dfy"
include "../../core/IO.dfy"
include "../../core/IOContract.dfy"
include "../../core/StringEscaping.dfy"
include "TeeSchema.dfy"

module TeeSpec {

  const ReadErrorMessageSpecText0: BenchWorld.Bytes := "tee: "

  const ReadErrorMessageSpecText1: BenchWorld.Bytes := ": "

  const ReadErrorMessageSpecText2: BenchWorld.Bytes := "\n"

  const WriteErrorMessageTextText0: BenchWorld.Bytes := "tee: "

  const WriteErrorMessageTextText1: BenchWorld.Bytes := ": "

  const WriteErrorMessageTextText2: BenchWorld.Bytes := "\n"

  const StdinReadErrorTextText0: BenchWorld.Bytes := "tee: read error: "

  const StdinReadErrorTextText1: BenchWorld.Bytes := "\n"

  const WriteErrorTextText0: BenchWorld.Bytes := "tee: 'standard output': "

  const WriteErrorTextText1: BenchWorld.Bytes := "tee: write error: "

  const WriteErrorTextText2: BenchWorld.Bytes := "\n"

  import StreamWorld = BenchWorld
  import StreamContract = IOContract

  import Errno = Errnos
  import BenchIO
  import BenchWorld
  import IOContract
  import Schema = TeeSchema
  import Utf8 = Utf8Semantics
  import SE = StringEscaping




  function HelpTextSpec(): BenchWorld.Bytes
  {
    "Usage: tee [OPTION]... [FILE]...\n"
    + "Copy standard input to each FILE, and also to standard output.\n"
    + "\n"
    + "  -a, --append\n"
    + "         append to the given FILEs, do not overwrite\n"
    + "  -i, --ignore-interrupts\n"
    + "         ignore interrupt signals\n"
    + "  -p\n"
    + "         operate in a more appropriate MODE with pipes\n"
    + "      --output-error[=MODE]\n"
    + "         set behavior on write error.  See MODE below\n"
    + "      --help\n"
    + "         display this help and exit\n"
    + "      --version\n"
    + "         output version information and exit\n"
    + "\n"
    + "MODE determines behavior with write errors on the outputs:\n"
    + "  warn           diagnose errors writing to any output\n"
    + "  warn-nopipe    diagnose errors writing to any output not a pipe\n"
    + "  exit           exit on error writing to any output\n"
    + "  exit-nopipe    exit on error writing to any output not a pipe\n"
    + "The default MODE for the -p option is 'warn-nopipe'.\n"
    + "With \"nopipe\" MODEs, exit immediately if all outputs become broken pipes.\n"
    + "The default operation when --output-error is not specified, is to\n"
    + "exit immediately on error writing to a pipe, and diagnose errors\n"
    + "writing to non pipe outputs.\n"
    + "\n"
    + "Report bugs to: bug-coreutils@gnu.org\n"
    + "GNU coreutils home page: <https://www.gnu.org/software/coreutils/>\n"
    + "General help using GNU software: <https://www.gnu.org/gethelp/>\n"
    + "Report any translation bugs to <https://translationproject.org/team/>\n"
    + "Full documentation <https://www.gnu.org/software/coreutils/tee>\n"
    + "or available locally via: info '(coreutils) tee invocation'\n"
  }

  function VersionTextSpec(): BenchWorld.Bytes
  {
    "tee (GNU coreutils) 9.10.13-2cf49\n"
    + "Copyright (C) 2026 Free Software Foundation, Inc.\n"
    + "License GPLv3+: GNU GPL version 3 or later <https://gnu.org/licenses/gpl.html>.\n"
    + "This is free software: you are free to change and redistribute it.\n"
    + "There is NO WARRANTY, to the extent permitted by law.\n"
    + "\n"
    + "Written by Mike Parker, Richard M. Stallman, and David MacKenzie.\n"
  }

  function ReadErrnoTextSpec(err: BenchWorld.IOError): string
  {
    match err
    case NoSuchFile => "No such file or directory"
    case IsDirectory => "Is a directory"
    case NotDirectory => "Not a directory"
    case PermissionDenied => "Permission denied"
    case InvalidPath => "Too many levels of symbolic links"
    case Other(msg) => msg
    case ReadFailure(_, message, _, _) => message
    case NativeFailure(_, message) => message
    case WriteFailure(_, message, _, _) => message
    case StreamFailure(_, message, _, _) => message
    case TimeParseFailure(message, _, _) => message
  }

  ghost function WriteErrnoTextSpec(err: int): string
  {
    IOContract.CLocaleErrnoTextResult(err)
  }

  ghost function ReadErrorMessageSpec(path: BenchWorld.Path, err: BenchWorld.IOError): BenchWorld.Bytes
  {
    ReadErrorMessageSpecText0 + SE.SpecQuoteFBytes(Utf8.Encode(path)) +
    ReadErrorMessageSpecText1 + Utf8.Encode(ReadErrnoTextSpec(err)) + ReadErrorMessageSpecText2
  }

  ghost function WriteErrorMessageText(path: BenchWorld.Path, reason: string): BenchWorld.Bytes
  {
    WriteErrorMessageTextText0 + SE.SpecQuoteFBytes(Utf8.Encode(path)) +
    WriteErrorMessageTextText1 + Utf8.Encode(reason) + WriteErrorMessageTextText2
  }

  ghost function WriteErrorMessageSpec(path: BenchWorld.Path, err: int): BenchWorld.Bytes
  {
    WriteErrorMessageText(path, WriteErrnoTextSpec(err))
  }

  function CommandSpec(raw: Schema.TeeCmdRaw): Schema.TeeCmd
  {
    var mode :=
      if raw.seenHelp && (!raw.seenVersion || raw.helpTokenIndex <= raw.versionTokenIndex) then
        Schema.ModeHelp
      else if raw.seenVersion then
        Schema.ModeVersion
      else
        Schema.ModeRun;
    Schema.TeeCmd(mode, raw.seenAppend, raw.seenIgnoreInterrupts, raw.operands)
  }

  ghost predicate WriteOneSpecFields(
    append: bool,
    path: BenchWorld.Path,
    input: BenchWorld.Bytes,
    preFs: BenchWorld.FileSystem,
    preProps: map<string, string>,
    preNow: int,
    preCredentials: BenchWorld.ProcessCredentials,
    preTrustedFilesystem: (BenchWorld.TrustedFilesystemRequest) -> BenchWorld.TrustedFilesystemResult,
    fs2: BenchWorld.FileSystem,
    stderr: BenchWorld.Bytes,
    exit: int
  )
  {
    if append then
      exists ok: bool, writeErr: int, committed: nat, stage: BenchWorld.FileWriteStage ::
        IOContract.AppendFileSpec(preFs, preProps, preNow, preCredentials, preTrustedFilesystem,
                                  fs2, path, input, ok, writeErr, committed, stage) &&
        stderr == (if ok then [] else WriteErrorMessageSpec(path, writeErr)) &&
        exit == (if ok then 0 else 1)
    else
      exists ok: bool, writeErr: int, committed: nat, stage: BenchWorld.FileWriteStage ::
        IOContract.WriteFileSpec(preFs, preProps, preNow, preCredentials, preTrustedFilesystem,
                                 fs2, path, input, ok, writeErr, committed, stage) &&
        stderr == (if ok then [] else WriteErrorMessageSpec(path, writeErr)) &&
        exit == (if ok then 0 else 1)
  }

  datatype WriteState = WriteState(
    fs: BenchWorld.FileSystem,
    stderr: BenchWorld.Bytes,
    exit: int
  )

  opaque ghost predicate WriteStepRelation(
    append: bool,
    path: BenchWorld.Path,
    input: BenchWorld.Bytes,
    preProps: map<string, string>,
    preNow: int,
    preCredentials: BenchWorld.ProcessCredentials,
    preTrustedFilesystem: (BenchWorld.TrustedFilesystemRequest) -> BenchWorld.TrustedFilesystemResult,
    before: WriteState,
    after: WriteState
  )
  {
    exists stepErr: BenchWorld.Bytes, stepExit: int ::
      WriteOneSpecFields(append, path, input, before.fs, preProps, preNow, preCredentials,
                         preTrustedFilesystem, after.fs, stepErr, stepExit) &&
      after.stderr == before.stderr + stepErr &&
      after.exit == (if before.exit == 0 && stepExit == 0 then 0 else 1)
  }

  opaque ghost predicate WriteOutputsSpecFields(
    append: bool,
    outputs: seq<BenchWorld.Path>,
    input: BenchWorld.Bytes,
    preFs: BenchWorld.FileSystem,
    preProps: map<string, string>,
    preNow: int,
    preCredentials: BenchWorld.ProcessCredentials,
    preTrustedFilesystem: (BenchWorld.TrustedFilesystemRequest) -> BenchWorld.TrustedFilesystemResult,
    fs2: BenchWorld.FileSystem,
    stderr: BenchWorld.Bytes,
    exit: int
  )
  {
    exists states: seq<WriteState> ::
      |states| == |outputs| + 1 &&
      states[0] == WriteState(preFs, [], 0) &&
      states[|outputs|] == WriteState(fs2, stderr, exit) &&
      forall i {:trigger WriteStepRelation(append, outputs[i], input, preProps, preNow, preCredentials,
                                           preTrustedFilesystem, states[i], states[i + 1])} ::
        0 <= i < |outputs| ==>
          WriteStepRelation(append, outputs[i], input, preProps, preNow, preCredentials,
                            preTrustedFilesystem, states[i], states[i + 1])
  }

  ghost function StdinReadErrorText(reason: string): BenchWorld.Bytes
  {
    StdinReadErrorTextText0 + Utf8.Encode(reason) + StdinReadErrorTextText1
  }

  ghost function StdinReadError(err: int): BenchWorld.Bytes
  {
    StdinReadErrorText(IOContract.CLocaleErrnoTextResult(err))
  }


  ghost function WriteErrorText(raw: Schema.TeeCmdRaw, reason: string): StreamWorld.Bytes
  {
    (if CommandSpec(raw).mode == Schema.ModeRun then WriteErrorTextText0
     else WriteErrorTextText1) + Utf8.Encode(reason) + WriteErrorTextText2
  }

  ghost predicate EmissionOutcomeFields(
    raw: Schema.TeeCmdRaw,
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
                            (if outErr == 0 then [] else WriteErrorText(raw, StreamContract.CLocaleErrnoTextResult(outErr)));
    (if |finalDiagnostics| == 0 then afterErr == beforeErr && errCommitted == 0 && errErr == 0
     else StreamContract.WriteStderrSpec(beforeErr, observations, afterErr, finalDiagnostics, errCommitted, errErr)) &&
    exit == (if outErr != 0 || errErr != 0 then 1 else normalExit)
  }

  ghost predicate EmissionFields(
    raw: Schema.TeeCmdRaw,
    beforeOut: StreamWorld.Bytes, beforeErr: StreamWorld.Bytes,
    afterOut: StreamWorld.Bytes, afterErr: StreamWorld.Bytes,
    observations: (StreamWorld.TrustedStreamRequest) -> StreamWorld.TrustedStreamResult,
    output: StreamWorld.Bytes, diagnostics: StreamWorld.Bytes,
    normalExit: int, exit: int
  )
  {
    exists committed: nat, outErr: int, errCommitted: nat, errErr: int ::
      EmissionOutcomeFields(raw, beforeOut, beforeErr, afterOut, afterErr, observations,
                            output, diagnostics, normalExit, exit,
                            committed, outErr, errCommitted, errErr)
  }
  opaque twostate predicate PreparedSpec(raw: Schema.TeeCmdRaw, io: BenchIO.IO, exit: int, plannedStdout: StreamWorld.Bytes, plannedStderr: StreamWorld.Bytes)
    reads io.fsRegion, io.stdinRegion
  {
    var cmd := CommandSpec(raw);
    if cmd.mode == Schema.ModeHelp then
      io.fs() == old(io.fs()) &&
      io.stdin() == old(io.stdin()) &&
      plannedStdout == old(io.stdout()) + HelpTextSpec() &&
      plannedStderr == old(io.stderr()) &&
      exit == 0
    else if cmd.mode == Schema.ModeVersion then
      io.fs() == old(io.fs()) &&
      io.stdin() == old(io.stdin()) &&
      plannedStdout == old(io.stdout()) + VersionTextSpec() &&
      plannedStderr == old(io.stderr()) &&
      exit == 0
    else
      var read := IOContract.ObservedReadStdinResultFields(old(io.stdin()), old(io.trustedStreams()));
      var input := IOContract.ReadResultData(read);
      exists errOut: BenchWorld.Bytes, writeExit: int ::
        WriteOutputsSpecFields(cmd.append, cmd.outputs, input, old(io.fs()), old(io.props()),
                               old(io.now()), old(io.credentials()), old(io.trustedFilesystem()),
                               io.fs(), errOut, writeExit) &&
        io.stdin() == IOContract.ObservedReadStdinRemainingFields(old(io.stdin()), old(io.trustedStreams())) &&
        plannedStdout == old(io.stdout()) + input &&
        plannedStderr == old(io.stderr()) + errOut +
        (if read.Ok? then [] else StdinReadError(IOContract.ResultErrno(read))) &&
        exit == (if read.Ok? then writeExit else 1)
  }

  twostate predicate Spec(raw: Schema.TeeCmdRaw, io: BenchIO.IO, exit: int)
    reads io.Footprint()
  {
    exists output: StreamWorld.Bytes, diagnostics: StreamWorld.Bytes, normalExit: int ::
      PreparedSpec(raw, io, normalExit, old(io.stdout()) + output, old(io.stderr()) + diagnostics) &&
      EmissionFields(raw, old(io.stdout()), old(io.stderr()), io.stdout(), io.stderr(),
                     io.trustedStreams(), output, diagnostics, normalExit, exit)
  }
}
