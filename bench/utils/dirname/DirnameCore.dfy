include "../../core/IOContract.dfy"
include "../../core/World.dfy"
include "../../core/IO.dfy"
include "../../core/Utf8.dfy"
include "DirnameSchema.dfy"
include "DirnameSpec.dfy"

module DirnameCore {
  import StreamContract = IOContract

  import Utf8 = Utf8Semantics
  import BenchIO
  import BenchWorld
  import Schema = DirnameSchema
  import Spec = DirnameSpec

  datatype DirnameMode = ModeRun | ModeHelp | ModeVersion

  datatype DirnameCmd = DirnameCmd(
    mode: DirnameMode,
    zeroTerminated: bool,
    operands: seq<string>
  )

  function Command(raw: Schema.DirnameCmdRaw): DirnameCmd
  {
    var mode :=
      if raw.seenHelp &&
         (!raw.seenVersion || raw.helpTokenIndex <= raw.versionTokenIndex) then
        ModeHelp
      else if raw.seenVersion then
        ModeVersion
      else
        ModeRun;
    DirnameCmd(mode, raw.seenZero, raw.operands)
  }

  ghost predicate TrimmedSummary(path: string, trimmed: string)
  {
    if |path| == 0 then
      trimmed == ""
    else if forall i :: 0 <= i < |path| ==> path[i] == '/' then
      trimmed == "/"
    else
      exists end: int ::
        0 < end <= |path| &&
        trimmed == path[..end] &&
        path[end - 1] != '/' &&
        forall i :: end <= i < |path| ==> path[i] == '/'
  }

  ghost predicate LastSlashSummary(path: string, limit: int, slash: int)
    requires 0 <= limit <= |path|
  {
    -1 <= slash < limit &&
    (slash == -1 ==> forall i :: 0 <= i < limit ==> path[i] != '/') &&
    (0 <= slash ==> path[slash] == '/' && forall i :: slash < i < limit ==> path[i] != '/')
  }

  ghost predicate DirnameValueSummary(path: string, value: string)
  {
    if |path| == 0 then
      value == "."
    else
      exists trimmed: string ::
        TrimmedSummary(path, trimmed) &&
        if trimmed == "/" then
          value == "/"
        else
          exists slash: int ::
            LastSlashSummary(trimmed, |trimmed|, slash) &&
            if slash == -1 then
              value == "."
            else if slash == 0 then
              value == "/"
            else
              TrimmedSummary(trimmed[..slash], value)
  }

  ghost predicate RenderSummary(paths: seq<string>, sep: string, out: string)
    decreases |paths|
  {
    if |paths| == 0 then
      out == ""
    else
      exists prefixOut: string, value: string ::
        RenderSummary(paths[..|paths| - 1], sep, prefixOut) &&
        DirnameValueSummary(paths[|paths| - 1], value) &&
        out == prefixOut + value + sep
  }

  ghost predicate RunOutputSummary(cmd: DirnameCmd, out: string)
  {
    RenderSummary(cmd.operands, if cmd.zeroTerminated then ['\0'] else "\n", out)
  }

  twostate predicate PreparedSummary(raw: Schema.DirnameCmdRaw, io: BenchIO.IO, exit: int, plannedStdout: BenchWorld.Bytes, plannedStderr: BenchWorld.Bytes)

  {
    var cmd := Command(raw);
    if cmd.mode == ModeHelp then
      plannedStdout == old(io.stdout()) + Spec.HelpTextSpec() &&
      plannedStderr == old(io.stderr()) &&
      exit == 0
    else if cmd.mode == ModeVersion then
      plannedStdout == old(io.stdout()) + Spec.VersionTextSpec() &&
      plannedStderr == old(io.stderr()) &&
      exit == 0
    else if |cmd.operands| == 0 then
      plannedStdout == old(io.stdout()) &&
      plannedStderr == old(io.stderr()) + Spec.MissingOperandMessageSpec() &&
      exit == 1
    else
      exists out: string ::
        RunOutputSummary(cmd, out) &&
        plannedStdout == old(io.stdout()) + Utf8.Encode(out) &&
        plannedStderr == old(io.stderr()) &&
        exit == 0
  }

  method Prepare(raw: Schema.DirnameCmdRaw, io: BenchIO.IO) returns (exit: int, plannedOut: BenchWorld.Bytes, plannedErr: BenchWorld.Bytes)

    ensures PreparedSummary(raw, io, exit, old(io.stdout()) + plannedOut, old(io.stderr()) + plannedErr)
    decreases *
  {
    plannedOut := [];
    plannedErr := [];
    ghost var initialStdout := io.stdout();
    ghost var initialStderr := io.stderr();

    var cmd := Command(raw);
    if cmd.mode == ModeHelp {
      var out := Spec.HelpTextSpec();
      plannedOut := plannedOut + out;
      exit := 0;
      return;
    }

    if cmd.mode == ModeVersion {
      var out := Spec.VersionTextSpec();
      plannedOut := plannedOut + out;
      exit := 0;
      return;
    }

    if |cmd.operands| == 0 {
      var err := Spec.MissingOperandMessageSpec();
      plannedErr := plannedErr + err;
      exit := 1;
      return;
    }

    var out := BuildRunOutput(cmd);
    plannedOut := plannedOut + Utf8.Encode(out);
    exit := 0;
  }

  method BuildRunOutput(cmd: DirnameCmd) returns (out: string)
    requires |cmd.operands| > 0
    ensures RunOutputSummary(cmd, out)
    decreases *
  {
    var sep := if cmd.zeroTerminated then ['\0'] else "\n";
    out := "";
    var i := 0;
    while i < |cmd.operands|
      invariant 0 <= i <= |cmd.operands|
      invariant RenderSummary(cmd.operands[..i], sep, out)
      decreases |cmd.operands| - i
    {
      var value := ComputeDirnameValue(cmd.operands[i]);
      out := out + value + sep;
      i := i + 1;
      assert cmd.operands[..i] == cmd.operands[..i - 1] + [cmd.operands[i - 1]];
      assert RenderSummary(cmd.operands[..i], sep, out);
    }
    assert cmd.operands[..i] == cmd.operands;
  }

  method ComputeDirnameValue(path: string) returns (value: string)
    ensures DirnameValueSummary(path, value)
    decreases *
  {
    if |path| == 0 {
      value := ".";
      return;
    }

    var trimmed := TrimTrailingSlashes(path);
    if trimmed == "/" {
      value := "/";
      assert TrimmedSummary(path, trimmed);
      return;
    }

    var slash := LastSlashIndex(trimmed, |trimmed|);
    if slash < 0 {
      value := ".";
      assert TrimmedSummary(path, trimmed);
      assert LastSlashSummary(trimmed, |trimmed|, slash);
      return;
    }

    if slash == 0 {
      value := "/";
      assert TrimmedSummary(path, trimmed);
      assert LastSlashSummary(trimmed, |trimmed|, slash);
      return;
    }

    value := TrimTrailingSlashes(trimmed[..slash]);
    assert TrimmedSummary(path, trimmed);
    assert LastSlashSummary(trimmed, |trimmed|, slash);
    assert TrimmedSummary(trimmed[..slash], value);
  }

  method TrimTrailingSlashes(path: string) returns (trimmed: string)
    ensures TrimmedSummary(path, trimmed)
    decreases *
  {
    if |path| == 0 {
      trimmed := "";
      return;
    }

    var allSlash := true;
    var i := 0;
    while i < |path|
      invariant 0 <= i <= |path|
      invariant allSlash ==> forall j :: 0 <= j < i ==> path[j] == '/'
      invariant !allSlash ==> exists j :: 0 <= j < i && path[j] != '/'
      decreases |path| - i
    {
      if path[i] != '/' {
        allSlash := false;
      }
      i := i + 1;
    }

    if allSlash {
      trimmed := "/";
      return;
    }

    var end := |path|;
    while 0 < end && path[end - 1] == '/'
      invariant 0 < end <= |path|
      invariant forall j :: end <= j < |path| ==> path[j] == '/'
      invariant exists j :: 0 <= j < end && path[j] != '/'
      decreases end
    {
      end := end - 1;
    }

    trimmed := path[..end];
  }

  method LastSlashIndex(path: string, limit: int) returns (slash: int)
    requires 0 <= limit <= |path|
    ensures LastSlashSummary(path, limit, slash)
    decreases *
  {
    slash := -1;
    var i := limit;
    while 0 < i && slash == -1
      invariant 0 <= i <= limit
      invariant -1 <= slash < limit
      invariant slash == -1 ==> forall j :: i <= j < limit ==> path[j] != '/'
      invariant 0 <= slash ==> path[slash] == '/'
      invariant 0 <= slash ==> forall j :: slash < j < limit ==> path[j] != '/'
      decreases i
    {
      i := i - 1;
      if path[i] == '/' {
        assert forall j :: i < j < limit ==> path[j] != '/';
        slash := i;
      }
    }
    if slash == -1 {
      assert forall j :: 0 <= j < limit ==> path[j] != '/';
    } else {
      assert 0 <= slash < limit;
      assert path[slash] == '/';
      assert forall j :: slash < j < limit ==> path[j] != '/';
    }
  }

  twostate predicate CoreSummary(raw: Schema.DirnameCmdRaw, io: BenchIO.IO, exit: int)
    reads io.stdoutRegion, io.stderrRegion
  {
    exists out: BenchWorld.Bytes, diagnostics: BenchWorld.Bytes, normalExit: int ::
      PreparedSummary(raw, io, normalExit,
        old(io.stdout()) + out, old(io.stderr()) + diagnostics) &&
      Spec.Emission(raw, io, out, diagnostics, normalExit, exit)
  }

  method Flush(io: BenchIO.IO, out: BenchWorld.Bytes,
    diagnostics: BenchWorld.Bytes, normalExit: int) returns (exit: int)
    modifies io.stdoutRegion, io.stderrRegion
    ensures Spec.EmitFields(old(io.trustedStreams()), old(io.stdout()), old(io.stderr()),
      io.stdout(), io.stderr(), out, diagnostics, normalExit, exit)
  {
    var outErr := 0;
    if out != [] {
      var written := io.WriteStdout(out);
      outErr := StreamContract.ResultErrno(written);
    }
    var errors := diagnostics;
    if outErr != 0 {
      var message := io.GetCLocaleErrnoText(outErr);
      errors := errors + Spec.StreamWriteErrorMessage(message);
    }
    assert errors == diagnostics + (if outErr == 0 then [] else
      Spec.StreamWriteErrorMessage(StreamContract.CLocaleErrnoTextResult(outErr)));
    var errErr := 0;
    if errors != [] {
      var diagnosed := io.WriteStderr(errors);
      errErr := StreamContract.ResultErrno(diagnosed);
      assert StreamContract.WriteStderrSpec(old(io.stderr()), io.trustedStreams(), io.stderr(),
        errors, StreamContract.WriteResultCommitted(diagnosed), errErr);
    }
    exit := if outErr != 0 || errErr != 0 then 1 else normalExit;
  }

  method RunCore(raw: Schema.DirnameCmdRaw, io: BenchIO.IO) returns (exit: int)
    modifies io.stdoutRegion, io.stderrRegion
    ensures CoreSummary(raw, io, exit)
    decreases *
  {
    var normalExit, out, diagnostics := Prepare(raw, io);

    assert PreparedSummary(raw, io, normalExit, old(io.stdout()) + out, old(io.stderr()) + diagnostics);
    if Spec.Emits(raw) {
      exit := Flush(io, out, diagnostics, normalExit);
    } else {
      exit := normalExit;
    }
    assert PreparedSummary(raw, io, normalExit, old(io.stdout()) + out, old(io.stderr()) + diagnostics);
    assert Spec.Emission(raw, io, out, diagnostics, normalExit, exit);
  }
}
