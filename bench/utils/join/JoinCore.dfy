include "JoinPlanCore.dfy"

module JoinCore {
  import S = JoinSchema
  import Spec = JoinSpec
  import Plan = JoinPlanCore
  import BW = BenchWorld
  import BenchIO
  import Errno = Errnos
  import C = IOContract
  import R = Results

  method Probe(io: BenchIO.IO, operand: string) returns (result: BW.IOResult<BW.Bytes>)
    ensures result == Spec.Probe(io.fs(),io.trustedStreams(),operand)
  {
    if operand == "-" { result := R.Ok([]); }
    else { result := io.ProbeReadFile(operand); }
  }
  method Read(io: BenchIO.IO, operand: string) returns (result: BW.IOResult<BW.Bytes>)
    modifies io.stdinRegion
    ensures result == Spec.ReadInput(old(io.fs()),old(io.trustedStreams()),old(io.stdin()),operand)
    ensures io.stdin() == Spec.Remaining(old(io.trustedStreams()),old(io.stdin()),operand)
  {
    if operand == "-" { result := io.ReadStdin(); }
    else { result := io.ReadFile(operand); }
  }
  method Prepare(cmd: S.JoinCmdRaw, io: BenchIO.IO) returns (output: BW.Bytes, diagnostic: BW.Bytes, exit: int)
    modifies io.stdinRegion
    ensures Spec.Prepared(cmd,io,output,diagnostic,exit)
  {
    output := []; diagnostic := []; exit := 0;
    var mode := Spec.Mode(cmd);
    if mode == S.Help {
      output := Spec.HelpText();
      assert Spec.Prepared(cmd,io,output,diagnostic,exit) by { reveal Spec.Prepared(); }
      return;
    }
    if mode == S.Version {
      output := Spec.VersionText();
      assert Spec.Prepared(cmd,io,output,diagnostic,exit) by { reveal Spec.Prepared(); }
      return;
    }
    if mode.Error? {
      diagnostic := Spec.ArgumentMessage(mode.error); exit := 1;
      assert Spec.Prepared(cmd,io,output,diagnostic,exit) by { reveal Spec.Prepared(); }
      return;
    }
    var op1 := cmd.operands[0]; var op2 := cmd.operands[1];
    var p1 := Probe(io,op1);
    if p1.Err? {
      var reason := io.GetCLocaleErrnoText(C.ResultErrno(p1));
      diagnostic := Spec.FileError(op1,reason); exit := 1;
      assert Spec.Prepared(cmd,io,output,diagnostic,exit) by { reveal Spec.Prepared(); }
      return;
    }
    var p2 := Probe(io,op2);
    if p2.Err? {
      var reason := io.GetCLocaleErrnoText(C.ResultErrno(p2));
      diagnostic := Spec.FileError(op2,reason); exit := 1;
      assert Spec.Prepared(cmd,io,output,diagnostic,exit) by { reveal Spec.Prepared(); }
      return;
    }
    if op1 == "-" && op2 == "-" {
      if cmd.mode == S.RunWithRangeError {
        var reason := io.GetCLocaleErrnoText(Errno.ERANGE);
        diagnostic := Spec.BothStdinError(reason);
      } else { diagnostic := Spec.BothStdin; }
      exit := 1;
      assert Spec.Prepared(cmd,io,output,diagnostic,exit) by { reveal Spec.Prepared(); }
      return;
    }
    var first := Read(io,op1);
    if Spec.FirstReadAborts(cmd,first) {
      var reason := io.GetCLocaleErrnoText(C.ResultErrno(first));
      diagnostic := Spec.ReadError(reason); exit := 1;
      assert Spec.Prepared(cmd,io,output,diagnostic,exit) by { reveal Spec.Prepared(); }
      return;
    }
    var second := Read(io,op2);
    output, diagnostic, exit := Plan.Join(cmd,io,first,second);
    assert Spec.Prepared(cmd,io,output,diagnostic,exit) by { reveal Spec.Prepared(); }
  }
  method Emit(io: BenchIO.IO, output: BW.Bytes, diagnostic: BW.Bytes, normal: int) returns (exit: int)
    modifies io.stdoutRegion, io.stderrRegion
    ensures Spec.Emitted(old(io.trustedStreams()),old(io.stdout()),old(io.stderr()),io.stdout(),io.stderr(),output,diagnostic,normal,exit)
  {
    var outErr := 0;
    if output != [] {
      var written := io.WriteStdout(output);
      outErr := C.ResultErrno(written);
    }
    var errors := diagnostic;
    if outErr != 0 {
      var message := io.GetCLocaleErrnoText(outErr);
      errors := errors+Spec.WriteError(message);
    }
    assert errors == diagnostic+(if outErr==0 then [] else Spec.WriteError(C.CLocaleErrnoTextResult(outErr)));
    var errErr := 0;
    if errors != [] {
      var reported := io.WriteStderr(errors);
      errErr := C.ResultErrno(reported);
      assert C.WriteStderrSpec(old(io.stderr()),io.trustedStreams(),io.stderr(),errors,C.WriteResultCommitted(reported),errErr);
    }
    exit := if outErr != 0 || errErr != 0 then 1 else normal;
  }
  twostate predicate CoreSummary(raw: S.JoinCmdRaw, io: BenchIO.IO, exit: int)
    reads io.stdinRegion, io.stdoutRegion, io.stderrRegion
  {
    exists output: BW.Bytes, diagnostic: BW.Bytes, normal: int ::
      Spec.Prepared(raw,io,output,diagnostic,normal) &&
      Spec.Emitted(old(io.trustedStreams()),old(io.stdout()),old(io.stderr()),io.stdout(),io.stderr(),output,diagnostic,normal,exit)
  }
  method RunCore(raw: S.JoinCmdRaw, io: BenchIO.IO) returns (exit: int)
    modifies io.stdinRegion, io.stdoutRegion, io.stderrRegion
    ensures CoreSummary(raw,io,exit)
  {
    var output, diagnostic, normal := Prepare(raw,io);
    exit := Emit(io,output,diagnostic,normal);
  }
}
