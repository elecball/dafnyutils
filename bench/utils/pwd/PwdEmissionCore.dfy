include "PwdTextCore.dfy"
include "PwdEmissionSpec.dfy"

module PwdEmissionCore {
  import Text = PwdTextCore
  import BenchIO
  import W = BenchWorld
  import C = IOContract
  import Recovery = PwdRecoverySpec
  import Spec = PwdEmissionSpec

  method Flush(output: W.Bytes, diagnostics: W.Bytes, normalExit: int, io: BenchIO.IO)
    returns (exit: int)
    modifies io.stdoutRegion,io.stderrRegion
    ensures Spec.EmissionFields(old(io.stdout()),old(io.stderr()),io.stdout(),io.stderr(),
      io.trustedStreams(),output,diagnostics,normalExit,exit)
  {
    var committed: nat := 0;
    var outErr := 0;
    if |output| != 0 {
      var result := io.WriteStdout(output);
      committed := C.WriteResultCommitted(result);
      outErr := C.ResultErrno(result);
    }
    var finalDiagnostics := diagnostics;
    if outErr != 0 {
      var reason := io.GetCLocaleErrnoText(outErr);
      finalDiagnostics := diagnostics+Text.WriteErrorText(reason);
    }
    assert finalDiagnostics == diagnostics + (if outErr == 0 then []
      else Recovery.WriteErrorText(C.CLocaleErrnoTextResult(outErr)));
    var errCommitted: nat := 0;
    var errErr := 0;
    if |finalDiagnostics| != 0 {
      var result := io.WriteStderr(finalDiagnostics);
      errCommitted := C.WriteResultCommitted(result);
      errErr := C.ResultErrno(result);
      assert C.WriteStderrSpec(old(io.stderr()),io.trustedStreams(),io.stderr(),
        finalDiagnostics,errCommitted,errErr);
    }
    exit := if outErr != 0 || errErr != 0 then 1 else normalExit;
    assert Spec.EmissionOutcomeFields(old(io.stdout()),old(io.stderr()),io.stdout(),io.stderr(),
      io.trustedStreams(),output,diagnostics,normalExit,exit,committed,outErr,errCommitted,errErr);
  }
}
