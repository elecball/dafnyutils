include "PwdRecoverySpec.dfy"

module PwdEmissionSpec {
  import W = BenchWorld
  import C = IOContract
  import Utf8 = Utf8Semantics
  import Recovery = PwdRecoverySpec

  function CurrentDirectoryTextSpecPart1(): W.Bytes
  {
    "\n"
  }

  ghost function CurrentDirectoryTextSpec(directory: string): W.Bytes
  {
    Utf8.Encode(directory)+CurrentDirectoryTextSpecPart1()
  }

  ghost predicate EmissionOutcomeFields(
    beforeOut: W.Bytes, beforeErr: W.Bytes, afterOut: W.Bytes, afterErr: W.Bytes,
    observations: (W.TrustedStreamRequest)->W.TrustedStreamResult,
    output: W.Bytes, diagnostics: W.Bytes, normalExit: int, exit: int,
    committed: nat, outErr: int, errCommitted: nat, errErr: int)
  {
    (if |output| == 0 then afterOut == beforeOut && committed == 0 && outErr == 0
     else C.WriteStdoutSpec(beforeOut,observations,afterOut,output,committed,outErr)) &&
    var finalDiagnostics := diagnostics +
      (if outErr == 0 then [] else Recovery.WriteErrorText(C.CLocaleErrnoTextResult(outErr)));
    (if |finalDiagnostics| == 0 then afterErr == beforeErr && errCommitted == 0 && errErr == 0
     else C.WriteStderrSpec(beforeErr,observations,afterErr,finalDiagnostics,errCommitted,errErr)) &&
    exit == (if outErr != 0 || errErr != 0 then 1 else normalExit)
  }

  ghost predicate EmissionFields(
    beforeOut: W.Bytes, beforeErr: W.Bytes, afterOut: W.Bytes, afterErr: W.Bytes,
    observations: (W.TrustedStreamRequest)->W.TrustedStreamResult,
    output: W.Bytes, diagnostics: W.Bytes, normalExit: int, exit: int)
  {
    exists committed: nat, outErr: int, errCommitted: nat, errErr: int ::
      EmissionOutcomeFields(beforeOut,beforeErr,afterOut,afterErr,observations,
        output,diagnostics,normalExit,exit,committed,outErr,errCommitted,errErr)
  }

  ghost predicate PhysicalEmissionFields(outcome: Recovery.DirectoryOutcome,
    beforeOut: W.Bytes, beforeErr: W.Bytes, afterOut: W.Bytes, afterErr: W.Bytes,
    observations: (W.TrustedStreamRequest)->W.TrustedStreamResult, exit: int)
  {
    Recovery.DirectoryOutcomeFields(outcome) &&
    if outcome.DirectoryRecovered? then
      EmissionFields(beforeOut,beforeErr,afterOut,afterErr,observations,
        CurrentDirectoryTextSpec(outcome.directory),[],0,exit)
    else EmissionFields(beforeOut,beforeErr,afterOut,afterErr,observations,
      [],Recovery.RecoveryDiagnosticSpec(outcome.failure),1,exit)
  }
}
