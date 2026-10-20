include "PwdSpec.dfy"
include "PwdLogicalCore.dfy"
include "PwdRecoveryCore.dfy"
include "PwdEmissionCore.dfy"

module PwdCore {
  import BenchIO
  import W = BenchWorld
  import C = IOContract
  import Schema = PwdSchema
  import Text = PwdTextSpec
  import Spec = PwdSpec
  import Model = PwdRuntimeModel
  import Recovery = PwdRecoverySpec
  import RecoveryCore = PwdRecoveryCore
  import Logical = PwdLogicalSpec
  import LogicalCore = PwdLogicalCore
  import Physical = PwdPhysicalSpec
  import Emission = PwdEmissionSpec
  import Emit = PwdEmissionCore

  method UseLogical(raw: Schema.PwdCmdRaw, io: BenchIO.IO) returns (logical: bool)
    ensures logical == Text.UseLogicalFields(raw,io.env())
  {
    if raw.seenLogical && raw.seenPhysical {
      logical := raw.logicalOccurrenceIndex > raw.physicalOccurrenceIndex;
    } else if raw.seenLogical {
      logical := true;
    } else if raw.seenPhysical {
      logical := false;
    } else {
      var posix := io.GetEnv("POSIXLY_CORRECT");
      logical := posix.Ok?;
    }
  }

  method SelectDirectory(raw: Schema.PwdCmdRaw, io: BenchIO.IO)
    returns (outcome: Recovery.DirectoryOutcome, ghost evidence: Spec.DirectoryEvidence)
    modifies io.directoryStateRegion,io.cwdRegion,io.statusObservationsRegion
    ensures Model.Inputs(io) == old(Model.Inputs(io))
    ensures Recovery.DirectoryOutcomeFields(outcome)
    ensures Spec.DirectorySelectionFields(raw,old(io.env()),old(Model.Inputs(io)),
      old(Model.State(io)),Model.State(io),outcome,evidence)
    decreases *
  {
    ghost var inputs := Model.Inputs(io);
    ghost var before := Model.State(io);
    ghost var env := io.env();
    ghost var logicalEvidence := Logical.SelectionEvidence([],[]);
    var selected := false;
    var logicalDirectory := "";
    var logical := UseLogical(raw,io);
    if logical {
      var pwd := io.GetEnv("PWD");
      if pwd.Ok? {
        selected,logicalEvidence := LogicalCore.SelectLogical(pwd.v,io);
        logicalDirectory := pwd.v;
      }
    }
    ghost var logicalAfter := Model.State(io);
    if selected {
      outcome := Recovery.DirectoryRecovered(logicalDirectory);
      evidence := Spec.DirectoryEvidence(true,logicalAfter,logicalEvidence,[]);
      assert Recovery.DirectoryOutcomeFields(outcome) by {
        reveal Logical.NativeSelectionFields(),Recovery.LogicalSelectionFields(),Recovery.LogicalTextFields();
      }
    } else {
      outcome := RecoveryCore.PhysicalDirectory(io);
      ghost var physical :| Physical.PhysicalSelectionFields(inputs,logicalAfter,Model.State(io),outcome,physical);
      evidence := Spec.DirectoryEvidence(false,logicalAfter,logicalEvidence,[physical]);
    }
    assert Spec.DirectorySelectionFields(raw,env,inputs,before,Model.State(io),outcome,evidence);
  }

  method WarnIgnoredOperands(raw: Schema.PwdCmdRaw, io: BenchIO.IO) returns (warningErr: int)
    modifies io.stderrRegion
    ensures Spec.WarningFields(raw,old(io.stderr()),io.stderr(),io.trustedStreams(),warningErr)
  {
    warningErr := 0;
    if |raw.operands| != 0 {
      var written := io.WriteStderr(Text.IgnoredOperandsWarningSpec());
      warningErr := C.ResultErrno(written);
      assert C.WriteStderrSpec(old(io.stderr()),io.trustedStreams(),io.stderr(),
        Text.IgnoredOperandsWarningSpec(),C.WriteResultCommitted(written),warningErr);
    }
  }

  method RunCore(raw: Schema.PwdCmdRaw, io: BenchIO.IO) returns (exit: int)
    modifies io.stdoutRegion,io.stderrRegion,io.directoryStateRegion,io.cwdRegion,io.statusObservationsRegion
    ensures Spec.Spec(raw,io,exit)
    decreases *
  {
    ghost var inputs := Model.Inputs(io);
    ghost var before := Model.State(io);
    ghost var beforeOut := io.stdout();
    ghost var beforeErr := io.stderr();
    if Text.HelpSelected(raw) {
      exit := Emit.Flush(Text.HelpTextSpec(),[],0,io);
    } else if Text.VersionSelected(raw) {
      exit := Emit.Flush(Text.VersionTextSpec(),[],0,io);
    } else {
      var warningErr := WarnIgnoredOperands(raw,io);
      ghost var middleErr := io.stderr();
      var outcome, evidence := SelectDirectory(raw,io);
      var emissionExit := RecoveryCore.FlushPhysical(outcome,io);
      exit := if warningErr == 0 then emissionExit else 1;
    }
    assert Model.Inputs(io) == inputs by {
      hide *;
    }
    assert Spec.RunFields(raw,io.env(),inputs,before,Model.State(io),
      beforeOut,beforeErr,io.stdout(),io.stderr(),io.trustedStreams(),exit) by {
      hide *;
      reveal Spec.RunFields();
    }
    assert Spec.Spec(raw,io,exit) by {
      hide *;
      reveal Spec.Spec();
    }
  }
}
