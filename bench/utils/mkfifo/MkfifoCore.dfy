include "../../core/Utf8.dfy"
include "MkfifoSpec.dfy"
include "MkfifoModeCore.dfy"
include "MkfifoProof.dfy"

module MkfifoCore {
  import BenchIO
  import BW = BenchWorld
  import C = IOContract
  import Schema = MkfifoSchema
  import Spec = MkfifoSpec
  import P = MkfifoModeCore
  import Proof = MkfifoProof

  method FormatOutcome(path: string, outcome: Spec.OperandOutcome, io: BenchIO.IO)
    returns (piece: BW.Bytes)
    ensures piece == Spec.OutcomeDiagnostic(path, outcome)
  {
    match outcome {
      case Created =>
        piece := [];
      case CreateFailed(err) =>
        var quoted := io.QuoteafPath(path);
        var reason := io.GetCLocaleErrnoText(err);
        piece := Spec.CreateFailureText(quoted, reason);
      case PermissionFailed(err) =>
        var quoted := io.QuoteafPath(path);
        var reason := io.GetCLocaleErrnoText(err);
        piece := Spec.PermissionFailureText(quoted, reason);
    }
  }

  // All diagnostics are written to stderr once, after the operands.
  method Flush(diagnostics: BW.Bytes, runExit: int, io: BenchIO.IO) returns (exit: int)
    modifies io.stderrRegion
    ensures Spec.StderrResult(old(io.stderr()), io.stderr(), io.trustedStreams(),
                              diagnostics, runExit, exit)
  {
    ghost var observations := io.trustedStreams();
    ghost var beforeErr := io.stderr();
    var errResult := io.WriteStderr(diagnostics);
    ghost var errObservation := observations(BW.StreamWriteStderr(beforeErr, diagnostics));
    assert errObservation.StreamWriteResult? && errObservation.err == C.ResultErrno(errResult);
    exit := if runExit == 0 && C.ResultErrno(errResult) == 0 then 0 else 1;
  }

  // Decides the MODE plan before any operand, as GNU does.
  method DecideMode(raw: Schema.MkfifoCmdRaw, io: BenchIO.IO) returns (plan: Spec.ModePlan)
    ensures Proof.ComputedPlan(raw, C.GetUmaskResultFields(io.props()), plan)
  {
    plan := Spec.NoModeOption;
    if raw.mode.Some? {
      var umask := io.GetUmask();
      var parsed := P.ParseMode(raw.mode.value);
      if parsed.None? {
        plan := Spec.RejectInvalidMode;
      } else {
        var bits := Spec.Meaning(parsed.value, umask);
        plan := if Spec.OnlyPermissionBits(bits) then Spec.ExplicitMode(bits)
        else Spec.RejectSpecialBits;
      }
    }
  }

  // One operand: create the FIFO and, with -m, set its permissions.
  method ProcessOperand(path: string, plan: Spec.ModePlan, createMode: bv32, io: BenchIO.IO)
    returns (outcome: Spec.OperandOutcome, piece: BW.Bytes)
    requires plan.NoModeOption? || plan.ExplicitMode?
    requires createMode == (if plan.ExplicitMode? then plan.bits else Spec.MKFIFO_BASE_MODE)
    modifies io.fsRegion
    ensures Spec.OperandStep(old(io.fs()), io.fs(), path, plan, io.now(), io.umask(),
                             io.trustedFilesystem(), io.trustedNativeFailures(), outcome)
    ensures piece == Spec.OutcomeDiagnostic(path, outcome)
  {
    // Keep the native contracts folded: the lemmas only pass them along.
    hide C.CreateSpecialNodeSpec();
    hide C.SetFileModeSpec();
    hide *;
    var created := io.CreateSpecialNode(path, BW.FifoNode, createMode, 0, 0);
    assert Proof.CreateFact(old(io.fs()), io.now(), io.trustedFilesystem(), io.umask(), io.fs(), path,
                            createMode, created.Ok?, C.ResultErrno(created)) by {
      reveal Proof.CreateFact();
    }
    if created.Err? || plan.NoModeOption? {
      outcome := if created.Ok? then Spec.Created else Spec.CreateFailed(C.ResultErrno(created));
      Proof.StepCreateOnly(old(io.fs()), io.fs(), path, plan, io.now(), io.umask(),
                           io.trustedFilesystem(), io.trustedNativeFailures(),
                           created.Ok?, C.ResultErrno(created), outcome);
    } else {
      ghost var mid := io.fs();
      var changed := io.SetFileMode(path, false, plan.bits);
      assert Proof.PermissionFact(mid, io.now(), io.trustedNativeFailures(), io.fs(), path,
                                  plan.bits, changed.Ok?, C.ResultErrno(changed)) by {
        reveal Proof.PermissionFact();
      }
      outcome := if changed.Ok? then Spec.Created else Spec.PermissionFailed(C.ResultErrno(changed));
      Proof.StepCreateThenPermission(old(io.fs()), mid, io.fs(), path, plan, io.now(), io.umask(),
                                     io.trustedFilesystem(), io.trustedNativeFailures(),
                                     C.ResultErrno(created), changed.Ok?, C.ResultErrno(changed),
                                     outcome);
    }
    piece := FormatOutcome(path, outcome, io);
  }

  method RunOperands(paths: seq<string>, plan: Spec.ModePlan, io: BenchIO.IO)
    returns (diagnostics: BW.Bytes, runExit: int)
    requires plan.NoModeOption? || plan.ExplicitMode?
    modifies io.fsRegion
    ensures Spec.PlanRun(paths, plan, old(io.fs()), io.fs(), io.now(), io.umask(),
                         io.trustedFilesystem(), io.trustedNativeFailures(), diagnostics, runExit)
  {
    // The relations are used only through the Proof lemmas.
    hide *;
    var createMode := if plan.ExplicitMode? then plan.bits else Spec.MKFIFO_BASE_MODE;
    diagnostics := [];
    runExit := 0;
    ghost var states := [io.fs()];
    ghost var outcomes: seq<Spec.OperandOutcome> := [];
    ghost var cuts: seq<nat> := [0];
    Proof.EmptyLoop(paths, plan, io.fs(), io.now(), io.umask(), io.trustedFilesystem(),
                    io.trustedNativeFailures());
    var i := 0;
    while i < |paths|
      modifies io.fsRegion
      invariant 0 <= i <= |paths|
      invariant Proof.LoopState(paths, i, plan, old(io.fs()), io.fs(), io.now(), io.umask(),
                                io.trustedFilesystem(), io.trustedNativeFailures(),
                                states, outcomes, cuts, diagnostics, runExit)
      decreases |paths| - i
    {
      ghost var before := io.fs();
      var outcome, piece := ProcessOperand(paths[i], plan, createMode, io);
      Proof.ExtendLoop(paths, i, plan, old(io.fs()), before, io.fs(), io.now(), io.umask(),
                       io.trustedFilesystem(), io.trustedNativeFailures(),
                       states, outcomes, cuts, diagnostics, runExit, outcome, piece);
      states := states + [io.fs()];
      cuts := cuts + [|diagnostics| + |piece|];
      outcomes := outcomes + [outcome];
      diagnostics := diagnostics + piece;
      runExit := if outcome.Created? then runExit else 1;
      i := i + 1;
    }
    Proof.FinishLoop(paths, plan, old(io.fs()), io.fs(), io.now(), io.umask(),
                     io.trustedFilesystem(), io.trustedNativeFailures(),
                     states, outcomes, cuts, diagnostics, runExit);
  }

  method {:isolate_assertions} RunCore(raw: Schema.MkfifoCmdRaw, io: BenchIO.IO) returns (exit: int)
    modifies io.fsRegion, io.stderrRegion
    ensures Spec.Spec(raw, io, exit)
  {
    hide *;
    ghost var modeUmask := C.GetUmaskResultFields(io.props());
    var plan := DecideMode(raw, io);
    Proof.ComputedPlanIsSpecPlan(raw, modeUmask, plan);
    var paths := Schema.Operands(raw);
    var diagnostics: BW.Bytes;
    var runExit: int;
    if plan.RejectInvalidMode? || plan.RejectSpecialBits? {
      diagnostics := if plan.RejectInvalidMode? then Spec.InvalidModeText() else Spec.SpecialBitsText();
      runExit := 1;
      Proof.RejectRun(paths, plan, io.fs(), io.now(), io.umask(),
                      io.trustedFilesystem(), io.trustedNativeFailures(), diagnostics, runExit);
    } else {
      diagnostics, runExit := RunOperands(paths, plan, io);
    }
    Proof.AssembleRun(raw, plan, old(io.fs()), io.fs(), io.now(), io.umask(), modeUmask,
                      io.trustedFilesystem(), io.trustedNativeFailures(), diagnostics, runExit);
    ghost var runExitValue := runExit;
    exit := Flush(diagnostics, runExit, io);
    Proof.Complete(raw, io, diagnostics, runExitValue, exit);
  }
}
