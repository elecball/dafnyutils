include "MkfifoSpec.dfy"
include "MkfifoModeCore.dfy"
include "MkfifoModeProof.dfy"

module MkfifoProof {
  import BenchIO
  import BW = BenchWorld
  import C = IOContract
  import Spec = MkfifoSpec
  import Schema = MkfifoSchema
  import P = MkfifoModeCore
  import MP = MkfifoModeProof

  // ---------------------------------------------------------------------------
  // MODE decision
  // ---------------------------------------------------------------------------

  // The decision RunCore computes from the parser result.
  ghost predicate ComputedPlan(raw: Schema.MkfifoCmdRaw, umask: bv32, plan: Spec.ModePlan)
  {
    match raw.mode
    case None => plan == Spec.NoModeOption
    case Some(s) =>
      match P.ParseMode(s)
      case None => plan == Spec.RejectInvalidMode
      case Some(e) =>
        var bits := Spec.Meaning(e, umask);
        plan == (if Spec.OnlyPermissionBits(bits) then Spec.ExplicitMode(bits) else Spec.RejectSpecialBits)
  }

  lemma ComputedPlanIsSpecPlan(raw: Schema.MkfifoCmdRaw, umask: bv32, plan: Spec.ModePlan)
    requires ComputedPlan(raw, umask, plan)
    ensures Spec.ModePlanOf(raw, umask, plan)
  {
    match raw.mode
    case None =>
    case Some(s) =>
      match P.ParseMode(s)
      case None =>
        MP.ParseNoneIsInvalid(s);
      case Some(e) =>
        MP.ParseSomeDenotes(s, umask);
        var bits := Spec.Meaning(e, umask);
        assert Spec.ModeDenotes(s, umask, bits);
  }

  // ---------------------------------------------------------------------------
  // One operand
  // ---------------------------------------------------------------------------

  // Folded copies of the native contracts. Passing them to lemmas keeps each
  // call-site check a single fact instead of every conjunct of the contract.
  opaque ghost predicate CreateFact(
    before: BW.FileSystem, now: int, fsObservations: C.ValidFilesystemObservations, umask: bv32,
    after: BW.FileSystem, path: string, mode: bv32, ok: bool, err: int)
  {
    C.CreateSpecialNodeSpec(before, now, fsObservations, umask, after, path, BW.FifoNode,
                            mode, 0, 0, ok, err)
  }

  opaque ghost predicate PermissionFact(
    before: BW.FileSystem, now: int, failures: C.ValidNativeFailureObservations,
    after: BW.FileSystem, path: string, mode: bv32, ok: bool, err: int)
  {
    C.SetFileModeSpec(before, now, failures, after, path, false, mode, ok, err)
  }

  // Creation alone: it failed, or no -m was given.
  lemma StepCreateOnly(
    before: BW.FileSystem, after: BW.FileSystem, path: string, plan: Spec.ModePlan,
    now: int, umask: bv32,
    fsObservations: C.ValidFilesystemObservations,
    failures: C.ValidNativeFailureObservations,
    ok: bool, err: int, outcome: Spec.OperandOutcome)
    requires plan.NoModeOption? || plan.ExplicitMode?
    requires CreateFact(before, now, fsObservations, umask, after, path,
                        if plan.ExplicitMode? then plan.bits else Spec.MKFIFO_BASE_MODE, ok, err)
    requires !ok || plan.NoModeOption?
    requires outcome == (if ok then Spec.Created else Spec.CreateFailed(err))
    ensures Spec.OperandStep(before, after, path, plan, now, umask, fsObservations, failures, outcome)
  {
    reveal CreateFact();
    var created := after;
    if !ok {
      assert after == created && outcome == Spec.CreateFailed(err);
    } else {
      assert plan.NoModeOption? && after == created && outcome == Spec.Created;
    }
  }

  // Creation succeeded and -m was given: one non-following permission change.
  lemma StepCreateThenPermission(
    before: BW.FileSystem, created: BW.FileSystem, after: BW.FileSystem, path: string,
    plan: Spec.ModePlan, now: int, umask: bv32,
    fsObservations: C.ValidFilesystemObservations,
    failures: C.ValidNativeFailureObservations,
    err: int, permOk: bool, permErr: int, outcome: Spec.OperandOutcome)
    requires plan.ExplicitMode?
    requires CreateFact(before, now, fsObservations, umask, created, path, plan.bits, true, err)
    requires PermissionFact(created, now, failures, after, path, plan.bits, permOk, permErr)
    requires outcome == (if permOk then Spec.Created else Spec.PermissionFailed(permErr))
    ensures Spec.OperandStep(before, after, path, plan, now, umask, fsObservations, failures, outcome)
  {
    reveal CreateFact();
    reveal PermissionFact();
    assert outcome == (if permOk then Spec.Created else Spec.PermissionFailed(permErr));
  }

  // ---------------------------------------------------------------------------
  // The operand loop
  // ---------------------------------------------------------------------------

  lemma ExtendOperands(
    paths: seq<string>, plan: Spec.ModePlan, states: seq<BW.FileSystem>,
    outcomes: seq<Spec.OperandOutcome>, now: int, umask: bv32,
    fsObservations: C.ValidFilesystemObservations,
    failures: C.ValidNativeFailureObservations,
    path: string, after: BW.FileSystem, outcome: Spec.OperandOutcome)
    requires plan.NoModeOption? || plan.ExplicitMode?
    requires Spec.OperandResults(paths, plan, states, outcomes, now, umask, fsObservations, failures)
    requires Spec.OperandStep(states[|paths|], after, path, plan, now, umask,
                              fsObservations, failures, outcome)
    ensures Spec.OperandResults(paths + [path], plan, states + [after], outcomes + [outcome],
                                now, umask, fsObservations, failures)
  {
    hide Spec.OperandStep();
    forall j | 0 <= j < |paths| + 1
      ensures Spec.OperandStep((states + [after])[j], (states + [after])[j + 1], (paths + [path])[j],
                               plan, now, umask, fsObservations, failures, (outcomes + [outcome])[j])
    {
      if j < |paths| {
        assert Spec.OperandStep(states[j], states[j + 1], paths[j], plan, now, umask,
                                fsObservations, failures, outcomes[j]);
      }
    }
  }

  lemma {:isolate_assertions} ExtendDiagnostics(
    paths: seq<string>, outcomes: seq<Spec.OperandOutcome>, diagnostics: BW.Bytes, cuts: seq<nat>,
    path: string, outcome: Spec.OperandOutcome, piece: BW.Bytes)
    requires Spec.OrderedDiagnostics(paths, outcomes, diagnostics, cuts)
    requires piece == Spec.OutcomeDiagnostic(path, outcome)
    ensures Spec.OrderedDiagnostics(paths + [path], outcomes + [outcome], diagnostics + piece,
                                    cuts + [|diagnostics| + |piece|])
  {
    hide Spec.OutcomeDiagnostic();
    var next := diagnostics + piece;
    var nextCuts := cuts + [|next|];
    forall j {:trigger nextCuts[j]} | 0 <= j < |paths| + 1
      ensures nextCuts[j] <= nextCuts[j + 1] <= |next|
      ensures next[nextCuts[j]..nextCuts[j + 1]] ==
              Spec.OutcomeDiagnostic((paths + [path])[j], (outcomes + [outcome])[j])
    {
      if j < |paths| {
        assert cuts[j] <= cuts[j + 1] <= |diagnostics|;
        assert diagnostics[cuts[j]..cuts[j + 1]] == Spec.OutcomeDiagnostic(paths[j], outcomes[j]);
        assert nextCuts[j] == cuts[j] && nextCuts[j + 1] == cuts[j + 1];
        assert next[..|diagnostics|] == diagnostics;
        assert next[nextCuts[j]..nextCuts[j + 1]] == diagnostics[cuts[j]..cuts[j + 1]];
      } else {
        assert nextCuts[j] == |diagnostics| && nextCuts[j + 1] == |next|;
        assert next[nextCuts[j]..nextCuts[j + 1]] == piece;
      }
    }
  }

  lemma AllCreatedSnoc(outcomes: seq<Spec.OperandOutcome>, outcome: Spec.OperandOutcome)
    ensures (forall j | 0 <= j < |outcomes + [outcome]| :: (outcomes + [outcome])[j].Created?) <==>
            ((forall j | 0 <= j < |outcomes| :: outcomes[j].Created?) && outcome.Created?)
  {
    if forall j | 0 <= j < |outcomes + [outcome]| :: (outcomes + [outcome])[j].Created? {
      assert (outcomes + [outcome])[|outcomes|] == outcome;
      forall j | 0 <= j < |outcomes|
        ensures outcomes[j].Created?
      {
        assert (outcomes + [outcome])[j] == outcomes[j];
      }
    }
    if (forall j | 0 <= j < |outcomes| :: outcomes[j].Created?) && outcome.Created? {
      forall j | 0 <= j < |outcomes + [outcome]|
        ensures (outcomes + [outcome])[j].Created?
      {
        if j < |outcomes| {
          assert (outcomes + [outcome])[j] == outcomes[j];
        }
      }
    }
  }

  lemma EmptyOperands(
    plan: Spec.ModePlan, start: BW.FileSystem, now: int, umask: bv32,
    fsObservations: C.ValidFilesystemObservations,
    failures: C.ValidNativeFailureObservations)
    requires plan.NoModeOption? || plan.ExplicitMode?
    ensures Spec.OperandResults([], plan, [start], [], now, umask, fsObservations, failures)
    ensures Spec.OrderedDiagnostics([], [], [], [0])
  {}

  // A rejected MODE leaves the filesystem alone and reports one line.
  lemma RejectRun(
    paths: seq<string>, plan: Spec.ModePlan, fs: BW.FileSystem, now: int, umask: bv32,
    fsObservations: C.ValidFilesystemObservations,
    failures: C.ValidNativeFailureObservations,
    diagnostics: BW.Bytes, runExit: int)
    requires plan.RejectInvalidMode? || plan.RejectSpecialBits?
    requires diagnostics == (if plan.RejectInvalidMode? then Spec.InvalidModeText() else Spec.SpecialBitsText())
    requires runExit == 1
    ensures Spec.PlanRun(paths, plan, fs, fs, now, umask, fsObservations, failures, diagnostics, runExit)
  {}

  // The loop invariant of RunOperands after i operands.
  ghost predicate LoopState(
    paths: seq<string>, i: nat, plan: Spec.ModePlan, start: BW.FileSystem, current: BW.FileSystem,
    now: int, umask: bv32,
    fsObservations: C.ValidFilesystemObservations,
    failures: C.ValidNativeFailureObservations,
    states: seq<BW.FileSystem>, outcomes: seq<Spec.OperandOutcome>, cuts: seq<nat>,
    diagnostics: BW.Bytes, runExit: int)
    requires plan.NoModeOption? || plan.ExplicitMode?
  {
    i <= |paths| &&
    |states| == i + 1 && states[0] == start && states[i] == current && |outcomes| == i &&
    Spec.OperandResults(paths[..i], plan, states, outcomes, now, umask, fsObservations, failures) &&
    Spec.OrderedDiagnostics(paths[..i], outcomes, diagnostics, cuts) &&
    runExit == (if forall j | 0 <= j < i :: outcomes[j].Created? then 0 else 1)
  }

  lemma EmptyLoop(
    paths: seq<string>, plan: Spec.ModePlan, start: BW.FileSystem, now: int, umask: bv32,
    fsObservations: C.ValidFilesystemObservations,
    failures: C.ValidNativeFailureObservations)
    requires plan.NoModeOption? || plan.ExplicitMode?
    ensures LoopState(paths, 0, plan, start, start, now, umask, fsObservations, failures,
                      [start], [], [0], [], 0)
  {
    EmptyOperands(plan, start, now, umask, fsObservations, failures);
    assert paths[..0] == [];
  }

  lemma ExtendLoop(
    paths: seq<string>, i: nat, plan: Spec.ModePlan, start: BW.FileSystem,
    before: BW.FileSystem, after: BW.FileSystem, now: int, umask: bv32,
    fsObservations: C.ValidFilesystemObservations,
    failures: C.ValidNativeFailureObservations,
    states: seq<BW.FileSystem>, outcomes: seq<Spec.OperandOutcome>, cuts: seq<nat>,
    diagnostics: BW.Bytes, runExit: int, outcome: Spec.OperandOutcome, piece: BW.Bytes)
    requires plan.NoModeOption? || plan.ExplicitMode?
    requires i < |paths|
    requires LoopState(paths, i, plan, start, before, now, umask, fsObservations, failures,
                       states, outcomes, cuts, diagnostics, runExit)
    requires Spec.OperandStep(before, after, paths[i], plan, now, umask, fsObservations, failures, outcome)
    requires piece == Spec.OutcomeDiagnostic(paths[i], outcome)
    ensures LoopState(paths, i + 1, plan, start, after, now, umask, fsObservations, failures,
                      states + [after], outcomes + [outcome], cuts + [|diagnostics| + |piece|],
                      diagnostics + piece, if outcome.Created? then runExit else 1)
  {
    hide Spec.OperandResults();
    hide Spec.OrderedDiagnostics();
    hide Spec.OperandStep();
    hide Spec.OutcomeDiagnostic();
    assert paths[..i + 1] == paths[..i] + [paths[i]];
    ExtendOperands(paths[..i], plan, states, outcomes, now, umask, fsObservations, failures,
                   paths[i], after, outcome);
    ExtendDiagnostics(paths[..i], outcomes, diagnostics, cuts, paths[i], outcome, piece);
    AllCreatedSnoc(outcomes, outcome);
  }

  lemma FinishLoop(
    paths: seq<string>, plan: Spec.ModePlan, start: BW.FileSystem, current: BW.FileSystem,
    now: int, umask: bv32,
    fsObservations: C.ValidFilesystemObservations,
    failures: C.ValidNativeFailureObservations,
    states: seq<BW.FileSystem>, outcomes: seq<Spec.OperandOutcome>, cuts: seq<nat>,
    diagnostics: BW.Bytes, runExit: int)
    requires plan.NoModeOption? || plan.ExplicitMode?
    requires LoopState(paths, |paths|, plan, start, current, now, umask, fsObservations, failures,
                       states, outcomes, cuts, diagnostics, runExit)
    ensures Spec.PlanRun(paths, plan, start, current, now, umask, fsObservations, failures,
                         diagnostics, runExit)
  {
    assert paths[..|paths|] == paths;
    AssembleOperands(paths, plan, start, current, now, umask, fsObservations, failures,
                     diagnostics, runExit, states, outcomes, cuts);
  }

  // ---------------------------------------------------------------------------
  // Assembling the run
  // ---------------------------------------------------------------------------

  lemma AssembleOperands(
    paths: seq<string>, plan: Spec.ModePlan, before: BW.FileSystem, after: BW.FileSystem,
    now: int, umask: bv32,
    fsObservations: C.ValidFilesystemObservations,
    failures: C.ValidNativeFailureObservations,
    diagnostics: BW.Bytes, runExit: int,
    states: seq<BW.FileSystem>, outcomes: seq<Spec.OperandOutcome>, cuts: seq<nat>)
    requires plan.NoModeOption? || plan.ExplicitMode?
    requires Spec.OperandResults(paths, plan, states, outcomes, now, umask, fsObservations, failures)
    requires states[0] == before && states[|paths|] == after
    requires Spec.OrderedDiagnostics(paths, outcomes, diagnostics, cuts)
    requires runExit == (if forall i | 0 <= i < |paths| :: outcomes[i].Created? then 0 else 1)
    ensures Spec.PlanRun(paths, plan, before, after, now, umask, fsObservations, failures,
                         diagnostics, runExit)
  {
    assert |states| == |paths| + 1;
    hide Spec.OperandResults();
    hide Spec.OrderedDiagnostics();
  }

  lemma AssembleRun(
    raw: Schema.MkfifoCmdRaw, plan: Spec.ModePlan,
    before: BW.FileSystem, after: BW.FileSystem, now: int, createUmask: bv32, modeUmask: bv32,
    fsObservations: C.ValidFilesystemObservations,
    failures: C.ValidNativeFailureObservations,
    diagnostics: BW.Bytes, runExit: int)
    requires Spec.ModePlanOf(raw, modeUmask, plan)
    requires Spec.PlanRun(Schema.Operands(raw), plan, before, after, now, createUmask,
                          fsObservations, failures, diagnostics, runExit)
    ensures Spec.RunRelation(raw, before, after, now, createUmask, modeUmask,
                             fsObservations, failures, diagnostics, runExit)
  {
    hide Spec.ModePlanOf();
    hide Spec.PlanRun();
  }

  twostate lemma Complete(
    raw: Schema.MkfifoCmdRaw, io: BenchIO.IO, diagnostics: BW.Bytes, runExit: int, exit: int)
    requires Spec.RunRelation(raw, old(io.fs()), io.fs(), io.now(), io.umask(),
                              C.GetUmaskResultFields(io.props()),
                              io.trustedFilesystem(), io.trustedNativeFailures(),
                              diagnostics, runExit)
    requires Spec.StderrResult(old(io.stderr()), io.stderr(), io.trustedStreams(),
                               diagnostics, runExit, exit)
    requires io.stdout() == old(io.stdout())
    ensures Spec.Spec(raw, io, exit)
  {
    hide Spec.RunRelation();
    hide Spec.StderrResult();
    assert exists chosenDiagnostics: BW.Bytes, chosenExit: int ::
        chosenDiagnostics == diagnostics && chosenExit == runExit &&
        Spec.RunRelation(raw, old(io.fs()), io.fs(), io.now(), io.umask(),
                         C.GetUmaskResultFields(io.props()),
                         io.trustedFilesystem(), io.trustedNativeFailures(),
                         chosenDiagnostics, chosenExit) &&
        Spec.StderrResult(old(io.stderr()), io.stderr(), io.trustedStreams(),
                          chosenDiagnostics, chosenExit, exit);
  }
}
