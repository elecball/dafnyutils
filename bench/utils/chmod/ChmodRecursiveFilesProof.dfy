include "ChmodNormalEntryProof.dfy"
include "ChmodDescriptorProof.dfy"

module ChmodRecursiveFilesProof {
  import W = BenchWorld
  import C = IOContract
  import Base = ChmodSpec
  import Spec = ChmodDescriptorSpec
  import Operand = ChmodOperandSpec
  import Recursive = ChmodRecursiveSpec
  import Schema = ChmodSchema
  import Proof = ChmodDescriptorProof

  lemma {:isolate_assertions} TopPath(cwd: W.Path, native: W.CwdContext, path: W.Path)
    ensures Operand.ModelPath(cwd, native, Operand.CwdOperand(path)) == Base.MakeAbsolute(cwd, path)
    ensures var actual := Operand.ModelPath(cwd, native, Operand.CwdOperand(path));
      actual == "" || W.IsAbsolutePath(actual)
    ensures (path == "/") == (Operand.ModelPath(cwd, native, Operand.CwdOperand(path)) == "/")
  {
    hide *;
    reveal Operand.ModelPath(), C.AtCwdPathFields(), Base.MakeAbsolute(),
      W.IsAbsolutePath(), W.BuildPath(), W.AppendPath();
  }

  lemma {:isolate_assertions} NormalFiles(cmd: Schema.ChmodCmd, plan: Base.SpecModePlan,
    scope: Spec.Scope, fs: W.FileSystem, native: W.CwdContext, cursor: nat,
    result: Spec.State, observation: Spec.Files) returns (logical: seq<Recursive.RecursiveVisit>)
    requires cmd.recursive && scope.context.cwd == scope.cwd
    requires C.CwdContextFields(fs, native)
    requires Spec.FilesFields(cmd.files, cmd, plan, scope, fs, native, cursor, result, observation)
    requires Spec.SuccessfulFiles(cmd, scope, observation) && Spec.CompatibleFiles(cmd, scope, observation)
    ensures Recursive.TopLevelOutcomeSpec(cmd, plan, scope.cwd, logical, fs,
      result.fs, result.output, result.diagnostics, result.ok, scope.now)
  {
    hide *;
    reveal Spec.FilesFields(), Spec.SuccessfulFiles(), Spec.CompatibleFiles();
    logical := [];
    var i: nat := 0;
    assert Recursive.VisitsOutcomeSpec(cmd, plan, logical, {}, fs, observation.states[0].fs,
      observation.states[0].output, observation.states[0].diagnostics, observation.states[0].ok, scope.now) by {
      reveal Recursive.VisitsOutcomeSpec();
    }
    while i < |cmd.files|
      invariant i <= |cmd.files| && |logical| == i
      invariant C.CwdContextFields(observation.states[i].fs, observation.states[i].native)
      invariant Recursive.VisitsOutcomeSpec(cmd, plan, logical, {}, fs, observation.states[i].fs,
        observation.states[i].output, observation.states[i].diagnostics, observation.states[i].ok, scope.now)
      invariant forall j: nat | j < i ::
        Recursive.VisitIdentitySpec(logical[j]).displayPath == cmd.files[j] &&
        Recursive.VisitIdentitySpec(logical[j]).accessPath == Base.MakeAbsolute(scope.cwd, cmd.files[j]) &&
        Recursive.VisitIdentitySpec(logical[j]).isTopLevel
      decreases |cmd.files|-i
    {
      var before := observation.states[i];
      var step := observation.visits[i];
      assert Spec.FileStepFields(cmd.files[i], cmd, plan, scope, before, observation.states[i+1], step);
      reveal Spec.FileStepFields();
      TopPath(scope.cwd, before.native, cmd.files[i]);
      var logicalStep := Proof.NormalVisit(cmd, plan, scope, cmd.files[i], Operand.CwdOperand(cmd.files[i]),
        true, {}, {}, before.fs, before.native, before.cursor, step);
      var observed := Spec.Result(step);
      assert C.CwdContextFields(observed.fs, observed.native);
      assert observation.states[i+1].fs == observed.fs && observation.states[i+1].native == observed.native;
      Proof.AppendLogicalVisits(cmd, plan, logical, logicalStep, {}, fs, before.fs, observed.fs,
        before.output, before.diagnostics, before.ok, observed.output, observed.diagnostics, observed.ok, scope.now);
      logical := logical+[logicalStep];
      assert Recursive.VisitsOutcomeSpec(cmd, plan, logical, {}, fs, observation.states[i+1].fs,
        observation.states[i+1].output, observation.states[i+1].diagnostics, observation.states[i+1].ok, scope.now);
      i := i+1;
    }
    reveal Recursive.TopLevelOutcomeSpec();
  }
}
