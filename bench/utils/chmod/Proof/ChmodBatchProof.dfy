include "ChmodNonrecursiveProof.dfy"

module ChmodBatchProof {
  import W = BenchWorld
  import Schema = ChmodSchema
  import Base = ChmodSpec
  import Spec = ChmodDescriptorSpec
  import Steps = ChmodNonrecursiveProof

  lemma {:isolate_assertions} BuildFrom(cmd: Schema.ChmodCmd, plan: Base.SpecModePlan,
                                        scope: Spec.Scope, files: seq<string>, fs: W.FileSystem, native: W.CwdContext,
                                        cursor: nat, result: Spec.State, observation: Spec.Files, position: nat)
    returns (trace: Base.SpecBatchTrace)
    requires !cmd.recursive && scope.context.cwd == scope.cwd
    requires Spec.FilesFields(files, cmd, plan, scope, fs, native, cursor, result, observation)
    requires Spec.SuccessfulFiles(cmd, scope, observation) && Spec.CompatibleFiles(cmd, scope, observation)
    requires position <= |files|
    ensures var before := observation.states[position];
            Base.SpecBatchTraceRelation(files[position..], cmd, plan, scope.cwd, before.fs,
                                        before.output, before.diagnostics, before.ok, result.fs, result.output,
                                        result.diagnostics, result.ok, trace, scope.now)
    decreases |files|-position
  {
    hide *;
    reveal Spec.FilesFields(), Spec.SuccessfulFiles(), Spec.CompatibleFiles();
    var before := observation.states[position];
    if position == |files| {
      trace := Base.SpecBatchEnd(before.fs, before.output, before.diagnostics, before.ok);
      assert Base.SpecBatchTraceRelation(files[position..], cmd, plan, scope.cwd, before.fs,
                                         before.output, before.diagnostics, before.ok, result.fs, result.output,
                                         result.diagnostics, result.ok, trace, scope.now) by { reveal Base.SpecBatchTraceRelation(); }
    } else {
      var after := observation.states[position+1];
      var visit := observation.visits[position];
      assert Spec.FileStepFields(files[position], cmd, plan, scope, before, after, visit);
      reveal Spec.FileStepFields();
      var step := Steps.NonrecursiveVisit(cmd, plan, scope, files[position], before.fs,
                                          before.native, before.cursor, visit);
      var rest := BuildFrom(cmd, plan, scope, files, fs, native, cursor, result, observation, position+1);
      trace := Base.SpecBatchNext(before.fs, before.output, before.diagnostics, before.ok, rest);
      assert files[position..][1..] == files[position+1..];
      assert Base.SpecBatchTraceRelation(files[position..], cmd, plan, scope.cwd, before.fs,
                                         before.output, before.diagnostics, before.ok, result.fs, result.output,
                                         result.diagnostics, result.ok, trace, scope.now) by { reveal Base.SpecBatchTraceRelation(); }
    }
  }

  lemma {:isolate_assertions} NormalNonrecursiveFiles(cmd: Schema.ChmodCmd, plan: Base.SpecModePlan,
                                                      scope: Spec.Scope, fs: W.FileSystem, native: W.CwdContext, cursor: nat,
                                                      result: Spec.State, observation: Spec.Files) returns (trace: Base.SpecBatchTrace)
    requires !cmd.recursive && scope.context.cwd == scope.cwd
    requires Spec.FilesFields(cmd.files, cmd, plan, scope, fs, native, cursor, result, observation)
    requires Spec.SuccessfulFiles(cmd, scope, observation) && Spec.CompatibleFiles(cmd, scope, observation)
    ensures Base.SpecBatchTraceRelation(cmd.files, cmd, plan, scope.cwd, fs, [], [], true,
                                        result.fs, result.output, result.diagnostics, result.ok, trace, scope.now)
  {
    hide *;
    trace := BuildFrom(cmd, plan, scope, cmd.files, fs, native, cursor, result, observation, 0);
    reveal Spec.FilesFields();
  }
}
