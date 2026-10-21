include "ChmodDescriptorSpec.dfy"

module ChmodDescriptorPrincipalSpec {
  import W = BenchWorld
  import BenchIO
  import C = IOContract
  import Base = ChmodSpec
  import Recursive = ChmodRecursiveSpec
  import Descriptor = ChmodDescriptorSpec
  import Operand = ChmodOperandSpec
  import Schema = ChmodSchema

  datatype PreparedWitness = PreparedWitness(plan: Base.SpecModePlan,
                                             result: Descriptor.State, files: Descriptor.Files)

  predicate EarlyCase(cmd: Schema.ChmodCmd)
  {
    cmd.mode == Schema.ModeHelp || cmd.mode == Schema.ModeVersion ||
    (cmd.recursive && cmd.dereferenceMode == 1 && cmd.traversalMode == 0) ||
    (cmd.seenReference && cmd.diagnoseSurprises) || |cmd.files| == 0 ||
    (!cmd.seenReference && !Schema.IsValidModeExpr(cmd.modeExpr))
  }

  ghost predicate EarlyFields(cmd: Schema.ChmodCmd, fs: W.FileSystem, native: W.CwdContext,
                              cursor: nat, afterFs: W.FileSystem, afterNative: W.CwdContext, afterCursor: nat,
                              output: W.Bytes, diagnostics: W.Bytes, exit: int)
  {
    afterFs == fs && afterNative == native && afterCursor == cursor &&
    if cmd.mode == Schema.ModeHelp then
      output == Base.HelpTextSpec() && diagnostics == [] && exit == 0
    else if cmd.mode == Schema.ModeVersion then
      output == Base.VersionTextSpec() && diagnostics == [] && exit == 0
    else if cmd.recursive && cmd.dereferenceMode == 1 && cmd.traversalMode == 0 then
      output == [] && diagnostics == Recursive.RecursiveDereferenceRequirementMessageSpec() && exit == 1
    else if cmd.seenReference && cmd.diagnoseSurprises then
      output == [] && diagnostics == Base.CombineModeReferenceMessageSpec() && exit == 1
    else if |cmd.files| == 0 then
      output == [] && diagnostics == Base.MissingOperandMessageSpec(cmd) && exit == 1
    else
      !cmd.seenReference && !Schema.IsValidModeExpr(cmd.modeExpr) &&
      output == [] && diagnostics == Base.InvalidModeMessageSpec(cmd.modeExpr) && exit == 1
  }

  ghost predicate ReferenceFailureFields(cmd: Schema.ChmodCmd, fs: W.FileSystem,
                                         context: Base.ObservationContext, native: W.CwdContext,
                                         afterFs: W.FileSystem, afterNative: W.CwdContext, afterCursor: nat,
                                         output: W.Bytes, diagnostics: W.Bytes, exit: int)
  {
    var reference := Operand.StatusAt(context, fs, native,
                                      Operand.CwdOperand(cmd.referenceFile), 0, true);
    cmd.seenReference && reference.Err? && afterFs == fs &&
    afterNative == Operand.AtOffset(native, 1) && afterCursor == context.cursor+1 &&
    output == [] && diagnostics == Base.ReferenceErrorMessageSpec(cmd.referenceFile,
                                                                  C.CLocaleErrnoTextResult(C.ResultErrno(reference))) && exit == 1
  }

  ghost predicate ModePlanFields(cmd: Schema.ChmodCmd, fs: W.FileSystem,
                                 props: map<string,string>, context: Base.ObservationContext, native: W.CwdContext,
                                 plan: Base.SpecModePlan, planNative: W.CwdContext, cursor: nat)
  {
    if cmd.seenReference then
      var reference := Operand.StatusAt(context, fs, native,
                                        Operand.CwdOperand(cmd.referenceFile), 0, true);
      reference.Ok? && plan == Base.SpecReferenceModePlan(reference.v.mode) &&
      cursor == context.cursor+1 && planNative == Operand.AtOffset(native, 1)
    else
      Base.SpecGeneralModePlanRelation(cmd.modeExpr, C.GetUmaskResultFields(props), plan) &&
      cursor == context.cursor && planNative == native
  }

  ghost predicate RootFields(cmd: Schema.ChmodCmd, fs: W.FileSystem,
                             context: Base.ObservationContext, now: int, directories: W.DirectoryObservations,
                             planNative: W.CwdContext, planCursor: nat,
                             scope: Descriptor.Scope, filesNative: W.CwdContext, filesCursor: nat)
  {
    scope.context == context && scope.cwd == context.cwd && scope.now == now &&
    scope.directories == directories &&
    if cmd.recursive && cmd.preserveRoot then
      var root := Operand.StatusAt(Base.AtCursor(context, planCursor), fs,
                                   planNative, Operand.CwdOperand("/"), 0, false);
      root.Ok? && scope.root == Descriptor.RootChecked(root.v.hostKey) &&
      filesCursor == planCursor+1 && filesNative == Operand.AtOffset(planNative, 1)
    else
      scope.root.RootUnchecked? && filesCursor == planCursor && filesNative == planNative
  }

  ghost predicate RootFailureFields(cmd: Schema.ChmodCmd, fs: W.FileSystem,
                                    context: Base.ObservationContext, planNative: W.CwdContext, planCursor: nat,
                                    afterFs: W.FileSystem, afterNative: W.CwdContext, afterCursor: nat,
                                    output: W.Bytes, diagnostics: W.Bytes, exit: int)
  {
    var root := Operand.StatusAt(Base.AtCursor(context, planCursor), fs,
                                 planNative, Operand.CwdOperand("/"), 0, false);
    cmd.recursive && cmd.preserveRoot && root.Err? && afterFs == fs &&
    afterNative == Operand.AtOffset(planNative, 1) && afterCursor == planCursor+1 &&
    output == [] && diagnostics == Base.ReferenceErrorMessageSpec("/",
                                                                  C.CLocaleErrnoTextResult(C.ResultErrno(root))) && exit == 1
  }

  ghost predicate PreparedFields(cmd: Schema.ChmodCmd, scope: Descriptor.Scope,
                                 fs: W.FileSystem, native: W.CwdContext, cursor: nat,
                                 afterFs: W.FileSystem, afterNative: W.CwdContext, afterCursor: nat,
                                 output: W.Bytes, diagnostics: W.Bytes, exit: int, observation: PreparedWitness)
  {
    Descriptor.FilesFields(cmd.files, cmd, observation.plan, scope, fs, native, cursor,
                           observation.result, observation.files) &&
    observation.result.fs == afterFs && observation.result.native == afterNative &&
    observation.result.cursor == afterCursor &&
    output == observation.result.output && diagnostics == observation.result.diagnostics &&
    exit == (if observation.result.ok then 0 else 1)
  }

  ghost predicate NormalOutcomeFields(cmd: Schema.ChmodCmd, scope: Descriptor.Scope,
                                      fs: W.FileSystem, observation: PreparedWitness)
  {
    Descriptor.SuccessfulFiles(cmd, scope, observation.files) &&
    Descriptor.CompatibleFiles(cmd, scope, observation.files) ==>
      if cmd.recursive then
        exists visits: seq<Recursive.RecursiveVisit> ::
          Recursive.TopLevelOutcomeSpec(cmd, observation.plan, scope.cwd, visits, fs,
                                        observation.result.fs, observation.result.output, observation.result.diagnostics,
                                        observation.result.ok, scope.now)
      else
        exists trace: Base.SpecBatchTrace ::
          Base.SpecBatchTraceRelation(cmd.files, cmd, observation.plan, scope.cwd, fs,
                                      [], [], true, observation.result.fs, observation.result.output,
                                      observation.result.diagnostics, observation.result.ok, trace, scope.now)
  }

  twostate predicate PreparedSpec(raw: Schema.ChmodCmdRaw, io: BenchIO.IO,
                                  exit: int, plannedStdout: W.Bytes, plannedStderr: W.Bytes)
    reads io.fsRegion, io.cwdRegion, io.propsRegion, io.nowRegion, io.directoryStateRegion,
          io.dirHandlesRegion, io.statusObservationsRegion, io.trustedNativeFailuresRegion
  {
    var cmd := Schema.Command(raw);
    var context := old(Base.Context(io));
    var native := old(io.cwdContext());
    !Base.SpecExternalDomain(raw) ||
    (io.dirHandles() == old(io.dirHandles()) &&
     io.directoryOrigins() == old(io.directoryOrigins()) &&
     io.directoryCapabilities() == old(io.directoryCapabilities()) &&
     io.directoryObservations() == old(io.directoryObservations()) &&
     if EarlyCase(cmd) then
       EarlyFields(cmd, old(io.fs()), native, context.cursor,
                   io.fs(), io.cwdContext(), io.statusCursor(), plannedStdout, plannedStderr, exit)
     else if cmd.seenReference && Operand.StatusAt(context, old(io.fs()), native,
                                                   Operand.CwdOperand(cmd.referenceFile), 0, true).Err? then
       ReferenceFailureFields(cmd, old(io.fs()), context, native,
                              io.fs(), io.cwdContext(), io.statusCursor(), plannedStdout, plannedStderr, exit)
     else
       exists plan: Base.SpecModePlan, planNative: W.CwdContext, planCursor: nat ::
         ModePlanFields(cmd, old(io.fs()), old(io.props()), context, native, plan, planNative, planCursor) &&
         (RootFailureFields(cmd, old(io.fs()), context, planNative, planCursor,
                            io.fs(), io.cwdContext(), io.statusCursor(), plannedStdout, plannedStderr, exit) ||
          exists scope: Descriptor.Scope, filesNative: W.CwdContext, filesCursor: nat,
            observation: PreparedWitness ::
            RootFields(cmd, old(io.fs()), context, old(io.now()), old(io.directoryObservations()),
                       planNative, planCursor, scope, filesNative, filesCursor) &&
            observation.plan == plan &&
            PreparedFields(cmd, scope, old(io.fs()), filesNative, filesCursor,
                           io.fs(), io.cwdContext(), io.statusCursor(), plannedStdout, plannedStderr, exit, observation) &&
            NormalOutcomeFields(cmd, scope, old(io.fs()), observation)))
  }

  twostate predicate Spec(raw: Schema.ChmodCmdRaw, io: BenchIO.IO, exit: int)
    reads io.fsRegion, io.cwdRegion, io.propsRegion, io.nowRegion, io.directoryStateRegion,
          io.dirHandlesRegion, io.statusObservationsRegion, io.trustedNativeFailuresRegion,
          io.stdoutRegion, io.stderrRegion, io.trustedStreamsRegion
  {
    exists output: W.Bytes, diagnostics: W.Bytes, normalExit: int ::
      PreparedSpec(raw, io, normalExit, output, diagnostics) &&
      Base.EmissionFields(old(io.stdout()), old(io.stderr()), io.stdout(), io.stderr(),
                          io.trustedStreams(), output, diagnostics, normalExit, exit)
  }
}
