include "ChmodDescriptorRuntime.dfy"
include "ChmodDescriptorPrincipalSpec.dfy"
include "ChmodDescriptorProof.dfy"
include "ChmodBatchProof.dfy"
include "ChmodRecursiveFilesProof.dfy"

module ChmodDescriptorCore {
  import W = BenchWorld
  import BenchIO
  import C = IOContract
  import Schema = ChmodSchema
  import Base = ChmodCore
  import BaseSpec = ChmodSpec
  import BaseProof = ChmodProof
  import Recursive = ChmodRecursiveSpec
  import Descriptor = ChmodDescriptorSpec
  import Operand = ChmodOperandSpec
  import Dispatch = ChmodOperandCore
  import Entry = ChmodEntryRuntime
  import Runtime = ChmodDescriptorRuntime
  import RecursiveProof = ChmodRecursiveFilesProof
  import BatchProof = ChmodBatchProof
  import Spec = ChmodDescriptorPrincipalSpec

  method {:isolate_assertions} PrepareEarly(raw: Schema.ChmodCmdRaw, io: BenchIO.IO,
    output: Base.Output) returns (exit: int)
    requires Spec.EarlyCase(Schema.Command(raw))
    requires output.stdout == [] && output.stderr == []
    modifies output
    ensures Spec.PreparedSpec(raw, io, exit, output.stdout, output.stderr)
  {
    hide *;
    reveal Spec.EarlyCase();
    var cmd := Schema.Command(raw);
    if cmd.mode == Schema.ModeHelp {
      output.stdout := BaseSpec.HelpTextSpec();
      exit := 0;
    } else if cmd.mode == Schema.ModeVersion {
      output.stdout := BaseSpec.VersionTextSpec();
      exit := 0;
    } else if cmd.recursive && cmd.dereferenceMode == 1 && cmd.traversalMode == 0 {
      output.stderr := Recursive.RecursiveDereferenceRequirementMessageSpec();
      exit := 1;
    } else if cmd.seenReference && cmd.diagnoseSurprises {
      output.stderr := BaseSpec.CombineModeReferenceMessageSpec();
      exit := 1;
    } else if |cmd.files| == 0 {
      output.stderr := BaseSpec.MissingOperandMessageSpec(cmd);
      exit := 1;
    } else {
      output.stderr := BaseSpec.InvalidModeMessageSpec(cmd.modeExpr);
      exit := 1;
    }
    assert Spec.PreparedSpec(raw, io, exit, output.stdout, output.stderr) by {
      reveal Spec.PreparedSpec(), Spec.EarlyFields(), BaseSpec.Context();
    }
  }

  method {:isolate_assertions} Prepare(raw: Schema.ChmodCmdRaw, io: BenchIO.IO,
    output: Base.Output) returns (exit: int)
    requires output.stdout == [] && output.stderr == []
    modifies io.fsRegion, io.directoryStateRegion, io.statusObservationsRegion, output
    ensures Spec.PreparedSpec(raw, io, exit, output.stdout, output.stderr)
    decreases *
  {
    hide *;
    var cmd := Schema.Command(raw);
    reveal Operand.AtOffset();
    ghost var fs0 := io.fs();
    ghost var context := BaseSpec.Context(io);
    ghost var native0 := io.cwdContext();
    ghost var directories := io.directoryObservations();
    if cmd.mode == Schema.ModeHelp || cmd.mode == Schema.ModeVersion ||
      (cmd.recursive && cmd.dereferenceMode == 1 && cmd.traversalMode == 0) ||
      (cmd.seenReference && cmd.diagnoseSurprises) || |cmd.files| == 0 ||
      (!cmd.seenReference && !Schema.IsValidModeExpr(cmd.modeExpr)) {
      assert Spec.EarlyCase(cmd) by { reveal Spec.EarlyCase(); }
      exit := PrepareEarly(raw, io, output);
      return;
    }
    reveal Spec.EarlyCase();
    var plan := Base.CoreGeneralModePlan(cmd.modeExpr, 0 as bv32);
    if cmd.seenReference {
      assert Operand.AnchorFields(io, Operand.CwdOperand(cmd.referenceFile)) by {
        reveal Operand.AnchorFields(), Operand.AnchorSnapshot();
      }
      var reference := Dispatch.ReadStatus(Operand.CwdOperand(cmd.referenceFile), true, io);
      if reference.Err? {
        output.stderr := Base.ReferenceErrorMessageCore(cmd.referenceFile,
          Base.NativeErrnoTextCore(C.ResultErrno(reference), io));
        exit := 1;
        assert Spec.ReferenceFailureFields(cmd, fs0, context, native0,
          io.fs(), io.cwdContext(), io.statusCursor(), output.stdout, output.stderr, exit) by {
          reveal Spec.ReferenceFailureFields(), Base.ReferenceErrorMessageCore();
        }
        assert Spec.PreparedSpec(raw, io, exit, output.stdout, output.stderr) by {
          reveal Spec.PreparedSpec();
        }
        return;
      }
      plan := Base.CoreReferenceModePlan(reference.v.mode);
    } else {
      var umask := io.GetUmask();
      plan := Base.CoreGeneralModePlan(cmd.modeExpr, umask);
      BaseProof.ValidModeProgramSatisfiesRelation(cmd.modeExpr);
      assert BaseSpec.SpecGeneralModePlanRelation(cmd.modeExpr, umask,
        BaseProof.SpecModePlanOfCore(plan)) by {
        reveal BaseSpec.SpecGeneralModePlanRelation(), BaseProof.SpecModePlanOfCore();
        ghost var changes := BaseProof.SpecChangesOfExpr(cmd.modeExpr);
      }
    }
    ghost var modePlan := BaseProof.SpecModePlanOfCore(plan);
    ghost var planNative := io.cwdContext();
    ghost var planCursor := io.statusCursor();
    assert Spec.ModePlanFields(cmd, fs0, old(io.props()), context, native0,
      modePlan, planNative, planCursor) by {
      reveal Spec.ModePlanFields(), BaseProof.SpecModePlanOfCore(), BaseSpec.Context();
    }
    var rootGuard := Descriptor.RootUnchecked;
    if cmd.recursive && cmd.preserveRoot {
      ghost var rootContext := BaseSpec.Context(io);
      assert rootContext == BaseSpec.AtCursor(context, planCursor) by {
        reveal BaseSpec.Context(), BaseSpec.AtCursor();
      }
      assert Operand.AnchorFields(io, Operand.CwdOperand("/")) by {
        reveal Operand.AnchorFields(), Operand.AnchorSnapshot();
      }
      var root := Dispatch.ReadStatus(Operand.CwdOperand("/"), false, io);
      if root.Err? {
        output.stderr := Base.ReferenceErrorMessageCore("/",
          Base.NativeErrnoTextCore(C.ResultErrno(root), io));
        exit := 1;
        assert Spec.RootFailureFields(cmd, fs0, context, planNative, planCursor,
          io.fs(), io.cwdContext(), io.statusCursor(), output.stdout, output.stderr, exit) by {
          reveal Spec.RootFailureFields(), Base.ReferenceErrorMessageCore();
        }
        assert Spec.PreparedSpec(raw, io, exit, output.stdout, output.stderr) by {
          reveal Spec.PreparedSpec();
        }
        return;
      }
      rootGuard := Descriptor.RootChecked(root.v.hostKey);
    }
    ghost var filesNative := io.cwdContext();
    ghost var filesCursor := io.statusCursor();
    var scope := Descriptor.Scope(context, io.cwd(), io.now(), rootGuard, directories);
    assert Spec.RootFields(cmd, fs0, context, io.now(), directories, planNative,
      planCursor, scope, filesNative, filesCursor) by {
      reveal Spec.RootFields(), BaseSpec.Context();
    }
    assert Entry.ScopeFields(io, scope) by {
      reveal Entry.ScopeFields(), BaseSpec.Context();
    }
    var allOk, files, result := Runtime.RunFiles(cmd.files, cmd, plan, scope, io, output);
    exit := if allOk then 0 else 1;
    ghost var prepared := Spec.PreparedWitness(modePlan, result, files);
    assert Spec.PreparedFields(cmd, scope, fs0, filesNative, filesCursor,
      io.fs(), io.cwdContext(), io.statusCursor(), output.stdout, output.stderr, exit, prepared) by {
      reveal Spec.PreparedFields();
    }
    if Descriptor.SuccessfulFiles(cmd, scope, files) && Descriptor.CompatibleFiles(cmd, scope, files) {
      if cmd.recursive {
        ghost var visits := RecursiveProof.NormalFiles(cmd, modePlan, scope, fs0, filesNative,
          filesCursor, result, files);
      } else {
        ghost var trace := BatchProof.NormalNonrecursiveFiles(cmd, modePlan, scope, fs0, filesNative,
          filesCursor, result, files);
      }
    }
    assert Spec.NormalOutcomeFields(cmd, scope, fs0, prepared) by {
      reveal Spec.NormalOutcomeFields();
    }
    assert Spec.PreparedSpec(raw, io, exit, output.stdout, output.stderr) by {
      reveal Spec.PreparedSpec();
    }
  }

  method RunCore(raw: Schema.ChmodCmdRaw, io: BenchIO.IO) returns (exit: int)
    modifies io.fsRegion, io.stdoutRegion, io.stderrRegion,
      io.directoryStateRegion, io.statusObservationsRegion
    ensures Spec.Spec(raw, io, exit)
    decreases *
  {
    var output := new Base.Output();
    var normalExit := Prepare(raw, io, output);
    exit := Base.Flush(output.stdout, output.stderr, normalExit, io);
    assert Spec.Spec(raw, io, exit) by { reveal Spec.Spec(); }
  }
}
