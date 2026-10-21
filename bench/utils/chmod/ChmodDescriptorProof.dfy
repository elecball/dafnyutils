include "ChmodDirectoryProof.dfy"
include "ChmodRecursiveProof.dfy"

module ChmodDescriptorProof {
  import W = BenchWorld
  import C = IOContract
  import R = Results
  import Base = ChmodSpec
  import BaseCore = ChmodCore
  import BaseProof = ChmodProof
  import Recursive = ChmodRecursiveSpec
  import RecursiveProof = ChmodRecursiveProof
  import Spec = ChmodDescriptorSpec
  import Operand = ChmodOperandSpec
  import Schema = ChmodSchema
  import Normal = ChmodNormalEntryProof
  import Visits = ChmodVisitFrameProof
  import Directory = ChmodDirectoryProof
  import State = ChmodObservationProof

  lemma {:isolate_assertions} AppendLogicalVisits(cmd: Schema.ChmodCmd, plan: Base.SpecModePlan,
                                                  visits: seq<Recursive.RecursiveVisit>, child: Recursive.RecursiveVisit, active: set<seq<string>>,
                                                  fs0: W.FileSystem, fs1: W.FileSystem, fs2: W.FileSystem,
                                                  output: W.Bytes, diagnostics: W.Bytes, ok: bool,
                                                  childOutput: W.Bytes, childDiagnostics: W.Bytes, childOk: bool, now: int)
    requires Recursive.VisitsOutcomeSpec(cmd, plan, visits, active, fs0, fs1, output, diagnostics, ok, now)
    requires Recursive.VisitOutcomeSpec(cmd, plan, child, active, fs1, fs2, childOutput, childDiagnostics, childOk, now)
    ensures Recursive.VisitsOutcomeSpec(cmd, plan, visits + [child], active, fs0, fs2,
                                        output + childOutput, diagnostics + childDiagnostics, ok && childOk, now)
    decreases |visits|
  {
    hide *;
    reveal Recursive.VisitsOutcomeSpec();
    if |visits| == 0 {
      assert visits == [] && fs0 == fs1 && output == [] && diagnostics == [] && ok;
      assert Recursive.VisitsOutcomeSpec(cmd, plan, [], active, fs2, fs2, [], [], true, now);
      IntroduceLogicalCons(cmd, plan, child, [], active, fs1, fs2, fs2,
                           childOutput, childDiagnostics, childOk, [], [], true, now);
      assert visits + [child] == [child] + [];
      assert Recursive.VisitsOutcomeSpec(cmd, plan, visits + [child], active, fs0, fs2,
                                         output + childOutput, diagnostics + childDiagnostics, ok && childOk, now);
    } else {
      var stepFs: W.FileSystem, stepOutput: W.Bytes, stepDiagnostics: W.Bytes, stepOk: bool,
          restOutput: W.Bytes, restDiagnostics: W.Bytes, restOk: bool :|
        Recursive.VisitOutcomeSpec(cmd, plan, visits[0], active, fs0, stepFs,
                                   stepOutput, stepDiagnostics, stepOk, now) &&
        Recursive.VisitsOutcomeSpec(cmd, plan, visits[1..], active, stepFs, fs1,
                                    restOutput, restDiagnostics, restOk, now) &&
        output == stepOutput + restOutput && diagnostics == stepDiagnostics + restDiagnostics && ok == (stepOk && restOk);
      AppendLogicalVisits(cmd, plan, visits[1..], child, active, stepFs, fs1, fs2,
                          restOutput, restDiagnostics, restOk, childOutput, childDiagnostics, childOk, now);
      IntroduceLogicalCons(cmd, plan, visits[0], visits[1..] + [child], active, fs0, stepFs, fs2,
                           stepOutput, stepDiagnostics, stepOk, restOutput + childOutput, restDiagnostics + childDiagnostics,
                           restOk && childOk, now);
      assert visits + [child] == [visits[0]] + (visits[1..] + [child]);
      assert (visits + [child])[1..] == visits[1..] + [child];
      assert Recursive.VisitsOutcomeSpec(cmd, plan, (visits + [child])[1..], active, stepFs, fs2,
                                         restOutput + childOutput, restDiagnostics + childDiagnostics, restOk && childOk, now);
    }
  }

  lemma MakeAbsoluteShape(cwd: W.Path, path: W.Path)
    ensures Base.MakeAbsolute(cwd, path) == "" || W.IsAbsolutePath(Base.MakeAbsolute(cwd, path))
  {
    BaseProof.BridgeMakeAbsolute(cwd, path);
    reveal BaseCore.MakeAbsoluteCore(), W.IsAbsolutePath(), W.BuildPath(), W.AppendPath();
  }

  lemma {:isolate_assertions} IntroduceLogicalCons(cmd: Schema.ChmodCmd, plan: Base.SpecModePlan,
                                                   first: Recursive.RecursiveVisit, rest: seq<Recursive.RecursiveVisit>, active: set<seq<string>>,
                                                   fs: W.FileSystem, middle: W.FileSystem, after: W.FileSystem,
                                                   firstOut: W.Bytes, firstErr: W.Bytes, firstOk: bool, restOut: W.Bytes, restErr: W.Bytes, restOk: bool, now: int)
    requires Recursive.VisitOutcomeSpec(cmd, plan, first, active, fs, middle, firstOut, firstErr, firstOk, now)
    requires Recursive.VisitsOutcomeSpec(cmd, plan, rest, active, middle, after, restOut, restErr, restOk, now)
    ensures Recursive.VisitsOutcomeSpec(cmd, plan, [first] + rest, active, fs, after,
                                        firstOut + restOut, firstErr + restErr, firstOk && restOk, now)
  {
    hide *;
    reveal Recursive.VisitsOutcomeSpec();
    assert ([first] + rest)[0] == first && ([first] + rest)[1..] == rest;
  }

  lemma {:isolate_assertions} NormalVisit(cmd: Schema.ChmodCmd, plan: Base.SpecModePlan,
                                          scope: Spec.Scope, display: string, operand: Operand.Operand, top: bool,
                                          keys: set<W.HostInodeKey>, paths: set<seq<string>>, fs: W.FileSystem,
                                          native: W.CwdContext, cursor: nat, visit: Spec.Visit) returns (logical: Recursive.RecursiveVisit)
    requires cmd.recursive && scope.context.cwd == scope.cwd
    requires C.CwdContextFields(fs, native)
    requires Spec.VisitFields(cmd, plan, scope, display, operand, top, keys, fs, native, cursor, visit)
    requires Spec.SuccessfulVisit(cmd, scope, visit) && Spec.CompatibleVisit(cmd, scope, keys, paths, visit)
    requires (display == "/") <==> (Operand.ModelPath(scope.cwd, native, operand) == "/")
    ensures Recursive.VisitIdentitySpec(logical) == Normal.LogicalIdentity(cmd, scope, visit.entry)
    ensures Recursive.VisitIdentitySpec(logical).displayPath == display &&
            Recursive.VisitIdentitySpec(logical).accessPath == Operand.ModelPath(scope.cwd, native, operand) &&
            Recursive.VisitIdentitySpec(logical).isTopLevel == top
    ensures var result := Spec.Result(visit);
            Recursive.VisitOutcomeSpec(cmd, plan, logical, paths, fs,
                                       result.fs, result.output, result.diagnostics, result.ok, scope.now)
    ensures C.CwdContextFields(Spec.Result(visit).fs, Spec.Result(visit).native)
    decreases visit
  {
    hide *;
    reveal Spec.VisitFields(), Spec.SuccessfulVisit(), Spec.CompatibleVisit(), Spec.Result();
    var entry := visit.entry;
    assert entry.fs == fs && entry.native == native && entry.cursor == cursor &&
           entry.identity.displayPath == display && entry.identity.operand == operand && entry.identity.top == top by {
      reveal Spec.EntryFields();
    }
    Visits.VisitFrame(cmd, plan, scope, display, operand, top, keys, fs, native, cursor, visit);
    Normal.SuccessfulEntry(cmd, scope, display, operand, top, fs, native, cursor, entry);
    var identity := Normal.LogicalIdentity(cmd, scope, entry);
    var result := Spec.Result(visit);
    if Normal.LogicalSkip(cmd, entry) {
      assert visit.NodeVisit? && visit.listing.ListingSkipped?;
      assert entry.identity.isSymlink && !Spec.ModeFollow(cmd, top) by { reveal Normal.LogicalSkip(); }
      Normal.SkipChange(cmd, plan, scope, entry, visit.change);
      logical := Recursive.RecursiveSkip(identity);
      assert Recursive.VisitOutcomeBodySpec(cmd, plan, logical, paths, fs,
                                            result.fs, result.output, result.diagnostics, result.ok, scope.now) by {
        reveal Recursive.VisitOutcomeBodySpec(), Recursive.VisitIdentitySpec();
      }
    } else if visit.EntryVisit? {
      assert entry.decision.EntryPreserved?;
      logical := Recursive.RecursivePreserveRoot(identity, entry.decision.alias);
      assert identity.isSymlink ==> Recursive.TraversalFollowSpec(cmd, top) || Recursive.ChmodFollowSpec(cmd, top) by {
        reveal Normal.LogicalSkip(), Spec.ModeFollow();
      }
      assert Recursive.VisitOutcomeBodySpec(cmd, plan, logical, paths, fs,
                                            result.fs, result.output, result.diagnostics, result.ok, scope.now) by {
        reveal Recursive.VisitOutcomeBodySpec(), Recursive.VisitIdentitySpec(), Spec.EntryFields(),
               Spec.CompatibleEntry(), Normal.LogicalIdentity(), Spec.MathematicalIdentity();
      }
    } else {
      var change := visit.change;
      var parent := Normal.SuccessfulChange(cmd, plan, scope, entry, change);
      assert identity.isDirectory == entry.identity.isDirectory &&
             identity.isSymlink == entry.identity.isSymlink by {
        reveal Normal.LogicalIdentity(), Spec.MathematicalIdentity();
      }
      assert !identity.isSymlink || Recursive.TraversalFollowSpec(cmd, top) || Recursive.ChmodFollowSpec(cmd, top) by {
        reveal Normal.LogicalSkip(), Spec.ModeFollow();
      }
      assert !(cmd.preserveRoot && identity.isDirectory && identity.resolvedPath == "/") by {
        reveal Spec.EntryFields(), Spec.CompatibleEntry(), Normal.LogicalIdentity();
      }
      var listing := visit.listing;
      if listing.ListingSkipped? {
        logical := Recursive.RecursiveNode(identity, [], Recursive.RecursiveEof);
        assert Recursive.VisitsOutcomeSpec(cmd, plan, [], paths+{W.PathSegments(identity.resolvedPath)},
                                           parent.fs, parent.fs, [], [], true, scope.now) by { reveal Recursive.VisitsOutcomeSpec(); }
        assert Recursive.VisitOutcomeBodySpec(cmd, plan, logical, paths, fs,
                                              result.fs, result.output, result.diagnostics, result.ok, scope.now) by {
          reveal Recursive.VisitOutcomeBodySpec(), Recursive.VisitIdentitySpec(),
                 Recursive.RecursiveReadStdoutSpec(), Recursive.RecursiveReadStderrSpec();
        }
      } else {
        assert listing.ListingOpened?;
        var entries := Directory.Schedule(cmd, plan, scope, display, operand, top, keys, fs, native, cursor, visit);
        var n := |listing.children|;
        var logicalChildren: seq<Recursive.RecursiveVisit> := [];
        var childPaths := paths+{W.PathSegments(identity.resolvedPath)};
        var descendantsOutput: W.Bytes := [];
        var descendantsDiagnostics: W.Bytes := [];
        var descendantsOk := true;
        var i: nat := 0;
        assert Recursive.VisitsOutcomeSpec(cmd, plan, logicalChildren, childPaths, parent.fs,
                                           listing.states[0].fs, descendantsOutput, descendantsDiagnostics, descendantsOk, scope.now) by {
          reveal Recursive.VisitsOutcomeSpec();
        }
        while i < n
          invariant i <= n && |logicalChildren| == i
          invariant Recursive.VisitsOutcomeSpec(cmd, plan, logicalChildren, childPaths, parent.fs,
                                                listing.states[i].fs, descendantsOutput, descendantsDiagnostics, descendantsOk, scope.now)
          invariant listing.states[i].output == parent.stdoutChunk+descendantsOutput
          invariant listing.states[i].diagnostics == parent.stderrChunk+descendantsDiagnostics
          invariant listing.states[i].ok == (parent.ok && descendantsOk)
          invariant forall j: nat | j < i :: Recursive.VisitMatchesEntrySpec(identity, entries[j], logicalChildren[j])
          decreases n-i
        {
          var before := listing.states[i];
          var read := listing.readSteps[i];
          var child := listing.children[i];
          assert Spec.DirectoryStepFields(cmd, plan, scope, entry.identity, keys, listing.handle,
                                          before, listing.states[i+1], read, child);
          reveal Spec.DirectoryStepFields();
          assert C.ContextOperationSpec(before.fs, read.before, scope.directories, W.DirectoryReadNext,
                                        listing.handle, 0, "", before.cursor, before.cursor, read.response, read.after) by {
            reveal Spec.ReadFields();
          }
          State.DirectoryState(before.fs, read.before, scope.directories, W.DirectoryReadNext,
                               listing.handle, before.cursor, read.response, read.after);
          Directory.AppendLeafNotRoot(display, entries[i].name);
          Directory.AppendLeafNotRoot(identity.resolvedPath, entries[i].name);
          assert !Normal.LogicalSkip(cmd, entry) && identity == Spec.MathematicalIdentity(scope, entry);
          var logicalChild := NormalVisit(cmd, plan, scope, W.AppendPath(display, entries[i].name),
                                          Operand.DirectoryOperand(listing.handle, entries[i].name), false, keys+{entry.identity.key},
                                          childPaths, before.fs, read.after, before.cursor, child);
          var childResult := Spec.Result(child);
          assert listing.states[i+1].fs == childResult.fs && listing.states[i+1].output == before.output+childResult.output &&
                 listing.states[i+1].diagnostics == before.diagnostics+childResult.diagnostics &&
                 listing.states[i+1].ok == (before.ok && childResult.ok);
          AppendLogicalVisits(cmd, plan, logicalChildren, logicalChild, childPaths,
                              parent.fs, before.fs, childResult.fs, descendantsOutput, descendantsDiagnostics, descendantsOk,
                              childResult.output, childResult.diagnostics, childResult.ok, scope.now);
          assert Recursive.VisitMatchesEntrySpec(identity, entries[i], logicalChild) by { reveal Recursive.VisitMatchesEntrySpec(); }
          logicalChildren := logicalChildren+[logicalChild];
          descendantsOutput := descendantsOutput+childResult.output;
          descendantsDiagnostics := descendantsDiagnostics+childResult.diagnostics;
          descendantsOk := descendantsOk && childResult.ok;
          i := i+1;
        }
        logical := Recursive.RecursiveNode(identity, logicalChildren, Recursive.RecursiveEof);
        assert result.fs == listing.states[n].fs && result.output == listing.states[n].output &&
               result.diagnostics == listing.states[n].diagnostics && result.ok == listing.states[n].ok;
        assert W.PathSegments(identity.resolvedPath) !in paths;
        assert result.output == parent.stdoutChunk+descendantsOutput &&
               result.diagnostics == parent.stderrChunk+descendantsDiagnostics && result.ok == (parent.ok && descendantsOk);
        reveal Recursive.RecursiveReadStdoutSpec(), Recursive.RecursiveReadStderrSpec();
        RecursiveProof.IntroduceRecursiveNodeOutcome(cmd, plan, identity, logicalChildren, Recursive.RecursiveEof,
                                                     paths, fs, parent, result.fs, result.output, result.diagnostics, result.ok, scope.now);
      }
    }
    Recursive.IntroduceVisitOutcomeSpec(cmd, plan, logical, paths, fs,
                                        result.fs, result.output, result.diagnostics, result.ok, scope.now);
    reveal Recursive.VisitIdentitySpec();
  }
}
