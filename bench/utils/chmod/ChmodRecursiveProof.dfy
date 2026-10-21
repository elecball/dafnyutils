include "../../core/World.dfy"
include "ChmodSchema.dfy"
include "ChmodSpec.dfy"
include "ChmodCore.dfy"
include "ChmodProof.dfy"
include "ChmodRecursiveSpec.dfy"
include "ChmodRecursiveCore.dfy"
include "ChmodRecursiveRuntimeProof.dfy"

module ChmodRecursiveProof {
  import BW = BenchWorld
  import IOC = IOContract
  import BenchIO
  import Schema = ChmodSchema
  import BaseSpec = ChmodSpec
  import BaseCore = ChmodCore
  import BaseProof = ChmodProof
  import Spec = ChmodRecursiveSpec
  import Core = ChmodRecursiveCore

  function SpecIdentityOfCore(identity: Core.RecursiveIdentity): Spec.RecursiveIdentity
  {
    Spec.RecursiveIdentity(
      identity.displayPath,
      identity.accessPath,
      identity.resolvedPath,
      identity.isTopLevel,
      identity.isSymlink,
      identity.isDirectory
    )
  }

  function SpecVisitOfCore(visit: Core.RecursiveVisit): Spec.RecursiveVisit
    decreases visit
  {
    match visit
    case RecursiveSkip(identity) =>
      Spec.RecursiveSkip(SpecIdentityOfCore(identity))
    case RecursiveAccessFailure(identity, err, failureKind) =>
      Spec.RecursiveAccessFailure(
        SpecIdentityOfCore(identity),
        err,
        Core.SpecFailureKindOfCore(failureKind)
      )
    case RecursivePreserveRoot(identity, alias) =>
      Spec.RecursivePreserveRoot(SpecIdentityOfCore(identity), alias)
    case RecursiveNode(identity, children, terminal) =>
      Spec.RecursiveNode(
        SpecIdentityOfCore(identity),
        SpecVisitsOfCore(children),
        Core.SpecTerminalOfCore(terminal)
      )
  }

  function SpecVisitsOfCore(visits: seq<Core.RecursiveVisit>): seq<Spec.RecursiveVisit>
    decreases visits
  {
    if |visits| == 0 then []
    else [SpecVisitOfCore(visits[0])] + SpecVisitsOfCore(visits[1..])
  }

  lemma SpecVisitsShape(visits: seq<Core.RecursiveVisit>)
    ensures |SpecVisitsOfCore(visits)| == |visits|
    ensures forall i :: 0 <= i < |visits| ==>
                          SpecVisitsOfCore(visits)[i] == SpecVisitOfCore(visits[i])
    decreases visits
  {
    if |visits| > 0 {
      SpecVisitsShape(visits[1..]);
    }
  }

  lemma BridgeVisitSize(visit: Core.RecursiveVisit)
    ensures Core.VisitSizeCore(visit) == Spec.VisitSizeSpec(SpecVisitOfCore(visit))
    decreases visit
  {
    match visit
    case RecursiveSkip(_) | RecursiveAccessFailure(_, _, _) |
        RecursivePreserveRoot(_, _) =>
    case RecursiveNode(_, children, _) => BridgeVisitsSize(children);
  }

  lemma BridgeVisitsSize(visits: seq<Core.RecursiveVisit>)
    ensures Core.VisitsSizeCore(visits) == Spec.VisitsSizeSpec(SpecVisitsOfCore(visits))
    decreases visits
  {
    if |visits| > 0 {
      BridgeVisitSize(visits[0]);
      BridgeVisitsSize(visits[1..]);
    }
  }

  lemma BridgeResolutionFailureKind(
    cmd: Schema.ChmodCmd,
    isTopLevel: bool,
    isSymlink: bool,
    err: int
  )
    ensures Core.SpecFailureKindOfCore(
              Core.ResolutionFailureKindCore(cmd, isTopLevel, isSymlink, err)
            ) == Spec.ResolutionFailureKindSpec(
                   cmd, isTopLevel, isSymlink, err
                 )
  {

  }

  lemma BridgeApplyResolved(
    cmd: Schema.ChmodCmd,
    plan: BaseCore.CoreModePlan,
    identity: Core.RecursiveIdentity,
    fs: BW.FileSystem,
    now: int
  )
    ensures Spec.ApplyResolvedSpecRelation(
              cmd,
              BaseProof.SpecModePlanOfCore(plan),
              SpecIdentityOfCore(identity),
              fs,
              BaseProof.SpecPathResultOfCore(
                Core.ApplyResolvedCore(cmd, plan, identity, fs, now)
              ),
              now
            )
  {

    if identity.isSymlink && !Spec.ChmodFollowSpec(cmd, identity.isTopLevel) {

    } else if !BW.FsContainsPath(fs, identity.resolvedPath) {

    } else {
      var node := BW.FsNodeAt(fs, identity.resolvedPath);
      var before := BW.NodeMode(node);
      BaseProof.BridgePlannedMode(plan, before, identity.isDirectory);
      var desired := BaseCore.CorePlannedMode(plan, before, identity.isDirectory);
      BaseProof.BridgeModeSetFs(
        fs, true, identity.resolvedPath, desired, now
      );
      BaseProof.BridgeSuccessfulChangeResult(
        cmd,
        plan,
        identity.displayPath,
        identity.accessPath,
        true,
        before,
        BW.NormalizeMode(desired),
        identity.isDirectory,
        BaseCore.CoreModeSetFs(
          fs, true, identity.resolvedPath, desired, now
        )
      );
      BaseProof.BridgeNaiveMode(plan, before, identity.isDirectory);
      BaseProof.BridgeDiagnoseSurprise(
        cmd,
        plan,
        before,
        BW.NormalizeMode(desired),
        identity.isDirectory
      );

    }
  }

  lemma BridgeVisitIdentity(visit: Core.RecursiveVisit)
    ensures SpecIdentityOfCore(Core.VisitIdentityCore(visit)) ==
            Spec.VisitIdentitySpec(SpecVisitOfCore(visit))
  {
  }

  lemma BridgeIdentityResolves(
    fs: BW.FileSystem,
    identity: Core.RecursiveIdentity
  )
    requires Core.IdentityResolvesCore(fs, identity)
    ensures Spec.IdentityResolvesSpec(fs, SpecIdentityOfCore(identity))
  {
  }

  lemma BridgeSkipVisit(
    cmd: Schema.ChmodCmd,
    identity: Core.RecursiveIdentity,
    fs: BW.FileSystem
  )
    requires Core.SkipVisitCore(cmd, identity, fs)
    ensures Spec.SkipVisitSpec(cmd, SpecIdentityOfCore(identity), fs)
  {

    var followed := IOC.ResolvePathForMetadataFields(
      fs, identity.accessPath, true
    );
    if followed.Err? {

    }
  }

  lemma BridgeAccessFailureVisit(
    cmd: Schema.ChmodCmd,
    identity: Core.RecursiveIdentity,
    err: int,
    failureKind: Core.RecursiveFailureKind,
    fs: BW.FileSystem
  )
    requires Core.AccessFailureVisitCore(
               cmd, identity, err, failureKind, fs
             )
    ensures Spec.AccessFailureVisitSpec(
              cmd,
              SpecIdentityOfCore(identity),
              err,
              Core.SpecFailureKindOfCore(failureKind),
              fs
            )
  {

    BridgeResolutionFailureKind(
      cmd, identity.isTopLevel, identity.isSymlink, err
    );
  }

  lemma BridgeSchedule(
    snapshot: set<BW.DirEntry>,
    entries: seq<BW.DirEntry>,
    terminal: Core.RecursiveTerminal
  )
    ensures Core.ValidOpenSchedule(snapshot, entries, terminal) ==
            Spec.ValidOpenSchedule(
              snapshot, entries, Core.SpecTerminalOfCore(terminal)
            )
  {
  }

  lemma BridgeVisitMatchesEntry(
    parent: Core.RecursiveIdentity,
    entry: BW.DirEntry,
    visit: Core.RecursiveVisit
  )
    requires Core.VisitMatchesEntryCore(parent, entry, visit)
    ensures Spec.VisitMatchesEntrySpec(
              SpecIdentityOfCore(parent), entry, SpecVisitOfCore(visit)
            )
  {
    BridgeVisitIdentity(visit);
  }

  // Package the concrete parent witness without the recursive core's proof context.
  lemma IntroduceRecursiveNodeOutcome(
    cmd: Schema.ChmodCmd,
    plan: BaseSpec.SpecModePlan,
    identity: Spec.RecursiveIdentity,
    children: seq<Spec.RecursiveVisit>,
    terminal: Spec.RecursiveTerminal,
    activeResolved: set<seq<string>>,
    fs0: BW.FileSystem,
    parent: BaseSpec.SpecPathResult,
    fs2: BW.FileSystem,
    stdoutChunk: BW.Bytes,
    stderrChunk: BW.Bytes,
    allOk: bool,
    now: int
  )
    requires Spec.IdentityResolvesSpec(fs0, identity)
    requires !identity.isSymlink ||
             Spec.TraversalFollowSpec(cmd, identity.isTopLevel) ||
             Spec.ChmodFollowSpec(cmd, identity.isTopLevel)
    requires !(cmd.preserveRoot && identity.isDirectory &&
               identity.resolvedPath == "/")
    requires BW.PathSegments(identity.resolvedPath) !in activeResolved
    requires Spec.ApplyResolvedSpecRelation(cmd, plan, identity, fs0, parent, now)
    requires
      if identity.isSymlink && !Spec.TraversalFollowSpec(cmd, identity.isTopLevel) then
        |children| == 0 && terminal.RecursiveEof?
      else if !identity.isDirectory then
        |children| == 0 && terminal.RecursiveEof?
      else
        BW.FsContainsPath(parent.fs, identity.resolvedPath) &&
        exists entries: seq<BW.DirEntry> ::
          |entries| == |children| &&
          Spec.ValidOpenSchedule(
            IOC.DirectoryEntriesForPathFields(parent.fs, identity.resolvedPath),
            entries, terminal
          ) &&
          (forall j :: 0 <= j < |children| ==>
                         Spec.VisitMatchesEntrySpec(identity, entries[j], children[j]))
    requires exists descendantsStdout: BW.Bytes,
               descendantsStderr: BW.Bytes, descendantsOk: bool ::
               Spec.VisitsOutcomeSpec(
                 cmd, plan, children,
                 activeResolved + {BW.PathSegments(identity.resolvedPath)},
                 parent.fs, fs2, descendantsStdout, descendantsStderr, descendantsOk, now
               ) &&
               stdoutChunk == parent.stdoutChunk + descendantsStdout +
               Spec.RecursiveReadStdoutSpec(cmd, identity.displayPath, terminal) &&
               stderrChunk == parent.stderrChunk + descendantsStderr +
               Spec.RecursiveReadStderrSpec(cmd, identity.displayPath, terminal) &&
               allOk == (parent.ok && descendantsOk && terminal.RecursiveEof?)
    ensures Spec.VisitOutcomeBodySpec(
              cmd, plan, Spec.RecursiveNode(identity, children, terminal),
              activeResolved, fs0, fs2, stdoutChunk, stderrChunk, allOk, now
            )
  {
  }

  lemma {:isolate_assertions} {:vcs_split_on_every_assert}
    BridgeVisitOutcome(
    cmd: Schema.ChmodCmd,
    plan: BaseCore.CoreModePlan,
    visit: Core.RecursiveVisit,
    activeResolved: set<seq<string>>,
    fs: BW.FileSystem,
    now: int
  )
    requires Core.ValidVisitCore(
               cmd, plan, visit, activeResolved, fs, now
             )
    ensures
      var result := Core.EvalVisitCore(
                      cmd, plan, visit, activeResolved, fs, now
                    );
      Spec.VisitOutcomeSpec(
        cmd,
        BaseProof.SpecModePlanOfCore(plan),
        SpecVisitOfCore(visit),
        activeResolved,
        fs,
        result.fs,
        result.stdoutChunk,
        result.stderrChunk,
        result.allOk,
        now
      )
    decreases Core.VisitSizeCore(visit), 0
  {
    hide *;
    reveal Core.EvalVisitCore(), Core.VisitIdentityCore(), Core.VisitSizeCore(), Core.VisitsSizeCore();
    reveal SpecVisitOfCore(), SpecIdentityOfCore(), Core.SpecTerminalOfCore(), Spec.VisitIdentitySpec();
    reveal Spec.VisitOutcomeBodySpec(), BaseProof.SpecPathResultOfCore();
    reveal Core.RecursiveReadStdoutCore(), Core.RecursiveReadStderrCore();
    reveal Spec.RecursiveReadStdoutSpec(), Spec.RecursiveReadStderrSpec();
    reveal Core.ValidVisitCore;
    var identity := Core.VisitIdentityCore(visit);
    BridgeVisitIdentity(visit);
    match visit
    case RecursiveSkip(_) =>
      BridgeSkipVisit(cmd, identity, fs);

      var result := Core.EvalVisitCore(
        cmd, plan, visit, activeResolved, fs, now
      );
      assert Spec.VisitOutcomeBodySpec(
          cmd,
          BaseProof.SpecModePlanOfCore(plan),
          SpecVisitOfCore(visit),
          activeResolved,
          fs,
          result.fs,
          result.stdoutChunk,
          result.stderrChunk,
          result.allOk,
          now
        );
      Spec.IntroduceVisitOutcomeSpec(
        cmd,
        BaseProof.SpecModePlanOfCore(plan),
        SpecVisitOfCore(visit),
        activeResolved,
        fs,
        result.fs,
        result.stdoutChunk,
        result.stderrChunk,
        result.allOk,
        now
      );
    case RecursiveAccessFailure(_, err, failureKind) =>
      reveal Core.RecursiveAccessStderrCore();
             BridgeAccessFailureVisit(
               cmd, identity, err, failureKind, fs
             );

             var result := Core.EvalVisitCore(
               cmd, plan, visit, activeResolved, fs, now
             );
             assert Spec.VisitOutcomeBodySpec(
                 cmd,
                 BaseProof.SpecModePlanOfCore(plan),
                 SpecVisitOfCore(visit),
                 activeResolved,
                 fs,
                 result.fs,
                 result.stdoutChunk,
                 result.stderrChunk,
                 result.allOk,
                 now
               );
             Spec.IntroduceVisitOutcomeSpec(
               cmd,
               BaseProof.SpecModePlanOfCore(plan),
               SpecVisitOfCore(visit),
               activeResolved,
               fs,
               result.fs,
               result.stdoutChunk,
               result.stderrChunk,
               result.allOk,
               now
             );
    case RecursivePreserveRoot(_, alias) =>
      BridgeIdentityResolves(fs, identity);

      var result := Core.EvalVisitCore(
        cmd, plan, visit, activeResolved, fs, now
      );
      assert Spec.VisitOutcomeBodySpec(
          cmd,
          BaseProof.SpecModePlanOfCore(plan),
          SpecVisitOfCore(visit),
          activeResolved,
          fs,
          result.fs,
          result.stdoutChunk,
          result.stderrChunk,
          result.allOk,
          now
        );
      Spec.IntroduceVisitOutcomeSpec(
        cmd,
        BaseProof.SpecModePlanOfCore(plan),
        SpecVisitOfCore(visit),
        activeResolved,
        fs,
        result.fs,
        result.stdoutChunk,
        result.stderrChunk,
        result.allOk,
        now
      );
    case RecursiveNode(_, children, terminal) =>
      BridgeIdentityResolves(fs, identity);

      BridgeApplyResolved(cmd, plan, identity, fs, now);
      var parent := Core.ApplyResolvedCore(
        cmd, plan, identity, fs, now
      );
      ghost var specParent :=
        BaseProof.SpecPathResultOfCore(parent);
      ghost var specIdentity := SpecIdentityOfCore(identity);
      ghost var specChildren := SpecVisitsOfCore(children);
      ghost var specTerminal := Core.SpecTerminalOfCore(terminal);
      ghost var specPlan := BaseProof.SpecModePlanOfCore(plan);
      SpecVisitsShape(children);
      assert exists candidate: BaseSpec.SpecPathResult ::
          Spec.ApplyResolvedSpecRelation(
            cmd,
            BaseProof.SpecModePlanOfCore(plan),
            SpecIdentityOfCore(identity),
            fs,
            candidate,
            now
          ) &&
          candidate == specParent by {
        ghost var candidate := specParent;
      }
      if BW.PathSegments(identity.resolvedPath) !in activeResolved {
        if identity.isSymlink &&
           !Spec.TraversalFollowSpec(
             cmd, identity.isTopLevel
           ) {
          assert |children| == 0;
          reveal Core.ValidVisitsCore;
        } else if !identity.isDirectory {
          assert |children| == 0;
          reveal Core.ValidVisitsCore;
        } else {
          var entries :|
            |entries| == |children| &&
            Core.ValidOpenSchedule(
              IOC.DirectoryEntriesForPathFields(
                parent.fs, identity.resolvedPath
              ),
              entries,
              terminal
            ) &&
            (forall j :: 0 <= j < |children| ==>
                           Core.VisitMatchesEntryCore(
                             identity, entries[j], children[j]
                           )) &&
            Core.ValidVisitsCore(
              cmd,
              plan,
              children,
              0,
              activeResolved + {
                BW.PathSegments(identity.resolvedPath)
              },
              parent.fs,
              now
            );
          BridgeSchedule(
            IOC.DirectoryEntriesForPathFields(
              parent.fs, identity.resolvedPath
            ),
            entries,
            terminal
          );
          forall j | 0 <= j < |children|
            ensures Spec.VisitMatchesEntrySpec(
                      SpecIdentityOfCore(identity),
                      entries[j],
                      SpecVisitsOfCore(children)[j]
                    )
          {
            BridgeVisitMatchesEntry(
              identity, entries[j], children[j]
            );
          }
        }
        assert
          if specIdentity.isSymlink &&
             !Spec.TraversalFollowSpec(
               cmd, specIdentity.isTopLevel
             ) then
            |specChildren| == 0 && specTerminal.RecursiveEof?
          else if !specIdentity.isDirectory then
            |specChildren| == 0 && specTerminal.RecursiveEof?
          else
            BW.FsContainsPath(
              specParent.fs, specIdentity.resolvedPath
            ) &&
            exists specEntries: seq<BW.DirEntry> ::
              |specEntries| == |specChildren| &&
              Spec.ValidOpenSchedule(
                IOC.DirectoryEntriesForPathFields(
                  specParent.fs, specIdentity.resolvedPath
                ),
                specEntries,
                specTerminal
              ) &&
              (forall j :: 0 <= j < |specChildren| ==>
                             Spec.VisitMatchesEntrySpec(
                               specIdentity, specEntries[j], specChildren[j]
                             ));
        BridgeVisitsOutcome(
          cmd,
          plan,
          children,
          0,
          activeResolved + {
            BW.PathSegments(identity.resolvedPath)
          },
          parent.fs,
          now
        );
        if terminal.RecursiveReadError? {
          var err := terminal.err;

        }
        var result := Core.EvalVisitCore(
          cmd, plan, visit, activeResolved, fs, now
        );
        var descendants := Core.EvalChildrenCore(
          cmd,
          plan,
          children,
          0,
          activeResolved + {
            BW.PathSegments(identity.resolvedPath)
          },
          parent.fs,
          now
        );
        assert children[0..] == children;
        assert SpecVisitsOfCore(children[0..]) ==
               SpecVisitsOfCore(children);
        assert Spec.VisitsOutcomeSpec(
            cmd,
            BaseProof.SpecModePlanOfCore(plan),
            SpecVisitsOfCore(children),
            activeResolved + {
              BW.PathSegments(identity.resolvedPath)
            },
            parent.fs,
            descendants.fs,
            descendants.stdoutChunk,
            descendants.stderrChunk,
            descendants.allOk,
            now
          );
        assert Core.RecursiveReadStdoutCore(
            cmd, identity.displayPath, terminal
          ) == Spec.RecursiveReadStdoutSpec(
                      cmd,
                      SpecIdentityOfCore(identity).displayPath,
                      Core.SpecTerminalOfCore(terminal)
                    );
        assert Core.RecursiveReadStderrCore(
            cmd, identity.displayPath, terminal
          ) == Spec.RecursiveReadStderrSpec(
                      cmd,
                      SpecIdentityOfCore(identity).displayPath,
                      Core.SpecTerminalOfCore(terminal)
                    );
        assert specParent.fs == parent.fs;
        assert specParent.stdoutChunk == parent.stdoutChunk;
        assert specParent.stderrChunk == parent.stderrChunk;
        assert specParent.ok == parent.ok;
        assert Spec.IdentityResolvesSpec(fs, specIdentity);
        assert !specIdentity.isSymlink ||
               Spec.TraversalFollowSpec(cmd, specIdentity.isTopLevel) ||
               Spec.ChmodFollowSpec(cmd, specIdentity.isTopLevel);
        assert !(cmd.preserveRoot && specIdentity.isDirectory &&
                 specIdentity.resolvedPath == "/");
        assert Spec.ApplyResolvedSpecRelation(
            cmd, specPlan, specIdentity, fs, specParent, now
          );
        assert exists descendantsStdout: BW.Bytes,
            descendantsStderr: BW.Bytes,
            descendantsOk: bool ::
            Spec.VisitsOutcomeSpec(
              cmd,
              specPlan,
              specChildren,
              activeResolved + {
                BW.PathSegments(specIdentity.resolvedPath)
              },
              specParent.fs,
              result.fs,
              descendantsStdout,
              descendantsStderr,
              descendantsOk,
              now
            ) &&
            result.stdoutChunk ==
            specParent.stdoutChunk + descendantsStdout +
            Spec.RecursiveReadStdoutSpec(
              cmd, specIdentity.displayPath, specTerminal
            ) &&
            result.stderrChunk ==
            specParent.stderrChunk + descendantsStderr +
            Spec.RecursiveReadStderrSpec(
              cmd, specIdentity.displayPath, specTerminal
            ) &&
            result.allOk == (
              specParent.ok && descendantsOk &&
              specTerminal.RecursiveEof?
            ) by {
          ghost var descendantsStdout :=
            descendants.stdoutChunk;
          ghost var descendantsStderr :=
            descendants.stderrChunk;
          ghost var descendantsOk := descendants.allOk;
          assert result == Core.RecursiveResult(
                             descendants.fs,
                             specParent.stdoutChunk + descendantsStdout +
                             Spec.RecursiveReadStdoutSpec(
                               cmd, specIdentity.displayPath, specTerminal
                             ),
                             specParent.stderrChunk + descendantsStderr +
                             Spec.RecursiveReadStderrSpec(
                               cmd, specIdentity.displayPath, specTerminal
                             ),
                             specParent.ok && descendantsOk && specTerminal.RecursiveEof?
                           );
        }
        IntroduceRecursiveNodeOutcome(
          cmd, specPlan, specIdentity, specChildren, specTerminal,
          activeResolved, fs, specParent, result.fs,
          result.stdoutChunk, result.stderrChunk, result.allOk, now
        );
        Spec.IntroduceVisitOutcomeSpec(
          cmd,
          BaseProof.SpecModePlanOfCore(plan),
          SpecVisitOfCore(visit),
          activeResolved,
          fs,
          result.fs,
          result.stdoutChunk,
          result.stderrChunk,
          result.allOk,
          now
        );
      } else {
        var result := Core.EvalVisitCore(
          cmd, plan, visit, activeResolved, fs, now
        );
        assert Spec.VisitOutcomeBodySpec(
            cmd,
            BaseProof.SpecModePlanOfCore(plan),
            SpecVisitOfCore(visit),
            activeResolved,
            fs,
            result.fs,
            result.stdoutChunk,
            result.stderrChunk,
            result.allOk,
            now
          ) by {
          ghost var parentCandidate := specParent;
        }
        Spec.IntroduceVisitOutcomeSpec(
          cmd,
          BaseProof.SpecModePlanOfCore(plan),
          SpecVisitOfCore(visit),
          activeResolved,
          fs,
          result.fs,
          result.stdoutChunk,
          result.stderrChunk,
          result.allOk,
          now
        );
      }
  }

  lemma {:isolate_assertions} {:vcs_split_on_every_assert}
    BridgeVisitsOutcome(
    cmd: Schema.ChmodCmd,
    plan: BaseCore.CoreModePlan,
    visits: seq<Core.RecursiveVisit>,
    i: nat,
    activeResolved: set<seq<string>>,
    fs: BW.FileSystem,
    now: int
  )
    requires i <= |visits|
    requires Core.ValidVisitsCore(
               cmd, plan, visits, i, activeResolved, fs, now
             )
    ensures
      var result := Core.EvalChildrenCore(
                      cmd, plan, visits, i, activeResolved, fs, now
                    );
      Spec.VisitsOutcomeSpec(
        cmd,
        BaseProof.SpecModePlanOfCore(plan),
        SpecVisitsOfCore(visits[i..]),
        activeResolved,
        fs,
        result.fs,
        result.stdoutChunk,
        result.stderrChunk,
        result.allOk,
        now
      )
    decreases Core.VisitsSizeCore(visits[i..]), 2
  {
    if i < |visits| {
      BridgeNonemptyVisitsOutcome(
        cmd, plan, visits, i, activeResolved, fs, now
      );
    } else {
      reveal Core.ValidVisitsCore;
      reveal Spec.VisitsOutcomeSpec;
      assert i == |visits|;
      assert visits[i..] == [];
    }
  }

  lemma {:isolate_assertions} {:vcs_split_on_every_assert}
    BridgeNonemptyVisitsOutcome(
    cmd: Schema.ChmodCmd,
    plan: BaseCore.CoreModePlan,
    visits: seq<Core.RecursiveVisit>,
    i: nat,
    activeResolved: set<seq<string>>,
    fs: BW.FileSystem,
    now: int
  )
    requires i < |visits|
    requires Core.ValidVisitsCore(
               cmd, plan, visits, i, activeResolved, fs, now
             )
    ensures
      var result := Core.EvalChildrenCore(
                      cmd, plan, visits, i, activeResolved, fs, now
                    );
      Spec.VisitsOutcomeSpec(
        cmd,
        BaseProof.SpecModePlanOfCore(plan),
        SpecVisitsOfCore(visits[i..]),
        activeResolved,
        fs,
        result.fs,
        result.stdoutChunk,
        result.stderrChunk,
        result.allOk,
        now
      )
    decreases Core.VisitsSizeCore(visits[i..]), 1
  {
    reveal Core.ValidVisitsCore;
    reveal Spec.VisitsOutcomeSpec;
    BridgeVisitOutcome(
      cmd, plan, visits[i], activeResolved, fs, now
    );
    var step := Core.EvalVisitCore(
      cmd, plan, visits[i], activeResolved, fs, now
    );
    BridgeVisitsOutcome(
      cmd,
      plan,
      visits,
      i + 1,
      activeResolved,
      step.fs,
      now
    );
    var rest := Core.EvalChildrenCore(
      cmd, plan, visits, i + 1, activeResolved, step.fs, now
    );
    assert visits[i..][0] == visits[i];
    assert visits[i..][1..] == visits[i + 1..];
    assert visits[i..] == [visits[i]] + visits[i + 1..];
    assert SpecVisitsOfCore(visits[i..]) ==
           [SpecVisitOfCore(visits[i])] +
           SpecVisitsOfCore(visits[i + 1..]);
    assert SpecVisitsOfCore(visits[i..])[0] ==
           SpecVisitOfCore(visits[i]);
    assert SpecVisitsOfCore(visits[i..])[1..] ==
           SpecVisitsOfCore(visits[i + 1..]);
    assert Core.EvalChildrenCore(
        cmd, plan, visits, i, activeResolved, fs, now
      ) == Core.RecursiveResult(
                  rest.fs,
                  step.stdoutChunk + rest.stdoutChunk,
                  step.stderrChunk + rest.stderrChunk,
                  step.allOk && rest.allOk
                );
    assert Spec.VisitOutcomeSpec(
        cmd,
        BaseProof.SpecModePlanOfCore(plan),
        SpecVisitOfCore(visits[i]),
        activeResolved,
        fs,
        step.fs,
        step.stdoutChunk,
        step.stderrChunk,
        step.allOk,
        now
      );
    assert Spec.VisitsOutcomeSpec(
        cmd,
        BaseProof.SpecModePlanOfCore(plan),
        SpecVisitsOfCore(visits[i + 1..]),
        activeResolved,
        step.fs,
        rest.fs,
        rest.stdoutChunk,
        rest.stderrChunk,
        rest.allOk,
        now
      );
    assert exists stepFs: BW.FileSystem,
        stepStdout: BW.Bytes,
        stepStderr: BW.Bytes,
        stepOk: bool,
        restStdout: BW.Bytes,
        restStderr: BW.Bytes,
        restOk: bool ::
        Spec.VisitOutcomeSpec(
          cmd,
          BaseProof.SpecModePlanOfCore(plan),
          SpecVisitsOfCore(visits[i..])[0],
          activeResolved,
          fs,
          stepFs,
          stepStdout,
          stepStderr,
          stepOk,
          now
        ) &&
        Spec.VisitsOutcomeSpec(
          cmd,
          BaseProof.SpecModePlanOfCore(plan),
          SpecVisitsOfCore(visits[i..])[1..],
          activeResolved,
          stepFs,
          rest.fs,
          restStdout,
          restStderr,
          restOk,
          now
        ) &&
        step.stdoutChunk + rest.stdoutChunk ==
        stepStdout + restStdout &&
        step.stderrChunk + rest.stderrChunk ==
        stepStderr + restStderr &&
        (step.allOk && rest.allOk) == (stepOk && restOk);
    assert Spec.VisitsOutcomeSpec(
        cmd,
        BaseProof.SpecModePlanOfCore(plan),
        SpecVisitsOfCore(visits[i..]),
        activeResolved,
        fs,
        rest.fs,
        step.stdoutChunk + rest.stdoutChunk,
        step.stderrChunk + rest.stderrChunk,
        step.allOk && rest.allOk,
        now
      );
  }

  lemma BridgeRecursivePlan(
    cmd: Schema.ChmodCmd,
    fs: BW.FileSystem,
    cwd: BW.Path,
    props: map<string, string>,
    plan: BaseCore.CoreModePlan
  )
    requires Core.RecursivePlanCore(cmd, fs, cwd, props, plan)
    requires cmd.seenReference ||
             Schema.IsValidModeExpr(cmd.modeExpr)
    ensures Spec.RecursivePlanSpec(
              cmd,
              fs,
              cwd,
              props,
              BaseProof.SpecModePlanOfCore(plan)
            )
  {
    if cmd.seenReference {

    } else {
      BaseProof.ValidModeProgramSatisfiesRelation(cmd.modeExpr);
      var umask := IOC.GetUmaskResultFields(props);
      assert plan == BaseCore.CoreGeneralModePlan(
                       cmd.modeExpr, umask
                     );
      assert BaseSpec.SpecGeneralModePlanRelation(
          cmd.modeExpr,
          umask,
          BaseProof.SpecModePlanOfCore(plan)
        ) by {
        assert exists changes: seq<Schema.ModeChange> ::
            BaseSpec.SpecModeProgramRelation(cmd.modeExpr, changes) &&
            BaseProof.SpecModePlanOfCore(plan) ==
            BaseSpec.SpecGeneralModePlan(changes, umask) by {
          ghost var changes :=
            BaseProof.SpecChangesOfExpr(cmd.modeExpr);
        }
      }
    }
  }

  twostate lemma {:isolate_assertions} RecursiveCoreSummaryImpliesSpec(
    raw: Schema.ChmodCmdRaw,
    io: BenchIO.IO,
    exit: int
  )
    requires Core.RecursiveCoreSummary(raw, io, exit)
    ensures Spec.RecursiveSpec(raw, io, exit)
  {
    var cmd := Schema.Command(raw);
    if cmd.seenReference {
      BaseProof.BridgeReferenceFailureEquivalent(
        cmd, old(io.fs()), old(io.cwd())
      );
    }
    if cmd.mode == Schema.ModeHelp || cmd.mode == Schema.ModeVersion {
      BaseProof.CoreSummaryImpliesSpec(raw, io, exit);
    } else if cmd.dereferenceMode == 1 && cmd.traversalMode == 0 {

    } else if (cmd.seenReference && cmd.diagnoseSurprises) ||
              |cmd.files| == 0 ||
              ((cmd.seenReference &&
                BaseCore.CoreReferenceFailure(cmd, old(io.fs()), old(io.cwd()))) ||
               (!cmd.seenReference &&
                !Schema.IsValidModeExpr(cmd.modeExpr))) {
      BaseProof.CoreSummaryImpliesSpec(raw, io, exit);
    } else {
      var plan: BaseCore.CoreModePlan, visits: seq<Core.RecursiveVisit> :|
        Core.RecursivePlanCore(
          cmd, old(io.fs()), old(io.cwd()), old(io.props()), plan
        ) &&
        Core.TopLevelVisitsCore(
          cmd, plan, old(io.cwd()), visits, old(io.fs()), old(io.now())
        ) &&
        var result := Core.EvalChildrenCore(
                        cmd,
                        plan,
                        visits,
                        0,
                        {},
                        old(io.fs()),
                        old(io.now())
                      );
        io.fs() == result.fs &&
        io.stdout() == old(io.stdout()) + result.stdoutChunk &&
        io.stderr() == old(io.stderr()) + result.stderrChunk &&
        exit == (if result.allOk then 0 else 1);
      BridgeRecursivePlan(
        cmd, old(io.fs()), old(io.cwd()), old(io.props()), plan
      );
      reveal Core.TopLevelVisitsCore;
      SpecVisitsShape(visits);
      forall i | 0 <= i < |visits|
        ensures Spec.VisitIdentitySpec(
                  SpecVisitsOfCore(visits)[i]
                ).displayPath == cmd.files[i]
        ensures Spec.VisitIdentitySpec(
                  SpecVisitsOfCore(visits)[i]
                ).accessPath ==
                BaseSpec.MakeAbsolute(old(io.cwd()), cmd.files[i])
        ensures Spec.VisitIdentitySpec(
                  SpecVisitsOfCore(visits)[i]
                ).isTopLevel
      {
        BridgeVisitIdentity(visits[i]);

      }
      BridgeVisitsOutcome(
        cmd, plan, visits, 0, {}, old(io.fs()), old(io.now())
      );
      var specPlan := BaseProof.SpecModePlanOfCore(plan);
      var specVisits := SpecVisitsOfCore(visits);
      var result := Core.EvalChildrenCore(
        cmd, plan, visits, 0, {}, old(io.fs()), old(io.now())
      );
      reveal Spec.TopLevelOutcomeSpec;
      assert Spec.TopLevelOutcomeSpec(
          cmd,
          specPlan,
          old(io.cwd()),
          specVisits,
          old(io.fs()),
          result.fs,
          result.stdoutChunk,
          result.stderrChunk,
          result.allOk,
          old(io.now())
        );
      assert exists stdoutChunk: BW.Bytes,
          stderrChunk: BW.Bytes,
          allOk: bool ::
          Spec.TopLevelOutcomeSpec(
            cmd,
            specPlan,
            old(io.cwd()),
            specVisits,
            old(io.fs()),
            io.fs(),
            stdoutChunk,
            stderrChunk,
            allOk,
            old(io.now())
          ) &&
          io.stdout() == old(io.stdout()) + stdoutChunk &&
          io.stderr() == old(io.stderr()) + stderrChunk &&
          exit == (if allOk then 0 else 1);
      assert exists publicPlan: BaseSpec.SpecModePlan ::
          Spec.RecursivePlanSpec(
            cmd,
            old(io.fs()),
            old(io.cwd()),
            old(io.props()),
            publicPlan
          ) &&
          exists publicVisits: seq<Spec.RecursiveVisit>,
            stdoutChunk: BW.Bytes,
            stderrChunk: BW.Bytes,
            allOk: bool ::
            Spec.TopLevelOutcomeSpec(
              cmd,
              publicPlan,
              old(io.cwd()),
              publicVisits,
              old(io.fs()),
              io.fs(),
              stdoutChunk,
              stderrChunk,
              allOk,
              old(io.now())
            ) &&
            io.stdout() == old(io.stdout()) + stdoutChunk &&
            io.stderr() == old(io.stderr()) + stderrChunk &&
            exit == (if allOk then 0 else 1);
    }
    reveal Spec.RecursiveSpec;
  }

}
