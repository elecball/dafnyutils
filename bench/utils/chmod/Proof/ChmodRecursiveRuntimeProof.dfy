include "../Impl/ChmodRecursiveCore.dfy"

module ChmodRecursiveRuntimeProof {
  import BenchWorld
  import Schema = ChmodSchema
  import Base = ChmodCore
  import opened ChmodRecursiveCore

  lemma {:induction false} RuntimeVisitOutcomeIdentitySubstitution(
    cmd: Schema.ChmodCmd,
    plan: Base.CoreModePlan,
    identity: RecursiveIdentity,
    displayPath: string,
    accessPath: BenchWorld.Path,
    isTopLevel: bool,
    activeSegments: set<seq<string>>,
    fs0: BenchWorld.FileSystem,
    stdout0: BenchWorld.Bytes,
    stderr0: BenchWorld.Bytes,
    fs1: BenchWorld.FileSystem,
    stdout1: BenchWorld.Bytes,
    stderr1: BenchWorld.Bytes,
    ok: bool,
    visit: RecursiveVisit,
    now0: int
  )
    requires identity.displayPath == displayPath
    requires identity.accessPath == accessPath
    requires identity.isTopLevel == isTopLevel
    requires RuntimeVisitOutcomeCore(
               cmd, plan, identity.displayPath, identity.accessPath,
               identity.isTopLevel, activeSegments, fs0, stdout0, stderr0,
               fs1, stdout1, stderr1, ok, visit, now0
             )
    ensures RuntimeVisitOutcomeCore(
              cmd, plan, displayPath, accessPath, isTopLevel,
              activeSegments, fs0, stdout0, stderr0,
              fs1, stdout1, stderr1, ok, visit, now0
            )
  {
  }
}
