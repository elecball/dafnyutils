include "TruncateSpec.dfy"

module TruncateProof {
  import S = TruncateSchema
  import Spec = TruncateSpec
  import W = BenchWorld
  import BenchIO
  import C = IOContract

  lemma ModeAppend(parsed: seq<S.ParsedSize>, index: nat, before: S.Modifier)
    requires index < |parsed|
    requires Spec.ModeAt(parsed, index, before)
    ensures Spec.ModeAt(parsed, index + 1,
      if parsed[index].modifier == S.Absolute then before else parsed[index].modifier)
  {
    if parsed[index].modifier != S.Absolute {
      assert forall j :: index < j < index + 1 ==> parsed[j].modifier == S.Absolute;
    } else if before != S.Absolute {
      var last: nat :| last < index && parsed[last].modifier != S.Absolute &&
        before == parsed[last].modifier &&
        forall j :: last < j < index ==> parsed[j].modifier == S.Absolute;
      assert forall j :: last < j < index + 1 ==> parsed[j].modifier == S.Absolute;
    }
  }
  lemma ResizeWitness(
    observations: (W.TrustedFilesystemRequest) -> W.TrustedFilesystemResult,
    statusTimes: W.StatusTimeObservations, now: int, path: string,
    mode: S.Modifier, delta: int, blocks: bool, reference: int,
    before: W.FileSystem, cursor: nat, after: W.FileSystem, cursor2: nat, error: W.Bytes,
    status: W.FileStatus, statOk: bool, statErr: int
  )
    requires Spec.ResizeOutcome(observations, statusTimes, now, path, mode, delta, blocks,
      reference, before, cursor, after, cursor2, error, status, statOk, statErr)
    ensures Spec.ResizeRelation(observations, statusTimes, now, path, mode, delta, blocks,
      reference, before, cursor, after, cursor2, error)
  { reveal Spec.ResizeRelation(); }

  lemma FileWitness(
    observations: (W.TrustedFilesystemRequest) -> W.TrustedFilesystemResult,
    statusTimes: W.StatusTimeObservations, now: int, path: string,
    noCreate: bool, mode: S.Modifier, delta: int, blocks: bool, reference: int,
    before: W.FileSystem, cursor: nat, after: W.FileSystem, cursor2: nat, error: W.Bytes,
    openedFs: W.FileSystem, isOpen: bool, err: int
  )
    requires Spec.OpenRelation(observations, now, path, noCreate, before, openedFs, isOpen, err)
    requires if !isOpen then after == openedFs && cursor2 == cursor &&
      error == (if err == 0 then [] else Spec.CannotOpen(path, err))
      else Spec.ResizeRelation(observations, statusTimes, now, path, mode, delta, blocks, reference,
        openedFs, cursor, after, cursor2, error)
    ensures Spec.FileStep(observations, statusTimes, now, path, noCreate, mode, delta, blocks,
      reference, before, cursor, after, cursor2, error)
  { reveal Spec.FileStep(); }

  lemma FileStepImpliesRelation(
    observations: (W.TrustedFilesystemRequest) -> W.TrustedFilesystemResult,
    statusTimes: W.StatusTimeObservations, now: int, path: string,
    noCreate: bool, mode: S.Modifier, delta: int, blocks: bool, reference: int,
    before: Spec.FileState, after: Spec.FileState, error: W.Bytes
  )
    requires Spec.FileStep(observations, statusTimes, now, path, noCreate, mode, delta, blocks,
      reference, before.fs, before.cursor, after.fs, after.cursor, error)
    requires after.errors == before.errors + error
    requires after.failed == (before.failed || error != [])
    ensures Spec.FileRelation(observations, statusTimes, now, path, noCreate, mode, delta, blocks,
      reference, before, after)
  { reveal Spec.FileRelation(); }

  lemma FilesWitness(
    raw: S.TruncateCmdRaw, mode: S.Modifier, delta: int, reference: int,
    observations: (W.TrustedFilesystemRequest) -> W.TrustedFilesystemResult,
    statusTimes: W.StatusTimeObservations, now: int,
    before: W.FileSystem, cursor: nat, after: W.FileSystem, cursor2: nat,
    errors: W.Bytes, exit: int, states: seq<Spec.FileState>
  )
    requires |states| == |raw.files| + 1
    requires states[0] == Spec.FileState(before, cursor, [], false)
    requires states[|raw.files|].fs == after && states[|raw.files|].cursor == cursor2
    requires states[|raw.files|].errors == errors
    requires exit == (if states[|raw.files|].failed then 1 else 0)
    requires forall i :: 0 <= i < |raw.files| ==>
      Spec.FileRelation(observations, statusTimes, now, raw.files[i], raw.noCreate,
        mode, delta, raw.blocks, reference, states[i], states[i + 1])
    ensures Spec.FilesRelation(raw, mode, delta, reference, observations, statusTimes, now,
      before, cursor, after, cursor2, errors, exit)
  { reveal Spec.FilesRelation(); }

  lemma ReferenceRunWitness(
    raw: S.TruncateCmdRaw, mode: S.Modifier, value: int,
    observations: (W.TrustedFilesystemRequest) -> W.TrustedFilesystemResult,
    statusTimes: W.StatusTimeObservations, now: int,
    before: W.FileSystem, cursor: nat, after: W.FileSystem, cursor2: nat,
    errors: W.Bytes, exit: int, ok: bool, status: W.FileStatus, err: int, next: nat
  )
    requires raw.hasReference
    requires Spec.StatusRelation(statusTimes, cursor, next, before, raw.reference, ok, status, err)
    requires if !ok then after == before && cursor2 == next && exit == 1 &&
      errors == Spec.CannotStat(raw.reference, err, true)
      else Spec.FilesRelation(raw, mode, if |raw.sizes| == 0 then status.storage.size else value,
        if |raw.sizes| == 0 then -1 else status.storage.size,
        observations, statusTimes, now, before, next, after, cursor2, errors, exit)
    ensures Spec.RunRelation(raw, mode, value, observations, statusTimes, now,
      before, cursor, after, cursor2, errors, exit)
  {
    hide Spec.StatusRelation();
    hide Spec.FilesRelation();
    reveal Spec.RunRelation();
    assert exists chosenOk: bool, chosenStatus: W.FileStatus, chosenErr: int, chosenNext: nat ::
      chosenOk == ok && chosenStatus == status && chosenErr == err && chosenNext == next &&
      Spec.StatusRelation(statusTimes, cursor, chosenNext, before, raw.reference,
        chosenOk, chosenStatus, chosenErr) &&
      (if !chosenOk then after == before && cursor2 == chosenNext && exit == 1 &&
         errors == Spec.CannotStat(raw.reference, chosenErr, true)
       else Spec.FilesRelation(raw, mode, if |raw.sizes| == 0 then chosenStatus.storage.size else value,
         if |raw.sizes| == 0 then -1 else chosenStatus.storage.size,
         observations, statusTimes, now, before, chosenNext, after, cursor2, errors, exit));
  }

  lemma NoReferenceRunWitness(
    raw: S.TruncateCmdRaw, mode: S.Modifier, value: int,
    observations: (W.TrustedFilesystemRequest) -> W.TrustedFilesystemResult,
    statusTimes: W.StatusTimeObservations, now: int,
    before: W.FileSystem, cursor: nat, after: W.FileSystem, cursor2: nat,
    errors: W.Bytes, exit: int
  )
    requires !raw.hasReference
    requires Spec.FilesRelation(raw, mode, value, -1, observations, statusTimes, now,
      before, cursor, after, cursor2, errors, exit)
    ensures Spec.RunRelation(raw, mode, value, observations, statusTimes, now,
      before, cursor, after, cursor2, errors, exit)
  {
    hide Spec.FilesRelation();
    reveal Spec.RunRelation();
  }

  twostate lemma RunWitness(
    raw: S.TruncateCmdRaw, mode: S.Modifier, value: int, error: W.Bytes, io: BenchIO.IO, exit: int
  )
    requires Spec.Resolved(raw, mode, value, error)
    requires Spec.ExecutionRelation(raw, mode, value, error, io, exit)
    ensures Spec.Spec(raw, io, exit)
  {}

  lemma {:isolate_assertions} HelpOutputWitness(
    before: W.Bytes, observations: (W.TrustedStreamRequest) -> W.TrustedStreamResult,
    after: W.Bytes, mode: S.Mode, beforeError: W.Bytes, afterError: W.Bytes,
    exit: int, committed: nat, err: int
  )
    requires C.WriteStdoutSpec(before, observations, after,
      if mode == S.Help then Spec.HelpText() else Spec.VersionText(), W.ReturnError, committed, err)
    requires afterError == beforeError + (if err == 0 then [] else Spec.WriteError(err))
    requires exit == (if err == 0 then 0 else 1)
    ensures Spec.HelpResult(mode, before, after, beforeError, afterError, observations, exit)
  {
    hide *;
    reveal Spec.HelpResult();
    // Match the concrete payload in the stdout receipt trigger.
    if mode == S.Help {
      assert Spec.HelpResult(mode, before, after, beforeError, afterError, observations, exit);
    } else {
      assert Spec.HelpResult(mode, before, after, beforeError, afterError, observations, exit);
    }
  }


}
