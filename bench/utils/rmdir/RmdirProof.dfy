include "RmdirSpec.dfy"
include "../../core/PathCore.dfy"
include "../../core/PathProof.dfy"

module RmdirProof {
  import BenchIO
  import C = IOContract
  import opened BenchWorld
  import S = RmdirSchema
  import Spec = RmdirSpec
  import Path = MvPathSpec
  import PathCore = MvPathCore
  import PathProof = MvPathProof

  lemma RemovalFacts(before: FileSystem, after: FileSystem, path: string, now: int,
    trusted: (TrustedFilesystemRequest) -> TrustedFilesystemResult, ok: bool, err: int)
    requires C.RemoveDirectorySpec(before, now, trusted, after, path, ok, err)
    ensures ok <==> err == 0
  {
    hide *;
    reveal C.RemoveDirectorySpec();
    reveal C.TrustedFilesystemEffectContractFields();
  }

  lemma NonemptyWitness(fs: FileSystem, path: string,
    linkOk: bool, link: bool, linkErr: int,
    before: map<int, DirHandleState>, openState: map<int, DirHandleState>,
    after: map<int, DirHandleState>, handle: int, openOk: bool, openErr: int,
    more: bool, name: string, kind: DirectoryEntryKind, readErr: int, nonempty: bool)
    requires C.IsSymlinkContractFields(fs, path, linkOk, link, linkErr)
    requires if linkOk && link then !nonempty else
      C.OpenDirContractFields(fs, before, path, false, openOk, handle, openErr, openState) &&
      (if !openOk then !nonempty else
        C.ReadDirContractFields(fs, openState, handle, more, name, kind, readErr, after) &&
        nonempty == (more && readErr == 0))
    ensures Spec.NonemptyObservation(fs, path, nonempty)
  {
    hide *;
    reveal Spec.NonemptyObservation();
    if !(linkOk && link) {
      if openOk {
        assert exists a: map<int, DirHandleState>, m: bool, n: string,
                      k: DirectoryEntryKind, re: int ::
          a == after && m == more && n == name && k == kind && re == readErr &&
          C.ReadDirContractFields(fs, openState, handle, m, n, k, re, a) &&
          nonempty == (m && re == 0);
      }
      assert exists b: map<int, DirHandleState>, o: map<int, DirHandleState>,
                    h: int, ok: bool, e: int ::
        b == before && o == openState && h == handle && ok == openOk && e == openErr &&
        C.OpenDirContractFields(fs, b, path, false, ok, h, e, o) &&
        (if !ok then !nonempty else
          exists a: map<int, DirHandleState>, m: bool, n: string,
                 k: DirectoryEntryKind, re: int ::
            C.ReadDirContractFields(fs, o, h, m, n, k, re, a) &&
            nonempty == (m && re == 0));
    }
    assert exists lok: bool, l: bool, le: int ::
      lok == linkOk && l == link && le == linkErr &&
      C.IsSymlinkContractFields(fs, path, lok, l, le) &&
      (if lok && l then !nonempty else
        exists b: map<int, DirHandleState>, o: map<int, DirHandleState>,
               h: int, ok: bool, e: int ::
          C.OpenDirContractFields(fs, b, path, false, ok, h, e, o) &&
          (if !ok then !nonempty else
            exists a: map<int, DirHandleState>, m: bool, n: string,
                   k: DirectoryEntryKind, re: int ::
              C.ReadDirContractFields(fs, o, h, m, n, k, re, a) &&
              nonempty == (m && re == 0)));
  }

  lemma RemovalWitness(raw: S.RmdirCmdRaw, now: int,
    trusted: (TrustedFilesystemRequest) -> TrustedFilesystemResult, r: Spec.Removal)
    requires C.RemoveDirectorySpec(r.before, now, trusted, r.after, r.path, r.err == 0, r.err)
    requires if r.err == 0 then !r.ignored && !r.custom && r.display == r.path
      else (Spec.IgnoredFailure(raw, r.after, r.path, r.err, r.ignored) &&
        (if r.ignored then !r.custom && r.display == r.path
         else Spec.FailureDisplay(r.after, r.path, r.parent, r.err, r.display, r.custom)))
    ensures Spec.RemovalRelation(raw, now, trusted, r)
  {
    hide *;
    reveal Spec.RemovalRelation();
  }

  lemma TrimmedRelation(path: string, trimmed: string)
    requires PathCore.TrimmedSummary(path, trimmed)
    ensures Spec.Trimmed(path, trimmed)
  {
    if path != "" && !Path.SlashesOnly(path) {
      var end :| 0 < end <= |path| && trimmed == path[..end] &&
        path[end - 1] != '/' && forall i :: end <= i < |path| ==> path[i] == '/';
      assert Path.PathWithoutTrailingSlashes(path, trimmed, path[end..]);
    }
  }

  lemma ParentAvailability(path: string, trimmed: string, slash: int)
    requires PathCore.TrimmedSummary(path, trimmed)
    requires PathCore.LastSlashSummary(trimmed, |trimmed|, slash)
    ensures Spec.HasParent(path) <==> trimmed != "/" && slash >= 0
    ensures trimmed != "/" && slash >= 0 ==> 0 < slash + 1 < |trimmed|
  {
    if path == "" || Path.SlashesOnly(path) {
      if Spec.HasParent(path) {
        var i, j :| 0 <= i < j < |path| && path[i] == '/' && path[j] != '/';
      }
    } else {
      var end :| 0 < end <= |path| && trimmed == path[..end] &&
        path[end - 1] != '/' && forall i :: end <= i < |path| ==> path[i] == '/';
      assert trimmed != "/";
      if Spec.HasParent(path) {
        var i, j :| 0 <= i < j < |path| && path[i] == '/' && path[j] != '/';
        assert j < end;
        assert trimmed[i] == '/';
      }
      if slash >= 0 {
        assert slash < end - 1;
        assert path[slash] == '/' && path[end - 1] != '/';
      }
    }
  }

  lemma ParentValue(path: string, trimmed: string, slash: int, parent: string)
    requires PathCore.TrimmedSummary(path, trimmed)
    requires PathCore.LastSlashSummary(trimmed, |trimmed|, slash)
    requires trimmed != "/" && slash >= 0
    requires if slash == 0 then parent == "/"
             else PathCore.TrimmedSummary(trimmed[..slash], parent)
    ensures Spec.ParentRelation(path, parent)
    ensures |parent| < |path|
  {
    ParentAvailability(path, trimmed, slash);
    assert PathCore.DirnameValueSummary(path, parent);
    PathProof.DirnameValueSummaryGivesRelation(path, parent);
    if slash > 0 {
      if Path.SlashesOnly(trimmed[..slash]) {
      } else {
        var end :| 0 < end <= slash && parent == trimmed[..slash][..end] &&
          trimmed[..slash][end - 1] != '/' &&
          forall i :: end <= i < slash ==> trimmed[..slash][i] == '/';
      }
    }
  }

  lemma AppendPartition(parts: seq<Bytes>, whole: Bytes, cuts: seq<nat>, part: Bytes)
    requires Spec.BytePartition(parts, whole, cuts)
    ensures Spec.BytePartition(parts + [part], whole + part, cuts + [|whole + part|])
  {
    var nextParts := parts + [part];
    var nextWhole := whole + part;
    var nextCuts := cuts + [|nextWhole|];
    forall i {:trigger nextCuts[i]} | 0 <= i < |nextParts|
      ensures nextCuts[i] <= nextCuts[i + 1] <= |nextWhole|
      ensures nextWhole[nextCuts[i]..nextCuts[i + 1]] == nextParts[i]
    {
      if i < |parts| {
        assert cuts[i] <= cuts[i + 1] <= |whole|;
        assert whole[cuts[i]..cuts[i + 1]] == parts[i];
        assert nextCuts[i] == cuts[i] && nextCuts[i + 1] == cuts[i + 1];
        assert nextWhole[..|whole|] == whole;
        assert nextWhole[nextCuts[i]..nextCuts[i + 1]] == whole[cuts[i]..cuts[i + 1]];
      } else {
        assert i == |parts|;
        assert nextCuts[i] == |whole| && nextCuts[i + 1] == |nextWhole|;
        assert nextWhole[nextCuts[i]..nextCuts[i + 1]] == part;
      }
    }
  }

  lemma {:isolate_assertions} {:fuel Spec.ChainPrefix, 0, 0} AppendChain(raw: S.RmdirCmdRaw, path: string, now: int,
    trusted: (TrustedFilesystemRequest) -> TrustedFilesystemResult,
    rs: seq<Spec.Removal>, r: Spec.Removal)
    requires Spec.ChainPrefix(raw, path, now, trusted, rs)
    requires Spec.RemovalRelation(raw, now, trusted, r)
    requires if |rs| == 0 then r.path == path && !r.parent
      else (r.parent && rs[|rs| - 1].err == 0 && raw.parents &&
        Spec.ParentRelation(rs[|rs| - 1].path, r.path) && rs[|rs| - 1].after == r.before)
    ensures Spec.ChainPrefix(raw, path, now, trusted, rs + [r])
  {
    assert Spec.ChainPrefix(raw, path, now, trusted, rs + [r]) by {
      reveal Spec.ChainPrefix();
      assert (rs + [r])[0].path == path && !(rs + [r])[0].parent by {
        if |rs| == 0 {
          assert (rs + [r])[0] == r;
        } else {
          assert (rs + [r])[0] == rs[0];
        }
      }
      forall i | 0 <= i < |rs + [r]|
        ensures Spec.RemovalRelation(raw, now, trusted, (rs + [r])[i])
      {
        if i < |rs| {
          assert (rs + [r])[i] == rs[i];
          assert Spec.RemovalRelation(raw, now, trusted, rs[i]);
        } else {
          assert (rs + [r])[i] == r;
        }
      }
      forall i {:trigger (rs + [r])[i]} | 0 < i < |rs + [r]|
        ensures (rs + [r])[i].parent && (rs + [r])[i - 1].err == 0 && raw.parents &&
          Spec.ParentRelation((rs + [r])[i - 1].path, (rs + [r])[i].path) &&
          (rs + [r])[i - 1].after == (rs + [r])[i].before
      {
        if i < |rs| {
          assert (rs + [r])[i] == rs[i] && (rs + [r])[i - 1] == rs[i - 1];
          assert rs[i].parent && rs[i - 1].err == 0 && raw.parents &&
            Spec.ParentRelation(rs[i - 1].path, rs[i].path) && rs[i - 1].after == rs[i].before;
        } else {
          assert i == |rs|;
          assert (rs + [r])[i] == r && (rs + [r])[i - 1] == rs[|rs| - 1];
        }
      }
    }
  }

  lemma ChainExists(raw: S.RmdirCmdRaw, path: string, now: int,
    trusted: (TrustedFilesystemRequest) -> TrustedFilesystemResult,
    before: FileSystem, after: FileSystem, out: Bytes, error: Bytes, good: bool,
    rs: seq<Spec.Removal>, outCuts: seq<nat>, errCuts: seq<nat>)
    requires Spec.ChainWitness(raw, path, now, trusted, before, after,
                              out, error, good, rs, outCuts, errCuts)
    ensures Spec.ChainEffect(raw, path, now, trusted, before, after, out, error, good)
  {
    hide *;
    reveal Spec.ChainEffect();
  }

  lemma BatchExists(raw: S.RmdirCmdRaw, now: int,
    trusted: (TrustedFilesystemRequest) -> TrustedFilesystemResult,
    before: FileSystem, after: FileSystem, out: Bytes, error: Bytes, good: bool,
    states: seq<FileSystem>, outputs: seq<Bytes>, errors: seq<Bytes>,
    goods: seq<bool>, outCuts: seq<nat>, errCuts: seq<nat>)
    requires Spec.BatchWitness(raw, raw.operands, now, trusted, before, after,
                              out, error, good, states, outputs, errors, goods, outCuts, errCuts)
    ensures Spec.BatchEffect(raw, now, trusted, before, after, out, error, good)
  {
    hide *;
    reveal Spec.BatchEffect();
  }
  lemma AllTrueSnoc(values: seq<bool>, value: bool)
    ensures (forall i :: 0 <= i < |values + [value]| ==> (values + [value])[i]) <==>
      ((forall i :: 0 <= i < |values| ==> values[i]) && value)
  {
    if (forall i :: 0 <= i < |values| ==> values[i]) && value {
      forall i | 0 <= i < |values + [value]|
        ensures (values + [value])[i]
      {}
    }
    if forall i :: 0 <= i < |values + [value]| ==> (values + [value])[i] {
      assert (values + [value])[|values|] == value;
      forall i | 0 <= i < |values|
        ensures values[i]
      { assert (values + [value])[i]; }
    }
  }

  lemma ExtendBatch(raw: S.RmdirCmdRaw, paths: seq<string>, now: int,
    trusted: (TrustedFilesystemRequest) -> TrustedFilesystemResult,
    before: FileSystem, after: FileSystem, out: Bytes, error: Bytes, allGood: bool,
    states: seq<FileSystem>, outputs: seq<Bytes>, errors: seq<Bytes>,
    goods: seq<bool>, outCuts: seq<nat>, errCuts: seq<nat>,
    path: string, next: FileSystem, partOut: Bytes, partErr: Bytes, good: bool)
    requires Spec.BatchWitness(raw, paths, now, trusted, before, after,
      out, error, allGood, states, outputs, errors, goods, outCuts, errCuts)
    requires Spec.ChainEffect(raw, path, now, trusted, after, next, partOut, partErr, good)
    ensures Spec.BatchWitness(raw, paths + [path], now, trusted, before, next,
      out + partOut, error + partErr, allGood && good, states + [next],
      outputs + [partOut], errors + [partErr], goods + [good],
      outCuts + [|out + partOut|], errCuts + [|error + partErr|])
  {
    hide *;
    reveal Spec.BatchWitness();
    AppendPartition(outputs, out, outCuts, partOut);
    AppendPartition(errors, error, errCuts, partErr);
    AllTrueSnoc(goods, good);
    forall i | 0 <= i < |paths| + 1
      ensures Spec.ChainEffect(raw, (paths + [path])[i], now, trusted,
        (states + [next])[i], (states + [next])[i + 1],
        (outputs + [partOut])[i], (errors + [partErr])[i], (goods + [good])[i])
    {
      if i < |paths| {
        assert Spec.ChainEffect(raw, paths[i], now, trusted, states[i], states[i + 1],
          outputs[i], errors[i], goods[i]);
      }
    }
  }

  twostate lemma Complete(raw: S.RmdirCmdRaw, io: BenchIO.IO,
    out: Bytes, error: Bytes, good: bool, exit: int)
    requires raw.mode == S.ModeRun && |raw.operands| > 0
    requires Spec.BatchEffect(raw, io.now(), io.trustedFilesystem(), old(io.fs()),
      io.fs(), out, error, good)
    requires Spec.StreamResults(old(io.stdout()), io.stdout(), old(io.stderr()), io.stderr(),
      io.trustedStreams(), out, error, if good then 0 else 1, exit)
    ensures Spec.Spec(raw, io, exit)
  {
    hide *;
    reveal Spec.Spec();
    assert exists chosenOut: Bytes, chosenError: Bytes, chosenGood: bool ::
      chosenOut == out && chosenError == error && chosenGood == good &&
      Spec.BatchEffect(raw, io.now(), io.trustedFilesystem(), old(io.fs()), io.fs(),
        chosenOut, chosenError, chosenGood) &&
      Spec.StreamResults(old(io.stdout()), io.stdout(), old(io.stderr()), io.stderr(),
        io.trustedStreams(), chosenOut, chosenError, if chosenGood then 0 else 1, exit);
  }

}
