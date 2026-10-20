include "../../core/World.dfy"
include "../../core/IOContract.dfy"
include "MvPathProof.dfy"
include "MvSchema.dfy"
include "MvCore.dfy"
include "MvSpec.dfy"

module MvProof {
  import Result = Results
  import BenchIO
  import IOContract
  import BW = BenchWorld
  import BasenameSpec = MvPathSpec
  import PathProof = MvPathProof
  import DirnameSpec = MvPathSpec
  import Schema = MvSchema
  import Core = MvCore
  import Spec = MvSpec

  lemma EntryNameEvidenceImpliesPathRelations(
    fs: BW.FileSystem,
    path: string,
    evidence: Core.EntryNameEvidence
  )
    requires Core.EntryNameEvidenceFor(fs, path, evidence)
    ensures BasenameSpec.BasenameRelation(path, evidence.leaf)
    ensures DirnameSpec.DirnameRelation(path, evidence.parent)
  {
    reveal Core.EntryNameEvidenceFor();
    PathProof.BasenameValueSummaryGivesRelation(
      path, evidence.leaf
    );
    PathProof.DirnameValueSummaryGivesRelation(
      path, evidence.parent
    );
  }

  lemma SourceRenameDiagnosticErrCoreEqualsSpec(
    target: string,
    sourceIsDir: bool,
    renameErr: int
  )
    ensures Core.SourceRenameDiagnosticErr(
              target, sourceIsDir, renameErr
            ) == Spec.SourceRenameDiagnosticErrSpec(
                   target, sourceIsDir, renameErr
                 )
  {
  }

  lemma DigitCharSpecEqualsCore(d: nat)
    requires d < 10
    ensures Spec.DigitCharSpec(d) == Core.DigitChar(d)
  { PathProof.DigitCharSpecEqualsCore(d); }

  lemma DecimalNatSpecEqualsCore(n: nat)
    ensures Spec.DecimalNatSpec(n) == Core.DecimalNat(n)
  { PathProof.DecimalNatSpecEqualsCore(n); }

  lemma BackupStatusSuffixCoreImpliesSpec(
    backupMode: Schema.BackupMode,
    fs: BW.FileSystem,
    target: string,
    calls: seq<Spec.StatusCallEvidence>
  )
    requires Core.BackupStatusSuffixFor(backupMode, fs, target, calls)
    ensures Spec.BackupStatusSuffix(backupMode, fs, target, calls)
  {
    if backupMode == Schema.BackupExisting && |calls| > 0 {
      DecimalNatSpecEqualsCore(1);
      if calls[0].ok {
        forall i: nat | 1 <= i < |calls|
          ensures Spec.StatusRequest(
            calls[i], fs, Spec.NumberedBackupPathSpec(target, i), false
          )
        {
          DecimalNatSpecEqualsCore(i);
        }
      }
    } else if backupMode == Schema.BackupNumbered {
      forall i: nat | i < |calls|
        ensures Spec.StatusRequest(
          calls[i], fs, Spec.NumberedBackupPathSpec(target, i + 1), false
        )
      {
        DecimalNatSpecEqualsCore(i + 1);
      }
    }
  }

  // Core keeps its index recursion, so each bridge carries the suffix or prefix
  // generalisation the structural specification needs.
  lemma AllSlashesSpecEqualsCore(text: string, i: nat)
    requires i <= |text|
    ensures Spec.AllSlashesSpec(text[i..]) == Core.AllSlashes(text, i)
    decreases |text| - i
  {
    if i < |text| {
      assert text[i..][0] == text[i];
      assert text[i..][1..] == text[i + 1..];
      if text[i] == '/' {
        AllSlashesSpecEqualsCore(text, i + 1);
      }
    }
  }

  lemma TrimTrailingSlashesSpecEqualsCore(text: string, end: nat)
    requires end <= |text|
    ensures Spec.TrimTrailingSlashesSpec(text[..end]) == Core.TrimTrailingSlashes(text, end)
    decreases end
  {
    if end > 0 {
      var prefix := text[..end];
      assert |prefix| == end;
      assert prefix[|prefix| - 1] == text[end - 1];
      assert prefix[..|prefix| - 1] == text[..end - 1];
      if text[end - 1] == '/' {
        TrimTrailingSlashesSpecEqualsCore(text, end - 1);
      }
    }
  }

  lemma NormalizeSourceSpecEqualsCore(source: string, stripTrailingSlashes: bool)
    ensures Spec.NormalizeSourceSpec(source, stripTrailingSlashes) == Core.NormalizeSource(source, stripTrailingSlashes)
  {
    if stripTrailingSlashes && source != "" {
      assert source[0..] == source;
      assert source[..|source|] == source;
      if Core.AllSlashes(source, 0) {
        AllSlashesSpecEqualsCore(source, 0);
      } else {
        AllSlashesSpecEqualsCore(source, 0);
        TrimTrailingSlashesSpecEqualsCore(source, |source|);
      }
    }
  }

  lemma TargetInDirectorySpecEqualsCore(
    directory: string,
    source: string
  )
    ensures Spec.TargetInDirectorySpec(directory, source) ==
            Core.TargetInDirectory(directory, source)
  {
    assert Spec.SourceLeafNameSpec(source) ==
           Core.SourceLeafName(source);
  }

  lemma NonSlashPrefixSlashSuffixFunctional(
    path: string,
    left: string,
    leftTrailing: string,
    right: string,
    rightTrailing: string
  )
    requires path == left + leftTrailing
    requires path == right + rightTrailing
    requires 0 < |left| && left[|left| - 1] != '/'
    requires 0 < |right| && right[|right| - 1] != '/'
    requires forall i :: 0 <= i < |leftTrailing| ==>
                           leftTrailing[i] == '/'
    requires forall i :: 0 <= i < |rightTrailing| ==>
                           rightTrailing[i] == '/'
    ensures left == right
  {
    if |left| < |right| {
      var i := |right| - 1;
      assert path[i] == right[i];
      assert i - |left| < |leftTrailing|;
      assert path[i] == leftTrailing[i - |left|];
      assert false;
    } else if |right| < |left| {
      var i := |left| - 1;
      assert path[i] == left[i];
      assert i - |right| < |rightTrailing|;
      assert path[i] == rightTrailing[i - |right|];
      assert false;
    }
    assert left == path[..|left|];
    assert right == path[..|right|];
  }

  lemma MaximalSlashFreeSuffixFunctional(
    text: string,
    left: string,
    right: string
  )
    requires BasenameSpec.MaximalSlashFreeSuffix(text, left)
    requires BasenameSpec.MaximalSlashFreeSuffix(text, right)
    ensures left == right
  {
    if |left| < |right| {
      var boundary := |text| - |left| - 1;
      assert 0 <= boundary < |text|;
      assert BasenameSpec.IsSlash(text[boundary]);
      assert |text| - |right| <= boundary;
      var i := boundary - (|text| - |right|);
      assert 0 <= i < |right|;
      assert right[i] == text[boundary];
      assert !BasenameSpec.IsSlash(right[i]);
      assert false;
    } else if |right| < |left| {
      var boundary := |text| - |right| - 1;
      assert 0 <= boundary < |text|;
      assert BasenameSpec.IsSlash(text[boundary]);
      assert |text| - |left| <= boundary;
      var i := boundary - (|text| - |left|);
      assert 0 <= i < |left|;
      assert left[i] == text[boundary];
      assert !BasenameSpec.IsSlash(left[i]);
      assert false;
    }
    assert left == text[|text| - |left|..];
    assert right == text[|text| - |right|..];
  }

  lemma BasenameRelationFunctional(
    path: string,
    left: string,
    right: string
  )
    requires BasenameSpec.BasenameRelation(path, left)
    requires BasenameSpec.BasenameRelation(path, right)
    ensures left == right
  {
    if |path| == 0 || BasenameSpec.SlashesOnly(path) {
    } else {
      var leftTrimmed, leftPrefix, leftTrailing :|
        path == leftTrimmed + leftTrailing &&
        BasenameSpec.SlashesOnly(leftTrailing) &&
        0 < |leftTrimmed| &&
        !BasenameSpec.IsSlash(leftTrimmed[|leftTrimmed| - 1]) &&
        leftTrimmed == leftPrefix + left &&
        BasenameSpec.MaximalSlashFreeSuffix(leftTrimmed, left);
      var rightTrimmed, rightPrefix, rightTrailing :|
        path == rightTrimmed + rightTrailing &&
        BasenameSpec.SlashesOnly(rightTrailing) &&
        0 < |rightTrimmed| &&
        !BasenameSpec.IsSlash(rightTrimmed[|rightTrimmed| - 1]) &&
        rightTrimmed == rightPrefix + right &&
        BasenameSpec.MaximalSlashFreeSuffix(rightTrimmed, right);
      NonSlashPrefixSlashSuffixFunctional(
        path,
        leftTrimmed,
        leftTrailing,
        rightTrimmed,
        rightTrailing
      );
      MaximalSlashFreeSuffixFunctional(
        leftTrimmed, left, right
      );
    }
  }

  lemma MaximalDirnamePrefixFunctional(
    trimmed: string,
    leftPrefix: string,
    leftComponent: string,
    rightPrefix: string,
    rightComponent: string
  )
    requires DirnameSpec.MaximalDirnamePrefix(
               trimmed, leftPrefix, leftComponent
             )
    requires DirnameSpec.MaximalDirnamePrefix(
               trimmed, rightPrefix, rightComponent
             )
    ensures leftPrefix == rightPrefix
  {
    assert trimmed[|leftPrefix|] == '/';
    assert trimmed[|rightPrefix|] == '/';
    if |leftPrefix| < |rightPrefix| {
      assert |rightPrefix| <= |leftPrefix|;
      assert false;
    } else if |rightPrefix| < |leftPrefix| {
      assert |leftPrefix| <= |rightPrefix|;
      assert false;
    }
    assert leftPrefix == trimmed[..|leftPrefix|];
    assert rightPrefix == trimmed[..|rightPrefix|];
  }

  lemma NormalizedDirnamePrefixFunctional(
    prefix: string,
    left: string,
    right: string
  )
    requires DirnameSpec.NormalizedDirnamePrefix(prefix, left)
    requires DirnameSpec.NormalizedDirnamePrefix(prefix, right)
    ensures left == right
  {
    if |prefix| == 0 || DirnameSpec.SlashesOnly(prefix) {
    } else {
      var leftTrailing :|
        prefix == left + leftTrailing &&
        DirnameSpec.SlashesOnly(leftTrailing) &&
        0 < |left| &&
        !DirnameSpec.IsSlash(left[|left| - 1]);
      var rightTrailing :|
        prefix == right + rightTrailing &&
        DirnameSpec.SlashesOnly(rightTrailing) &&
        0 < |right| &&
        !DirnameSpec.IsSlash(right[|right| - 1]);
      NonSlashPrefixSlashSuffixFunctional(
        prefix, left, leftTrailing, right, rightTrailing
      );
    }
  }

  lemma DirnameRelationFunctional(
    path: string,
    left: string,
    right: string
  )
    requires DirnameSpec.DirnameRelation(path, left)
    requires DirnameSpec.DirnameRelation(path, right)
    ensures left == right
  {
    reveal DirnameSpec.DirnameRelation();
    if |path| == 0 || DirnameSpec.SlashesOnly(path) {
    } else {
      var leftTrimmed, leftTrailing :|
        DirnameSpec.PathWithoutTrailingSlashes(
          path, leftTrimmed, leftTrailing
        ) &&
        (if DirnameSpec.SlashFree(leftTrimmed) then
           left == "."
         else
           exists leftPrefix: string, leftComponent: string ::
             DirnameSpec.MaximalDirnamePrefix(
               leftTrimmed, leftPrefix, leftComponent
             ) &&
             DirnameSpec.NormalizedDirnamePrefix(leftPrefix, left));
      var rightTrimmed, rightTrailing :|
        DirnameSpec.PathWithoutTrailingSlashes(
          path, rightTrimmed, rightTrailing
        ) &&
        (if DirnameSpec.SlashFree(rightTrimmed) then
           right == "."
         else
           exists rightPrefix: string, rightComponent: string ::
             DirnameSpec.MaximalDirnamePrefix(
               rightTrimmed, rightPrefix, rightComponent
             ) &&
             DirnameSpec.NormalizedDirnamePrefix(rightPrefix, right));
      NonSlashPrefixSlashSuffixFunctional(
        path,
        leftTrimmed,
        leftTrailing,
        rightTrimmed,
        rightTrailing
      );
      if !DirnameSpec.SlashFree(leftTrimmed) {
        var leftPrefix, leftComponent :|
          DirnameSpec.MaximalDirnamePrefix(
            leftTrimmed, leftPrefix, leftComponent
          ) &&
          DirnameSpec.NormalizedDirnamePrefix(leftPrefix, left);
        var rightPrefix, rightComponent :|
          DirnameSpec.MaximalDirnamePrefix(
            leftTrimmed, rightPrefix, rightComponent
          ) &&
          DirnameSpec.NormalizedDirnamePrefix(rightPrefix, right);
        MaximalDirnamePrefixFunctional(
          leftTrimmed,
          leftPrefix,
          leftComponent,
          rightPrefix,
          rightComponent
        );
        NormalizedDirnamePrefixFunctional(
          leftPrefix, left, right
        );
      }
    }
  }

  lemma MetadataEvidenceKeysImplySameResolvedObject(
    fs: BW.FileSystem,
    leftPath: string,
    rightPath: string,
    followLeft: bool,
    followRight: bool,
    left: Core.MetadataEvidence,
    right: Core.MetadataEvidence
  )
    requires Core.MetadataEvidenceFor(
               fs, leftPath, followLeft, left
             )
    requires Core.MetadataEvidenceFor(
               fs, rightPath, followRight, right
             )
    requires left.ok && right.ok
    requires left.key == right.key
    ensures exists
              resolvedLeft: BW.Path,
              resolvedRight: BW.Path
              ::
                IOContract.ResolvePathForMetadataFields(
                  fs, leftPath, followLeft
                ) == Result.Ok(resolvedLeft) &&
                IOContract.ResolvePathForMetadataFields(
                  fs, rightPath, followRight
                ) == Result.Ok(resolvedRight) &&
                BW.InodeSameObject(fs, resolvedLeft, resolvedRight)
  {
    var resolvedLeft :=
      IOContract.ResolvePathForMetadataFields(
        fs, leftPath, followLeft
      ).v;
    var resolvedRight :=
      IOContract.ResolvePathForMetadataFields(
        fs, rightPath, followRight
      ).v;
    var leftId := BW.FsIdAt(fs, resolvedLeft);
    var rightId := BW.FsIdAt(fs, resolvedRight);
    assert BW.InodeUniqueHostKeys(fs);
    assert fs.inodes[leftId].hostKey == left.key;
    assert fs.inodes[rightId].hostKey == right.key;
    assert leftId == rightId;
    assert BW.InodeSameObject(fs, resolvedLeft, resolvedRight);
  }

  lemma MetadataEvidenceImpliesSameInode(
    fs: BW.FileSystem,
    leftPath: string,
    rightPath: string,
    left: Core.MetadataEvidence,
    right: Core.MetadataEvidence
  )
    requires Core.MetadataEvidenceFor(fs, leftPath, false, left)
    requires Core.MetadataEvidenceFor(fs, rightPath, false, right)
    requires left.ok && right.ok
    requires left.key == right.key
    ensures Spec.SameInode(fs, leftPath, rightPath)
  {
    MetadataEvidenceKeysImplySameResolvedObject(
      fs, leftPath, rightPath, false, false, left, right
    );
  }

  lemma SameInodeImpliesMetadataKeysEqual(
    fs: BW.FileSystem,
    leftPath: string,
    rightPath: string,
    left: Core.MetadataEvidence,
    right: Core.MetadataEvidence
  )
    requires Core.MetadataEvidenceFor(fs, leftPath, false, left)
    requires Core.MetadataEvidenceFor(fs, rightPath, false, right)
    requires left.ok && right.ok
    requires Spec.SameInode(fs, leftPath, rightPath)
    ensures left.key == right.key
  {
    var resolvedLeft :=
      IOContract.ResolvePathForMetadataFields(fs, leftPath, false).v;
    var resolvedRight :=
      IOContract.ResolvePathForMetadataFields(fs, rightPath, false).v;
    assert fs.inodes[BW.FsIdAt(fs, resolvedLeft)].hostKey == left.key;
    assert fs.inodes[BW.FsIdAt(fs, resolvedRight)].hostKey == right.key;
  }

  lemma SameResolvedObjectImpliesMetadataKeysEqual(
    fs: BW.FileSystem,
    leftPath: string,
    rightPath: string,
    followLeft: bool,
    followRight: bool,
    left: Core.MetadataEvidence,
    right: Core.MetadataEvidence
  )
    requires Core.MetadataEvidenceFor(
               fs, leftPath, followLeft, left
             )
    requires Core.MetadataEvidenceFor(
               fs, rightPath, followRight, right
             )
    requires left.ok && right.ok
    requires exists
               resolvedLeft: BW.Path,
               resolvedRight: BW.Path
               ::
                 IOContract.ResolvePathForMetadataFields(
                   fs, leftPath, followLeft
                 ) == Result.Ok(resolvedLeft) &&
                 IOContract.ResolvePathForMetadataFields(
                   fs, rightPath, followRight
                 ) == Result.Ok(resolvedRight) &&
                 BW.InodeSameObject(fs, resolvedLeft, resolvedRight)
    ensures left.key == right.key
  {
    var resolvedLeft :=
      IOContract.ResolvePathForMetadataFields(
        fs, leftPath, followLeft
      ).v;
    var resolvedRight :=
      IOContract.ResolvePathForMetadataFields(
        fs, rightPath, followRight
      ).v;
    assert fs.inodes[BW.FsIdAt(fs, resolvedLeft)].hostKey == left.key;
    assert fs.inodes[BW.FsIdAt(fs, resolvedRight)].hostKey == right.key;
  }

  lemma EntryNameEvidenceImpliesSameDirectoryEntry(
    fs: BW.FileSystem,
    leftPath: string,
    rightPath: string,
    left: Core.EntryNameEvidence,
    right: Core.EntryNameEvidence
  )
    requires Core.EntryNameEvidenceFor(fs, leftPath, left)
    requires Core.EntryNameEvidenceFor(fs, rightPath, right)
    requires Core.EvidenceNamesSame(left, right)
    ensures Spec.SameDirectoryEntry(fs, leftPath, rightPath)
  {
    EntryNameEvidenceImpliesPathRelations(fs, leftPath, left);
    EntryNameEvidenceImpliesPathRelations(fs, rightPath, right);
    MetadataEvidenceImpliesSameInode(
      fs,
      left.parent,
      right.parent,
      left.parentMetadata,
      right.parentMetadata
    );
  }

  lemma {:isolate_assertions} SameDirectoryEntryImpliesEvidenceNamesSame(
    fs: BW.FileSystem,
    leftPath: string,
    rightPath: string,
    left: Core.EntryNameEvidence,
    right: Core.EntryNameEvidence
  )
    requires Core.EntryNameEvidenceFor(fs, leftPath, left)
    requires Core.EntryNameEvidenceFor(fs, rightPath, right)
    requires Spec.SameDirectoryEntry(fs, leftPath, rightPath)
    requires left.parentMetadata.ok ||
      !Spec.StatusExistsOutcomeFields(fs, left.parent, false, true, 0)
    requires right.parentMetadata.ok ||
      !Spec.StatusExistsOutcomeFields(fs, right.parent, false, true, 0)
    ensures Core.EvidenceNamesSame(left, right)
  {
    EntryNameEvidenceImpliesPathRelations(fs, leftPath, left);
    EntryNameEvidenceImpliesPathRelations(fs, rightPath, right);
    var leftParent, rightParent, leftLeaf, rightLeaf,
        resolvedLeftParent, resolvedRightParent :|
      DirnameSpec.DirnameRelation(leftPath, leftParent) &&
      DirnameSpec.DirnameRelation(rightPath, rightParent) &&
      BasenameSpec.BasenameRelation(leftPath, leftLeaf) &&
      BasenameSpec.BasenameRelation(rightPath, rightLeaf) &&
      leftLeaf == rightLeaf &&
      IOContract.ResolvePathForMetadataFields(
        fs, leftParent, false
      ) == Result.Ok(resolvedLeftParent) &&
      IOContract.ResolvePathForMetadataFields(
        fs, rightParent, false
      ) == Result.Ok(resolvedRightParent) &&
      BW.InodeSameObject(
        fs, resolvedLeftParent, resolvedRightParent
      );
    BasenameRelationFunctional(leftPath, left.leaf, leftLeaf);
    BasenameRelationFunctional(rightPath, right.leaf, rightLeaf);
    DirnameRelationFunctional(leftPath, left.parent, leftParent);
    DirnameRelationFunctional(rightPath, right.parent, rightParent);
    reveal BW.InodeSameObject();
    reveal BW.FsContainsPath();
    reveal Core.EntryNameEvidenceFor();
    reveal Core.MetadataEvidenceFor();
    assert IOContract.ResolvePathForMetadataFields(
        fs, left.parent, false
      ) == Result.Ok(resolvedLeftParent);
    assert IOContract.ResolvePathForMetadataFields(
        fs, right.parent, false
      ) == Result.Ok(resolvedRightParent);
    assert BW.FsContainsPath(fs, resolvedLeftParent);
    assert BW.FsContainsPath(fs, resolvedRightParent);
    assert left.parentMetadata.ok;
    assert right.parentMetadata.ok;
    assert Spec.SameInode(fs, left.parent, right.parent);
    SameInodeImpliesMetadataKeysEqual(
      fs,
      left.parent,
      right.parent,
      left.parentMetadata,
      right.parentMetadata
    );
  }

  lemma ResolvePathIdentitySuccessFunctional(
    fs: BW.FileSystem,
    cwd: BW.Path,
    path: BW.Path,
    left: BW.Path,
    right: BW.Path
  )
    requires IOContract.ResolvePathIdentityContractFields(
               fs, cwd, path, true, left, 0
             )
    requires IOContract.ResolvePathIdentityContractFields(
               fs, cwd, path, true, right, 0
             )
    ensures left == right
  {
  }

  lemma {:isolate_assertions} SameFileEvidenceImpliesPolicy(
    cmd: Schema.MvCmd,
    fs: BW.FileSystem,
    preCwd: BW.Path,
    source: string,
    target: string,
    evidence: Core.SameFileEvidence
  )
    requires Core.SameFileEvidenceFor(
               cmd, fs, preCwd, source, target, evidence
             )
    requires evidence.CheckedSameFile? && !evidence.decision.FailedParentStat?
    requires evidence.sourceEntry.parentMetadata.ok ||
      !Spec.StatusExistsOutcomeFields(fs, evidence.sourceEntry.parent, false, true, 0)
    requires evidence.targetEntry.parentMetadata.ok ||
      !Spec.StatusExistsOutcomeFields(fs, evidence.targetEntry.parent, false, true, 0)
    requires evidence.source.isSymlink ==> evidence.sourceReferentEntry.SomeEntryNameEvidence?
    requires evidence.sourceReferentEntry.SomeEntryNameEvidence? ==>
      evidence.sourceReferentEntry.value.parentMetadata.ok ||
      !Spec.StatusExistsOutcomeFields(fs, evidence.sourceReferentEntry.value.parent, false, true, 0)
    ensures
      var decision :=
        match evidence
        case NoSameFileCheck => Spec.ContinueMove
        case CheckedSameFile(_, _, _, _, _, _, _, value) =>
          value;
      Spec.SameFilePolicyRelation(
        cmd, fs, preCwd, source, target, decision
      )
  {
    reveal Core.SameFileEvidenceFor();
    match evidence {
      case NoSameFileCheck =>
      case CheckedSameFile(
        sourceMetadata,
        targetMetadata,
        sourceFollowed,
        sourceEntry,
        targetEntry,
        sourceReferentEntry,
        _,
        decision
        ) =>
        if Core.EvidenceNamesSame(sourceEntry, targetEntry) {
          EntryNameEvidenceImpliesSameDirectoryEntry(
            fs, source, target, sourceEntry, targetEntry
          );
        }
        if sourceMetadata.key == targetMetadata.key {
          MetadataEvidenceImpliesSameInode(
            fs, source, target, sourceMetadata, targetMetadata
          );
        }
        match sourceReferentEntry {
          case SomeEntryNameEvidence(resolvedPath, referentEntry) =>
            if Core.EvidenceNamesSame(referentEntry, targetEntry) {
              EntryNameEvidenceImpliesSameDirectoryEntry(
                fs,
                resolvedPath,
                target,
                referentEntry,
                targetEntry
              );
            }
          case _ =>
        }
        if Spec.SameDirectoryEntry(fs, source, target) {
          SameDirectoryEntryImpliesEvidenceNamesSame(
            fs, source, target, sourceEntry, targetEntry
          );
        }
        if Spec.SameInode(fs, source, target) {
          SameInodeImpliesMetadataKeysEqual(
            fs, source, target, sourceMetadata, targetMetadata
          );
        }
        if Spec.SourceSymlinkReferentHasTargetName(
            fs, preCwd, source, target
          ) {
          var publicResolvedSource, publicResolvedReferent :|
            IOContract.ResolvePathForMetadataFields(
              fs, source, false
            ) == Result.Ok(publicResolvedSource) &&
            BW.FsContainsPath(fs, publicResolvedSource) &&
            BW.FsNodeAt(fs, publicResolvedSource).Symlink? &&
            IOContract.ResolvePathIdentityContractFields(
              fs,
              preCwd,
              source,
              true,
              publicResolvedReferent,
              0
            ) &&
            Spec.SameDirectoryEntry(
              fs, publicResolvedReferent, target
            );
          assert sourceMetadata.isSymlink;
          match sourceReferentEntry {
            case SomeEntryNameEvidence(resolvedPath, referentEntry) =>
              ResolvePathIdentitySuccessFunctional(
                fs,
                preCwd,
                source,
                resolvedPath,
                publicResolvedReferent
              );
              assert Spec.SameDirectoryEntry(
                  fs, resolvedPath, target
                );
              SameDirectoryEntryImpliesEvidenceNamesSame(
                fs,
                resolvedPath,
                target,
                referentEntry,
                targetEntry
              );
            case _ =>
          }
        }
        var capturedReject :=
          Core.EvidenceNamesSame(sourceEntry, targetEntry) ||
          (cmd.backupMode == Schema.BackupOff &&
           ((sourceMetadata.ok &&
             targetMetadata.ok &&
             sourceMetadata.key == targetMetadata.key) ||
            Core.ReferentEvidenceNamesTarget(
              sourceReferentEntry, targetEntry
            )));
        assert Spec.SameFileMustBeRejected(
            cmd, fs, preCwd, source, target
          )
          ==> capturedReject by {
          if Spec.SameFileMustBeRejected(
              cmd, fs, preCwd, source, target
            ) {
            if Spec.SameDirectoryEntry(fs, source, target) {
              assert Core.EvidenceNamesSame(
                  sourceEntry, targetEntry
                );
            } else if Spec.SameInode(fs, source, target) {
              assert sourceMetadata.key == targetMetadata.key;
            } else {
              assert Spec.SourceSymlinkReferentHasTargetName(
                  fs, preCwd, source, target
                );
              assert Core.ReferentEvidenceNamesTarget(
                  sourceReferentEntry, targetEntry
                );
            }
          }
        }
        assert capturedReject ==> Spec.SameFileMustBeRejected(
              cmd, fs, preCwd, source, target
            ) by {
          if capturedReject {
            if Core.EvidenceNamesSame(sourceEntry, targetEntry) {
              assert Spec.SameDirectoryEntry(fs, source, target);
            } else if sourceMetadata.key == targetMetadata.key {
              assert Spec.SameInode(fs, source, target);
            } else {
              assert Core.ReferentEvidenceNamesTarget(
                  sourceReferentEntry, targetEntry
                );
              match sourceReferentEntry {
                case SomeEntryNameEvidence(
                  resolvedPath, referentEntry
                  ) =>
        assert Spec.SourceSymlinkReferentHasTargetName(
            fs, preCwd, source, target
          );
                case _ =>
              }
            }
          }
        }
        assert Spec.SameFileMustBeRejected(
            cmd, fs, preCwd, source, target
          ) == capturedReject;
        assert Spec.SameFilePolicyRelation(
            cmd, fs, preCwd, source, target, decision
          );
    }
  }

  lemma BackupCollisionEvidenceImpliesSpec(
    cmd: Schema.MvCmd,
    fs: BW.FileSystem,
    source: string,
    target: string,
    sourceMetadata: Core.MetadataEvidence,
    sourceEntry: Core.EntryNameEvidence,
    targetEntry: Core.EntryNameEvidence,
    collision: Core.BackupCollisionEvidence
  )
    requires Core.MetadataEvidenceFor(
               fs, source, false, sourceMetadata
             )
    requires sourceMetadata.ok
    requires Core.EntryNameEvidenceFor(fs, source, sourceEntry)
    requires Core.EntryNameEvidenceFor(fs, target, targetEntry)
    requires Core.BackupCollisionEvidenceFor(
               cmd,
               fs,
               source,
               target,
               sourceMetadata,
               sourceEntry,
               targetEntry,
               collision
             )
    requires collision.CheckedBackupCollision? ==>
      collision.simpleCandidateFollowed.ok ||
      !Spec.StatusExistsOutcomeFields(fs, Core.SimpleBackupPath(target, cmd.backupSuffix), true, true, 0)
    ensures Core.BackupCollisionDetected(collision) ==
            Spec.BackupWouldDestroySource(cmd, fs, source, target)
  {
    hide Core.MetadataEvidenceFor(), Core.EntryNameEvidenceFor(), Core.StatusCallsFor(), Spec.StatusCallsFor();
    EntryNameEvidenceImpliesPathRelations(
      fs, source, sourceEntry
    );
    EntryNameEvidenceImpliesPathRelations(
      fs, target, targetEntry
    );
    match collision {
      case NoBackupCollisionCheck =>
        if Spec.BackupWouldDestroySource(cmd, fs, source, target) {
          var sourceLeaf, targetLeaf :|
            BasenameSpec.BasenameRelation(source, sourceLeaf) &&
            BasenameSpec.BasenameRelation(target, targetLeaf) &&
            sourceLeaf == targetLeaf + cmd.backupSuffix;
          BasenameRelationFunctional(
            source, sourceEntry.leaf, sourceLeaf
          );
          BasenameRelationFunctional(
            target, targetEntry.leaf, targetLeaf
          );
        }
      case CheckedBackupCollision(sourceNoFollow, candidateFollowed) =>
        var candidate :=
          Core.SimpleBackupPath(target, cmd.backupSuffix);
        assert sourceNoFollow == sourceMetadata;
        assert Spec.SimpleBackupPathSpec(target, cmd.backupSuffix) ==
               candidate;
        if Core.BackupCollisionDetected(collision) {
          MetadataEvidenceKeysImplySameResolvedObject(
            fs,
            source,
            candidate,
            false,
            true,
            sourceMetadata,
            candidateFollowed
          );
        }
        if Spec.BackupWouldDestroySource(cmd, fs, source, target) {
          assert candidateFollowed.ok;
          SameResolvedObjectImpliesMetadataKeysEqual(
            fs,
            source,
            candidate,
            false,
            true,
            sourceMetadata,
            candidateFollowed
          );
        }
    }
  }

  lemma BackupChecksImplyNumberedTarget(
    target: string,
    start: nat,
    fs: BW.FileSystem,
    checks: seq<Core.BackupCheckEvidence>,
    path: string
  )
    requires Core.BackupChecksFor(target, start, fs, checks)
    requires path == checks[|checks| - 1].candidate
    ensures Spec.NumberedBackupTargetSpecFromFields(
              fs, target, start, path
            )
  {
    var index: nat := start + |checks| - 1;
    DecimalNatSpecEqualsCore(index);
    assert path == Core.NumberedBackupPath(target, index);
    assert path == Spec.NumberedBackupPathSpec(target, index);
    assert Spec.StatusExistsOutcomeFields(
        fs, path, false, false, checks[|checks| - 1].err
      );
    assert forall j: nat | start <= j < index ::
        Spec.StatusExistsOutcomeFields(
          fs,
          Spec.NumberedBackupPathSpec(target, j),
          false,
          true,
          0
        ) by {
      forall j: nat | start <= j < index
        ensures Spec.StatusExistsOutcomeFields(
                  fs,
                  Spec.NumberedBackupPathSpec(target, j),
                  false,
                  true,
                  0
                )
      {
        var i: nat := j - start;
        assert i + 1 < |checks|;
        assert checks[i].found;
        DecimalNatSpecEqualsCore(j);
        assert checks[i].candidate ==
               Core.NumberedBackupPath(target, j);
        assert Spec.NumberedBackupPathSpec(target, j) ==
               Core.NumberedBackupPath(target, j);
        assert Spec.StatusExistsOutcomeFields(
            fs, checks[i].candidate, false, true, checks[i].err
          );
        assert checks[i].err == 0;
      }
    }
  }

  lemma BackupSelectionEvidenceImpliesSpec(
    target: string,
    mode: Schema.BackupMode,
    suffix: string,
    fs: BW.FileSystem,
    evidence: Core.BackupSelectionEvidence
  )
    requires Core.BackupSelectionEvidenceFor(
               target, mode, suffix, fs, evidence
             )
    ensures Spec.BackupTargetSpecFields(
              fs, target, mode, suffix,
              match evidence
              case NoBackupSelection => ""
              case SelectedBackup(path, _, _, _, _) => path
            )
  {
    match evidence {
      case NoBackupSelection =>
      case SelectedBackup(
        path,
        checks,
        existingFirstCheckCalled,
        existingFirstFound,
        existingFirstErr
        ) =>
        if mode == Schema.BackupSimple {
          assert Spec.SimpleBackupPathSpec(target, suffix) ==
                 Core.SimpleBackupPath(target, suffix);
        } else if mode == Schema.BackupExisting {
          DecimalNatSpecEqualsCore(1);
          assert Spec.NumberedBackupPathSpec(target, 1) ==
                 Core.NumberedBackupPath(target, 1);
          if existingFirstFound {
            BackupChecksImplyNumberedTarget(
              target, 1, fs, checks, path
            );
            assert Spec.NumberedBackupTargetSpecFields(
                fs, target, path
              );
          } else {
            assert Spec.SimpleBackupPathSpec(target, suffix) ==
                   Core.SimpleBackupPath(target, suffix);
          }
        } else {
          assert mode == Schema.BackupNumbered;
          BackupChecksImplyNumberedTarget(
            target, 1, fs, checks, path
          );
          assert Spec.NumberedBackupTargetSpecFields(
              fs, target, path
            );
        }
    }
  }

  lemma RenameEvidenceImpliesRelation(
    source: string,
    target: string,
    sourceIsDir: bool,
    targetWasFound: bool,
    backupPath: string,
    verbose: bool,
    debug: bool,
    beforeFs: BW.FileSystem,
    preCwd: BW.Path,
    afterFs: BW.FileSystem,
    outcome: Spec.MoveOutcome,
    calls: seq<Core.RenameCallEvidence>,
    backupFs: BW.FileSystem
  )
    requires Core.RenameEvidenceFor(
               source, target, sourceIsDir,
          targetWasFound, backupPath, verbose, debug,
               beforeFs, preCwd, afterFs, outcome, calls, backupFs
             )
    requires backupPath != "" || targetWasFound ==
      Spec.StatusExistsOutcomeFields(beforeFs, target, false, true, 0)
    ensures Spec.RenameEffectRelation(
              source, target, backupPath, verbose, debug,
              beforeFs, preCwd, afterFs, outcome
            )
  {
    assert Spec.ShowActionMessageSpec(verbose, debug) ==
           Core.ShowActionMessage(verbose, debug);
    assert Spec.StepSuccessStdoutSpec(
        source, target, backupPath, verbose, debug
      ) == Core.StepSuccessStdout(
                  source, target, backupPath, verbose, debug
                );
    if |calls| > 0 {
      SourceRenameDiagnosticErrCoreEqualsSpec(
        target, sourceIsDir, calls[0].err
      );
    }
    if |calls| > 1 {
      SourceRenameDiagnosticErrCoreEqualsSpec(
        target, sourceIsDir, calls[1].err
      );
    }
  }

  lemma RenameNativeEvidenceImpliesObservedRelation(
    source: string, target: string, cmd: Schema.MvCmd, cwd: BW.Path,
    step: Core.StepEvidence, backupPath: string
  )
    requires Core.RenameEvidenceFor(source, target, step.sourceIsDir, step.targetFound,
      backupPath, cmd.verbose, cmd.debug, step.beforeFs, cwd, step.afterFs,
      step.outcome, step.renames, step.backupFs)
    requires Core.RenameNativeObservationsFor(source, target, step)
    requires if backupPath == "" then step.backup.NoBackupSelection?
      else step.backup.SelectedBackup? && step.backup.backupPath == backupPath
    ensures Spec.ObservedRenameEffectRelation(source, target, backupPath, cmd,
      step.sourceIsDir, step.targetFound, step.inputs, step.beforeFs, step.afterFs, step.outcome)
  {
    assert Spec.ShowActionMessageSpec(cmd.verbose, cmd.debug) == Core.ShowActionMessage(cmd.verbose, cmd.debug);
    assert Spec.StepSuccessStdoutSpec(source, target, backupPath, cmd.verbose, cmd.debug) ==
      Core.StepSuccessStdout(source, target, backupPath, cmd.verbose, cmd.debug);
    if |step.renames| > 0 {
      SourceRenameDiagnosticErrCoreEqualsSpec(target, step.sourceIsDir, step.renames[0].err);
    }
    if |step.renames| > 1 {
      SourceRenameDiagnosticErrCoreEqualsSpec(target, step.sourceIsDir, step.renames[1].err);
    }
    reveal Core.RenameEvidenceFor(), Core.RenameNativeObservationsFor();
    if backupPath == "" {
      assert |step.renames| == 1;
      assert step.renames[0].ok ==> step.renames[0].err == 0;
    } else {
      assert step.renames[0].ok ==> step.renames[0].err == 0;
      if |step.renames| == 2 {
        assert step.renames[1].ok ==> step.renames[1].err == 0;
      }
    }
    hide IOContract.RenamePathSpec(), IOContract.RenamePathContractFields();
    reveal Spec.ObservedRenameEffectRelation();
  }

  lemma BackupSelectionCallsImpliesObservedPath(
    cmd: Schema.MvCmd, fs: BW.FileSystem, target: string,
    evidence: Core.BackupSelectionEvidence, calls: seq<Spec.StatusCallEvidence>
  )
    requires Core.BackupSelectionFromStatusCallsFor(cmd.backupMode, cmd.backupSuffix,
      fs, target, evidence, calls)
    ensures Spec.BackupPathFromObservations(cmd, fs, target, calls,
      if evidence.SelectedBackup? then evidence.backupPath else "")
  {
    BackupStatusSuffixCoreImpliesSpec(cmd.backupMode, fs, target, calls);
    assert Spec.SimpleBackupPathSpec(target, cmd.backupSuffix) ==
      Core.SimpleBackupPath(target, cmd.backupSuffix);
    if cmd.backupMode == Schema.BackupExisting && calls[0].ok {
      DecimalNatSpecEqualsCore(|calls| - 1);
    } else if cmd.backupMode == Schema.BackupNumbered {
      DecimalNatSpecEqualsCore(|calls|);
    }
  }

  lemma ExistingTargetRenameEvidenceImpliesRelation(
    source: string,
    target: string,
    cmd: Schema.MvCmd,
    preCwd: BW.Path,
    evidence: Core.StepEvidence
  )
    requires Core.ExistingTargetRenameEvidenceFor(
               source, target, cmd, preCwd, evidence
             )
    requires evidence.targetFound ==
      Spec.StatusExistsOutcomeFields(evidence.beforeFs, target, false, true, 0)
    requires evidence.sameFile.CheckedSameFile?
    requires evidence.sameFile.backupCollision.CheckedBackupCollision? ==>
      evidence.sameFile.backupCollision.simpleCandidateFollowed.ok ||
      !Spec.StatusExistsOutcomeFields(evidence.beforeFs, Core.SimpleBackupPath(target, cmd.backupSuffix), true, true, 0)
    ensures Spec.ExistingTargetRenameEffectRelation(
              source,
              target,
              cmd,
              evidence.beforeFs,
              preCwd,
              evidence.afterFs,
              evidence.outcome
            )
  {
    hide Core.RenameEvidenceFor(), Core.MetadataEvidenceFor(), Core.EntryNameEvidenceFor();
    hide Core.StatusCallsFor(), Spec.StatusCallsFor();
    reveal Core.SameFileEvidenceFor();
    match evidence.sameFile {
      case NoSameFileCheck =>
      case CheckedSameFile(
        sourceMetadata,
        _,
        _,
        sourceEntry,
        targetEntry,
        _,
        collision,
        _
        ) =>
        BackupCollisionEvidenceImpliesSpec(
          cmd,
          evidence.beforeFs,
          source,
          target,
          sourceMetadata,
          sourceEntry,
          targetEntry,
          collision
        );
        if !Core.BackupCollisionDetected(collision) {
          if cmd.backupMode == Schema.BackupOff {
            RenameEvidenceImpliesRelation(
              source,
              target,
              evidence.sourceIsDir,
          evidence.targetFound,
              "",
              cmd.verbose,
              cmd.debug,
              evidence.beforeFs,
              preCwd,
              evidence.afterFs,
              evidence.outcome,
              evidence.renames,
              evidence.backupFs
            );
          } else {
            match evidence.backup {
              case NoBackupSelection =>
              case SelectedBackup(path, _, _, _, _) =>
                BackupSelectionEvidenceImpliesSpec(
                  target,
                  cmd.backupMode,
                  cmd.backupSuffix,
                  evidence.beforeFs,
                  evidence.backup
                );
                RenameEvidenceImpliesRelation(
                  source,
                  target,
                  evidence.sourceIsDir,
          evidence.targetFound,
                  path,
                  cmd.verbose,
                  cmd.debug,
                  evidence.beforeFs,
                  preCwd,
                  evidence.afterFs,
                  evidence.outcome,
                  evidence.renames,
                  evidence.backupFs
                );
            }
          }
        }
    }
  }

  lemma ParentMetadataFailureEvidenceImpliesEffect(
    source: string, target: string, cmd: Schema.MvCmd, cwd: BW.Path,
    step: Core.StepEvidence
  )
    requires Core.StepEvidenceFor(source, target, cmd, cwd, step)
    requires step.sameFile.CheckedSameFile? && step.sameFile.decision.FailedParentStat?
    requires step.sameFile.sourceReferentEntry.NoEntryNameEvidence?
    ensures Spec.ParentMetadataFailureEffect(source, target, cmd,
      step.beforeFs, step.afterFs, step.outcome)
  {
    reveal Core.StepEvidenceFor();
    reveal Core.SameFileEvidenceFor();
    DirectParentDecisionFields(source,target,cmd,step.beforeFs,cwd,step.sameFile);
    var sourceEntry := step.sameFile.sourceEntry;
    var targetEntry := step.sameFile.targetEntry;
    EntryNameEvidenceImpliesPathRelations(step.beforeFs, source, sourceEntry);
    EntryNameEvidenceImpliesPathRelations(step.beforeFs, target, targetEntry);
    assert cmd.overwriteMode != Schema.OverwriteSkip &&
      cmd.updateMode != Schema.UpdateNone && cmd.updateMode != Schema.UpdateNoneFail;
    assert sourceEntry.leaf == targetEntry.leaf;
    assert !sourceEntry.parentMetadata.ok || !targetEntry.parentMetadata.ok;
    assert step.afterFs == step.beforeFs;
    assert step.outcome == Spec.MoveOutcome([], Spec.ParentStatFailureMessageSpec(
      if !sourceEntry.parentMetadata.ok then sourceEntry.parent else targetEntry.parent,
      if !sourceEntry.parentMetadata.ok then sourceEntry.parentMetadata.err else targetEntry.parentMetadata.err), true);
    assert Core.MetadataEvidenceFor(step.beforeFs, sourceEntry.parent, false, sourceEntry.parentMetadata);
    assert Core.MetadataEvidenceFor(step.beforeFs, targetEntry.parent, false, targetEntry.parentMetadata);
    if !sourceEntry.parentMetadata.ok {
      assert IOContract.FileStatusStructureContractFields(step.beforeFs, sourceEntry.parent,
        false, false, sourceEntry.parentMetadata.rawStatus, sourceEntry.parentMetadata.err);
      assert sourceEntry.parentMetadata.err > 0;
      hide *;
      reveal Spec.ParentMetadataFailureEffect();
      assert exists sp: string, tp: string, failedPath: string,
        status: BW.FileStatus, err: int, leaf: string ::
        sp == sourceEntry.parent && tp == targetEntry.parent && leaf == sourceEntry.leaf &&
        failedPath == sp && status == sourceEntry.parentMetadata.rawStatus &&
        err == sourceEntry.parentMetadata.err &&
        DirnameSpec.DirnameRelation(source, sp) && DirnameSpec.DirnameRelation(target, tp) &&
        BasenameSpec.BasenameRelation(source, leaf) && BasenameSpec.BasenameRelation(target, leaf) &&
        failedPath in {sp, tp} &&
        IOContract.FileStatusStructureContractFields(step.beforeFs, failedPath, false, false, status, err) &&
        err > 0 && step.afterFs == step.beforeFs &&
        step.outcome == Spec.MoveOutcome([], Spec.ParentStatFailureMessageSpec(failedPath, err), true);
    } else {
      assert !targetEntry.parentMetadata.ok;
      assert IOContract.FileStatusStructureContractFields(step.beforeFs, targetEntry.parent,
        false, false, targetEntry.parentMetadata.rawStatus, targetEntry.parentMetadata.err);
      assert targetEntry.parentMetadata.err > 0;
      hide *;
      reveal Spec.ParentMetadataFailureEffect();
      assert exists sp: string, tp: string, failedPath: string,
        status: BW.FileStatus, err: int, leaf: string ::
        sp == sourceEntry.parent && tp == targetEntry.parent && leaf == sourceEntry.leaf &&
        failedPath == tp && status == targetEntry.parentMetadata.rawStatus &&
        err == targetEntry.parentMetadata.err &&
        DirnameSpec.DirnameRelation(source, sp) && DirnameSpec.DirnameRelation(target, tp) &&
        BasenameSpec.BasenameRelation(source, leaf) && BasenameSpec.BasenameRelation(target, leaf) &&
        failedPath in {sp, tp} &&
        IOContract.FileStatusStructureContractFields(step.beforeFs, failedPath, false, false, status, err) &&
        err > 0 && step.afterFs == step.beforeFs &&
        step.outcome == Spec.MoveOutcome([], Spec.ParentStatFailureMessageSpec(failedPath, err), true);
    }
  }

  lemma ParentMetadataFailureStatusImpliesShape(
    source: string, target: string, cmd: Schema.MvCmd, cwd: BW.Path,
    step: Core.StepEvidence
  )
    requires Core.StepEvidenceFor(source, target, cmd, cwd, step)
    requires Core.StepStatusEvidenceFor(source, target, cmd, step)
    requires step.sameFile.CheckedSameFile? && step.sameFile.decision.FailedParentStat?
    requires step.sameFile.sourceReferentEntry.NoEntryNameEvidence?
    ensures Spec.MoveStatusShape(cmd, step.beforeFs, cwd, source, target, step.statusCalls, step.inputs)
  {
    hide *;
    StepStatusEvidenceImpliesMoveStatusShape(source, target, cmd, cwd, step);
  }

  lemma ParentMetadataFailureStatusImpliesOutcome(
    source: string, target: string, cmd: Schema.MvCmd, cwd: BW.Path,
    step: Core.StepEvidence
  )
    requires Core.StepEvidenceFor(source, target, cmd, cwd, step)
    requires Core.StepStatusEvidenceFor(source, target, cmd, step)
    requires step.sameFile.CheckedSameFile? && step.sameFile.decision.FailedParentStat?
    requires step.sameFile.sourceReferentEntry.NoEntryNameEvidence?
    ensures Spec.ObservedParentFailureOutcome(source, target, cmd, step.beforeFs, cwd,
      step.afterFs, step.outcome, step.statusCalls)
    ensures Spec.ObservedMoveOutcome(source, target, cmd, step.beforeFs, cwd,
      step.afterFs, step.outcome, step.statusCalls, step.inputs)
  {
    hide *;
    StepEvidenceImpliesObservedOutcome(source, target, cmd, cwd, step);
    reveal Core.StepEvidenceFor(), Core.StepStatusEvidenceFor(), Core.SameFileEvidenceFor();
    reveal Core.MetadataStatusCall(), Spec.StatusRequest();
    DirectParentDecisionFields(source, target, cmd, step.beforeFs, cwd, step.sameFile);
    var sourceEntry := step.sameFile.sourceEntry;
    var targetEntry := step.sameFile.targetEntry;
    EntryNameEvidenceImpliesPathRelations(step.beforeFs, source, sourceEntry);
    EntryNameEvidenceImpliesPathRelations(step.beforeFs, target, targetEntry);
    assert sourceEntry.leaf == targetEntry.leaf;
    assert |step.statusCalls| == 4;
    assert step.statusCalls[0].ok && step.statusCalls[1].ok;
    assert !step.statusCalls[2].ok || !step.statusCalls[3].ok;
    assert exists leaf: string :: BasenameSpec.BasenameRelation(source, leaf) &&
      BasenameSpec.BasenameRelation(target, leaf);
    assert step.afterFs == step.beforeFs;
    assert step.outcome == Spec.MoveOutcome([], Spec.ParentStatFailureMessageSpec(
      if !step.statusCalls[2].ok then sourceEntry.parent else targetEntry.parent,
      if !step.statusCalls[2].ok then step.statusCalls[2].err else step.statusCalls[3].err), true);
    assert Spec.StatusRequest(step.statusCalls[2], step.beforeFs, sourceEntry.parent, false);
    assert Spec.StatusRequest(step.statusCalls[3], step.beforeFs, targetEntry.parent, false);
    hide *;
    reveal Spec.ObservedParentFailureOutcome();
  }

  lemma ParentMetadataFailureEvidenceImpliesObservedStep(
    source: string, target: string, cmd: Schema.MvCmd, cwd: BW.Path,
    step: Core.StepEvidence, observations: Spec.NativeStatusInputs
  )
    requires Core.StepEvidenceFor(source, target, cmd, cwd, step)
    requires Core.StepStatusEvidenceFor(source, target, cmd, step)
    requires Core.StatusCallsFor(observations, step.firstStatus, step.statusCalls)
    requires step.inputs == observations
    requires step.sameFile.CheckedSameFile? && step.sameFile.decision.FailedParentStat?
    requires step.sameFile.sourceReferentEntry.NoEntryNameEvidence?
    ensures Spec.ObservedStepRelation(source, target, cmd, step.beforeFs, cwd,
      step.afterFs, step.outcome, observations, step.firstStatus,
      step.firstStatus + |step.statusCalls|, step.statusCalls)
  {
    hide *;
    StepStatusEvidenceImpliesObservedStep(source, target, cmd, cwd, step, observations);
  }

  lemma DirectParentDecisionFields(
    source: string, target: string, cmd: Schema.MvCmd, fs: BW.FileSystem, cwd: BW.Path,
    same: Core.SameFileEvidence
  )
    requires Core.SameFileEvidenceFor(cmd, fs, cwd, source, target, same)
    requires same.CheckedSameFile?
    ensures (same.sourceEntry.leaf == same.targetEntry.leaf &&
      (!same.sourceEntry.parentMetadata.ok || !same.targetEntry.parentMetadata.ok)) ==
      (same.decision.FailedParentStat? && same.sourceReferentEntry.NoEntryNameEvidence?)
  {
    hide *;
    reveal Core.SameFileEvidenceFor();
  }

  lemma FailedParentDecisionImpliesObservedFault(
    source: string, target: string, cmd: Schema.MvCmd, cwd: BW.Path,
    step: Core.StepEvidence
  )
    requires Core.StepEvidenceFor(source, target, cmd, cwd, step)
    requires step.sameFile.CheckedSameFile? && step.sameFile.decision.FailedParentStat?
    ensures Spec.ObservedMetadataFault(source, step.beforeFs, cwd, step.statusCalls, step.inputs)
  {
    hide *;
    reveal Core.StepEvidenceFor(), Core.StepStatusEvidenceFor(), Core.SameFileEvidenceFor();
    reveal Core.MetadataEvidenceFor(), Core.MetadataStatusCall();
    var same := step.sameFile;
    DirectParentDecisionFields(source, target, cmd, step.beforeFs, cwd, same);
    if same.sourceReferentEntry.NoEntryNameEvidence? {
      EntryNameEvidenceImpliesPathRelations(step.beforeFs, source, same.sourceEntry);
      EntryNameEvidenceImpliesPathRelations(step.beforeFs, target, same.targetEntry);
      assert same.sourceEntry.leaf == same.targetEntry.leaf;
      assert step.statusCalls[1].path == target;
      assert exists leaf: string :: leaf == same.sourceEntry.leaf &&
        BasenameSpec.BasenameRelation(source, leaf) && BasenameSpec.BasenameRelation(target, leaf);
    } else {
      assert same.sourceReferentEntry.SomeEntryNameEvidence?;
      assert |step.statusCalls| >= 6;
      assert !step.statusCalls[3].ok || !step.statusCalls[5].ok;
    }
    reveal Spec.ObservedMetadataFault();
  }

  lemma {:isolate_assertions} StepEvidenceImpliesOriginalEffectWithoutFault(
    source: string,
    target: string,
    cmd: Schema.MvCmd,
    preCwd: BW.Path,
    evidence: Core.StepEvidence
  )
    requires Core.StepEvidenceFor(
               source, target, cmd, preCwd, evidence
             )
    requires !Spec.ObservedMetadataFault(source, evidence.beforeFs, preCwd,
      evidence.statusCalls, evidence.inputs)
    ensures Spec.OriginalMoveEffectRelation(source, target, cmd,
      evidence.beforeFs, preCwd, evidence.afterFs, evidence.outcome)
  {
    hide Spec.RenameEffectRelation(), Spec.ExistingTargetRenameEffectRelation(), Spec.SameFilePolicyRelation();
    reveal Core.StepEvidenceFor(), Core.StepStatusEvidenceFor(), Core.SameFileEvidenceFor();
    reveal Core.SourceResolutionObservationFor(), IOContract.ResolvePathIdentitySpec();
    reveal IOContract.NativeFailureContractFields();
    assert (forall i: nat | i < |evidence.statusCalls| :: evidence.statusCalls[i].ok ||
      !Spec.StatusExistsOutcomeFields(evidence.statusCalls[i].fs, evidence.statusCalls[i].path,
        evidence.statusCalls[i].followSymlink, true, 0));
    assert IOContract.IsDirectoryStrictContractFields(evidence.beforeFs, source, false,
      evidence.sourceOk, evidence.sourceIsDir, evidence.sourceErr);
    assert Core.SkipStdout(target, cmd.debug) == Spec.SkipStdoutSpec(target, cmd.debug);
    if !evidence.sourceOk {
      assert evidence.afterFs == evidence.beforeFs && evidence.outcome == Spec.MoveOutcome([],
        Spec.SourceStatFailureMessageSpec(source, evidence.sourceErr), true);
    } else {
      assert Spec.StatusExistsOutcomeFields(evidence.beforeFs, target, false,
        evidence.targetFound, evidence.targetExistsErr);
      if !evidence.targetFound {
        RenameEvidenceImpliesRelation(source, target, evidence.sourceIsDir, false, "",
          cmd.verbose, cmd.debug, evidence.beforeFs, preCwd, evidence.afterFs,
          evidence.outcome, evidence.renames, evidence.backupFs);
      } else if cmd.overwriteMode == Schema.OverwriteSkip || cmd.updateMode == Schema.UpdateNone {
        assert evidence.afterFs == evidence.beforeFs && evidence.outcome ==
          Spec.MoveOutcome(Spec.SkipStdoutSpec(target, cmd.debug), [], false);
      } else if cmd.updateMode == Schema.UpdateNoneFail {
        assert evidence.afterFs == evidence.beforeFs && evidence.outcome ==
          Spec.MoveOutcome([], Spec.NotReplacingMessageSpec(target), true);
      } else {
        assert evidence.sameFile.CheckedSameFile?;
        var same := evidence.sameFile;
        if same.decision.FailedParentStat? {
          FailedParentDecisionImpliesObservedFault(source, target, cmd, preCwd, evidence);
          assert false;
        }
        assert same.source.isSymlink ==> same.sourceReferentEntry.SomeEntryNameEvidence?;
        SameFileEvidenceImpliesPolicy(cmd, evidence.beforeFs, preCwd, source, target, same);
        if same.decision == Spec.RejectSameFile {
          assert evidence.afterFs == evidence.beforeFs && evidence.outcome ==
            Spec.MoveOutcome([], Spec.SameFileMessageSpec(source, target), true);
        } else if cmd.updateMode == Schema.UpdateOlder && !Core.SourceNewer(
          same.source.times.mtimeSec, same.source.times.mtimeNsec,
          same.target.times.mtimeSec, same.target.times.mtimeNsec) {
          assert evidence.afterFs == evidence.beforeFs && evidence.outcome ==
            Spec.MoveOutcome(Spec.SkipStdoutSpec(target, cmd.debug), [], false);
          assert !Spec.SourceNewerSpec(same.source.times.mtimeSec, same.source.times.mtimeNsec,
            same.target.times.mtimeSec, same.target.times.mtimeNsec);
        } else {
          ExistingTargetRenameEvidenceImpliesRelation(source, target, cmd, preCwd, evidence);
          if cmd.updateMode == Schema.UpdateOlder {
            assert Spec.SourceNewerSpec(same.source.times.mtimeSec, same.source.times.mtimeNsec,
              same.target.times.mtimeSec, same.target.times.mtimeNsec);
          }
        }
      }
    }
    hide *;
    reveal Spec.OriginalMoveEffectRelation();
    assert Spec.OriginalMoveEffectRelation(source, target, cmd,
      evidence.beforeFs, preCwd, evidence.afterFs, evidence.outcome);
  }

  lemma StepEvidenceImpliesMoveEffect(
    source: string, target: string, cmd: Schema.MvCmd, cwd: BW.Path,
    step: Core.StepEvidence
  )
    requires Core.StepEvidenceFor(source, target, cmd, cwd, step)
    ensures Spec.MoveEffectRelation(source, target, cmd,
      step.beforeFs, cwd, step.afterFs, step.outcome)
    ensures !Spec.ObservedMetadataFault(source, step.beforeFs, cwd, step.statusCalls, step.inputs) ==>
      Spec.OriginalMoveEffectRelation(source, target, cmd, step.beforeFs, cwd, step.afterFs, step.outcome)
  {
    reveal Core.StepEvidenceFor();
    if Spec.ObservedMetadataFault(source, step.beforeFs, cwd, step.statusCalls, step.inputs) {
      StepEvidenceImpliesObservedOutcome(source, target, cmd, cwd, step);
      StepStatusEvidenceImpliesMoveStatusShape(source, target, cmd, cwd, step);
      reveal Core.StepEvidenceFor();
      assert exists inputs: Spec.NativeStatusInputs, first: nat, calls: seq<Spec.StatusCallEvidence> ::
        inputs == step.inputs && first == step.firstStatus && calls == step.statusCalls &&
        Spec.StatusCallsFor(inputs, first, calls) &&
        Spec.MoveStatusShape(cmd, step.beforeFs, cwd, source, target, calls, inputs) &&
        Spec.ObservedMoveOutcome(source, target, cmd, step.beforeFs, cwd, step.afterFs, step.outcome, calls, inputs) &&
        Spec.ObservedMetadataFault(source, step.beforeFs, cwd, calls, inputs);
    } else {
      StepEvidenceImpliesOriginalEffectWithoutFault(source, target, cmd, cwd, step);
    }
  }

  lemma CapturedSameFileDecisionScalarFields(
    source: string, target: string, cmd: Schema.MvCmd, cwd: BW.Path,
    fs: BW.FileSystem, same: Core.SameFileEvidence
  )
    requires Core.SameFileEvidenceFor(cmd,fs,cwd,source,target,same)
    requires same.CheckedSameFile?
    requires !same.decision.FailedParentStat? || same.sourceReferentEntry.SomeEntryNameEvidence?
    ensures same.decision.FailedParentStat? ==
      (same.sourceReferentEntry.SomeEntryNameEvidence? &&
       same.sourceReferentEntry.value.leaf == same.targetEntry.leaf &&
       (!same.sourceReferentEntry.value.parentMetadata.ok || !same.targetEntry.parentMetadata.ok))
    ensures !same.decision.FailedParentStat? ==>
      (same.decision == Spec.RejectSameFile) ==
      (Core.EvidenceNamesSame(same.sourceEntry,same.targetEntry) ||
       (cmd.backupMode == Schema.BackupOff &&
        (same.source.key == same.target.key ||
         Core.ReferentEvidenceNamesTarget(same.sourceReferentEntry,same.targetEntry))))
  {
    hide *;
    DirectParentDecisionFields(source,target,cmd,fs,cwd,same);
    reveal Core.SameFileEvidenceFor();
  }

  lemma CapturedSameFileDecisionMatchesObservations(
    source: string, target: string, cmd: Schema.MvCmd, cwd: BW.Path,
    step: Core.StepEvidence
  )
    requires Core.StepEvidenceFor(source, target, cmd, cwd, step)
    requires step.sameFile.CheckedSameFile?
    requires !step.sameFile.decision.FailedParentStat? ||
      step.sameFile.sourceReferentEntry.SomeEntryNameEvidence?
    ensures
      var referent := step.sameFile.sourceReferentEntry;
      var resolved := if referent.SomeEntryNameEvidence? then referent.resolvedPath else "";
      Spec.ObservedReferentParentFailure(step.statusCalls, step.sameFile.targetEntry.leaf,
        referent.SomeEntryNameEvidence?, resolved) == step.sameFile.decision.FailedParentStat?
    ensures !step.sameFile.decision.FailedParentStat? ==>
      var referent := step.sameFile.sourceReferentEntry;
      var resolved := if referent.SomeEntryNameEvidence? then referent.resolvedPath else "";
      Spec.ObservedSameFileRejection(cmd, step.statusCalls, step.sameFile.sourceEntry.leaf,
        step.sameFile.targetEntry.leaf, referent.SomeEntryNameEvidence?, resolved) ==
        (step.sameFile.decision == Spec.RejectSameFile)
  {
    hide IOContract.GetFileStatusResultFields(), IOContract.FileStatusStructureContractFields();
    hide Core.StatusCallsFor(), Spec.StatusCallsFor();
    hide Core.SourceResolutionObservationFor(), Core.RenameNativeObservationsFor();
    reveal Core.StepEvidenceFor(), Core.StepStatusEvidenceFor(), Core.SameFileEvidenceFor();
    CapturedSameFileDecisionScalarFields(source,target,cmd,cwd,step.beforeFs,step.sameFile);
    var sourceEntry := step.sameFile.sourceEntry;
    var targetEntry := step.sameFile.targetEntry;
    EntryNameEvidenceImpliesPathRelations(step.beforeFs, source, sourceEntry);
    EntryNameEvidenceImpliesPathRelations(step.beforeFs, target, targetEntry);
    assert |step.statusCalls| >= 4;
    assert step.sameFile.source.key == step.statusCalls[0].status.hostKey;
    assert step.sameFile.target.key == step.statusCalls[1].status.hostKey;
    assert Core.EvidenceNamesSame(sourceEntry, targetEntry) ==
      (sourceEntry.leaf == targetEntry.leaf && step.statusCalls[2].ok && step.statusCalls[3].ok &&
       step.statusCalls[2].status.hostKey == step.statusCalls[3].status.hostKey);
    assert targetEntry.parentMetadata.ok == step.statusCalls[3].ok;
    if step.sameFile.sourceReferentEntry.SomeEntryNameEvidence? {
      var referent := step.sameFile.sourceReferentEntry;
      EntryNameEvidenceImpliesPathRelations(step.beforeFs, referent.resolvedPath, referent.value);
      assert |step.statusCalls| >= 6;
      assert referent.value.parentMetadata.ok == step.statusCalls[5].ok;
      assert BasenameSpec.BasenameRelation(referent.resolvedPath,referent.value.leaf);
      assert forall leaf: string | BasenameSpec.BasenameRelation(referent.resolvedPath, leaf) ::
        leaf == referent.value.leaf by {
        forall leaf: string | BasenameSpec.BasenameRelation(referent.resolvedPath, leaf)
          ensures leaf == referent.value.leaf
        {
          BasenameRelationFunctional(referent.resolvedPath, referent.value.leaf, leaf);
        }
      }
    }
    if step.sameFile.sourceReferentEntry.SomeEntryNameEvidence? {
      var referent := step.sameFile.sourceReferentEntry;
      assert (exists leaf: string :: BasenameSpec.BasenameRelation(referent.resolvedPath,leaf) &&
        leaf == targetEntry.leaf) == (referent.value.leaf == targetEntry.leaf) by {
        hide *;
      }
    }
    var referent := step.sameFile.sourceReferentEntry;
    var resolved := if referent.SomeEntryNameEvidence? then referent.resolvedPath else "";
    assert Core.ReferentEvidenceNamesTarget(referent, targetEntry) ==
      (referent.SomeEntryNameEvidence? && |step.statusCalls| >= 6 &&
       step.statusCalls[3].ok && step.statusCalls[5].ok &&
       step.statusCalls[3].status.hostKey == step.statusCalls[5].status.hostKey &&
       (exists leaf: string :: BasenameSpec.BasenameRelation(resolved, leaf) && leaf == targetEntry.leaf));
    assert Spec.ObservedReferentParentFailure(step.statusCalls, targetEntry.leaf,
      referent.SomeEntryNameEvidence?, resolved) == step.sameFile.decision.FailedParentStat? by {
      hide *;
      reveal Spec.ObservedReferentParentFailure();
    }
    if !step.sameFile.decision.FailedParentStat? {
      assert Spec.ObservedSameFileRejection(cmd, step.statusCalls, sourceEntry.leaf,
        targetEntry.leaf, referent.SomeEntryNameEvidence?, resolved) ==
        (step.sameFile.decision == Spec.RejectSameFile) by {
        hide *;
        reveal Spec.ObservedSameFileRejection();
      }
    }
    hide *;

  }

  lemma ContinuingStepStatusTail(
    source: string, target: string, cmd: Schema.MvCmd, step: Core.StepEvidence
  )
    requires Core.StepStatusEvidenceFor(source, target, cmd, step)
    requires step.sourceOk && step.targetFound
    requires cmd.overwriteMode != Schema.OverwriteSkip && cmd.updateMode != Schema.UpdateNone &&
      cmd.updateMode != Schema.UpdateNoneFail
    requires step.sameFile.CheckedSameFile? && step.sameFile.decision == Spec.ContinueMove
    requires cmd.updateMode != Schema.UpdateOlder || Core.SourceNewer(
      step.sameFile.source.times.mtimeSec, step.sameFile.source.times.mtimeNsec,
      step.sameFile.target.times.mtimeSec, step.sameFile.target.times.mtimeNsec)
    ensures
      var same := step.sameFile;
      var afterEntries := if same.source.isSymlink then
        (if same.sourceReferentEntry.SomeEntryNameEvidence? then 6 else 5) else 4;
      var collisionNeeded :=
        (cmd.backupMode == Schema.BackupSimple || cmd.backupMode == Schema.BackupExisting) &&
        same.sourceEntry.leaf == same.targetEntry.leaf + cmd.backupSuffix;
      var afterCollision := afterEntries + (if collisionNeeded then 1 else 0);
      afterCollision <= |step.statusCalls| &&
      (collisionNeeded ==>
        same.backupCollision.CheckedBackupCollision? &&
        step.statusCalls[afterEntries] == Core.MetadataStatusCall(step.beforeFs,
          Core.SimpleBackupPath(target, cmd.backupSuffix), true,
          same.backupCollision.simpleCandidateFollowed)) &&
      (!Core.BackupCollisionDetected(same.backupCollision) ==>
        Core.BackupSelectionFromStatusCallsFor(cmd.backupMode, cmd.backupSuffix,
          step.beforeFs, target, step.backup, step.statusCalls[afterCollision..]))
  {
    hide *;
    reveal Core.StepStatusEvidenceFor();
  }

  lemma DirectParentEvidenceImpliesStatusWitness(
    source: string, target: string, cmd: Schema.MvCmd, cwd: BW.Path,
    step: Core.StepEvidence
  )
    requires Core.StepStatusEvidenceFor(source, target, cmd, step)
    requires Core.SameFileEvidenceFor(cmd, step.beforeFs, cwd, source, target, step.sameFile)
    requires step.sourceOk && step.targetFound && step.sameFile.CheckedSameFile?
    requires cmd.overwriteMode != Schema.OverwriteSkip && cmd.updateMode != Schema.UpdateNone &&
      cmd.updateMode != Schema.UpdateNoneFail
    requires step.sameFile.decision.FailedParentStat? &&
      step.sameFile.sourceReferentEntry.NoEntryNameEvidence?
    ensures Spec.MoveStatusShapeWitness(cmd, step.beforeFs, cwd, source, target,
      step.statusCalls, step.sameFile.sourceEntry.parent, step.sameFile.targetEntry.parent,
      step.sameFile.sourceEntry.leaf, step.sameFile.targetEntry.leaf,
      false, "", 0, 4, step.inputs)
  {
    hide *;
    reveal Core.StepStatusEvidenceFor(), Core.SameFileEvidenceFor();
    reveal Core.MetadataStatusCall(), Spec.StatusRequest();
    var same := step.sameFile;
    var sourceEntry := same.sourceEntry;
    var targetEntry := same.targetEntry;
    DirectParentDecisionFields(source, target, cmd, step.beforeFs, cwd, same);
    EntryNameEvidenceImpliesPathRelations(step.beforeFs, source, sourceEntry);
    EntryNameEvidenceImpliesPathRelations(step.beforeFs, target, targetEntry);
    assert |step.statusCalls| == 4;
    assert step.statusCalls[0].ok && step.statusCalls[1].ok;
    assert sourceEntry.leaf == targetEntry.leaf;
    assert !step.statusCalls[2].ok || !step.statusCalls[3].ok;
    assert Spec.StatusRequest(step.statusCalls[2], step.beforeFs, sourceEntry.parent, false);
    assert Spec.StatusRequest(step.statusCalls[3], step.beforeFs, targetEntry.parent, false);
    reveal Spec.MoveComparisonObservations(), Spec.MoveContinuationObservations();
    reveal Spec.MoveStatusShapeWitness();
  }

  lemma ComparisonEvidenceImpliesStatusObservations(
    source: string, target: string, cmd: Schema.MvCmd, cwd: BW.Path,
    step: Core.StepEvidence
  )
    requires Core.StepStatusEvidenceFor(source, target, cmd, step)
    requires Core.SameFileEvidenceFor(cmd, step.beforeFs, cwd, source, target, step.sameFile)
    requires Core.SourceResolutionObservationFor(source, cwd, step)
    requires step.sourceOk && step.targetFound && step.sameFile.CheckedSameFile?
    requires cmd.overwriteMode != Schema.OverwriteSkip && cmd.updateMode != Schema.UpdateNone &&
      cmd.updateMode != Schema.UpdateNoneFail
    requires !step.sameFile.decision.FailedParentStat? ||
      !step.sameFile.sourceReferentEntry.NoEntryNameEvidence?
    requires |step.statusCalls| >= 4
    requires step.sameFile.source.isSymlink ==
      (step.statusCalls[0].status.kind == BW.SymlinkKind)
    ensures
      var same := step.sameFile;
      var referent := same.sourceReferentEntry;
      var resolveOk := referent.SomeEntryNameEvidence?;
      var resolved := if resolveOk then referent.resolvedPath else "";
      var resolveErr := if referent.FailedEntryNameEvidence? then referent.err else 0;
      var afterEntries := if same.source.isSymlink then (if resolveOk then 6 else 5) else 4;
      Spec.MoveComparisonObservations(cmd, step.beforeFs, cwd, source, target, step.statusCalls,
        same.sourceEntry.parent, same.targetEntry.parent, same.sourceEntry.leaf, same.targetEntry.leaf,
        resolveOk, resolved, resolveErr, afterEntries, step.inputs)
  {
    hide *;
    reveal Core.StepStatusEvidenceFor(), Core.SameFileEvidenceFor();
    reveal Core.SourceResolutionObservationFor(), Core.MetadataStatusCall();
    reveal Spec.StatusRequest();
    var same := step.sameFile;
    var sourceEntry := same.sourceEntry;
    var targetEntry := same.targetEntry;
    DirectParentDecisionFields(source, target, cmd, step.beforeFs, cwd, same);
    EntryNameEvidenceImpliesPathRelations(step.beforeFs, source, sourceEntry);
    EntryNameEvidenceImpliesPathRelations(step.beforeFs, target, targetEntry);
    assert sourceEntry.leaf != targetEntry.leaf ||
      (sourceEntry.parentMetadata.ok && targetEntry.parentMetadata.ok);
    if same.source.isSymlink {
      match same.sourceReferentEntry {
        case SomeEntryNameEvidence(resolved, referentEntry) =>
          EntryNameEvidenceImpliesPathRelations(step.beforeFs, resolved, referentEntry);
          assert exists parent: string :: parent == referentEntry.parent &&
            DirnameSpec.DirnameRelation(resolved, parent) &&
            Spec.StatusRequest(step.statusCalls[5], step.beforeFs, parent, false);
        case FailedEntryNameEvidence(_) =>
        case NoEntryNameEvidence =>
      }
    }
    reveal Spec.MoveComparisonObservations();
  }

  lemma {:isolate_assertions} StepStatusEvidenceImpliesMoveStatusShape(
    source: string,
    target: string,
    cmd: Schema.MvCmd,
    preCwd: BW.Path,
    step: Core.StepEvidence
  )
    requires Core.StepEvidenceFor(source, target, cmd, preCwd, step)
    requires Core.StepStatusEvidenceFor(source, target, cmd, step)
    ensures Spec.MoveStatusShape(
      cmd, step.beforeFs, preCwd, source, target, step.statusCalls, step.inputs
    )
    ensures step.sameFile.CheckedSameFile? ==>
      var same := step.sameFile;
      var referent := same.sourceReferentEntry;
      var resolveOk := referent.SomeEntryNameEvidence?;
      var resolved := if resolveOk then referent.resolvedPath else "";
      var resolveErr := if referent.FailedEntryNameEvidence? then referent.err else 0;
      var afterEntries := if same.decision.FailedParentStat? && referent.NoEntryNameEvidence? then 4
        else if same.source.isSymlink then (if resolveOk then 6 else 5) else 4;
      Spec.MoveStatusShapeWitness(cmd, step.beforeFs, preCwd, source, target, step.statusCalls,
        same.sourceEntry.parent, same.targetEntry.parent, same.sourceEntry.leaf, same.targetEntry.leaf,
        resolveOk, resolved, resolveErr, afterEntries, step.inputs)
  {
    hide IOContract.GetFileStatusResultFields(), IOContract.FileStatusStructureContractFields();
    hide Core.StatusCallsFor(), Spec.StatusCallsFor(), Core.RenameNativeObservationsFor();
    hide Core.RenameEvidenceFor(), Core.ExistingTargetRenameEvidenceFor();
    hide Core.BackupSelectionFromStatusCallsFor(), Core.BackupStatusSuffixFor(), Spec.BackupStatusSuffix();
    reveal Core.StepEvidenceFor();
    reveal Core.StepStatusEvidenceFor();
    reveal Core.SameFileEvidenceFor();
    reveal Spec.MoveStatusShape(), Spec.MoveStatusShapeWitness();
    if step.sameFile.CheckedSameFile? && step.sameFile.decision.FailedParentStat? &&
       step.sameFile.sourceReferentEntry.NoEntryNameEvidence? {
      DirectParentEvidenceImpliesStatusWitness(source, target, cmd, preCwd, step);
    } else if !step.sourceOk {
      assert Spec.MoveStatusShape(
        cmd, step.beforeFs, preCwd, source, target, step.statusCalls, step.inputs
      );
    } else if !step.targetFound || cmd.overwriteMode == Schema.OverwriteSkip ||
       cmd.updateMode == Schema.UpdateNone ||
       cmd.updateMode == Schema.UpdateNoneFail {
      assert Spec.MoveStatusShape(
        cmd, step.beforeFs, preCwd, source, target, step.statusCalls, step.inputs
      );
    } else {
      CapturedSameFileDecisionMatchesObservations(source, target, cmd, preCwd, step);
      match step.sameFile {
        case NoSameFileCheck =>
        case CheckedSameFile(
          sourceMetadata, targetMetadata, sourceFollowed,
          sourceEntry, targetEntry, sourceReferentEntry,
          collision, decision
        ) =>
          DirectParentDecisionFields(source, target, cmd, step.beforeFs, preCwd, step.sameFile);
          assert sourceEntry.leaf != targetEntry.leaf ||
            (sourceEntry.parentMetadata.ok && targetEntry.parentMetadata.ok);
          assert sourceMetadata.isSymlink == (step.statusCalls[0].status.kind == BW.SymlinkKind);
          assert Spec.SourceNewerSpec(step.statusCalls[0].status.times.mtimeSec,
            step.statusCalls[0].status.times.mtimeNsec, step.statusCalls[1].status.times.mtimeSec,
            step.statusCalls[1].status.times.mtimeNsec) == Core.SourceNewer(
            sourceMetadata.times.mtimeSec, sourceMetadata.times.mtimeNsec,
            targetMetadata.times.mtimeSec, targetMetadata.times.mtimeNsec);
          var afterEntries: nat :=
            if sourceMetadata.isSymlink then
              (if sourceReferentEntry.SomeEntryNameEvidence? then 6 else 5)
            else 4;
          assert sourceEntry.leaf != targetEntry.leaf ||
            (step.statusCalls[2].ok && step.statusCalls[3].ok);
          if decision.FailedParentStat? || decision == Spec.RejectSameFile ||
             (cmd.updateMode == Schema.UpdateOlder && !Core.SourceNewer(
               sourceMetadata.times.mtimeSec, sourceMetadata.times.mtimeNsec,
               targetMetadata.times.mtimeSec, targetMetadata.times.mtimeNsec)) {
            assert |step.statusCalls| == afterEntries;
          }
          if decision == Spec.ContinueMove &&
             (cmd.updateMode != Schema.UpdateOlder ||
              Core.SourceNewer(
                sourceMetadata.times.mtimeSec,
                sourceMetadata.times.mtimeNsec,
                targetMetadata.times.mtimeSec,
                targetMetadata.times.mtimeNsec
              )) {
            ContinuingStepStatusTail(source, target, cmd, step);
            reveal Core.ExistingTargetRenameEvidenceFor();
            hide Core.BackupSelectionEvidenceFor();
            var collisionNeeded :=
              (cmd.backupMode == Schema.BackupSimple ||
               cmd.backupMode == Schema.BackupExisting) &&
              sourceEntry.leaf == targetEntry.leaf + cmd.backupSuffix;
            var afterCollision := afterEntries +
              (if collisionNeeded then 1 else 0);
            assert Spec.SimpleBackupPathSpec(
              target, cmd.backupSuffix
            ) == Core.SimpleBackupPath(target, cmd.backupSuffix);
            if !collisionNeeded {
              assert !Core.BackupCollisionDetected(collision);
            }
            if collisionNeeded {
              assert Spec.StatusRequest(step.statusCalls[afterEntries], step.beforeFs,
                Spec.SimpleBackupPathSpec(target, cmd.backupSuffix), true);
              assert Core.BackupCollisionDetected(collision) ==
                (step.statusCalls[afterEntries].ok &&
                 step.statusCalls[afterEntries].status.hostKey ==
                   step.statusCalls[0].status.hostKey);
            }
            if Core.BackupCollisionDetected(collision) {
              assert |step.statusCalls| == afterCollision;
            } else {
              assert Core.BackupSelectionFromStatusCallsFor(
                cmd.backupMode, cmd.backupSuffix, step.beforeFs, target,
                step.backup, step.statusCalls[afterCollision..]);
              reveal Core.BackupSelectionFromStatusCallsFor();
              assert Core.BackupStatusSuffixFor(cmd.backupMode, step.beforeFs, target,
                step.statusCalls[afterCollision..]);
              hide Core.BackupSelectionFromStatusCallsFor();
              BackupStatusSuffixCoreImpliesSpec(
                cmd.backupMode, step.beforeFs, target,
                step.statusCalls[afterCollision..]
              );
            }
          }
          var resolveOk := sourceReferentEntry.SomeEntryNameEvidence?;
          var resolvedSource := match sourceReferentEntry
            case SomeEntryNameEvidence(path, _) => path
            case _ => "";
          var resolveErr := match sourceReferentEntry
            case FailedEntryNameEvidence(error) => error
            case _ => 0;
          assert Spec.MoveComparisonObservations(
            cmd, step.beforeFs, preCwd, source, target, step.statusCalls,
            sourceEntry.parent, targetEntry.parent, sourceEntry.leaf, targetEntry.leaf,
            resolveOk, resolvedSource, resolveErr, afterEntries, step.inputs) by {
            ComparisonEvidenceImpliesStatusObservations(source, target, cmd, preCwd, step);
          }
          assert Spec.MoveContinuationObservations(
            cmd, step.beforeFs, preCwd, source, target, step.statusCalls,
            sourceEntry.parent, targetEntry.parent, sourceEntry.leaf, targetEntry.leaf,
            resolveOk, resolvedSource, resolveErr, afterEntries, step.inputs) by {
            hide *;
            reveal Spec.MoveContinuationObservations();
          }
          assert Spec.MoveStatusShapeWitness(
            cmd, step.beforeFs, preCwd, source, target,
            step.statusCalls, sourceEntry.parent, targetEntry.parent,
            sourceEntry.leaf, targetEntry.leaf,
            resolveOk, resolvedSource, resolveErr, afterEntries, step.inputs
          );
      }
    }
    assert Spec.MoveStatusShape(
      cmd, step.beforeFs, preCwd, source, target, step.statusCalls, step.inputs
    );
  }

  lemma CheckedStepImpliesObservedClassification(
    source: string, target: string, cmd: Schema.MvCmd, cwd: BW.Path,
    step: Core.StepEvidence
  )
    requires Core.StepEvidenceFor(source, target, cmd, cwd, step)
    requires step.sameFile.CheckedSameFile?
    ensures
      var same := step.sameFile;
      var referent := same.sourceReferentEntry;
      var resolveOk := referent.SomeEntryNameEvidence?;
      var resolved := if resolveOk then referent.resolvedPath else "";
      var resolveErr := if referent.FailedEntryNameEvidence? then referent.err else 0;
      var afterEntries := if same.decision.FailedParentStat? && referent.NoEntryNameEvidence? then 4
        else if same.source.isSymlink then (if resolveOk then 6 else 5) else 4;
      Spec.ObservedClassificationOutcome(source, target, cmd, step.beforeFs, cwd,
        step.afterFs, step.outcome, step.statusCalls, step.inputs,
        (same.sourceEntry.parent, same.targetEntry.parent, same.sourceEntry.leaf, same.targetEntry.leaf),
        resolveOk, resolved, resolveErr, afterEntries)
  {
    hide IOContract.GetFileStatusResultFields(), IOContract.FileStatusStructureContractFields();
    hide Core.StatusCallsFor(), Spec.StatusCallsFor(), Core.RenameNativeObservationsFor();
    hide Core.RenameEvidenceFor(), Core.BackupSelectionFromStatusCallsFor();
    reveal Core.StepEvidenceFor();
    StepStatusEvidenceImpliesMoveStatusShape(source, target, cmd, cwd, step);
    reveal Core.StepEvidenceFor(), Core.StepStatusEvidenceFor(), Core.SameFileEvidenceFor();
    assert |step.statusCalls| >= 4;
    var same := step.sameFile;
    var referent := same.sourceReferentEntry;
    var resolveOk := referent.SomeEntryNameEvidence?;
    var resolved := if resolveOk then referent.resolvedPath else "";
    var resolveErr := if referent.FailedEntryNameEvidence? then referent.err else 0;
    var afterEntries: nat := if same.decision.FailedParentStat? && referent.NoEntryNameEvidence? then 4
      else if same.source.isSymlink then (if resolveOk then 6 else 5) else 4;
    if !(same.decision.FailedParentStat? && referent.NoEntryNameEvidence?) {
      CapturedSameFileDecisionMatchesObservations(source, target, cmd, cwd, step);
    }
    if same.decision.FailedParentStat? {
      if referent.SomeEntryNameEvidence? {
        EntryNameEvidenceImpliesPathRelations(step.beforeFs, referent.resolvedPath, referent.value);
      }
    } else if same.decision == Spec.ContinueMove &&
      (cmd.updateMode != Schema.UpdateOlder || Core.SourceNewer(
        same.source.times.mtimeSec, same.source.times.mtimeNsec,
        same.target.times.mtimeSec, same.target.times.mtimeNsec)) {
      reveal Core.ExistingTargetRenameEvidenceFor();
      if !Core.BackupCollisionDetected(same.backupCollision) {
        var collisionNeeded :=
          (cmd.backupMode == Schema.BackupSimple || cmd.backupMode == Schema.BackupExisting) &&
          same.sourceEntry.leaf == same.targetEntry.leaf + cmd.backupSuffix;
        var afterCollision := afterEntries + (if collisionNeeded then 1 else 0);
        BackupSelectionCallsImpliesObservedPath(cmd, step.beforeFs, target,
          step.backup, step.statusCalls[afterCollision..]);
        var backupPath := if step.backup.SelectedBackup? then step.backup.backupPath else "";
        RenameNativeEvidenceImpliesObservedRelation(source, target, cmd, cwd, step, backupPath);
      }
    }
  }

  lemma StepEvidenceImpliesObservedOutcome(
    source: string, target: string, cmd: Schema.MvCmd, cwd: BW.Path,
    step: Core.StepEvidence
  )
    requires Core.StepEvidenceFor(source, target, cmd, cwd, step)
    ensures Spec.ObservedMoveOutcome(source, target, cmd, step.beforeFs, cwd,
      step.afterFs, step.outcome, step.statusCalls, step.inputs)
  {
    reveal Core.StepEvidenceFor(), Core.StepStatusEvidenceFor();
    if step.sourceOk && !step.targetFound {
      RenameNativeEvidenceImpliesObservedRelation(source, target, cmd, cwd, step, "");
    } else if step.sourceOk && step.targetFound &&
      cmd.overwriteMode != Schema.OverwriteSkip && cmd.updateMode != Schema.UpdateNone &&
      cmd.updateMode != Schema.UpdateNoneFail {
      CheckedStepImpliesObservedClassification(source, target, cmd, cwd, step);
    }
  }

  lemma {:isolate_assertions} StepStatusEvidenceImpliesObservedStep(
    source: string,
    target: string,
    cmd: Schema.MvCmd,
    preCwd: BW.Path,
    step: Core.StepEvidence,
    observations: Spec.NativeStatusInputs
  )
    requires Core.StepEvidenceFor(source, target, cmd, preCwd, step)
    requires Core.StepStatusEvidenceFor(source, target, cmd, step)
    requires Core.StatusCallsFor(
               observations, step.firstStatus, step.statusCalls)
    requires step.inputs == observations
    ensures Spec.ObservedStepRelation(
              source, target, cmd, step.beforeFs, preCwd,
              step.afterFs, step.outcome, observations,
              step.firstStatus,
              step.firstStatus + |step.statusCalls|,
              step.statusCalls
            )
  {
    StepEvidenceImpliesMoveEffect(source, target, cmd, preCwd, step);
    StepEvidenceImpliesObservedOutcome(source, target, cmd, preCwd, step);
    StepStatusEvidenceImpliesMoveStatusShape(source, target, cmd, preCwd, step);
  }

  lemma BatchStepEvidenceImpliesMoveEffect(
    source: string,
    directory: string,
    cmd: Schema.MvCmd,
    beforeFs: BW.FileSystem,
    preCwd: BW.Path,
    afterFs: BW.FileSystem,
    outcome: Spec.MoveOutcome,
    stdoutFragment: BW.Bytes,
    stderrFragment: BW.Bytes,
    step: Core.StepEvidence
  )
    requires Core.BatchStepEvidenceFor(
               source,
               directory,
               cmd,
               beforeFs,
               preCwd,
               afterFs,
               outcome,
               stdoutFragment,
               stderrFragment,
               step
             )
    ensures
      var normalized :=
        Spec.NormalizeSourceSpec(
          source, cmd.stripTrailingSlashes
        );
      Spec.MoveEffectRelation(
        normalized,
        Spec.TargetInDirectorySpec(directory, normalized),
        cmd,
        beforeFs,
        preCwd,
        afterFs,
        outcome
      ) &&
      stdoutFragment == outcome.stdoutFragment &&
      stderrFragment == outcome.stderrFragment
  {
    reveal Core.BatchStepEvidenceFor();
    var normalizedCore :=
      Core.NormalizeSource(source, cmd.stripTrailingSlashes);
    NormalizeSourceSpecEqualsCore(
      source, cmd.stripTrailingSlashes
    );
    TargetInDirectorySpecEqualsCore(directory, normalizedCore);
    StepEvidenceImpliesMoveEffect(
      normalizedCore,
      Core.TargetInDirectory(directory, normalizedCore),
      cmd,
      preCwd,
      step
    );
  }

  lemma BatchMoveComponentsImplyWitnessRelation(
    sources: seq<string>,
    directory: string,
    cmd: Schema.MvCmd,
    beforeFs: BW.FileSystem,
    preCwd: BW.Path,
    afterFs: BW.FileSystem,
    hadError: bool,
    out: BW.Bytes,
    err: BW.Bytes,
    fsBounds: seq<BW.FileSystem>,
    outcomes: seq<Spec.MoveOutcome>,
    stdoutFragments: seq<BW.Bytes>,
    stderrFragments: seq<BW.Bytes>
  )
    requires |fsBounds| == |sources| + 1
    requires |outcomes| == |sources|
    requires |stdoutFragments| == |sources|
    requires |stderrFragments| == |sources|
    requires fsBounds[0] == beforeFs
    requires fsBounds[|fsBounds| - 1] == afterFs
    requires forall i: nat | i < |sources| ::
               var normalizedSource :=
                 Spec.NormalizeSourceSpec(
                   sources[i], cmd.stripTrailingSlashes
                 );
               Spec.MoveEffectRelation(
                 normalizedSource,
                 Spec.TargetInDirectorySpec(directory, normalizedSource),
                 cmd,
                 fsBounds[i],
                 preCwd,
                 fsBounds[i + 1],
                 outcomes[i]
               )
    requires forall i: nat | i < |sources| ::
               stdoutFragments[i] == outcomes[i].stdoutFragment
    requires forall i: nat | i < |sources| ::
               stderrFragments[i] == outcomes[i].stderrFragment
    requires Spec.ConcatenateFragments(stdoutFragments) == out
    requires Spec.ConcatenateFragments(stderrFragments) == err
    requires hadError <==>
             exists i: nat :: i < |outcomes| && outcomes[i].failed
    ensures Spec.BatchMoveWitnessRelation(
              sources,
              directory,
              cmd,
              beforeFs,
              preCwd,
              afterFs,
              hadError,
              out,
              err,
              fsBounds,
              outcomes,
              stdoutFragments,
              stderrFragments
            )
  {
    hide Spec.MoveEffectRelation;
    forall i: nat {:trigger stdoutFragments[i]} | i < |sources|
      ensures
        var normalizedSource :=
          Spec.NormalizeSourceSpec(
            sources[i], cmd.stripTrailingSlashes
          );
        Spec.MoveEffectRelation(
          normalizedSource,
          Spec.TargetInDirectorySpec(directory, normalizedSource),
          cmd,
          fsBounds[i],
          preCwd,
          fsBounds[i + 1],
          outcomes[i]
        ) &&
        stdoutFragments[i] == outcomes[i].stdoutFragment &&
        stderrFragments[i] == outcomes[i].stderrFragment
    {
      var normalizedSource :=
        Spec.NormalizeSourceSpec(
          sources[i], cmd.stripTrailingSlashes
        );
      assert Spec.MoveEffectRelation(
          normalizedSource,
          Spec.TargetInDirectorySpec(directory, normalizedSource),
          cmd,
          fsBounds[i],
          preCwd,
          fsBounds[i + 1],
          outcomes[i]
        );
      assert stdoutFragments[i] == outcomes[i].stdoutFragment;
      assert stderrFragments[i] == outcomes[i].stderrFragment;
    }
    reveal Spec.BatchMoveWitnessRelation();
  }

  lemma {:vcs_split_on_every_assert} BatchEvidenceImpliesMoveRelation(
    sources: seq<string>,
    directory: string,
    cmd: Schema.MvCmd,
    beforeFs: BW.FileSystem,
    preCwd: BW.Path,
    afterFs: BW.FileSystem,
    hadError: bool,
    out: BW.Bytes,
    err: BW.Bytes,
    evidence: Core.BatchEvidence
  )
    requires Core.BatchEvidenceFor(
               sources, directory, cmd, beforeFs, preCwd, afterFs,
               hadError, out, err, evidence
             )
    ensures Spec.BatchMoveRelation(
              sources, directory, cmd, beforeFs, preCwd, afterFs,
              hadError, out, err
            )
    ensures Spec.BatchMoveWitnessRelation(
              sources, directory, cmd, beforeFs, preCwd, afterFs,
              hadError, out, err,
              evidence.fsBounds, evidence.outcomes,
              evidence.stdoutFragments, evidence.stderrFragments
            )
  {
    reveal Core.BatchEvidenceFor();
    assert |evidence.steps| == |sources|;
    assert |evidence.fsBounds| == |sources| + 1;
    assert |evidence.outcomes| == |sources|;
    assert |evidence.stdoutFragments| == |sources|;
    assert |evidence.stderrFragments| == |sources|;
    assert evidence.fsBounds[0] == beforeFs;
    assert evidence.fsBounds[|evidence.fsBounds| - 1] == afterFs;
    assert Spec.ConcatenateFragments(
        evidence.stdoutFragments
      ) == out;
    assert Spec.ConcatenateFragments(
        evidence.stderrFragments
      ) == err;
    assert hadError <==>
           exists i: nat ::
             i < |evidence.outcomes| &&
             evidence.outcomes[i].failed;
    hide Spec.MoveEffectRelation;
    forall i: nat | i < |sources|
      ensures
        var normalizedSpec :=
          Spec.NormalizeSourceSpec(
            sources[i], cmd.stripTrailingSlashes
          );
        Spec.MoveEffectRelation(
          normalizedSpec,
          Spec.TargetInDirectorySpec(
            directory, normalizedSpec
          ),
          cmd,
          evidence.fsBounds[i],
          preCwd,
          evidence.fsBounds[i + 1],
          evidence.outcomes[i]
        )
      ensures evidence.stdoutFragments[i] ==
              evidence.outcomes[i].stdoutFragment
      ensures evidence.stderrFragments[i] ==
              evidence.outcomes[i].stderrFragment
    {
      assert Core.BatchStepEvidenceFor(
          sources[i],
          directory,
          cmd,
          evidence.fsBounds[i],
          preCwd,
          evidence.fsBounds[i + 1],
          evidence.outcomes[i],
          evidence.stdoutFragments[i],
          evidence.stderrFragments[i],
          evidence.steps[i]
        );
      BatchStepEvidenceImpliesMoveEffect(
        sources[i],
        directory,
        cmd,
        evidence.fsBounds[i],
        preCwd,
        evidence.fsBounds[i + 1],
        evidence.outcomes[i],
        evidence.stdoutFragments[i],
        evidence.stderrFragments[i],
        evidence.steps[i]
      );
      var normalizedSource :=
        Spec.NormalizeSourceSpec(
          sources[i], cmd.stripTrailingSlashes
        );
      assert Spec.MoveEffectRelation(
          normalizedSource,
          Spec.TargetInDirectorySpec(directory, normalizedSource),
          cmd,
          evidence.fsBounds[i],
          preCwd,
          evidence.fsBounds[i + 1],
          evidence.outcomes[i]
        );
      assert evidence.stdoutFragments[i] ==
             evidence.outcomes[i].stdoutFragment;
      assert evidence.stderrFragments[i] ==
             evidence.outcomes[i].stderrFragment;
    }
    {
      hide *;
      BatchMoveComponentsImplyWitnessRelation(
      sources,
      directory,
      cmd,
      beforeFs,
      preCwd,
      afterFs,
      hadError,
      out,
      err,
      evidence.fsBounds,
      evidence.outcomes,
      evidence.stdoutFragments,
      evidence.stderrFragments
      );
    }
    reveal Spec.BatchMoveRelation();
    assert Spec.BatchMoveRelation(
        sources, directory, cmd, beforeFs, preCwd, afterFs,
        hadError, out, err
      );
  }

  lemma {:induction false} BatchStatusStepInterval(
    observations: Spec.NativeStatusInputs,
    batch: Core.BatchEvidence,
    i: nat
  )
    requires i < |batch.steps|
    requires Core.BatchStatusEvidenceFor(observations, batch)
    ensures Core.StatusCallsFor(
      observations, batch.firstStatus, batch.statusCalls)
    ensures i + 1 < |batch.statusBounds|
    ensures batch.firstStatus <= batch.statusBounds[i] <= batch.statusBounds[i + 1] <=
      batch.firstStatus + |batch.statusCalls|
    ensures batch.steps[i].inputs == observations
    ensures batch.steps[i].firstStatus == batch.statusBounds[i]
    ensures batch.statusBounds[i + 1] ==
      batch.steps[i].firstStatus + |batch.steps[i].statusCalls|
    ensures batch.statusCalls[
      batch.statusBounds[i] - batch.firstStatus ..
      batch.statusBounds[i + 1] - batch.firstStatus] == batch.steps[i].statusCalls
  {
    hide *;
    reveal Core.BatchStatusEvidenceFor();
  }

  lemma {:isolate_assertions} {:induction false} BatchStatusStepImpliesObserved(
    source: string,
    directory: string,
    cmd: Schema.MvCmd,
    preCwd: BW.Path,
    observations: Spec.NativeStatusInputs,
    batch: Core.BatchEvidence,
    i: nat
  )
    requires i < |batch.steps|
    requires i + 1 < |batch.fsBounds|
    requires i < |batch.outcomes|
    requires i < |batch.stdoutFragments|
    requires i < |batch.stderrFragments|
    requires Core.BatchStepEvidenceFor(
      source, directory, cmd, batch.fsBounds[i], preCwd,
      batch.fsBounds[i + 1], batch.outcomes[i],
      batch.stdoutFragments[i], batch.stderrFragments[i], batch.steps[i])
    requires Core.StepStatusEvidenceFor(
      Core.NormalizeSource(source, cmd.stripTrailingSlashes),
      Core.TargetInDirectory(
        directory, Core.NormalizeSource(source, cmd.stripTrailingSlashes)),
      cmd, batch.steps[i])
    requires Core.BatchStatusEvidenceFor(observations, batch)
    ensures Spec.ObservedStepRelation(
      Spec.NormalizeSourceSpec(source, cmd.stripTrailingSlashes),
      Spec.TargetInDirectorySpec(
        directory, Spec.NormalizeSourceSpec(source, cmd.stripTrailingSlashes)),
      cmd, batch.fsBounds[i], preCwd, batch.fsBounds[i + 1],
      batch.outcomes[i], observations,
      batch.statusBounds[i], batch.statusBounds[i + 1],
      batch.statusCalls[
        batch.statusBounds[i] - batch.firstStatus ..
        batch.statusBounds[i + 1] - batch.firstStatus])
  {
    hide *;
    hide Spec.ObservedStepRelation();
    hide Core.BatchStatusEvidenceFor();
    BatchStatusStepInterval(observations, batch, i);
    NormalizeSourceSpecEqualsCore(source, cmd.stripTrailingSlashes);
    var normalizedSource := Core.NormalizeSource(
      source, cmd.stripTrailingSlashes);
    TargetInDirectorySpecEqualsCore(directory, normalizedSource);
    reveal Core.BatchStepEvidenceFor();
    assert Core.StepEvidenceFor(
      normalizedSource, Core.TargetInDirectory(directory, normalizedSource),
      cmd, preCwd, batch.steps[i]);
    assert batch.steps[i].beforeFs == batch.fsBounds[i];
    assert batch.steps[i].afterFs == batch.fsBounds[i + 1];
    assert batch.steps[i].outcome == batch.outcomes[i];
    assert Spec.NormalizeSourceSpec(source, cmd.stripTrailingSlashes) == normalizedSource;
    assert Spec.TargetInDirectorySpec(directory, normalizedSource) ==
      Core.TargetInDirectory(directory, normalizedSource);
    var lo := batch.statusBounds[i] - batch.firstStatus;
    var hi := batch.statusBounds[i + 1] - batch.firstStatus;
    assert batch.statusCalls[lo..hi] == batch.steps[i].statusCalls;
    assert batch.steps[i].firstStatus == batch.statusBounds[i];
    assert batch.statusBounds[i + 1] ==
      batch.steps[i].firstStatus + |batch.steps[i].statusCalls|;
    assert Core.StatusCallsFor(
      observations, batch.steps[i].firstStatus,
      batch.steps[i].statusCalls) by {
      hide *;
      reveal Core.StepEvidenceFor();
    }
    StepStatusEvidenceImpliesObservedStep(
      normalizedSource, Core.TargetInDirectory(directory, normalizedSource),
      cmd, preCwd, batch.steps[i], observations);
    assert Spec.ObservedStepRelation(
      normalizedSource, Core.TargetInDirectory(directory, normalizedSource),
      cmd, batch.steps[i].beforeFs, preCwd, batch.steps[i].afterFs,
      batch.steps[i].outcome, observations, batch.steps[i].firstStatus,
      batch.steps[i].firstStatus + |batch.steps[i].statusCalls|,
      batch.steps[i].statusCalls);
    assert Spec.ObservedStepRelation(
      Spec.NormalizeSourceSpec(source, cmd.stripTrailingSlashes),
      Spec.TargetInDirectorySpec(directory, Spec.NormalizeSourceSpec(source, cmd.stripTrailingSlashes)),
      cmd, batch.fsBounds[i], preCwd, batch.fsBounds[i + 1], batch.outcomes[i],
      observations, batch.statusBounds[i], batch.statusBounds[i + 1], batch.statusCalls[lo..hi]);
  }

  lemma {:isolate_assertions} {:induction false} ObservedBatchComponentsImplyRelation(
    sources: seq<string>,
    directory: string,
    cmd: Schema.MvCmd,
    beforeFs: BW.FileSystem,
    preCwd: BW.Path,
    afterFs: BW.FileSystem,
    hadError: bool,
    out: BW.Bytes,
    err: BW.Bytes,
    observations: Spec.NativeStatusInputs,
    firstStatus: nat,
    afterStatus: nat,
    calls: seq<Spec.StatusCallEvidence>,
    fsBounds: seq<BW.FileSystem>,
    outcomes: seq<Spec.MoveOutcome>,
    stdoutFragments: seq<BW.Bytes>,
    stderrFragments: seq<BW.Bytes>,
    statusBounds: seq<nat>
  )
    requires afterStatus == firstStatus + |calls|
    requires Spec.StatusCallsFor(observations, firstStatus, calls)
    requires Spec.BatchMoveWitnessRelation(
      sources, directory, cmd, beforeFs, preCwd, afterFs,
      hadError, out, err, fsBounds, outcomes, stdoutFragments, stderrFragments)
    requires |fsBounds| == |sources| + 1
    requires |outcomes| == |sources|
    requires |statusBounds| == |sources| + 1
    requires statusBounds[0] == firstStatus
    requires statusBounds[|sources|] == afterStatus
    requires forall i: nat {:trigger statusBounds[i]} | i < |sources| ::
      firstStatus <= statusBounds[i] <= statusBounds[i + 1] <= afterStatus &&
      Spec.ObservedStepRelation(
        Spec.NormalizeSourceSpec(sources[i], cmd.stripTrailingSlashes),
        Spec.TargetInDirectorySpec(
          directory, Spec.NormalizeSourceSpec(sources[i], cmd.stripTrailingSlashes)),
        cmd, fsBounds[i], preCwd, fsBounds[i + 1], outcomes[i], observations,
        statusBounds[i], statusBounds[i + 1],
        calls[statusBounds[i] - firstStatus .. statusBounds[i + 1] - firstStatus])
    ensures Spec.ObservedBatchRelation(
      sources, directory, cmd, beforeFs, preCwd, afterFs,
      hadError, out, err, observations, firstStatus, afterStatus, calls)
  {
    hide Spec.ObservedStepRelation();
    hide Spec.BatchMoveWitnessRelation();
    hide Spec.StatusCallsFor();
    reveal Spec.ObservedBatchRelation();
  }

  lemma {:isolate_assertions} {:induction false} BatchStatusEvidenceImpliesObservedBatch(
    sources: seq<string>,
    directory: string,
    cmd: Schema.MvCmd,
    beforeFs: BW.FileSystem,
    preCwd: BW.Path,
    afterFs: BW.FileSystem,
    hadError: bool,
    out: BW.Bytes,
    err: BW.Bytes,
    observations: Spec.NativeStatusInputs,
    batch: Core.BatchEvidence
  )
    requires Core.BatchEvidenceFor(
      sources, directory, cmd, beforeFs, preCwd, afterFs,
      hadError, out, err, batch)
    requires Core.BatchMoveStatusEvidenceFor(
      sources, directory, cmd, observations, batch)
    ensures Spec.ObservedBatchRelation(
      sources, directory, cmd, beforeFs, preCwd, afterFs,
      hadError, out, err, observations,
      batch.firstStatus,
      batch.firstStatus + |batch.statusCalls|,
      batch.statusCalls)
  {
    hide *;
    reveal Core.StatusCallsFor();
    BatchEvidenceImpliesMoveRelation(
      sources, directory, cmd, beforeFs, preCwd, afterFs,
      hadError, out, err, batch
    );
    reveal Core.BatchMoveStatusEvidenceFor();
    reveal Core.BatchStatusEvidenceFor();
    reveal Core.BatchEvidenceFor();
    forall i: nat {:trigger batch.statusBounds[i]} | i < |sources|
      ensures batch.firstStatus <= batch.statusBounds[i] <=
        batch.statusBounds[i + 1] <= batch.firstStatus + |batch.statusCalls|
      ensures Spec.ObservedStepRelation(
        Spec.NormalizeSourceSpec(sources[i], cmd.stripTrailingSlashes),
        Spec.TargetInDirectorySpec(
          directory,
          Spec.NormalizeSourceSpec(sources[i], cmd.stripTrailingSlashes)
        ),
        cmd,
        batch.fsBounds[i], preCwd, batch.fsBounds[i + 1],
        batch.outcomes[i], observations,
        batch.statusBounds[i], batch.statusBounds[i + 1],
        batch.statusCalls[
          batch.statusBounds[i] - batch.firstStatus ..
          batch.statusBounds[i + 1] - batch.firstStatus]
      )
    {
      assert Core.BatchStepEvidenceFor(
        sources[i], directory, cmd, batch.fsBounds[i], preCwd,
        batch.fsBounds[i + 1], batch.outcomes[i],
        batch.stdoutFragments[i], batch.stderrFragments[i], batch.steps[i]);
      BatchStatusStepImpliesObserved(
        sources[i], directory, cmd, preCwd, observations, batch, i);
    }
    ObservedBatchComponentsImplyRelation(
      sources, directory, cmd, beforeFs, preCwd, afterFs,
      hadError, out, err, observations,
      batch.firstStatus, batch.firstStatus + |batch.statusCalls|,
      batch.statusCalls, batch.fsBounds, batch.outcomes,
      batch.stdoutFragments, batch.stderrFragments, batch.statusBounds);
  }

  lemma RunIntoDirectoryEvidenceImpliesCandidate(
    sources: seq<string>,
    directory: string,
    explicitTargetDirectory: bool,
    cmd: Schema.MvCmd,
    beforeFs: BW.FileSystem,
    preCwd: BW.Path,
    afterFs: BW.FileSystem,
    preStdout: BW.Bytes,
    preStderr: BW.Bytes,
    stdout2: BW.Bytes,
    stderr2: BW.Bytes,
    exit: int
  )
    requires Core.RunIntoDirectoryEvidenceFields(
               sources, directory, explicitTargetDirectory, cmd,
               beforeFs, preCwd, afterFs, preStdout, preStderr,
               stdout2, stderr2, exit
             )
    ensures Spec.CandidateRunIntoDirectoryFields(
              sources, directory, explicitTargetDirectory, cmd,
              beforeFs, preCwd, afterFs, preStdout, preStderr,
              stdout2, stderr2, exit
            )
  {
    forall ok: bool, directoryErr: int
      ensures Core.TargetDirectoryCheckSummaryFields(
                directory, beforeFs, ok, directoryErr
              )
              ==> Spec.TargetDirectoryCheckSpecFields(
                  directory, beforeFs, ok, directoryErr
                )
    {
      if Core.TargetDirectoryCheckSummaryFields(
          directory, beforeFs, ok, directoryErr
        ) {
        TargetDirectoryCheckSummaryFieldsImpliesSpec(
          directory, beforeFs, ok, directoryErr
        );
      }
    }
    forall
    hadError: bool,
      out: BW.Bytes,
      err: BW.Bytes,
      evidence: Core.BatchEvidence
      ensures Core.BatchEvidenceFor(
                sources, directory, cmd, beforeFs, preCwd, afterFs,
                hadError, out, err, evidence
              )
              ==> Spec.BatchMoveRelation(
                  sources, directory, cmd, beforeFs, preCwd, afterFs,
                  hadError, out, err
                )
    {
      if Core.BatchEvidenceFor(
          sources, directory, cmd, beforeFs, preCwd, afterFs,
          hadError, out, err, evidence
        ) {
        BatchEvidenceImpliesMoveRelation(
          sources, directory, cmd, beforeFs, preCwd, afterFs,
          hadError, out, err, evidence
        );
      }
    }
  }

  lemma RunTwoOperandEvidenceImpliesCandidate(
    cmd: Schema.MvCmd,
    beforeFs: BW.FileSystem,
    preCwd: BW.Path,
    afterFs: BW.FileSystem,
    preStdout: BW.Bytes,
    preStderr: BW.Bytes,
    stdout2: BW.Bytes,
    stderr2: BW.Bytes,
    exit: int
  )
    requires |cmd.operands| == 2
    requires Core.RunTwoOperandEvidenceFields(
               cmd, beforeFs, preCwd, afterFs, preStdout, preStderr,
               stdout2, stderr2, exit
             )
    ensures Spec.CandidateRunTwoOperandFields(
              cmd, beforeFs, preCwd, afterFs, preStdout, preStderr,
              stdout2, stderr2, exit
            )
  {
    var sourceCore :=
      Core.NormalizeSource(
        cmd.operands[0], cmd.stripTrailingSlashes
      );
    NormalizeSourceSpecEqualsCore(
      cmd.operands[0], cmd.stripTrailingSlashes
    );
    TargetInDirectorySpecEqualsCore(cmd.operands[1], sourceCore);
    forall step: Core.StepEvidence
      ensures Core.StepEvidenceFor(
                sourceCore, cmd.operands[1], cmd, preCwd, step
              )
              ==> Spec.MoveEffectRelation(
                  sourceCore,
                  cmd.operands[1],
                  cmd,
                  step.beforeFs,
                  preCwd,
                  step.afterFs,
                  step.outcome
                )
    {
      if Core.StepEvidenceFor(
          sourceCore, cmd.operands[1], cmd, preCwd, step
        ) {
        StepEvidenceImpliesMoveEffect(
          sourceCore, cmd.operands[1], cmd, preCwd, step
        );
      }
    }
    forall
    hadError: bool,
      out: BW.Bytes,
      err: BW.Bytes,
      evidence: Core.BatchEvidence
      ensures Core.BatchEvidenceFor(
                [cmd.operands[0]],
                cmd.operands[1],
                cmd,
                beforeFs,
                preCwd,
                afterFs,
                hadError,
                out,
                err,
                evidence
              )
              ==> Spec.BatchMoveRelation(
                  [cmd.operands[0]],
                  cmd.operands[1],
                  cmd,
                  beforeFs,
                  preCwd,
                  afterFs,
                  hadError,
                  out,
                  err
                )
    {
      if Core.BatchEvidenceFor(
          [cmd.operands[0]],
          cmd.operands[1],
          cmd,
          beforeFs,
          preCwd,
          afterFs,
          hadError,
          out,
          err,
          evidence
        ) {
        BatchEvidenceImpliesMoveRelation(
          [cmd.operands[0]],
          cmd.operands[1],
          cmd,
          beforeFs,
          preCwd,
          afterFs,
          hadError,
          out,
          err,
          evidence
        );
      }
    }
  }

  lemma TargetDirectoryCheckSummaryFieldsImpliesSpec(directory: string, preFs: BW.FileSystem, ok: bool, err: int)
    requires Core.TargetDirectoryCheckSummaryFields(directory, preFs, ok, err)
    ensures Spec.TargetDirectoryCheckSpecFields(directory, preFs, ok, err)
  {
    assert forall statOk: bool, isDir: bool, statErr: int ::
        Spec.TargetDirectoryErrSpec(statOk, isDir, statErr) == Core.TargetDirectoryErr(statOk, isDir, statErr);
  }

  lemma PreparedSummaryIOImpliesCandidateSpecFields(
    raw: Schema.MvCmdRaw,
    preFs: BW.FileSystem,
    preCwd: BW.Path,
    preStdout: BW.Bytes,
    preStderr: BW.Bytes,
    io: BenchIO.IO,
    exit: int,
    plannedStdout: BW.Bytes,
    plannedStderr: BW.Bytes
  )
    requires Core.PreparedSummaryIO(
               raw,
               preFs,
               preCwd,
               preStdout,
               preStderr,
               io,
               exit, plannedStdout, plannedStderr
             )
    ensures Spec.CandidateSpecFields(
              raw,
              preFs,
              preCwd,
              preStdout,
              preStderr,
              io.fs(), plannedStdout, plannedStderr,
              exit
            )
  {
    var cmd := Schema.Command(raw);
    if cmd.mode == Schema.ModeInvalidBackup {
    } else if cmd.mode == Schema.ModeInvalidUpdate {
    } else if cmd.mode == Schema.ModeHelp {
    } else if cmd.mode == Schema.ModeVersion {
    } else if cmd.targetDirectory != "" &&
              cmd.noTargetDirectory {
    } else if |cmd.operands| == 0 {
    } else if cmd.targetDirectory != "" {
      RunIntoDirectoryEvidenceImpliesCandidate(
        cmd.operands,
        cmd.targetDirectory,
        true,
        cmd,
        preFs,
        preCwd,
        io.fs(),
        preStdout,
        preStderr,
        plannedStdout,
        plannedStderr,
        exit
      );
    } else if |cmd.operands| == 1 {
    } else if cmd.noTargetDirectory && |cmd.operands| > 2 {
    } else if |cmd.operands| == 2 {
      RunTwoOperandEvidenceImpliesCandidate(
        cmd,
        preFs,
        preCwd,
        io.fs(),
        preStdout,
        preStderr,
        plannedStdout,
        plannedStderr,
        exit
      );
    } else {
      RunIntoDirectoryEvidenceImpliesCandidate(
        cmd.operands[..|cmd.operands| - 1],
        cmd.operands[|cmd.operands| - 1],
        false,
        cmd,
        preFs,
        preCwd,
        io.fs(),
        preStdout,
        preStderr,
        plannedStdout,
        plannedStderr,
        exit
      );
    }
  }

  lemma {:isolate_assertions} ObservedBatchIntervalSubstitution(
    sources: seq<string>,
    directory: string,
    cmd: Schema.MvCmd,
    beforeFs: BW.FileSystem,
    preCwd: BW.Path,
    afterFs: BW.FileSystem,
    hadError: bool,
    out: BW.Bytes,
    err: BW.Bytes,
    observations: Spec.NativeStatusInputs,
    batch: Core.BatchEvidence,
    firstStatus: nat,
    afterStatus: nat,
    calls: seq<Spec.StatusCallEvidence>
  )
    requires batch.firstStatus == firstStatus + 1
    requires afterStatus == batch.firstStatus + |batch.statusCalls|
    requires |calls| >= 1
    requires calls[1..] == batch.statusCalls
    requires Spec.ObservedBatchRelation(
      sources, directory, cmd, beforeFs, preCwd, afterFs,
      hadError, out, err, observations,
      batch.firstStatus,
      batch.firstStatus + |batch.statusCalls|,
      batch.statusCalls)
    ensures Spec.ObservedBatchRelation(
      sources, directory, cmd, beforeFs, preCwd, afterFs,
      hadError, out, err, observations,
      firstStatus + 1, afterStatus, calls[1..])
  {
    hide Spec.ObservedBatchRelation;
  }

  lemma {:isolate_assertions} DirectoryStatusEvidenceImpliesObservedDirectory(
    sources: seq<string>,
    directory: string,
    cmd: Schema.MvCmd,
    beforeFs: BW.FileSystem,
    preCwd: BW.Path,
    afterFs: BW.FileSystem,
    beforeStdout: BW.Bytes,
    afterStdout: BW.Bytes,
    beforeStderr: BW.Bytes,
    afterStderr: BW.Bytes,
    exit: int,
    observations: Spec.NativeStatusInputs,
    firstStatus: nat,
    afterStatus: nat,
    calls: seq<Spec.StatusCallEvidence>,
    evidence: Core.DirectoryStatusEvidence
  )
    requires afterStatus == firstStatus + |calls|
    requires Core.DirectoryStatusEvidenceFor(
      sources, directory, cmd, beforeFs, preCwd, afterFs,
      beforeStdout, afterStdout, beforeStderr, afterStderr,
      exit, observations, firstStatus, calls, evidence)
    ensures |calls| >= 1
    ensures Spec.StatusRequest(calls[0], beforeFs, directory, true)
    ensures if calls[0].ok &&
               calls[0].status.kind == BW.DirectoryKind then
      exists hadError: bool, out: BW.Bytes, err: BW.Bytes
        {:trigger Spec.ObservedBatchRelation(
          sources, directory, cmd, beforeFs, preCwd, afterFs,
          hadError, out, err, observations,
          firstStatus + 1, afterStatus, calls[1..])} ::
        Spec.ObservedBatchRelation(
          sources, directory, cmd, beforeFs, preCwd, afterFs,
          hadError, out, err, observations,
          firstStatus + 1, afterStatus, calls[1..]) &&
        exit == (if hadError then 1 else 0) &&
        afterStdout == beforeStdout + out &&
        afterStderr == beforeStderr + err
    else |calls| == 1
  {
    reveal Core.DirectoryStatusEvidenceFor();
    match evidence {
      case FailedDirectoryStatus(_) =>
      case SuccessfulDirectoryStatus(dirCall, batch) =>
        var hadError, out, err :|
          Core.BatchEvidenceFor(
            sources, directory, cmd, beforeFs, preCwd, afterFs,
            hadError, out, err, batch) &&
          exit == (if hadError then 1 else 0) &&
          afterStdout == beforeStdout + out &&
          afterStderr == beforeStderr + err;
        BatchStatusEvidenceImpliesObservedBatch(
          sources, directory, cmd, beforeFs, preCwd, afterFs,
          hadError, out, err, observations, batch);
        assert calls == [dirCall] + batch.statusCalls;
        assert calls[1..] == batch.statusCalls;
        assert batch.firstStatus == firstStatus + 1;
        assert afterStatus ==
               batch.firstStatus + |batch.statusCalls|;
        ObservedBatchIntervalSubstitution(
          sources, directory, cmd, beforeFs, preCwd, afterFs,
          hadError, out, err, observations, batch,
          firstStatus, afterStatus, calls);
    }
  }

  lemma {:isolate_assertions} RunStatusEvidenceImpliesObservedStatusSpec(
    raw: Schema.MvCmdRaw,
    beforeFs: BW.FileSystem,
    preCwd: BW.Path,
    afterFs: BW.FileSystem,
    beforeStdout: BW.Bytes,
    afterStdout: BW.Bytes,
    beforeStderr: BW.Bytes,
    afterStderr: BW.Bytes,
    exit: int,
    observations: Spec.NativeStatusInputs,
    firstStatus: nat,
    afterStatus: nat,
    calls: seq<Spec.StatusCallEvidence>,
    evidence: Core.RunStatusEvidence
  )
    requires Core.RunStatusEvidenceFor(
      raw, beforeFs, preCwd, afterFs,
      beforeStdout, afterStdout, beforeStderr, afterStderr,
      exit, observations, firstStatus, afterStatus, calls, evidence)
    ensures Spec.ObservedStatusSpec(
      raw, beforeFs, preCwd, afterFs,
      beforeStdout, afterStdout, beforeStderr, afterStderr,
      exit, observations, firstStatus, afterStatus, calls)
  {
    hide *;
    reveal Core.StatusCallsFor();
    reveal Spec.ObservedStatusSpec();
    var cmd := Schema.Command(raw);
    reveal Core.RunStatusEvidenceFor();
    if cmd.mode != Schema.ModeRun ||
       (cmd.targetDirectory != "" && cmd.noTargetDirectory) ||
       |cmd.operands| == 0 ||
       (cmd.targetDirectory == "" && |cmd.operands| == 1) ||
       (cmd.targetDirectory == "" && cmd.noTargetDirectory &&
        |cmd.operands| > 2) {
      return;
    }
    if cmd.targetDirectory != "" {
      match evidence {
        case DirectoryRunStatus(directoryEvidence) =>
          DirectoryStatusEvidenceImpliesObservedDirectory(
            cmd.operands, cmd.targetDirectory, cmd,
            beforeFs, preCwd, afterFs,
            beforeStdout, afterStdout, beforeStderr, afterStderr,
            exit, observations, firstStatus, afterStatus, calls,
            directoryEvidence);
        case _ =>
      }
    } else if |cmd.operands| == 2 {
      var source := Core.NormalizeSource(
        cmd.operands[0], cmd.stripTrailingSlashes
      );
      NormalizeSourceSpecEqualsCore(
        cmd.operands[0], cmd.stripTrailingSlashes
      );
      match evidence {
        case DirectMoveStatus(step) =>
          StepStatusEvidenceImpliesObservedStep(
            source, cmd.operands[1], cmd, preCwd, step, observations
          );
        case ProbedMoveStatus(call, step) =>
          var target :=
            if call.ok && call.status.kind == BW.DirectoryKind then
              Core.TargetInDirectory(cmd.operands[1], source)
            else cmd.operands[1];
          if call.ok && call.status.kind == BW.DirectoryKind {
            TargetInDirectorySpecEqualsCore(cmd.operands[1], source);
          }
          assert !cmd.noTargetDirectory;
          assert step.firstStatus == firstStatus + 1;
          assert |calls| == 1 + |step.statusCalls|;
          assert calls[1..] == step.statusCalls;
          assert Core.StatusCallsFor(observations, step.firstStatus, step.statusCalls) by {
            hide *;
            reveal Core.RunStatusEvidenceFor(), Core.StepEvidenceFor();
          }
          StepStatusEvidenceImpliesObservedStep(
            source, target, cmd, preCwd, step, observations
          );
        case _ =>
      }
    } else {
      match evidence {
        case DirectoryRunStatus(directoryEvidence) =>
          DirectoryStatusEvidenceImpliesObservedDirectory(
            cmd.operands[..|cmd.operands| - 1],
            cmd.operands[|cmd.operands| - 1], cmd,
            beforeFs, preCwd, afterFs,
            beforeStdout, afterStdout, beforeStderr, afterStderr,
            exit, observations, firstStatus, afterStatus, calls,
            directoryEvidence);
        case _ =>
      }
    }
  }

  twostate lemma CoreSummaryImpliesSpec(
    raw: Schema.MvCmdRaw, io: BenchIO.IO, exit: int,
    calls: seq<Spec.StatusCallEvidence>, evidence: Core.RunStatusEvidence,
    plan: Core.PlannedOutput
  )
    requires Core.CoreSummary(raw, io, exit, plan)
    requires Core.RunStatusEvidenceFor(raw, old(io.fs()), old(io.cwd()), io.fs(),
      [], plan.stdout, [], plan.stderr, plan.normalExit, Spec.NativeStatusInputs(io.statusObservations(), io.trustedNativeFailures(), io.now()),
      old(io.statusCursor()), io.statusCursor(), calls, evidence)
    ensures Spec.Spec(raw, io, exit)
  {
    reveal Core.PreparedSummary();
    hide Core.PreparedSummaryIO;
    hide Core.RunStatusEvidenceFor;
    hide Spec.CandidateSpecFields;
    hide Spec.ObservedStatusSpec;
    PreparedSummaryIOImpliesCandidateSpecFields(raw, old(io.fs()), old(io.cwd()),
      [], [], io, plan.normalExit, plan.stdout, plan.stderr);
    RunStatusEvidenceImpliesObservedStatusSpec(raw, old(io.fs()), old(io.cwd()), io.fs(),
      [], plan.stdout, [], plan.stderr, plan.normalExit, Spec.NativeStatusInputs(io.statusObservations(), io.trustedNativeFailures(), io.now()),
      old(io.statusCursor()), io.statusCursor(), calls, evidence);
    reveal Spec.Spec();
  }
}
