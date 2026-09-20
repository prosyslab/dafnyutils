include "../../core/World.dfy"
include "../../core/IOContract.dfy"
include "MvPathProof.dfy"
include "MvSchema.dfy"
include "MvCore.dfy"
include "MvSpec.dfy"

module MvProof {
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
  {
  }

  lemma DecimalNatSpecEqualsCore(n: nat)
    ensures Spec.DecimalNatSpec(n) == Core.DecimalNat(n)
    decreases n
  {
    if n < 10 {
      DigitCharSpecEqualsCore(n);
    } else {
      DecimalNatSpecEqualsCore(n / 10);
      DecimalNatSpecEqualsCore(n % 10);
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
                ) == BW.Ok(resolvedLeft) &&
                IOContract.ResolvePathForMetadataFields(
                  fs, rightPath, followRight
                ) == BW.Ok(resolvedRight) &&
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
                 ) == BW.Ok(resolvedLeft) &&
                 IOContract.ResolvePathForMetadataFields(
                   fs, rightPath, followRight
                 ) == BW.Ok(resolvedRight) &&
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

  lemma SameDirectoryEntryImpliesEvidenceNamesSame(
    fs: BW.FileSystem,
    leftPath: string,
    rightPath: string,
    left: Core.EntryNameEvidence,
    right: Core.EntryNameEvidence
  )
    requires Core.EntryNameEvidenceFor(fs, leftPath, left)
    requires Core.EntryNameEvidenceFor(fs, rightPath, right)
    requires Spec.SameDirectoryEntry(fs, leftPath, rightPath)
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
      ) == BW.Ok(resolvedLeftParent) &&
      IOContract.ResolvePathForMetadataFields(
        fs, rightParent, false
      ) == BW.Ok(resolvedRightParent) &&
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
    reveal IOContract.GetFileTimesContractFields();
    assert IOContract.ResolvePathForMetadataFields(
        fs, left.parent, false
      ) == BW.Ok(resolvedLeftParent);
    assert IOContract.ResolvePathForMetadataFields(
        fs, right.parent, false
      ) == BW.Ok(resolvedRightParent);
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
            ) == BW.Ok(publicResolvedSource) &&
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
    ensures Core.BackupCollisionDetected(collision) ==
            Spec.BackupWouldDestroySource(cmd, fs, source, target)
  {
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
    assert IOContract.PathExistsContractFields(
        fs, path, false, false, checks[|checks| - 1].err
      );
    assert forall j: nat | start <= j < index ::
        IOContract.PathExistsContractFields(
          fs,
          Spec.NumberedBackupPathSpec(target, j),
          false,
          true,
          0
        ) by {
      forall j: nat | start <= j < index
        ensures IOContract.PathExistsContractFields(
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
        assert IOContract.PathExistsContractFields(
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
               source, target, sourceIsDir, backupPath, verbose, debug,
               beforeFs, preCwd, afterFs, outcome, calls, backupFs
             )
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

  lemma {:isolate_assertions} StepEvidenceImpliesMoveEffect(
    source: string,
    target: string,
    cmd: Schema.MvCmd,
    preCwd: BW.Path,
    evidence: Core.StepEvidence
  )
    requires Core.StepEvidenceFor(
               source, target, cmd, preCwd, evidence
             )
    ensures Spec.MoveEffectRelation(
              source,
              target,
              cmd,
              evidence.beforeFs,
              preCwd,
              evidence.afterFs,
              evidence.outcome
            )
  {
    reveal Core.StepEvidenceFor();
    if !evidence.sourceOk {
      assert Spec.MoveEffectRelation(
          source,
          target,
          cmd,
          evidence.beforeFs,
          preCwd,
          evidence.afterFs,
          evidence.outcome
        );
    } else {
      assert Spec.SkipStdoutSpec(target, cmd.debug) ==
             Core.SkipStdout(target, cmd.debug);
      if !evidence.targetFound {
        RenameEvidenceImpliesRelation(
          source,
          target,
          evidence.sourceIsDir,
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
        assert Spec.MoveEffectRelation(
            source,
            target,
            cmd,
            evidence.beforeFs,
            preCwd,
            evidence.afterFs,
            evidence.outcome
          );
      } else if cmd.overwriteMode == Schema.OverwriteSkip {
        assert Spec.MoveEffectRelation(
            source,
            target,
            cmd,
            evidence.beforeFs,
            preCwd,
            evidence.afterFs,
            evidence.outcome
          );
      } else if cmd.updateMode == Schema.UpdateNone {
        assert Spec.MoveEffectRelation(
            source,
            target,
            cmd,
            evidence.beforeFs,
            preCwd,
            evidence.afterFs,
            evidence.outcome
          );
      } else if cmd.updateMode == Schema.UpdateNoneFail {
        assert Spec.MoveEffectRelation(
            source,
            target,
            cmd,
            evidence.beforeFs,
            preCwd,
            evidence.afterFs,
            evidence.outcome
          );
      } else {
        SameFileEvidenceImpliesPolicy(
          cmd,
          evidence.beforeFs,
          preCwd,
          source,
          target,
          evidence.sameFile
        );
        reveal Core.SameFileEvidenceFor();
        match evidence.sameFile {
          case NoSameFileCheck =>
          case CheckedSameFile(
            sourceMetadata,
            targetMetadata,
            _,
            _,
            _,
            _,
            _,
            decision
            ) =>
            if decision == Spec.ContinueMove &&
               cmd.updateMode == Schema.UpdateOlder
            {
              assert Spec.SourceNewerSpec(
                  sourceMetadata.times.mtimeSec,
                  sourceMetadata.times.mtimeNsec,
                  targetMetadata.times.mtimeSec,
                  targetMetadata.times.mtimeNsec
                ) == Core.SourceNewer(
                            sourceMetadata.times.mtimeSec,
                            sourceMetadata.times.mtimeNsec,
                            targetMetadata.times.mtimeSec,
                            targetMetadata.times.mtimeNsec
                          );
              if Core.SourceNewer(
                  sourceMetadata.times.mtimeSec,
                  sourceMetadata.times.mtimeNsec,
                  targetMetadata.times.mtimeSec,
                  targetMetadata.times.mtimeNsec
                ) {
                ExistingTargetRenameEvidenceImpliesRelation(
                  source, target, cmd, preCwd, evidence
                );
              }
              assert Spec.MoveEffectRelation(
                  source,
                  target,
                  cmd,
                  evidence.beforeFs,
                  preCwd,
                  evidence.afterFs,
                  evidence.outcome
                );
            } else if decision == Spec.ContinueMove {
              ExistingTargetRenameEvidenceImpliesRelation(
                source, target, cmd, preCwd, evidence
              );
              assert Spec.MoveEffectRelation(
                  source,
                  target,
                  cmd,
                  evidence.beforeFs,
                  preCwd,
                  evidence.afterFs,
                  evidence.outcome
                );
            } else {
              assert Spec.MoveEffectRelation(
                  source,
                  target,
                  cmd,
                  evidence.beforeFs,
                  preCwd,
                  evidence.afterFs,
                  evidence.outcome
                );
            }
        }
      }
    }
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
    reveal Spec.BatchMoveRelation();
    assert Spec.BatchMoveRelation(
        sources, directory, cmd, beforeFs, preCwd, afterFs,
        hadError, out, err
      );
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
    assert Spec.ENOTDIR == Core.ENOTDIR;
    assert forall statOk: bool, isDir: bool, statErr: int ::
        Spec.TargetDirectoryErrSpec(statOk, isDir, statErr) == Core.TargetDirectoryErr(statOk, isDir, statErr);
  }

  lemma CoreSummaryIOImpliesCandidateSpecFields(
    raw: Schema.MvCmdRaw,
    preFs: BW.FileSystem,
    preCwd: BW.Path,
    preStdout: BW.Bytes,
    preStderr: BW.Bytes,
    io: BenchIO.IO,
    exit: int
  )
    requires Core.CoreSummaryIO(
               raw,
               preFs,
               preCwd,
               preStdout,
               preStderr,
               io,
               exit
             )
    ensures Spec.CandidateSpecFields(
              raw,
              preFs,
              preCwd,
              preStdout,
              preStderr,
              io,
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
        io.stdout(),
        io.stderr(),
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
        io.stdout(),
        io.stderr(),
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
        io.stdout(),
        io.stderr(),
        exit
      );
    }
  }

  twostate lemma CoreSummaryImpliesSpec(raw: Schema.MvCmdRaw, io: BenchIO.IO, exit: int)
    requires Core.CoreSummary(raw, io, exit)
    ensures Spec.Spec(raw, io, exit)
  {
    CoreSummaryIOImpliesCandidateSpecFields(
      raw,
      old(io.fs()),
      old(io.cwd()),
      old(io.stdout()),
      old(io.stderr()),
      io,
      exit
    );
  }
}
