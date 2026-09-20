include "../../core/World.dfy"
include "../../core/IO.dfy"
include "MvPathCore.dfy"
include "MvSchema.dfy"
include "MvSpec.dfy"

module MvCore {
  import BenchIO
  import Utf8 = Utf8Semantics
  import IOContract
  import BenchWorld
  import BasenameCore = MvPathCore
  import DirnameCore = MvPathCore
  import Schema = MvSchema
  import Spec = MvSpec

  const ENOENT: int := 2
  const EBUSY: int := 16
  const EISDIR: int := 21
  const ENOTDIR: int := 20
  const EINVAL: int := 22

  ghost function ShowActionMessage(verbose: bool, debug: bool): bool
  {
    verbose || debug
  }

  ghost function SkipStdout(target: string, debug: bool): BenchWorld.Bytes
  {
    if debug then Spec.DebugSkipMessageSpec(target) else []
  }

  function SourceRenameDiagnosticErr(
    target: string,
    sourceIsDir: bool,
    renameErr: int
  ): int
  {
    if target == "" then
      if sourceIsDir then EBUSY else EISDIR
    else
      renameErr
  }

  function SourceLeafName(source: string): string
  {
    var leaf := BenchWorld.LeafName(source);
    if leaf == "" then source else leaf
  } by method {
    var leaf := BenchWorld.LeafName(source);
    return if leaf == "" then source else leaf;
  }

  lemma AllSlashesFalseAt(text: string, i: nat, j: nat)
    requires i <= j < |text|
    requires forall k :: i <= k < j ==> text[k] == '/'
    requires text[j] != '/'
    ensures !AllSlashes(text, i)
    decreases j - i
  {
    if i < j {
      AllSlashesFalseAt(text, i + 1, j);
    }
  }

  lemma AllSlashesTrueFrom(text: string, i: nat)
    requires i <= |text|
    requires forall k :: i <= k < |text| ==> text[k] == '/'
    ensures AllSlashes(text, i)
    decreases |text| - i
  {
    if i < |text| {
      AllSlashesTrueFrom(text, i + 1);
    }
  }

  function AllSlashes(text: string, i: nat): bool
    decreases |text| - i
  {
    if i >= |text| then
      true
    else if text[i] != '/' then
      false
    else
      AllSlashes(text, i + 1)
  } by method {
    if i >= |text| {
      return true;
    }
    var j := i;
    while j < |text|
      invariant i <= j <= |text|
      invariant forall k | i <= k < j :: text[k] == '/'
      decreases |text| - j
    {
      if text[j] != '/' {
        AllSlashesFalseAt(text, i, j);
        return false;
      }
      j := j + 1;
    }
    AllSlashesTrueFrom(text, i);
    return true;
  }

  lemma TrimTrailingSlashesLoop(text: string, end: nat, i: nat)
    requires i <= end <= |text|
    requires forall k :: i <= k < end ==> text[k] == '/'
    requires i == 0 || text[i - 1] != '/'
    ensures TrimTrailingSlashes(text, end) == text[..i]
    decreases end - i
  {
    if end == i {
    } else {
      TrimTrailingSlashesLoop(text, end - 1, i);
    }
  }

  function TrimTrailingSlashes(text: string, end: nat): string
    requires end <= |text|
    decreases end
  {
    if end == 0 then
      ""
    else if text[end - 1] == '/' then
      TrimTrailingSlashes(text, end - 1)
    else
      text[..end]
  } by method {
    var i: nat := end;
    while i > 0 && text[i - 1] == '/'
      invariant i <= end <= |text|
      invariant forall k | i <= k < end :: text[k] == '/'
      decreases i
    {
      i := i - 1;
    }
    TrimTrailingSlashesLoop(text, end, i);
    return text[..i];
  }

  function NormalizeSource(source: string, stripTrailingSlashes: bool): string
  {
    if !stripTrailingSlashes then
      source
    else if source == "" then
      source
    else if AllSlashes(source, 0) then
      "/"
    else
      TrimTrailingSlashes(source, |source|)
  } by method {
    if !stripTrailingSlashes {
      return source;
    }
    if source == "" {
      return source;
    }
    if AllSlashes(source, 0) {
      return "/";
    }
    return TrimTrailingSlashes(source, |source|);
  }

  function TargetInDirectory(directory: string, source: string): string
  {
    BenchWorld.AppendPath(directory, SourceLeafName(source))
  } by method {
    return BenchWorld.AppendPath(directory, SourceLeafName(source));
  }

  function DigitChar(d: nat): char
    requires d < 10
  {
    if d == 0 then '0'
    else if d == 1 then '1'
    else if d == 2 then '2'
    else if d == 3 then '3'
    else if d == 4 then '4'
    else if d == 5 then '5'
    else if d == 6 then '6'
    else if d == 7 then '7'
    else if d == 8 then '8'
    else '9'
  } by method {
    if d == 0 {
      return '0';
    }
    if d == 1 {
      return '1';
    }
    if d == 2 {
      return '2';
    }
    if d == 3 {
      return '3';
    }
    if d == 4 {
      return '4';
    }
    if d == 5 {
      return '5';
    }
    if d == 6 {
      return '6';
    }
    if d == 7 {
      return '7';
    }
    if d == 8 {
      return '8';
    }
    return '9';
  }

  function DecimalNat(n: nat): string
    decreases n
  {
    if n < 10 then
      [DigitChar(n)]
    else
      DecimalNat(n / 10) + [DigitChar(n % 10)]
  } by method {
    var remaining: nat := n;
    var suffix: string := [];
    while remaining >= 10
      invariant DecimalNat(n) == DecimalNat(remaining) + suffix
      decreases remaining
    {
      assert 0 <= remaining % 10;
      assert remaining % 10 < 10;
      suffix := [DigitChar(remaining % 10)] + suffix;
      assert 0 <= remaining / 10;
      remaining := remaining / 10;
    }
    assert remaining < 10;
    return [DigitChar(remaining)] + suffix;
  }

  function NumberedBackupPath(target: string, index: nat): string
    requires index >= 1
  {
    target + ".~" + DecimalNat(index) + "~"
  } by method {
    return target + ".~" + DecimalNat(index) + "~";
  }

  function SimpleBackupPath(target: string, suffix: string): string
  {
    target + suffix
  } by method {
    return target + suffix;
  }

  function SourceNewer(
    srcSec: int, srcNsec: int, dstSec: int, dstNsec: int
  ): bool
  {
    srcSec > dstSec || (srcSec == dstSec && srcNsec > dstNsec)
  } by method {
    return srcSec > dstSec || (srcSec == dstSec && srcNsec > dstNsec);
  }

  ghost function TargetDirectoryErr(statOk: bool, isDir: bool, statErr: int): int
  {
    if statOk then
      if !isDir then ENOTDIR else statErr
    else
      statErr
  }

  ghost function StepSuccessStdout(source: string, target: string, backupPath: string, verbose: bool, debug: bool): BenchWorld.Bytes
  {
    if !ShowActionMessage(verbose, debug) then
      []
    else if backupPath == "" then
      Spec.VerboseRenameMessageSpec(source, target)
    else
      Spec.VerboseRenameWithBackupMessageSpec(source, target, backupPath)
  }

  datatype BackupCheckEvidence = BackupCheckEvidence(
    candidate: string,
    found: bool,
    err: int
  )

  datatype MetadataEvidence = MetadataEvidence(
    ok: bool,
    key: BenchWorld.HostInodeKey,
    links: BenchWorld.LinkCountObservation,
    isDir: bool,
    isSymlink: bool,
    times: BenchWorld.FileTimes,
    err: int
  )

  datatype EntryNameEvidence = EntryNameEvidence(
    parent: string,
    leaf: string,
    parentMetadata: MetadataEvidence
  )

  datatype OptionalMetadataEvidence =
    | NoMetadataEvidence
    | SomeMetadataEvidence(value: MetadataEvidence)

  datatype OptionalEntryNameEvidence =
    | NoEntryNameEvidence
    | FailedEntryNameEvidence(err: int)
    | SomeEntryNameEvidence(
        resolvedPath: string,
        value: EntryNameEvidence
      )

  datatype BackupCollisionEvidence =
    | NoBackupCollisionCheck
    | CheckedBackupCollision(
        sourceNoFollow: MetadataEvidence,
        simpleCandidateFollowed: MetadataEvidence
      )

  datatype SameFileEvidence =
    | NoSameFileCheck
    | CheckedSameFile(
        source: MetadataEvidence,
        target: MetadataEvidence,
        sourceFollowed: OptionalMetadataEvidence,
        sourceEntry: EntryNameEvidence,
        targetEntry: EntryNameEvidence,
        sourceReferentEntry: OptionalEntryNameEvidence,
        backupCollision: BackupCollisionEvidence,
        decision: Spec.SameFileDecision
      )

  datatype BackupSelectionEvidence =
    | NoBackupSelection
    | SelectedBackup(
        backupPath: string,
        checks: seq<BackupCheckEvidence>,
        existingFirstCheckCalled: bool,
        existingFirstFound: bool,
        existingFirstErr: int
      )

  datatype RenameCallEvidence = RenameCallEvidence(
    ok: bool,
    err: int,
    afterFs: BenchWorld.FileSystem
  )

  datatype StepEvidence = StepEvidence(
    beforeFs: BenchWorld.FileSystem,
    afterFs: BenchWorld.FileSystem,
    outcome: Spec.MoveOutcome,
    sourceOk: bool,
    sourceIsDir: bool,
    sourceErr: int,
    targetExistsCalled: bool,
    targetFound: bool,
    targetExistsErr: int,
    sameFile: SameFileEvidence,
    backup: BackupSelectionEvidence,
    renames: seq<RenameCallEvidence>,
    backupFs: BenchWorld.FileSystem
  )

  datatype BatchEvidence = BatchEvidence(
    steps: seq<StepEvidence>,
    fsBounds: seq<BenchWorld.FileSystem>,
    outcomes: seq<Spec.MoveOutcome>,
    stdoutFragments: seq<BenchWorld.Bytes>,
    stderrFragments: seq<BenchWorld.Bytes>
  )

  ghost function MakeStepEvidence(
    beforeFs: BenchWorld.FileSystem,
    afterFs: BenchWorld.FileSystem,
    out: BenchWorld.Bytes,
    err: BenchWorld.Bytes,
    failed: bool,
    sourceOk: bool,
    sourceIsDir: bool,
    sourceErr: int,
    targetExistsCalled: bool,
    targetFound: bool,
    targetExistsErr: int,
    sameFile: SameFileEvidence,
    backup: BackupSelectionEvidence,
    renames: seq<RenameCallEvidence>,
    backupFs: BenchWorld.FileSystem
  ): StepEvidence
  {
    StepEvidence(
      beforeFs,
      afterFs,
      Spec.MoveOutcome(out, err, failed),
      sourceOk,
      sourceIsDir,
      sourceErr,
      targetExistsCalled,
      targetFound,
      targetExistsErr,
      sameFile,
      backup,
      renames,
      backupFs
    )
  }

  ghost function MetadataLinkCountValue(
    evidence: MetadataEvidence
  ): int
  {
    match evidence.links
    case LinkCountKnown(count) => count
    case LinkCountUnknown => 0
  }

  ghost predicate MetadataEvidenceFor(
    fs: BenchWorld.FileSystem,
    path: string,
    followSymlink: bool,
    evidence: MetadataEvidence
  )
  {
    IOContract.GetFileTimesContractFields(
      fs,
      path,
      followSymlink,
      evidence.ok,
      evidence.times.atimeSec,
      evidence.times.atimeNsec,
      evidence.times.mtimeSec,
      evidence.times.mtimeNsec,
      evidence.isDir,
      evidence.isSymlink,
      evidence.key.device,
      evidence.key.inode,
      MetadataLinkCountValue(evidence),
      evidence.err
    )
  }

  ghost predicate EntryNameEvidenceFor(
    fs: BenchWorld.FileSystem,
    path: string,
    evidence: EntryNameEvidence
  )
  {
    BasenameCore.BasenameValueSummary(path, evidence.leaf) &&
    DirnameCore.DirnameValueSummary(path, evidence.parent) &&
    MetadataEvidenceFor(
      fs, evidence.parent, false, evidence.parentMetadata
    )
  }

  ghost predicate EvidenceNamesSame(
    left: EntryNameEvidence,
    right: EntryNameEvidence
  )
  {
    left.parentMetadata.ok &&
    right.parentMetadata.ok &&
    left.parentMetadata.key == right.parentMetadata.key &&
    left.leaf == right.leaf
  }

  ghost predicate ReferentEvidenceNamesTarget(
    referent: OptionalEntryNameEvidence,
    target: EntryNameEvidence
  )
  {
    match referent
    case SomeEntryNameEvidence(_, value) =>
      EvidenceNamesSame(value, target)
    case _ => false
  }

  opaque ghost predicate SameFileEvidenceFor(
    cmd: Schema.MvCmd,
    fs: BenchWorld.FileSystem,
    preCwd: BenchWorld.Path,
    source: string,
    target: string,
    evidence: SameFileEvidence
  )
  {
    match evidence
    case NoSameFileCheck => false
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
      MetadataEvidenceFor(fs, source, false, sourceMetadata) &&
      MetadataEvidenceFor(fs, target, false, targetMetadata) &&
      sourceMetadata.ok &&
      targetMetadata.ok &&
      EntryNameEvidenceFor(fs, source, sourceEntry) &&
      EntryNameEvidenceFor(fs, target, targetEntry) &&
      (if sourceMetadata.isSymlink then
         (match sourceFollowed
          case SomeMetadataEvidence(value) =>
            MetadataEvidenceFor(fs, source, true, value)
          case NoMetadataEvidence => false) &&
         (match sourceReferentEntry
          case NoEntryNameEvidence => false
          case FailedEntryNameEvidence(resolveErr) =>
            IOContract.ResolvePathIdentityContractFields(
              fs, preCwd, source, false, "", resolveErr
            )
          case SomeEntryNameEvidence(resolvedPath, value) =>
            IOContract.ResolvePathIdentityContractFields(
              fs, preCwd, source, true, resolvedPath, 0
            ) &&
            EntryNameEvidenceFor(fs, resolvedPath, value))
       else
         sourceFollowed == NoMetadataEvidence &&
         sourceReferentEntry == NoEntryNameEvidence) &&
      decision ==
      if EvidenceNamesSame(sourceEntry, targetEntry) ||
         (cmd.backupMode == Schema.BackupOff &&
          ((sourceMetadata.ok &&
            targetMetadata.ok &&
            sourceMetadata.key == targetMetadata.key) ||
           ReferentEvidenceNamesTarget(
             sourceReferentEntry, targetEntry
           )))
      then Spec.RejectSameFile
      else Spec.ContinueMove
  }

  lemma PackageSameFileEvidence(
    cmd: Schema.MvCmd,
    fs: BenchWorld.FileSystem,
    preCwd: BenchWorld.Path,
    source: string,
    target: string,
    sourceMetadata: MetadataEvidence,
    targetMetadata: MetadataEvidence,
    sourceFollowed: OptionalMetadataEvidence,
    sourceEntry: EntryNameEvidence,
    targetEntry: EntryNameEvidence,
    sourceReferentEntry: OptionalEntryNameEvidence,
    collision: BackupCollisionEvidence,
    decision: Spec.SameFileDecision
  )
    requires MetadataEvidenceFor(
               fs, source, false, sourceMetadata
             )
    requires MetadataEvidenceFor(
               fs, target, false, targetMetadata
             )
    requires sourceMetadata.ok && targetMetadata.ok
    requires EntryNameEvidenceFor(fs, source, sourceEntry)
    requires EntryNameEvidenceFor(fs, target, targetEntry)
    requires if sourceMetadata.isSymlink then
               (match sourceFollowed
                case SomeMetadataEvidence(value) =>
                  MetadataEvidenceFor(fs, source, true, value)
                case NoMetadataEvidence => false) &&
               (match sourceReferentEntry
                case NoEntryNameEvidence => false
                case FailedEntryNameEvidence(resolveErr) =>
                  IOContract.ResolvePathIdentityContractFields(
                    fs, preCwd, source, false, "", resolveErr
                  )
                case SomeEntryNameEvidence(resolvedPath, value) =>
                  IOContract.ResolvePathIdentityContractFields(
                    fs, preCwd, source, true, resolvedPath, 0
                  ) &&
                  EntryNameEvidenceFor(fs, resolvedPath, value))
             else
               sourceFollowed == NoMetadataEvidence &&
               sourceReferentEntry == NoEntryNameEvidence
    requires decision ==
             if EvidenceNamesSame(sourceEntry, targetEntry) ||
                (cmd.backupMode == Schema.BackupOff &&
                 ((sourceMetadata.ok &&
                   targetMetadata.ok &&
                   sourceMetadata.key == targetMetadata.key) ||
                  ReferentEvidenceNamesTarget(
                    sourceReferentEntry, targetEntry
                  )))
             then Spec.RejectSameFile
             else Spec.ContinueMove
    ensures SameFileEvidenceFor(
              cmd,
              fs,
              preCwd,
              source,
              target,
              CheckedSameFile(
                sourceMetadata,
                targetMetadata,
                sourceFollowed,
                sourceEntry,
                targetEntry,
                sourceReferentEntry,
                collision,
                decision
              )
            )
  {
    reveal SameFileEvidenceFor();
  }

  ghost predicate BackupCollisionEvidenceFor(
    cmd: Schema.MvCmd,
    fs: BenchWorld.FileSystem,
    source: string,
    target: string,
    sourceMetadata: MetadataEvidence,
    sourceEntry: EntryNameEvidence,
    targetEntry: EntryNameEvidence,
    evidence: BackupCollisionEvidence
  )
  {
    var needsCheck :=
      (cmd.backupMode == Schema.BackupSimple ||
       cmd.backupMode == Schema.BackupExisting) &&
      sourceEntry.leaf == targetEntry.leaf + cmd.backupSuffix;
    if !needsCheck then
      evidence == NoBackupCollisionCheck
    else
      match evidence
      case NoBackupCollisionCheck => false
      case CheckedBackupCollision(sourceNoFollow, candidateFollowed) =>
        sourceNoFollow == sourceMetadata &&
        MetadataEvidenceFor(
          fs,
          SimpleBackupPath(target, cmd.backupSuffix),
          true,
          candidateFollowed
        )
  }

  ghost predicate BackupCollisionDetected(
    evidence: BackupCollisionEvidence
  )
  {
    match evidence
    case NoBackupCollisionCheck => false
    case CheckedBackupCollision(source, candidate) =>
      source.ok && candidate.ok && source.key == candidate.key
  }

  ghost predicate BackupChecksFor(
    target: string,
    start: nat,
    fs: BenchWorld.FileSystem,
    checks: seq<BackupCheckEvidence>
  )
  {
    start >= 1 &&
    |checks| > 0 &&
    (forall i: nat | i < |checks| ::
       checks[i].candidate == NumberedBackupPath(target, start + i) &&
       IOContract.PathExistsContractFields(
         fs,
         checks[i].candidate,
         false,
         checks[i].found,
         checks[i].err
       )) &&
    (forall i: nat | i + 1 < |checks| :: checks[i].found) &&
    !checks[|checks| - 1].found
  }

  ghost predicate BackupSelectionEvidenceFor(
    target: string,
    backupMode: Schema.BackupMode,
    suffix: string,
    fs: BenchWorld.FileSystem,
    evidence: BackupSelectionEvidence
  )
  {
    match evidence
    case NoBackupSelection =>
      backupMode == Schema.BackupOff
    case SelectedBackup(
      backupPath,
      checks,
      existingFirstCheckCalled,
      existingFirstFound,
      existingFirstErr
      ) =>
      if backupMode == Schema.BackupSimple then
        backupPath == SimpleBackupPath(target, suffix) &&
        |checks| == 0 &&
        !existingFirstCheckCalled
      else if backupMode == Schema.BackupExisting then
        existingFirstCheckCalled &&
        IOContract.PathExistsContractFields(
          fs,
          NumberedBackupPath(target, 1),
          false,
          existingFirstFound,
          existingFirstErr
        ) &&
        if existingFirstFound then
          BackupChecksFor(target, 1, fs, checks) &&
          backupPath == checks[|checks| - 1].candidate
        else
          |checks| == 0 &&
          backupPath == SimpleBackupPath(target, suffix)
      else
        backupMode == Schema.BackupNumbered &&
        !existingFirstCheckCalled &&
        BackupChecksFor(target, 1, fs, checks) &&
        backupPath == checks[|checks| - 1].candidate
  }

  ghost predicate RenameEvidenceFor(
    source: string,
    target: string,
    sourceIsDir: bool,
    backupPath: string,
    verbose: bool,
    debug: bool,
    beforeFs: BenchWorld.FileSystem,
    preCwd: BenchWorld.Path,
    afterFs: BenchWorld.FileSystem,
    outcome: Spec.MoveOutcome,
    calls: seq<RenameCallEvidence>,
    backupFs: BenchWorld.FileSystem
  )
  {
    (exists sourceStatErr: int ::
       IOContract.IsDirectoryStrictContractFields(
         beforeFs,
         source,
         false,
         true,
         sourceIsDir,
         sourceStatErr
       )) &&
    |calls| <= 2 &&
    if backupPath == "" then
      |calls| == 1 &&
      IOContract.RenamePathContractFields(
        beforeFs,
        source,
        target,
        calls[0].ok,
        calls[0].err,
        calls[0].afterFs
      ) &&
      afterFs == calls[0].afterFs &&
      if calls[0].ok then
        outcome == Spec.MoveOutcome(
          StepSuccessStdout(source, target, "", verbose, debug), [], false
        )
      else
        outcome == Spec.MoveOutcome(
          [],
          Spec.SourceRenameFailureMessageSpec(
            source,
            target,
            SourceRenameDiagnosticErr(
              target, sourceIsDir, calls[0].err
            )
          ),
          true
        )
    else
      |calls| >= 1 &&
      IOContract.RenamePathContractFields(
        beforeFs,
        target,
        backupPath,
        calls[0].ok,
        calls[0].err,
        calls[0].afterFs
      ) &&
      if !calls[0].ok then
        |calls| == 1 &&
        afterFs == calls[0].afterFs &&
        outcome == Spec.MoveOutcome(
          [],
          Spec.RenameFailureMessageSpec(source, target, calls[0].err),
          true
        )
      else
        |calls| == 2 &&
        backupFs == calls[0].afterFs &&
        IOContract.RenamePathContractFields(
          backupFs,
          source,
          target,
          calls[1].ok,
          calls[1].err,
          calls[1].afterFs
        ) &&
        afterFs == calls[1].afterFs &&
        if calls[1].ok then
          outcome == Spec.MoveOutcome(
            StepSuccessStdout(
              source, target, backupPath, verbose, debug
            ),
            [],
            false
          )
        else
          outcome == Spec.MoveOutcome(
            [],
            Spec.SourceRenameFailureMessageSpec(
              source,
              target,
              SourceRenameDiagnosticErr(
                target, sourceIsDir, calls[1].err
              )
            ),
            true
          )
  }

  ghost predicate ExistingTargetRenameEvidenceFor(
    source: string,
    target: string,
    cmd: Schema.MvCmd,
    preCwd: BenchWorld.Path,
    evidence: StepEvidence
  )
  {
    SameFileEvidenceFor(
      cmd,
      evidence.beforeFs,
      preCwd,
      source,
      target,
      evidence.sameFile
    ) &&
    match evidence.sameFile
    case NoSameFileCheck => false
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
      BackupCollisionEvidenceFor(
        cmd,
        evidence.beforeFs,
        source,
        target,
        sourceMetadata,
        sourceEntry,
        targetEntry,
        collision
      ) &&
      if BackupCollisionDetected(collision) then
        evidence.backup == NoBackupSelection &&
        |evidence.renames| == 0 &&
        evidence.afterFs == evidence.beforeFs &&
        evidence.outcome == Spec.MoveOutcome(
          [],
          Spec.BackupWouldDestroySourceMessageSpec(source, target),
          true
        )
      else if cmd.backupMode == Schema.BackupOff then
        evidence.backup == NoBackupSelection &&
        RenameEvidenceFor(
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
        )
      else
        BackupSelectionEvidenceFor(
          target,
          cmd.backupMode,
          cmd.backupSuffix,
          evidence.beforeFs,
          evidence.backup
        ) &&
        RenameEvidenceFor(
          source,
          target,
          evidence.sourceIsDir,
          evidence.backup.backupPath,
          cmd.verbose,
          cmd.debug,
          evidence.beforeFs,
          preCwd,
          evidence.afterFs,
          evidence.outcome,
          evidence.renames,
          evidence.backupFs
        )
  }

  opaque ghost predicate StepEvidenceFor(
    source: string,
    target: string,
    cmd: Schema.MvCmd,
    preCwd: BenchWorld.Path,
    evidence: StepEvidence
  )
  {
    IOContract.IsDirectoryStrictContractFields(
      evidence.beforeFs,
      source,
      false,
      evidence.sourceOk,
      evidence.sourceIsDir,
      evidence.sourceErr
    ) &&
    |evidence.renames| <= 2 &&
    if !evidence.sourceOk then
      !evidence.targetExistsCalled &&
      evidence.sameFile == NoSameFileCheck &&
      evidence.backup == NoBackupSelection &&
      |evidence.renames| == 0 &&
      evidence.afterFs == evidence.beforeFs &&
      evidence.outcome == Spec.MoveOutcome(
        [],
        Spec.SourceStatFailureMessageSpec(source, evidence.sourceErr),
        true
      )
    else
      evidence.targetExistsCalled &&
      IOContract.PathExistsContractFields(
        evidence.beforeFs,
        target,
        false,
        evidence.targetFound,
        evidence.targetExistsErr
      ) &&
      (if !evidence.targetFound then
         evidence.sameFile == NoSameFileCheck &&
         evidence.backup == NoBackupSelection &&
         RenameEvidenceFor(
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
         )
       else if cmd.overwriteMode == Schema.OverwriteSkip then
         evidence.sameFile == NoSameFileCheck &&
         evidence.backup == NoBackupSelection &&
         |evidence.renames| == 0 &&
         evidence.afterFs == evidence.beforeFs &&
         evidence.outcome ==
         Spec.MoveOutcome(SkipStdout(target, cmd.debug), [], false)
       else if cmd.updateMode == Schema.UpdateNone then
         evidence.sameFile == NoSameFileCheck &&
         evidence.backup == NoBackupSelection &&
         |evidence.renames| == 0 &&
         evidence.afterFs == evidence.beforeFs &&
         evidence.outcome ==
         Spec.MoveOutcome(SkipStdout(target, cmd.debug), [], false)
       else if cmd.updateMode == Schema.UpdateNoneFail then
         evidence.sameFile == NoSameFileCheck &&
         evidence.backup == NoBackupSelection &&
         |evidence.renames| == 0 &&
         evidence.afterFs == evidence.beforeFs &&
         evidence.outcome ==
         Spec.MoveOutcome([], Spec.NotReplacingMessageSpec(target), true)
       else
         SameFileEvidenceFor(
           cmd,
           evidence.beforeFs,
           preCwd,
           source,
           target,
           evidence.sameFile
         ) &&
         match evidence.sameFile
         case NoSameFileCheck => false
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
           if decision == Spec.RejectSameFile then
             evidence.backup == NoBackupSelection &&
             |evidence.renames| == 0 &&
             evidence.afterFs == evidence.beforeFs &&
             evidence.outcome == Spec.MoveOutcome(
               [], Spec.SameFileMessageSpec(source, target), true
             )
           else if cmd.updateMode == Schema.UpdateOlder then
             if !SourceNewer(
                  sourceMetadata.times.mtimeSec,
                  sourceMetadata.times.mtimeNsec,
                  targetMetadata.times.mtimeSec,
                  targetMetadata.times.mtimeNsec
                ) then
               evidence.backup == NoBackupSelection &&
               |evidence.renames| == 0 &&
               evidence.afterFs == evidence.beforeFs &&
               evidence.outcome ==
               Spec.MoveOutcome(SkipStdout(target, cmd.debug), [], false)
             else
               ExistingTargetRenameEvidenceFor(
                 source, target, cmd, preCwd, evidence
               )
           else
             ExistingTargetRenameEvidenceFor(
               source, target, cmd, preCwd, evidence
             ))
  }

  lemma PackageSourceFailureStep(
    source: string,
    target: string,
    cmd: Schema.MvCmd,
    preCwd: BenchWorld.Path,
    evidence: StepEvidence
  )
    requires IOContract.IsDirectoryStrictContractFields(
               evidence.beforeFs,
               source,
               false,
               evidence.sourceOk,
               evidence.sourceIsDir,
               evidence.sourceErr
             )
    requires !evidence.sourceOk
    requires !evidence.targetExistsCalled
    requires evidence.sameFile == NoSameFileCheck
    requires evidence.backup == NoBackupSelection
    requires |evidence.renames| == 0
    requires evidence.afterFs == evidence.beforeFs
    requires evidence.outcome == Spec.MoveOutcome(
                                   [],
                                   Spec.SourceStatFailureMessageSpec(source, evidence.sourceErr),
                                   true
                                 )
    ensures StepEvidenceFor(source, target, cmd, preCwd, evidence)
  {
    reveal StepEvidenceFor();
  }

  lemma PackageMissingTargetStep(
    source: string,
    target: string,
    cmd: Schema.MvCmd,
    preCwd: BenchWorld.Path,
    evidence: StepEvidence
  )
    requires IOContract.IsDirectoryStrictContractFields(
               evidence.beforeFs,
               source,
               false,
               evidence.sourceOk,
               evidence.sourceIsDir,
               evidence.sourceErr
             )
    requires evidence.sourceOk
    requires evidence.targetExistsCalled
    requires IOContract.PathExistsContractFields(
               evidence.beforeFs,
               target,
               false,
               evidence.targetFound,
               evidence.targetExistsErr
             )
    requires !evidence.targetFound
    requires evidence.sameFile == NoSameFileCheck
    requires evidence.backup == NoBackupSelection
    requires RenameEvidenceFor(
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
             )
    ensures StepEvidenceFor(source, target, cmd, preCwd, evidence)
  {
    reveal StepEvidenceFor();
  }

  lemma PackageOverwriteSkipStep(
    source: string,
    target: string,
    cmd: Schema.MvCmd,
    preCwd: BenchWorld.Path,
    evidence: StepEvidence
  )
    requires IOContract.IsDirectoryStrictContractFields(
               evidence.beforeFs,
               source,
               false,
               evidence.sourceOk,
               evidence.sourceIsDir,
               evidence.sourceErr
             )
    requires evidence.sourceOk
    requires evidence.targetExistsCalled && evidence.targetFound
    requires IOContract.PathExistsContractFields(
               evidence.beforeFs,
               target,
               false,
               true,
               evidence.targetExistsErr
             )
    requires cmd.overwriteMode == Schema.OverwriteSkip
    requires evidence.sameFile == NoSameFileCheck
    requires evidence.backup == NoBackupSelection
    requires |evidence.renames| == 0
    requires evidence.afterFs == evidence.beforeFs
    requires evidence.outcome ==
             Spec.MoveOutcome(SkipStdout(target, cmd.debug), [], false)
    ensures StepEvidenceFor(source, target, cmd, preCwd, evidence)
  {
    reveal StepEvidenceFor();
  }

  lemma PackageUpdateNoneStep(
    source: string,
    target: string,
    cmd: Schema.MvCmd,
    preCwd: BenchWorld.Path,
    evidence: StepEvidence
  )
    requires IOContract.IsDirectoryStrictContractFields(
               evidence.beforeFs,
               source,
               false,
               evidence.sourceOk,
               evidence.sourceIsDir,
               evidence.sourceErr
             )
    requires evidence.sourceOk
    requires evidence.targetExistsCalled && evidence.targetFound
    requires IOContract.PathExistsContractFields(
               evidence.beforeFs,
               target,
               false,
               true,
               evidence.targetExistsErr
             )
    requires cmd.overwriteMode != Schema.OverwriteSkip
    requires cmd.updateMode == Schema.UpdateNone
    requires evidence.sameFile == NoSameFileCheck
    requires evidence.backup == NoBackupSelection
    requires |evidence.renames| == 0
    requires evidence.afterFs == evidence.beforeFs
    requires evidence.outcome ==
             Spec.MoveOutcome(SkipStdout(target, cmd.debug), [], false)
    ensures StepEvidenceFor(source, target, cmd, preCwd, evidence)
  {
    reveal StepEvidenceFor();
  }

  lemma PackageUpdateNoneFailStep(
    source: string,
    target: string,
    cmd: Schema.MvCmd,
    preCwd: BenchWorld.Path,
    evidence: StepEvidence
  )
    requires IOContract.IsDirectoryStrictContractFields(
               evidence.beforeFs,
               source,
               false,
               evidence.sourceOk,
               evidence.sourceIsDir,
               evidence.sourceErr
             )
    requires evidence.sourceOk
    requires evidence.targetExistsCalled && evidence.targetFound
    requires IOContract.PathExistsContractFields(
               evidence.beforeFs,
               target,
               false,
               true,
               evidence.targetExistsErr
             )
    requires cmd.overwriteMode != Schema.OverwriteSkip
    requires cmd.updateMode == Schema.UpdateNoneFail
    requires evidence.sameFile == NoSameFileCheck
    requires evidence.backup == NoBackupSelection
    requires |evidence.renames| == 0
    requires evidence.afterFs == evidence.beforeFs
    requires evidence.outcome ==
             Spec.MoveOutcome([], Spec.NotReplacingMessageSpec(target), true)
    ensures StepEvidenceFor(source, target, cmd, preCwd, evidence)
  {
    reveal StepEvidenceFor();
  }

  lemma PackageSameFileRejectStep(
    source: string,
    target: string,
    cmd: Schema.MvCmd,
    preCwd: BenchWorld.Path,
    evidence: StepEvidence
  )
    requires IOContract.IsDirectoryStrictContractFields(
               evidence.beforeFs,
               source,
               false,
               evidence.sourceOk,
               evidence.sourceIsDir,
               evidence.sourceErr
             )
    requires evidence.sourceOk
    requires evidence.targetExistsCalled && evidence.targetFound
    requires IOContract.PathExistsContractFields(
               evidence.beforeFs,
               target,
               false,
               true,
               evidence.targetExistsErr
             )
    requires cmd.overwriteMode != Schema.OverwriteSkip
    requires cmd.updateMode != Schema.UpdateNone
    requires cmd.updateMode != Schema.UpdateNoneFail
    requires SameFileEvidenceFor(
               cmd,
               evidence.beforeFs,
               preCwd,
               source,
               target,
               evidence.sameFile
             )
    requires evidence.sameFile.CheckedSameFile?
    requires evidence.sameFile.decision == Spec.RejectSameFile
    requires evidence.backup == NoBackupSelection
    requires |evidence.renames| == 0
    requires evidence.afterFs == evidence.beforeFs
    requires evidence.outcome ==
             Spec.MoveOutcome([], Spec.SameFileMessageSpec(source, target), true)
    ensures StepEvidenceFor(source, target, cmd, preCwd, evidence)
  {
    reveal StepEvidenceFor();
  }

  lemma PackageUpdateOlderSkipStep(
    source: string,
    target: string,
    cmd: Schema.MvCmd,
    preCwd: BenchWorld.Path,
    evidence: StepEvidence
  )
    requires IOContract.IsDirectoryStrictContractFields(
               evidence.beforeFs,
               source,
               false,
               evidence.sourceOk,
               evidence.sourceIsDir,
               evidence.sourceErr
             )
    requires evidence.sourceOk
    requires evidence.targetExistsCalled && evidence.targetFound
    requires IOContract.PathExistsContractFields(
               evidence.beforeFs,
               target,
               false,
               true,
               evidence.targetExistsErr
             )
    requires cmd.overwriteMode != Schema.OverwriteSkip
    requires cmd.updateMode == Schema.UpdateOlder
    requires SameFileEvidenceFor(
               cmd,
               evidence.beforeFs,
               preCwd,
               source,
               target,
               evidence.sameFile
             )
    requires evidence.sameFile.CheckedSameFile?
    requires evidence.sameFile.decision == Spec.ContinueMove
    requires !SourceNewer(
               evidence.sameFile.source.times.mtimeSec,
               evidence.sameFile.source.times.mtimeNsec,
               evidence.sameFile.target.times.mtimeSec,
               evidence.sameFile.target.times.mtimeNsec
             )
    requires evidence.backup == NoBackupSelection
    requires |evidence.renames| == 0
    requires evidence.afterFs == evidence.beforeFs
    requires evidence.outcome ==
             Spec.MoveOutcome(SkipStdout(target, cmd.debug), [], false)
    ensures StepEvidenceFor(source, target, cmd, preCwd, evidence)
  {
    reveal StepEvidenceFor();
  }

  lemma PackageExistingTargetRenameStep(
    source: string,
    target: string,
    cmd: Schema.MvCmd,
    preCwd: BenchWorld.Path,
    evidence: StepEvidence
  )
    requires IOContract.IsDirectoryStrictContractFields(
               evidence.beforeFs,
               source,
               false,
               evidence.sourceOk,
               evidence.sourceIsDir,
               evidence.sourceErr
             )
    requires evidence.sourceOk
    requires evidence.targetExistsCalled && evidence.targetFound
    requires IOContract.PathExistsContractFields(
               evidence.beforeFs,
               target,
               false,
               true,
               evidence.targetExistsErr
             )
    requires cmd.overwriteMode != Schema.OverwriteSkip
    requires cmd.updateMode != Schema.UpdateNone
    requires cmd.updateMode != Schema.UpdateNoneFail
    requires SameFileEvidenceFor(
               cmd,
               evidence.beforeFs,
               preCwd,
               source,
               target,
               evidence.sameFile
             )
    requires evidence.sameFile.CheckedSameFile?
    requires evidence.sameFile.decision == Spec.ContinueMove
    requires cmd.updateMode != Schema.UpdateOlder ||
             SourceNewer(
               evidence.sameFile.source.times.mtimeSec,
               evidence.sameFile.source.times.mtimeNsec,
               evidence.sameFile.target.times.mtimeSec,
               evidence.sameFile.target.times.mtimeNsec
             )
    requires ExistingTargetRenameEvidenceFor(
               source, target, cmd, preCwd, evidence
             )
    ensures StepEvidenceFor(source, target, cmd, preCwd, evidence)
  {
    reveal StepEvidenceFor();
  }

  opaque ghost predicate BatchStepEvidenceFor(
    source: string,
    directory: string,
    cmd: Schema.MvCmd,
    beforeFs: BenchWorld.FileSystem,
    preCwd: BenchWorld.Path,
    afterFs: BenchWorld.FileSystem,
    outcome: Spec.MoveOutcome,
    stdoutFragment: BenchWorld.Bytes,
    stderrFragment: BenchWorld.Bytes,
    step: StepEvidence
  )
  {
    var normalizedSource :=
      NormalizeSource(source, cmd.stripTrailingSlashes);
    StepEvidenceFor(
      normalizedSource,
      TargetInDirectory(directory, normalizedSource),
      cmd,
      preCwd,
      step
    ) &&
    beforeFs == step.beforeFs &&
    afterFs == step.afterFs &&
    outcome == step.outcome &&
    stdoutFragment == outcome.stdoutFragment &&
    stderrFragment == outcome.stderrFragment
  }

  ghost predicate BatchEvidenceFor(
    sources: seq<string>,
    directory: string,
    cmd: Schema.MvCmd,
    beforeFs: BenchWorld.FileSystem,
    preCwd: BenchWorld.Path,
    afterFs: BenchWorld.FileSystem,
    hadError: bool,
    out: BenchWorld.Bytes,
    err: BenchWorld.Bytes,
    evidence: BatchEvidence
  )
  {
    |evidence.steps| == |sources| &&
    |evidence.fsBounds| == |sources| + 1 &&
    |evidence.outcomes| == |sources| &&
    |evidence.stdoutFragments| == |sources| &&
    |evidence.stderrFragments| == |sources| &&
    evidence.fsBounds[0] == beforeFs &&
    evidence.fsBounds[|evidence.fsBounds| - 1] == afterFs &&
    (forall i: nat | i < |sources| ::
       BatchStepEvidenceFor(
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
       )) &&
    Spec.ConcatenateFragments(evidence.stdoutFragments) == out &&
    Spec.ConcatenateFragments(evidence.stderrFragments) == err &&
    (hadError <==>
     exists i: nat ::
       i < |evidence.outcomes| && evidence.outcomes[i].failed)
  }

  lemma ConcatenateFragmentsSnoc(
    fragments: seq<BenchWorld.Bytes>,
    fragment: BenchWorld.Bytes
  )
    ensures Spec.ConcatenateFragments(fragments + [fragment]) ==
            Spec.ConcatenateFragments(fragments) + fragment
    decreases |fragments|
  {
    if |fragments| > 0 {
      ConcatenateFragmentsSnoc(fragments[1..], fragment);
      assert (fragments + [fragment])[0] == fragments[0];
      assert (fragments + [fragment])[1..] ==
             fragments[1..] + [fragment];
    }
  }

  lemma FailureExistsSnoc(
    outcomes: seq<Spec.MoveOutcome>,
    outcome: Spec.MoveOutcome,
    prefixFailed: bool
  )
    requires prefixFailed <==>
             exists i: nat :: i < |outcomes| && outcomes[i].failed
    ensures prefixFailed || outcome.failed <==>
            exists i: nat ::
              i < |outcomes + [outcome]| &&
              (outcomes + [outcome])[i].failed
  {
    if prefixFailed {
      var i: nat :| i < |outcomes| && outcomes[i].failed;
      assert (outcomes + [outcome])[i] == outcomes[i];
    }
    if outcome.failed {
      assert (outcomes + [outcome])[|outcomes|] == outcome;
    }
    if exists i: nat ::
        i < |outcomes + [outcome]| &&
        (outcomes + [outcome])[i].failed {
      var i: nat :|
        i < |outcomes + [outcome]| &&
        (outcomes + [outcome])[i].failed;
      if i < |outcomes| {
        assert (outcomes + [outcome])[i] == outcomes[i];
        assert exists j: nat ::
            j < |outcomes| && outcomes[j].failed;
      } else {
        assert i == |outcomes|;
        assert (outcomes + [outcome])[i] == outcome;
      }
    }
  }

  method GetErrnoText(err: int) returns (out: string)
    ensures out == Spec.ErrnoTextSpec(err)
  {
    out := Spec.ErrnoTextSpec(err);
  }

  method GetHelpText() returns (out: BenchWorld.Bytes)
    ensures out == Spec.HelpTextSpec()
  {
    out := Spec.HelpTextSpec();
  }

  method GetVersionText() returns (out: BenchWorld.Bytes)
    ensures out == Spec.VersionTextSpec()
  {
    out := Spec.VersionTextSpec();
  }

  method GetMissingFileOperandMessage() returns (out: BenchWorld.Bytes)
    ensures out == Spec.MissingFileOperandMessageSpec()
  {
    out := Spec.MissingFileOperandMessageSpec();
  }

  method GetMissingDestinationMessage(source: string) returns (out: BenchWorld.Bytes)
    ensures out == Spec.MissingDestinationMessageSpec(source)
  {
    out := Spec.MissingDestinationMessageSpec(source);
  }

  method GetExtraOperandMessage(operand: string) returns (out: BenchWorld.Bytes)
    ensures out == Spec.ExtraOperandMessageSpec(operand)
  {
    out := Spec.ExtraOperandMessageSpec(operand);
  }

  method GetTargetDirectoryConflictMessage() returns (out: BenchWorld.Bytes)
    ensures out == Spec.TargetDirectoryConflictMessageSpec()
  {
    out := Spec.TargetDirectoryConflictMessageSpec();
  }

  method GetInvalidBackupArgumentMessage(value: string) returns (out: BenchWorld.Bytes)
    ensures out == Spec.InvalidBackupArgumentMessageSpec(value)
  {
    out := Spec.InvalidBackupArgumentMessageSpec(value);
  }

  method GetInvalidUpdateArgumentMessage(value: string) returns (out: BenchWorld.Bytes)
    ensures out == Spec.InvalidUpdateArgumentMessageSpec(value)
  {
    out := Spec.InvalidUpdateArgumentMessageSpec(value);
  }

  method GetTargetFailureMessage(path: string, explicitTargetDirectory: bool, err: int) returns (out: BenchWorld.Bytes)
    ensures out == Spec.TargetFailureMessageSpec(path, explicitTargetDirectory, err)
  {
    out := Spec.TargetFailureMessageSpec(path, explicitTargetDirectory, err);
  }

  method GetSourceStatFailureMessage(source: string, err: int) returns (out: BenchWorld.Bytes)
    ensures out == Spec.SourceStatFailureMessageSpec(source, err)
  {
    out := Spec.SourceStatFailureMessageSpec(source, err);
  }

  method GetRenameFailureMessage(source: string, target: string, err: int) returns (out: BenchWorld.Bytes)
    ensures out == Spec.RenameFailureMessageSpec(source, target, err)
  {
    out := Spec.RenameFailureMessageSpec(source, target, err);
  }

  method GetSourceRenameFailureMessage(
    source: string,
    target: string,
    sourceIsDir: bool,
    err: int
  ) returns (out: BenchWorld.Bytes)
    ensures out ==
            Spec.SourceRenameFailureMessageSpec(
              source,
              target,
              SourceRenameDiagnosticErr(target, sourceIsDir, err)
            )
  {
    out := Spec.SourceRenameFailureMessageSpec(
      source,
      target,
      SourceRenameDiagnosticErr(target, sourceIsDir, err)
    );
  }

  method GetSameFileMessage(
    source: string,
    target: string
  ) returns (out: BenchWorld.Bytes)
    ensures out == Spec.SameFileMessageSpec(source, target)
  {
    out := Spec.SameFileMessageSpec(source, target);
  }

  method GetBackupWouldDestroySourceMessage(
    source: string,
    target: string
  ) returns (out: BenchWorld.Bytes)
    ensures out == Spec.BackupWouldDestroySourceMessageSpec(source, target)
  {
    out := Spec.BackupWouldDestroySourceMessageSpec(source, target);
  }

  method GetVerboseRenameMessage(source: string, target: string) returns (out: BenchWorld.Bytes)
    ensures out == Spec.VerboseRenameMessageSpec(source, target)
  {
    out := Spec.VerboseRenameMessageSpec(source, target);
  }

  method GetVerboseRenameWithBackupMessage(source: string, target: string, backup: string) returns (out: BenchWorld.Bytes)
    ensures out == Spec.VerboseRenameWithBackupMessageSpec(source, target, backup)
  {
    out := Spec.VerboseRenameWithBackupMessageSpec(source, target, backup);
  }

  method GetDebugSkipMessage(target: string) returns (out: BenchWorld.Bytes)
    ensures out == Spec.DebugSkipMessageSpec(target)
  {
    out := Spec.DebugSkipMessageSpec(target);
  }

  method GetNotReplacingMessage(target: string) returns (out: BenchWorld.Bytes)
    ensures out == Spec.NotReplacingMessageSpec(target)
  {
    out := Spec.NotReplacingMessageSpec(target);
  }

  method FindUnusedNumberedBackupPath(
    target: string,
    index: nat,
    io: BenchIO.IO
  ) returns (path: string, ghost checks: seq<BackupCheckEvidence>)
    requires index >= 1
    ensures BackupChecksFor(target, index, old(io.fs()), checks)
    ensures path == checks[|checks| - 1].candidate
    decreases *
  {
    var candidate := NumberedBackupPath(target, index);
    var rawMetadataOk6, rawMetadataStatus6, rawMetadataErr6 := io.GetFileStatus(candidate, false);
    IOContract.FileStatusImpliesMetadata(io.fs(), candidate, false, rawMetadataOk6, rawMetadataStatus6, rawMetadataErr6);
    var found := rawMetadataOk6;
    var err := rawMetadataErr6;
    ghost var check := BackupCheckEvidence(candidate, found, err);
    if found {
      ghost var tail: seq<BackupCheckEvidence>;
      path, tail := FindUnusedNumberedBackupPath(
        target, index + 1, io
      );
      checks := [check] + tail;
      assert IOContract.PathExistsContractFields(
          old(io.fs()), candidate, false, true, err
        );
      assert forall i: nat | i < |checks| ::
          checks[i].candidate == NumberedBackupPath(target, index + i) &&
          IOContract.PathExistsContractFields(
            old(io.fs()),
            checks[i].candidate,
            false,
            checks[i].found,
            checks[i].err
          ) by {
        forall i: nat | i < |checks|
          ensures
            checks[i].candidate ==
            NumberedBackupPath(target, index + i) &&
            IOContract.PathExistsContractFields(
              old(io.fs()),
              checks[i].candidate,
              false,
              checks[i].found,
              checks[i].err
            )
        {
          if i > 0 {
            assert index + i == index + 1 + (i - 1);
          }
        }
      }
      assert forall i: nat | i + 1 < |checks| :: checks[i].found by {
        forall i: nat | i + 1 < |checks|
          ensures checks[i].found
        {
          if i > 0 {
            assert i - 1 + 1 < |tail|;
          }
        }
      }
    } else {
      path := candidate;
      checks := [check];
      assert IOContract.PathExistsContractFields(old(io.fs()), candidate, false, false, err);
    }
    assert BackupChecksFor(target, index, old(io.fs()), checks);
  }

  method PickBackupPath(
    target: string,
    backupMode: Schema.BackupMode,
    suffix: string,
    io: BenchIO.IO
  ) returns (path: string, ghost evidence: BackupSelectionEvidence)
    ensures BackupSelectionEvidenceFor(
              target, backupMode, suffix, old(io.fs()), evidence
            )
    ensures backupMode != Schema.BackupOff ==>
              evidence.SelectedBackup? &&
              evidence.backupPath == path
    decreases *
  {
    if backupMode == Schema.BackupOff {
      path := "";
      evidence := NoBackupSelection;
      return;
    }
    if backupMode == Schema.BackupSimple {
      path := SimpleBackupPath(target, suffix);
      evidence := SelectedBackup(path, [], false, false, 0);
      return;
    }
    if backupMode == Schema.BackupExisting {
      var numberedSeed := NumberedBackupPath(target, 1);
      var rawMetadataOk5, rawMetadataStatus5, rawMetadataErr5 := io.GetFileStatus(numberedSeed, false);
      IOContract.FileStatusImpliesMetadata(io.fs(), numberedSeed, false, rawMetadataOk5, rawMetadataStatus5, rawMetadataErr5);
      var found := rawMetadataOk5;
      var err := rawMetadataErr5;
      if !found {
        path := SimpleBackupPath(target, suffix);
        evidence := SelectedBackup(path, [], true, found, err);
        assert IOContract.PathExistsContractFields(old(io.fs()), numberedSeed, false, false, err);
        return;
      }
      ghost var checks: seq<BackupCheckEvidence>;
      path, checks := FindUnusedNumberedBackupPath(target, 1, io);
      evidence := SelectedBackup(path, checks, true, found, err);
      assert IOContract.PathExistsContractFields(
          old(io.fs()), numberedSeed, false, true, err
        );
      return;
    }
    ghost var checks: seq<BackupCheckEvidence>;
    path, checks := FindUnusedNumberedBackupPath(target, 1, io);
    evidence := SelectedBackup(path, checks, false, false, 0);
  }

  method CaptureMetadata(
    path: string,
    followSymlink: bool,
    io: BenchIO.IO
  ) returns (evidence: MetadataEvidence)
    ensures MetadataEvidenceFor(
              old(io.fs()), path, followSymlink, evidence
            )
  {
    var ok, status, err := io.GetFileStatus(path, followSymlink);
    IOContract.FileStatusImpliesMetadata(io.fs(), path, followSymlink, ok, status, err);
    var atimeSec := status.times.atimeSec;
    var atimeNsec := status.times.atimeNsec;
    var mtimeSec := status.times.mtimeSec;
    var mtimeNsec := status.times.mtimeNsec;
    var isDir := status.kind == BenchWorld.DirectoryKind;
    var isSymlink := status.kind == BenchWorld.SymlinkKind;
    var device := status.hostKey.device;
    var inode := status.hostKey.inode;
    var linkCount := status.linkCount;
    var links := BenchWorld.LinkCountUnknown;
    if ok && 0 <= linkCount {
      links := BenchWorld.LinkCountKnown(linkCount as nat);
    }
    evidence := MetadataEvidence(
      ok,
      BenchWorld.HostInodeKey(device, inode),
      links,
      isDir,
      isSymlink,
      BenchWorld.FileTimes(
        atimeSec, atimeNsec, mtimeSec, mtimeNsec, 0, 0
      ),
      err
    );
  }

  method CaptureEntryName(
    path: string,
    io: BenchIO.IO
  ) returns (evidence: EntryNameEvidence)
    ensures EntryNameEvidenceFor(old(io.fs()), path, evidence)
    decreases *
  {
    var leaf := BasenameCore.ComputeBasenameValue(path);
    var parent := DirnameCore.ComputeDirnameValue(path);
    var parentMetadata := CaptureMetadata(parent, false, io);
    evidence := EntryNameEvidence(parent, leaf, parentMetadata);
  }

  lemma StrictMetadataSuccess(
    fs: BenchWorld.FileSystem,
    path: string,
    isDir: bool,
    statErr: int,
    evidence: MetadataEvidence
  )
    requires IOContract.IsDirectoryStrictContractFields(
               fs, path, false, true, isDir, statErr
             )
    requires MetadataEvidenceFor(fs, path, false, evidence)
    ensures evidence.ok
  {
  }

  lemma ExistingMetadataSuccess(
    fs: BenchWorld.FileSystem,
    path: string,
    existsErr: int,
    evidence: MetadataEvidence
  )
    requires IOContract.PathExistsContractFields(
               fs, path, false, true, existsErr
             )
    requires MetadataEvidenceFor(fs, path, false, evidence)
    ensures evidence.ok
  {
  }

  ghost predicate TargetDirectoryCheckSummaryFields(directory: string, preFs: BenchWorld.FileSystem, ok: bool, err: int)
  {
    (exists statErr: int ::
       IOContract.IsDirectoryContractFields(preFs, directory, true, true, true, statErr) &&
       ok == true &&
       err == TargetDirectoryErr(true, true, statErr)) ||
    (exists statErr: int ::
       IOContract.IsDirectoryContractFields(preFs, directory, true, true, false, statErr) &&
       ok == false &&
       err == TargetDirectoryErr(true, false, statErr)) ||
    (exists statErr: int ::
       IOContract.IsDirectoryContractFields(preFs, directory, true, false, false, statErr) &&
       ok == false &&
       err == TargetDirectoryErr(false, false, statErr)) ||
    (exists statErr: int ::
       IOContract.IsDirectoryContractFields(preFs, directory, true, false, true, statErr) &&
       ok == false &&
       err == TargetDirectoryErr(false, true, statErr))
  }

  ghost predicate RunIntoDirectoryEvidenceFields(
    sources: seq<string>,
    directory: string,
    explicitTargetDirectory: bool,
    cmd: Schema.MvCmd,
    beforeFs: BenchWorld.FileSystem,
    preCwd: BenchWorld.Path,
    afterFs: BenchWorld.FileSystem,
    preStdout: BenchWorld.Bytes,
    preStderr: BenchWorld.Bytes,
    stdout2: BenchWorld.Bytes,
    stderr2: BenchWorld.Bytes,
    exit: int
  )
  {
    (exists
       hadError: bool,
       out: BenchWorld.Bytes,
       err: BenchWorld.Bytes,
       batch: BatchEvidence
       ::
         TargetDirectoryCheckSummaryFields(
           directory, beforeFs, true, 0
         ) &&
         BatchEvidenceFor(
           sources,
           directory,
           cmd,
           beforeFs,
           preCwd,
           afterFs,
           hadError,
           out,
           err,
           batch
         ) &&
         exit == (if hadError then 1 else 0) &&
         stdout2 == preStdout + out &&
         stderr2 == preStderr + err) ||
    (exists directoryErr: int ::
       TargetDirectoryCheckSummaryFields(
         directory, beforeFs, false, directoryErr
       ) &&
       afterFs == beforeFs &&
       exit == 1 &&
       stdout2 == preStdout &&
       stderr2 == preStderr +
       Spec.TargetFailureMessageSpec(
         directory, explicitTargetDirectory, directoryErr
       ))
  }

  ghost predicate RunTwoOperandEvidenceFields(
    cmd: Schema.MvCmd,
    beforeFs: BenchWorld.FileSystem,
    preCwd: BenchWorld.Path,
    afterFs: BenchWorld.FileSystem,
    preStdout: BenchWorld.Bytes,
    preStderr: BenchWorld.Bytes,
    stdout2: BenchWorld.Bytes,
    stderr2: BenchWorld.Bytes,
    exit: int
  )
    requires |cmd.operands| == 2
  {
    var source :=
      NormalizeSource(cmd.operands[0], cmd.stripTrailingSlashes);
    var destination := cmd.operands[1];
    if cmd.noTargetDirectory then
      exists step: StepEvidence ::
        StepEvidenceFor(source, destination, cmd, preCwd, step) &&
        step.beforeFs == beforeFs &&
        step.afterFs == afterFs &&
        exit == (if step.outcome.failed then 1 else 0) &&
        stdout2 == preStdout + step.outcome.stdoutFragment &&
        stderr2 == preStderr + step.outcome.stderrFragment
    else
      (exists
         directoryErr: int,
         batch: BatchEvidence,
         outcome: Spec.MoveOutcome
         ::
           IOContract.IsDirectoryContractFields(
             beforeFs, destination, true, true, true, directoryErr
           ) &&
           BatchEvidenceFor(
             [cmd.operands[0]],
             destination,
             cmd,
             beforeFs,
             preCwd,
             afterFs,
             outcome.failed,
             outcome.stdoutFragment,
             outcome.stderrFragment,
             batch
           ) &&
           exit == (if outcome.failed then 1 else 0) &&
           stdout2 == preStdout + outcome.stdoutFragment &&
           stderr2 == preStderr + outcome.stderrFragment) ||
      (exists directoryErr: int, step: StepEvidence ::
         IOContract.IsDirectoryContractFields(
           beforeFs, destination, true, true, false, directoryErr
         ) &&
         StepEvidenceFor(source, destination, cmd, preCwd, step) &&
         step.beforeFs == beforeFs &&
         step.afterFs == afterFs &&
         exit == (if step.outcome.failed then 1 else 0) &&
         stdout2 == preStdout + step.outcome.stdoutFragment &&
         stderr2 == preStderr + step.outcome.stderrFragment) ||
      (exists directoryErr: int, step: StepEvidence ::
         IOContract.IsDirectoryContractFields(
           beforeFs, destination, true, false, false, directoryErr
         ) &&
         StepEvidenceFor(source, destination, cmd, preCwd, step) &&
         step.beforeFs == beforeFs &&
         step.afterFs == afterFs &&
         exit == (if step.outcome.failed then 1 else 0) &&
         stdout2 == preStdout + step.outcome.stdoutFragment &&
         stderr2 == preStderr + step.outcome.stderrFragment) ||
      (exists directoryErr: int, step: StepEvidence ::
         IOContract.IsDirectoryContractFields(
           beforeFs, destination, true, false, true, directoryErr
         ) &&
         StepEvidenceFor(source, destination, cmd, preCwd, step) &&
         step.beforeFs == beforeFs &&
         step.afterFs == afterFs &&
         exit == (if step.outcome.failed then 1 else 0) &&
         stdout2 == preStdout + step.outcome.stdoutFragment &&
         stderr2 == preStderr + step.outcome.stderrFragment)
  }

  ghost predicate CoreSummaryIO(
    raw: Schema.MvCmdRaw,
    preFs: BenchWorld.FileSystem,
    preCwd: BenchWorld.Path,
    preStdout: BenchWorld.Bytes,
    preStderr: BenchWorld.Bytes,
    io: BenchIO.IO,
    exit: int
  )
    reads io.Footprint()
  {
    var cmd := Schema.Command(raw);
    if cmd.mode == Schema.ModeInvalidBackup then
      io.fs() == preFs &&
      exit == 1 &&
      io.stdout() == preStdout &&
      io.stderr() == preStderr + Spec.InvalidBackupArgumentMessageSpec(cmd.invalidBackupArg)
    else if cmd.mode == Schema.ModeInvalidUpdate then
      io.fs() == preFs &&
      exit == 1 &&
      io.stdout() == preStdout &&
      io.stderr() == preStderr + Spec.InvalidUpdateArgumentMessageSpec(cmd.invalidUpdateArg)
    else if cmd.mode == Schema.ModeHelp then
      io.fs() == preFs &&
      exit == 0 &&
      io.stdout() == preStdout + Spec.HelpTextSpec() &&
      io.stderr() == preStderr
    else if cmd.mode == Schema.ModeVersion then
      io.fs() == preFs &&
      exit == 0 &&
      io.stdout() == preStdout + Spec.VersionTextSpec() &&
      io.stderr() == preStderr
    else if cmd.targetDirectory != "" && cmd.noTargetDirectory then
      io.fs() == preFs &&
      exit == 1 &&
      io.stdout() == preStdout &&
      io.stderr() == preStderr + Spec.TargetDirectoryConflictMessageSpec()
    else if |cmd.operands| == 0 then
      io.fs() == preFs &&
      exit == 1 &&
      io.stdout() == preStdout &&
      io.stderr() == preStderr + Spec.MissingFileOperandMessageSpec()
    else if cmd.targetDirectory != "" then
      RunIntoDirectoryEvidenceFields(cmd.operands, cmd.targetDirectory, true, cmd, preFs, preCwd, io.fs(), preStdout, preStderr, io.stdout(), io.stderr(), exit)
    else if |cmd.operands| == 1 then
      io.fs() == preFs &&
      exit == 1 &&
      io.stdout() == preStdout &&
      io.stderr() == preStderr + Spec.MissingDestinationMessageSpec(cmd.operands[0])
    else if cmd.noTargetDirectory && |cmd.operands| > 2 then
      io.fs() == preFs &&
      exit == 1 &&
      io.stdout() == preStdout &&
      io.stderr() == preStderr + Spec.ExtraOperandMessageSpec(cmd.operands[2])
    else if |cmd.operands| == 2 then
      RunTwoOperandEvidenceFields(cmd, preFs, preCwd, io.fs(), preStdout, preStderr, io.stdout(), io.stderr(), exit)
    else
      RunIntoDirectoryEvidenceFields(cmd.operands[..|cmd.operands| - 1], cmd.operands[|cmd.operands| - 1], false, cmd, preFs, preCwd, io.fs(), preStdout, preStderr, io.stdout(), io.stderr(), exit)
  }

  twostate predicate CoreSummary(raw: Schema.MvCmdRaw, io: BenchIO.IO, exit: int)
    reads io.Footprint()
  {
    CoreSummaryIO(
      raw,
      old(io.fs()),
      old(io.cwd()),
      old(io.stdout()),
      old(io.stderr()),
      io,
      exit
    )
  }

  method {:isolate_assertions} RunCore(
    raw: Schema.MvCmdRaw,
    io: BenchIO.IO
  ) returns (exit: int)
    modifies io.fsRegion, io.stdoutRegion, io.stderrRegion
    ensures CoreSummary(raw, io, exit)
    ensures CoreSummaryIO(
              raw,
              old(io.fs()),
              old(io.cwd()),
              old(io.stdout()),
              old(io.stderr()),
              io,
              exit
            )
    decreases *
  {
    ghost var preFs := io.fs();
    ghost var preCwd := io.cwd();
    ghost var preStdout := io.stdout();
    ghost var preStderr := io.stderr();
    var cmd := Schema.Command(raw);
    if cmd.mode == Schema.ModeInvalidBackup {
      var err := GetInvalidBackupArgumentMessage(cmd.invalidBackupArg);
      io.AppendStderr(err);
      exit := 1;
      assert CoreSummaryIO(raw, preFs, preCwd, preStdout, preStderr, io, exit);
      return;
    }

    if cmd.mode == Schema.ModeInvalidUpdate {
      var err := GetInvalidUpdateArgumentMessage(cmd.invalidUpdateArg);
      io.AppendStderr(err);
      exit := 1;
      assert CoreSummaryIO(raw, preFs, preCwd, preStdout, preStderr, io, exit);
      return;
    }

    if cmd.mode == Schema.ModeHelp {
      var out := GetHelpText();
      io.AppendStdout(out);
      exit := 0;
      assert CoreSummaryIO(raw, preFs, preCwd, preStdout, preStderr, io, exit);
      return;
    }

    if cmd.mode == Schema.ModeVersion {
      var out := GetVersionText();
      io.AppendStdout(out);
      exit := 0;
      assert CoreSummaryIO(raw, preFs, preCwd, preStdout, preStderr, io, exit);
      return;
    }

    if cmd.targetDirectory != "" && cmd.noTargetDirectory {
      var err := GetTargetDirectoryConflictMessage();
      io.AppendStderr(err);
      exit := 1;
      assert CoreSummaryIO(raw, preFs, preCwd, preStdout, preStderr, io, exit);
      return;
    }

    if |cmd.operands| == 0 {
      var err := GetMissingFileOperandMessage();
      io.AppendStderr(err);
      exit := 1;
      assert CoreSummaryIO(raw, preFs, preCwd, preStdout, preStderr, io, exit);
      return;
    }

    if cmd.targetDirectory != "" {
      exit := RunIntoDirectory(cmd.operands, cmd.targetDirectory, true, cmd, io);
      assert CoreSummaryIO(raw, preFs, preCwd, preStdout, preStderr, io, exit);
      return;
    }

    if |cmd.operands| == 1 {
      var err := GetMissingDestinationMessage(cmd.operands[0]);
      io.AppendStderr(err);
      exit := 1;
      assert CoreSummaryIO(raw, preFs, preCwd, preStdout, preStderr, io, exit);
      return;
    }

    if cmd.noTargetDirectory && |cmd.operands| > 2 {
      var err := GetExtraOperandMessage(cmd.operands[2]);
      io.AppendStderr(err);
      exit := 1;
      assert CoreSummaryIO(raw, preFs, preCwd, preStdout, preStderr, io, exit);
      return;
    }

    if |cmd.operands| == 2 {
      var source := NormalizeSource(cmd.operands[0], cmd.stripTrailingSlashes);
      var dest := cmd.operands[1];
      var target := dest;
      var dirOk := false;
      var isDir := false;
      var dirErr := 0;
      if !cmd.noTargetDirectory {
        var rawMetadataOk4, rawMetadataStatus4, rawMetadataErr4 := io.GetFileStatus(dest, true);
        IOContract.FileStatusImpliesMetadata(io.fs(), dest, true, rawMetadataOk4, rawMetadataStatus4, rawMetadataErr4);
        dirOk := rawMetadataOk4;
        isDir := rawMetadataStatus4.kind == BenchWorld.DirectoryKind;
        dirErr := rawMetadataErr4;
        if dirOk && isDir {
          target := TargetInDirectory(dest, source);
        }
      }
      ghost var preMoveFs := io.fs();
      var hadError, out, errOut, step := MoveOne(
        source, target, cmd, io
      );
      ghost var movedFs := io.fs();
      io.AppendStdout(out);
      io.AppendStderr(errOut);
      exit := if hadError then 1 else 0;
      assert preMoveFs == preFs;
      assert (exit == 1) == hadError;
      assert step.beforeFs == preFs;
      assert step.afterFs == movedFs;
      assert step.outcome == Spec.MoveOutcome(out, errOut, hadError);
      assert io.fs() == movedFs;
      assert io.stdout() == preStdout + out;
      assert io.stderr() == preStderr + errOut;
      if !cmd.noTargetDirectory {
        if dirOk && isDir {
          assert target == TargetInDirectory(dest, source);
          assert IOContract.IsDirectoryContractFields(preFs, dest, true, true, true, dirErr);
          ghost var batch := BatchEvidence(
            [step],
            [preFs, movedFs],
            [step.outcome],
            [step.outcome.stdoutFragment],
            [step.outcome.stderrFragment]
          );
          assert Spec.ConcatenateFragments(
              [step.outcome.stdoutFragment]
            ) == out;
          assert Spec.ConcatenateFragments(
              [step.outcome.stderrFragment]
            ) == errOut;
          reveal BatchStepEvidenceFor();
          assert BatchStepEvidenceFor(
              cmd.operands[0],
              dest,
              cmd,
              preFs,
              preCwd,
              movedFs,
              step.outcome,
              step.outcome.stdoutFragment,
              step.outcome.stderrFragment,
              step
            );
          hide BatchStepEvidenceFor();
          assert BatchEvidenceFor(
              [cmd.operands[0]],
              dest,
              cmd,
              preFs,
              preCwd,
              movedFs,
              hadError,
              out,
              errOut,
              batch
            );
          ghost var batchOutcome := step.outcome;
          assert batchOutcome.failed == hadError;
          assert batchOutcome.stdoutFragment == out;
          assert batchOutcome.stderrFragment == errOut;
          assert BatchEvidenceFor(
              [cmd.operands[0]],
              dest,
              cmd,
              preFs,
              preCwd,
              movedFs,
              batchOutcome.failed,
              batchOutcome.stdoutFragment,
              batchOutcome.stderrFragment,
              batch
            );
          assert exit == (if batchOutcome.failed then 1 else 0);
          assert io.stdout() ==
                 preStdout + batchOutcome.stdoutFragment;
          assert io.stderr() ==
                 preStderr + batchOutcome.stderrFragment;
          assert
            IOContract.IsDirectoryContractFields(
              preFs, dest, true, true, true, dirErr
            ) &&
            BatchEvidenceFor(
              [cmd.operands[0]],
              dest,
              cmd,
              preFs,
              preCwd,
              movedFs,
              batchOutcome.failed,
              batchOutcome.stdoutFragment,
              batchOutcome.stderrFragment,
              batch
            ) &&
            exit == (if batchOutcome.failed then 1 else 0) &&
            io.stdout() ==
            preStdout + batchOutcome.stdoutFragment &&
            io.stderr() ==
            preStderr + batchOutcome.stderrFragment;
          assert exists
              directoryErr0: int,
              batch0: BatchEvidence,
              outcome0: Spec.MoveOutcome
              ::
                IOContract.IsDirectoryContractFields(
                  preFs, dest, true, true, true, directoryErr0
                ) &&
                BatchEvidenceFor(
                  [cmd.operands[0]],
                  dest,
                  cmd,
                  preFs,
                  preCwd,
                  movedFs,
                  outcome0.failed,
                  outcome0.stdoutFragment,
                  outcome0.stderrFragment,
                  batch0
                ) &&
                exit == (if outcome0.failed then 1 else 0) &&
                io.stdout() == preStdout + outcome0.stdoutFragment &&
                io.stderr() == preStderr + outcome0.stderrFragment;
        } else if dirOk && !isDir {
          assert target == dest;
          assert IOContract.IsDirectoryContractFields(preFs, dest, true, true, false, dirErr);
          assert exists directoryErr0: int, step0: StepEvidence ::
              IOContract.IsDirectoryContractFields(
                preFs, dest, true, true, false, directoryErr0
              ) &&
              StepEvidenceFor(source, dest, cmd, preCwd, step0) &&
              step0.beforeFs == preFs &&
              step0.afterFs == movedFs &&
              exit == (if step0.outcome.failed then 1 else 0) &&
              io.stdout() == preStdout + step0.outcome.stdoutFragment &&
              io.stderr() == preStderr + step0.outcome.stderrFragment;
        } else if !dirOk && !isDir {
          assert target == dest;
          assert IOContract.IsDirectoryContractFields(preFs, dest, true, false, false, dirErr);
          assert exists directoryErr0: int, step0: StepEvidence ::
              IOContract.IsDirectoryContractFields(
                preFs, dest, true, false, false, directoryErr0
              ) &&
              StepEvidenceFor(source, dest, cmd, preCwd, step0) &&
              step0.beforeFs == preFs &&
              step0.afterFs == movedFs &&
              exit == (if step0.outcome.failed then 1 else 0) &&
              io.stdout() == preStdout + step0.outcome.stdoutFragment &&
              io.stderr() == preStderr + step0.outcome.stderrFragment;
        } else {
          assert !dirOk && isDir;
          assert target == dest;
          assert IOContract.IsDirectoryContractFields(preFs, dest, true, false, true, dirErr);
          assert exists directoryErr0: int, step0: StepEvidence ::
              IOContract.IsDirectoryContractFields(
                preFs, dest, true, false, true, directoryErr0
              ) &&
              StepEvidenceFor(source, dest, cmd, preCwd, step0) &&
              step0.beforeFs == preFs &&
              step0.afterFs == movedFs &&
              exit == (if step0.outcome.failed then 1 else 0) &&
              io.stdout() == preStdout + step0.outcome.stdoutFragment &&
              io.stderr() == preStderr + step0.outcome.stderrFragment;
        }
      } else {
        assert target == dest;
        assert exists step0: StepEvidence ::
            StepEvidenceFor(source, dest, cmd, preCwd, step0) &&
            step0.beforeFs == preFs &&
            step0.afterFs == movedFs &&
            exit == (if step0.outcome.failed then 1 else 0) &&
            io.stdout() == preStdout + step0.outcome.stdoutFragment &&
            io.stderr() == preStderr + step0.outcome.stderrFragment;
      }
      assert RunTwoOperandEvidenceFields(
          cmd, preFs, preCwd, io.fs(),
          preStdout, preStderr, io.stdout(), io.stderr(), exit
        );
      hide RunTwoOperandEvidenceFields();
      assert CoreSummaryIO(raw, preFs, preCwd, preStdout, preStderr, io, exit);
      return;
    }

    var directory := cmd.operands[|cmd.operands| - 1];
    var sources := cmd.operands[..|cmd.operands| - 1];
    exit := RunIntoDirectory(sources, directory, false, cmd, io);
    assert CoreSummaryIO(raw, preFs, preCwd, preStdout, preStderr, io, exit);
  }

  method CheckTargetDirectory(directory: string, io: BenchIO.IO) returns (ok: bool, err: int)
    ensures TargetDirectoryCheckSummaryFields(directory, old(io.fs()), ok, err)
  {
    var rawMetadataOk3, rawMetadataStatus3, rawMetadataErr3 := io.GetFileStatus(directory, true);
    IOContract.FileStatusImpliesMetadata(io.fs(), directory, true, rawMetadataOk3, rawMetadataStatus3, rawMetadataErr3);
    var statOk := rawMetadataOk3;
    var isDir := rawMetadataStatus3.kind == BenchWorld.DirectoryKind;
    var statErr := rawMetadataErr3;
    ok := statOk && isDir;
    if statOk && !isDir {
      err := ENOTDIR;
    } else {
      err := statErr;
    }
  }

  method RunIntoDirectory(
    sources: seq<string>,
    directory: string,
    explicitTargetDirectory: bool,
    cmd: Schema.MvCmd,
    io: BenchIO.IO
  ) returns (exit: int)
    modifies io.fsRegion, io.stdoutRegion, io.stderrRegion
    ensures RunIntoDirectoryEvidenceFields(
              sources,
              directory,
              explicitTargetDirectory,
              cmd,
              old(io.fs()),
              old(io.cwd()),
              io.fs(),
              old(io.stdout()),
              old(io.stderr()),
              io.stdout(),
              io.stderr(),
              exit
            )
    decreases *
  {
    ghost var preFs := io.fs();
    ghost var preCwd := io.cwd();
    ghost var preStdout := io.stdout();
    ghost var preStderr := io.stderr();
    var dirOk, dirErr := CheckTargetDirectory(directory, io);
    if !dirOk {
      var err := GetTargetFailureMessage(directory, explicitTargetDirectory, dirErr);
      io.AppendStderr(err);
      exit := 1;
      assert TargetDirectoryCheckSummaryFields(directory, preFs, false, dirErr);
      assert RunIntoDirectoryEvidenceFields(
          sources, directory, explicitTargetDirectory, cmd,
          preFs, preCwd, io.fs(), preStdout, preStderr,
          io.stdout(), io.stderr(), exit
        );
      return;
    }

    var hadError, out, errOut, batch := MoveSourcesIntoDirectory(
      sources, directory, cmd, io
    );
    ghost var movedFs := io.fs();
    io.AppendStdout(out);
    io.AppendStderr(errOut);
    exit := if hadError then 1 else 0;
    assert dirErr == 0;
    assert (exit == 1) == hadError;
    assert TargetDirectoryCheckSummaryFields(directory, preFs, true, 0);
    assert io.fs() == movedFs;
    assert io.stdout() == preStdout + out;
    assert io.stderr() == preStderr + errOut;
    assert RunIntoDirectoryEvidenceFields(
        sources, directory, explicitTargetDirectory, cmd,
        preFs, preCwd, io.fs(), preStdout, preStderr,
        io.stdout(), io.stderr(), exit
      );
  }

  method {:isolate_assertions} MoveOne(
    source: string,
    target: string,
    cmd: Schema.MvCmd,
    io: BenchIO.IO
  ) returns (
      hadError: bool,
      out: BenchWorld.Bytes,
      errOut: BenchWorld.Bytes,
      ghost step: StepEvidence
    )
    modifies io.fsRegion
    ensures StepEvidenceFor(source, target, cmd, old(io.cwd()), step)
    ensures step.beforeFs == old(io.fs())
    ensures step.afterFs == io.fs()
    ensures step.outcome == Spec.MoveOutcome(out, errOut, hadError)
    decreases *
  {
    ghost var preFs := io.fs();
    ghost var preCwd := io.cwd();
    hadError := false;
    out := [];
    errOut := [];
    ghost var sameFileEvidence: SameFileEvidence := NoSameFileCheck;
    ghost var backupEvidence: BackupSelectionEvidence :=
      NoBackupSelection;
    ghost var renameCalls: seq<RenameCallEvidence> := [];
    ghost var backupFs := preFs;

    var rawMetadataOk2, rawMetadataStatus2, rawMetadataErr2 := io.GetFileStatus(source, false);
    IOContract.FileStatusImpliesMetadata(io.fs(), source, false, rawMetadataOk2, rawMetadataStatus2, rawMetadataErr2);
    var sourceOk := rawMetadataOk2;
    var sourceIsDir := rawMetadataStatus2.kind == BenchWorld.DirectoryKind;
    var sourceErr := rawMetadataErr2;
    if !sourceOk {
      hadError := true;
      errOut := GetSourceStatFailureMessage(source, sourceErr);
      step := MakeStepEvidence(
        preFs, io.fs(), out, errOut, hadError,
        sourceOk, sourceIsDir, sourceErr,
        false, false, 0,
        sameFileEvidence, backupEvidence, renameCalls, backupFs
      );
      PackageSourceFailureStep(
        source, target, cmd, preCwd, step
      );
      return;
    }

    var rawMetadataOk1, rawMetadataStatus1, rawMetadataErr1 := io.GetFileStatus(target, false);
    IOContract.FileStatusImpliesMetadata(io.fs(), target, false, rawMetadataOk1, rawMetadataStatus1, rawMetadataErr1);
    var found := rawMetadataOk1;
    var existsErr := rawMetadataErr1;
    if found {
      if cmd.overwriteMode == Schema.OverwriteSkip {
        if cmd.debug {
          out := GetDebugSkipMessage(target);
        }
        step := MakeStepEvidence(
          preFs, io.fs(), out, errOut, hadError,
          sourceOk, sourceIsDir, sourceErr,
          true, found, existsErr,
          sameFileEvidence, backupEvidence, renameCalls, backupFs
        );
        PackageOverwriteSkipStep(
          source, target, cmd, preCwd, step
        );
        return;
      }

      if cmd.updateMode == Schema.UpdateNone {
        if cmd.debug {
          out := GetDebugSkipMessage(target);
        }
        step := MakeStepEvidence(
          preFs, io.fs(), out, errOut, hadError,
          sourceOk, sourceIsDir, sourceErr,
          true, found, existsErr,
          sameFileEvidence, backupEvidence, renameCalls, backupFs
        );
        PackageUpdateNoneStep(
          source, target, cmd, preCwd, step
        );
        return;
      }

      if cmd.updateMode == Schema.UpdateNoneFail {
        hadError := true;
        errOut := GetNotReplacingMessage(target);
        step := MakeStepEvidence(
          preFs, io.fs(), out, errOut, hadError,
          sourceOk, sourceIsDir, sourceErr,
          true, found, existsErr,
          sameFileEvidence, backupEvidence, renameCalls, backupFs
        );
        PackageUpdateNoneFailStep(
          source, target, cmd, preCwd, step
        );
        return;
      }

      var sourceMetadata := CaptureMetadata(source, false, io);
      var targetMetadata := CaptureMetadata(target, false, io);
      StrictMetadataSuccess(
        preFs, source, sourceIsDir, sourceErr, sourceMetadata
      );
      ExistingMetadataSuccess(
        preFs, target, existsErr, targetMetadata
      );
      var sourceEntry := CaptureEntryName(source, io);
      var targetEntry := CaptureEntryName(target, io);
      var sourceFollowed: OptionalMetadataEvidence :=
        NoMetadataEvidence;
      var sourceReferentEntry: OptionalEntryNameEvidence :=
        NoEntryNameEvidence;
      if sourceMetadata.isSymlink {
        assert io.fs() == preFs;
        var followed := CaptureMetadata(source, true, io);
        assert MetadataEvidenceFor(preFs, source, true, followed);
        sourceFollowed := SomeMetadataEvidence(followed);
        var resolveOk, resolvedSource, resolveErr :=
          io.ResolvePathIdentity(source);
        if resolveOk {
          assert IOContract.ResolvePathIdentityContractFields(
              preFs, preCwd, source, true, resolvedSource, 0
            );
          var referentEntry := CaptureEntryName(resolvedSource, io);
          sourceReferentEntry :=
            SomeEntryNameEvidence(resolvedSource, referentEntry);
        } else {
          assert IOContract.ResolvePathIdentityContractFields(
              preFs, preCwd, source, false, "", resolveErr
            );
          sourceReferentEntry :=
            FailedEntryNameEvidence(resolveErr);
        }
      }
      var sameEntry :=
        sourceEntry.parentMetadata.ok &&
        targetEntry.parentMetadata.ok &&
        sourceEntry.parentMetadata.key ==
        targetEntry.parentMetadata.key &&
        sourceEntry.leaf == targetEntry.leaf;
      var referentSameEntry := false;
      match sourceReferentEntry {
        case SomeEntryNameEvidence(_, referentEntry) =>
          referentSameEntry :=
            referentEntry.parentMetadata.ok &&
            targetEntry.parentMetadata.ok &&
            referentEntry.parentMetadata.key ==
            targetEntry.parentMetadata.key &&
            referentEntry.leaf == targetEntry.leaf;
        case _ =>
      }
      var rejectSameFile :=
        sameEntry ||
        (cmd.backupMode == Schema.BackupOff &&
         (sourceMetadata.key == targetMetadata.key ||
          referentSameEntry));
      var sameFileDecision :=
        if rejectSameFile
        then Spec.RejectSameFile
        else Spec.ContinueMove;
      assert sameFileDecision ==
             if EvidenceNamesSame(sourceEntry, targetEntry) ||
                (cmd.backupMode == Schema.BackupOff &&
                 ((sourceMetadata.ok &&
                   targetMetadata.ok &&
                   sourceMetadata.key == targetMetadata.key) ||
                  ReferentEvidenceNamesTarget(
                    sourceReferentEntry, targetEntry
                  )))
             then Spec.RejectSameFile
             else Spec.ContinueMove;
      sameFileEvidence := CheckedSameFile(
        sourceMetadata,
        targetMetadata,
        sourceFollowed,
        sourceEntry,
        targetEntry,
        sourceReferentEntry,
        NoBackupCollisionCheck,
        sameFileDecision
      );
      PackageSameFileEvidence(
        cmd,
        preFs,
        preCwd,
        source,
        target,
        sourceMetadata,
        targetMetadata,
        sourceFollowed,
        sourceEntry,
        targetEntry,
        sourceReferentEntry,
        NoBackupCollisionCheck,
        sameFileDecision
      );
      if sameFileDecision == Spec.RejectSameFile {
        hadError := true;
        errOut := GetSameFileMessage(source, target);
        step := MakeStepEvidence(
          preFs, io.fs(), out, errOut, hadError,
          sourceOk, sourceIsDir, sourceErr,
          true, found, existsErr,
          sameFileEvidence, backupEvidence, renameCalls, backupFs
        );
        PackageSameFileRejectStep(
          source, target, cmd, preCwd, step
        );
        return;
      }
      assert sameFileDecision == Spec.ContinueMove;

      if cmd.updateMode == Schema.UpdateOlder {
        if !SourceNewer(
            sourceMetadata.times.mtimeSec,
            sourceMetadata.times.mtimeNsec,
            targetMetadata.times.mtimeSec,
            targetMetadata.times.mtimeNsec
          ) {
          if cmd.debug {
            out := GetDebugSkipMessage(target);
          }
          step := MakeStepEvidence(
            preFs, io.fs(), out, errOut, hadError,
            sourceOk, sourceIsDir, sourceErr,
            true, found, existsErr,
            sameFileEvidence, backupEvidence, renameCalls, backupFs
          );
          PackageUpdateOlderSkipStep(
            source, target, cmd, preCwd, step
          );
          return;
        }
      }

      ghost var collisionEvidence: BackupCollisionEvidence :=
        NoBackupCollisionCheck;
      if (cmd.backupMode == Schema.BackupSimple ||
          cmd.backupMode == Schema.BackupExisting) &&
         sourceEntry.leaf ==
         targetEntry.leaf + cmd.backupSuffix
      {
        var candidateMetadata := CaptureMetadata(
          SimpleBackupPath(target, cmd.backupSuffix), true, io
        );
        collisionEvidence := CheckedBackupCollision(
          sourceMetadata, candidateMetadata
        );
        sameFileEvidence := CheckedSameFile(
          sourceMetadata,
          targetMetadata,
          sourceFollowed,
          sourceEntry,
          targetEntry,
          sourceReferentEntry,
          collisionEvidence,
          sameFileDecision
        );
        PackageSameFileEvidence(
          cmd,
          preFs,
          preCwd,
          source,
          target,
          sourceMetadata,
          targetMetadata,
          sourceFollowed,
          sourceEntry,
          targetEntry,
          sourceReferentEntry,
          collisionEvidence,
          sameFileDecision
        );
        if candidateMetadata.ok &&
           candidateMetadata.key == sourceMetadata.key
        {
          hadError := true;
          errOut :=
            GetBackupWouldDestroySourceMessage(source, target);
          step := MakeStepEvidence(
            preFs, io.fs(), out, errOut, hadError,
            sourceOk, sourceIsDir, sourceErr,
            true, found, existsErr,
            sameFileEvidence, backupEvidence, renameCalls, backupFs
          );
          PackageExistingTargetRenameStep(
            source, target, cmd, preCwd, step
          );
          return;
        }
      }
      assert BackupCollisionEvidenceFor(
          cmd,
          preFs,
          source,
          target,
          sourceMetadata,
          sourceEntry,
          targetEntry,
          collisionEvidence
        );
      assert !BackupCollisionDetected(collisionEvidence);

      if cmd.backupMode != Schema.BackupOff {
        ghost var fsBeforeBackup := io.fs();
        var backupPath, selectedBackup := PickBackupPath(
          target, cmd.backupMode, cmd.backupSuffix, io
        );
        backupEvidence := selectedBackup;
        assert fsBeforeBackup == preFs;
        var okBackup, backupErr := io.RenamePath(target, backupPath);
        ghost var afterBackupFs := io.fs();
        backupFs := afterBackupFs;
        ghost var backupCall :=
          RenameCallEvidence(okBackup, backupErr, afterBackupFs);
        renameCalls := [backupCall];
        assert IOContract.RenamePathContractFields(
            preFs,
            target,
            backupPath,
            okBackup,
            backupErr,
            afterBackupFs
          );
        if !okBackup {
          hadError := true;
          errOut := GetRenameFailureMessage(source, target, backupErr);
          step := MakeStepEvidence(
            preFs, io.fs(), out, errOut, hadError,
            sourceOk, sourceIsDir, sourceErr,
            true, found, existsErr,
            sameFileEvidence, backupEvidence, renameCalls, backupFs
          );
          PackageExistingTargetRenameStep(
            source, target, cmd, preCwd, step
          );
          return;
        }

        var okRenameWithBackup, renameErrWithBackup := io.RenamePath(source, target);
        ghost var afterRenameFs := io.fs();
        ghost var sourceCall := RenameCallEvidence(
          okRenameWithBackup,
          renameErrWithBackup,
          afterRenameFs
        );
        renameCalls := [backupCall, sourceCall];
        assert IOContract.RenamePathContractFields(
            afterBackupFs,
            source,
            target,
            okRenameWithBackup,
            renameErrWithBackup,
            afterRenameFs
          );
        hadError := !okRenameWithBackup;
        if okRenameWithBackup {
          if cmd.verbose || cmd.debug {
            out := GetVerboseRenameWithBackupMessage(source, target, backupPath);
          }
          assert out == StepSuccessStdout(source, target, backupPath, cmd.verbose, cmd.debug);
          assert errOut == [];
        } else {
          errOut := GetSourceRenameFailureMessage(
            source, target, sourceIsDir, renameErrWithBackup
          );
          assert out == [];
        }
        assert IOContract.PathExistsContractFields(preFs, target, false, true, existsErr);
        assert cmd.overwriteMode != Schema.OverwriteSkip;
        assert !(cmd.updateMode == Schema.UpdateNone || cmd.updateMode == Schema.UpdateNoneFail);
        assert RenameEvidenceFor(
            source,
            target,
            sourceIsDir,
            backupPath,
            cmd.verbose,
            cmd.debug,
            preFs,
            preCwd,
            io.fs(),
            Spec.MoveOutcome(out, errOut, hadError),
            renameCalls,
            backupFs
          );
        step := MakeStepEvidence(
          preFs, io.fs(), out, errOut, hadError,
          sourceOk, sourceIsDir, sourceErr,
          true, found, existsErr,
          sameFileEvidence, backupEvidence, renameCalls, backupFs
        );
        PackageExistingTargetRenameStep(
          source, target, cmd, preCwd, step
        );
        return;
      }

      assert cmd.backupMode == Schema.BackupOff;
    }

    var okRename, renameErr := io.RenamePath(source, target);
    ghost var afterRenameFs := io.fs();
    assert IOContract.RenamePathContractFields(
        preFs,
        source,
        target,
        okRename,
        renameErr,
        afterRenameFs
      );
    renameCalls := [
      RenameCallEvidence(okRename, renameErr, afterRenameFs)
    ];
    hadError := !okRename;
    if okRename && (cmd.verbose || cmd.debug) {
      out := GetVerboseRenameMessage(source, target);
    }
    if !okRename {
      errOut := GetSourceRenameFailureMessage(
        source, target, sourceIsDir, renameErr
      );
      assert out == [];
    } else {
      assert out == StepSuccessStdout(source, target, "", cmd.verbose, cmd.debug);
      assert errOut == [];
    }
    if found {
      assert IOContract.PathExistsContractFields(preFs, target, false, true, existsErr);
      assert cmd.overwriteMode != Schema.OverwriteSkip;
      assert !(cmd.updateMode == Schema.UpdateNone || cmd.updateMode == Schema.UpdateNoneFail);
      assert cmd.backupMode == Schema.BackupOff;
    } else {
      assert IOContract.PathExistsContractFields(preFs, target, false, false, existsErr);
    }
    step := MakeStepEvidence(
      preFs, io.fs(), out, errOut, hadError,
      sourceOk, sourceIsDir, sourceErr,
      true, found, existsErr,
      sameFileEvidence, backupEvidence, renameCalls, backupFs
    );
    if found {
      PackageExistingTargetRenameStep(
        source, target, cmd, preCwd, step
      );
    } else {
      PackageMissingTargetStep(
        source, target, cmd, preCwd, step
      );
    }
  }

  method {:vcs_split_on_every_assert} MoveSourcesIntoDirectory(
    sources: seq<string>,
    directory: string,
    cmd: Schema.MvCmd,
    io: BenchIO.IO
  ) returns (
      hadError: bool,
      out: BenchWorld.Bytes,
      errOut: BenchWorld.Bytes,
      ghost batch: BatchEvidence
    )
    modifies io.fsRegion
    ensures BatchEvidenceFor(
              sources, directory, cmd, old(io.fs()), old(io.cwd()), io.fs(),
              hadError, out, errOut, batch
            )
    decreases *
  {
    ghost var preFs := io.fs();
    ghost var preCwd := io.cwd();
    ghost var steps: seq<StepEvidence> := [];
    ghost var fsBounds: seq<BenchWorld.FileSystem> := [preFs];
    ghost var outcomes: seq<Spec.MoveOutcome> := [];
    ghost var stdoutFragments: seq<BenchWorld.Bytes> := [];
    ghost var stderrFragments: seq<BenchWorld.Bytes> := [];
    hadError := false;
    out := [];
    errOut := [];
    var i := 0;
    while i < |sources|
      invariant 0 <= i <= |sources|
      invariant |steps| == i
      invariant |fsBounds| == |steps| + 1
      invariant |outcomes| == |steps|
      invariant |stdoutFragments| == |steps|
      invariant |stderrFragments| == |steps|
      invariant fsBounds[0] == preFs
      invariant fsBounds[|fsBounds| - 1] == io.fs()
      invariant forall j: nat | j < |steps| ::
                  BatchStepEvidenceFor(
                    sources[j],
                    directory,
                    cmd,
                    fsBounds[j],
                    preCwd,
                    fsBounds[j + 1],
                    outcomes[j],
                    stdoutFragments[j],
                    stderrFragments[j],
                    steps[j]
                  )
      invariant Spec.ConcatenateFragments(stdoutFragments) == out
      invariant Spec.ConcatenateFragments(stderrFragments) == errOut
      invariant hadError <==>
                exists j: nat :: j < |outcomes| && outcomes[j].failed
      decreases |sources| - i
    {
      var prefixError := hadError;
      var prefixOut := out;
      var prefixErr := errOut;
      ghost var prefixSteps := steps;
      ghost var prefixFsBounds := fsBounds;
      ghost var prefixOutcomes := outcomes;
      ghost var prefixStdoutFragments := stdoutFragments;
      ghost var prefixStderrFragments := stderrFragments;
      ghost var fsBeforeStep := io.fs();
      var source := sources[i];
      var normalizedSource := NormalizeSource(source, cmd.stripTrailingSlashes);
      var target := TargetInDirectory(directory, normalizedSource);
      assert target == TargetInDirectory(directory, normalizedSource);
      var stepError, stepOut, stepErr, step := MoveOne(
        normalizedSource, target, cmd, io
      );
      ghost var nextOutcome := step.outcome;
      steps := steps + [step];
      fsBounds := fsBounds + [step.afterFs];
      outcomes := outcomes + [nextOutcome];
      stdoutFragments :=
        stdoutFragments + [nextOutcome.stdoutFragment];
      stderrFragments :=
        stderrFragments + [nextOutcome.stderrFragment];
      hadError := prefixError || stepError;
      out := prefixOut + stepOut;
      errOut := prefixErr + stepErr;
      ConcatenateFragmentsSnoc(
        stdoutFragments[..|stdoutFragments| - 1],
        nextOutcome.stdoutFragment
      );
      ConcatenateFragmentsSnoc(
        stderrFragments[..|stderrFragments| - 1],
        nextOutcome.stderrFragment
      );
      assert step.outcome ==
             Spec.MoveOutcome(stepOut, stepErr, stepError);
      FailureExistsSnoc(
        prefixOutcomes, nextOutcome, prefixError
      );
      assert hadError <==>
             exists j: nat :: j < |outcomes| && outcomes[j].failed;
      reveal BatchStepEvidenceFor();
      assert BatchStepEvidenceFor(
          source,
          directory,
          cmd,
          fsBeforeStep,
          preCwd,
          step.afterFs,
          step.outcome,
          step.outcome.stdoutFragment,
          step.outcome.stderrFragment,
          step
        );
      hide BatchStepEvidenceFor();
      assert forall j: nat | j < |steps| ::
          BatchStepEvidenceFor(
            sources[j],
            directory,
            cmd,
            fsBounds[j],
            preCwd,
            fsBounds[j + 1],
            outcomes[j],
            stdoutFragments[j],
            stderrFragments[j],
            steps[j]
          ) by {
        forall j: nat | j < |steps|
          ensures BatchStepEvidenceFor(
                    sources[j],
                    directory,
                    cmd,
                    fsBounds[j],
                    preCwd,
                    fsBounds[j + 1],
                    outcomes[j],
                    stdoutFragments[j],
                    stderrFragments[j],
                    steps[j]
                  )
        {
          if j < i {
            assert steps[j] == prefixSteps[j];
            assert fsBounds[j] == prefixFsBounds[j];
            assert fsBounds[j + 1] == prefixFsBounds[j + 1];
            assert outcomes[j] == prefixOutcomes[j];
            assert stdoutFragments[j] ==
                   prefixStdoutFragments[j];
            assert stderrFragments[j] ==
                   prefixStderrFragments[j];
          } else {
            assert j == i;
            assert sources[j] == source;
          }
        }
      }
      assert |steps| == i + 1;
      assert |fsBounds| == |steps| + 1;
      assert |outcomes| == |steps|;
      assert |stdoutFragments| == |steps|;
      assert |stderrFragments| == |steps|;
      assert fsBounds[0] == preFs;
      assert fsBounds[|fsBounds| - 1] == io.fs();
      assert Spec.ConcatenateFragments(
          stdoutFragments
        ) == out;
      assert Spec.ConcatenateFragments(
          stderrFragments
        ) == errOut;
      i := i + 1;
    }
    assert sources[..i] == sources;
    batch := BatchEvidence(
      steps,
      fsBounds,
      outcomes,
      stdoutFragments,
      stderrFragments
    );
    assert forall j: nat | j < |sources| ::
        BatchStepEvidenceFor(
          sources[j],
          directory,
          cmd,
          batch.fsBounds[j],
          preCwd,
          batch.fsBounds[j + 1],
          batch.outcomes[j],
          batch.stdoutFragments[j],
          batch.stderrFragments[j],
          batch.steps[j]
        );
    assert BatchEvidenceFor(
        sources, directory, cmd, preFs, preCwd, io.fs(),
        hadError, out, errOut, batch
      );
  }
}
