include "../../../core/World.dfy"
include "../Spec/MvPathSpec.dfy"
include "../Spec/MvSpec.dfy"
include "../Proof/MvMetadataProof.dfy"
include "../../../core/Errno.dfy"
include "../../../core/IO.dfy"
include "MvPathCore.dfy"
include "../Spec/MvSchema.dfy"

module MvCore {
  import MvPathSpec

  import Text = MvSpec
  import MetadataProof = MvMetadataProof
  datatype PlannedOutput = PlannedOutput(stdout: BenchWorld.Bytes, stderr: BenchWorld.Bytes, normalExit: int)

  import Errno = Errnos
  import BenchIO
  import IOContract
  import BenchWorld
  import BasenameCore = MvPathCore
  import DirnameCore = MvPathCore
  import Schema = MvSchema
  import Spec = MvSpec

  datatype SameFileDecision =
    | ContinueMove
    | RejectSameFile
    | FailedParentStat(path: string, err: int)

  datatype BackupCheckEvidence = BackupCheckEvidence(
    candidate: string,
    found: bool,
    err: int
  )

  ghost predicate StatusCallsFor(
    observations: Spec.NativeStatusInputs,
    first: nat,
    calls: seq<Spec.StatusCallEvidence>
  )
  {
    Spec.StatusCallsFor(observations, first, calls)
  }

  lemma StatusTranscriptWitness(inputs: Spec.NativeStatusInputs, first: nat, after: nat,
                                calls: seq<Spec.StatusCallEvidence>)
    requires after == first + |calls| && StatusCallsFor(inputs, first, calls)
    ensures exists transcript: seq<Spec.StatusCallEvidence> ::
              after == first + |transcript| && StatusCallsFor(inputs, first, transcript)
  {
  }

  lemma StatusCallsConcat(
    observations: Spec.NativeStatusInputs,
    first: nat,
    left: seq<Spec.StatusCallEvidence>,
    right: seq<Spec.StatusCallEvidence>
  )
    requires StatusCallsFor(observations, first, left)
    requires StatusCallsFor(observations, first + |left|, right)
    ensures StatusCallsFor(observations, first, left + right)
  {
    forall i: nat | i < |left + right|
      ensures IOContract.ObservedNativeFileStatusContractFields(
                observations.times, observations.failures, first + i, (left + right)[i].fs,
                (left + right)[i].path, (left + right)[i].followSymlink,
                (left + right)[i].ok, (left + right)[i].status,
                (left + right)[i].err
              )
    {
      if i >= |left| {
        assert first + i == first + |left| + (i - |left|);
      }
    }
  }

  lemma StatusCallsSnoc(
    observations: Spec.NativeStatusInputs,
    first: nat,
    calls: seq<Spec.StatusCallEvidence>,
    call: Spec.StatusCallEvidence
  )
    requires StatusCallsFor(observations, first, calls)
    requires IOContract.ObservedNativeFileStatusContractFields(
               observations.times, observations.failures, first + |calls|, call.fs, call.path,
               call.followSymlink, call.ok, call.status, call.err
             )
    ensures StatusCallsFor(observations, first, calls + [call])
  {
    StatusCallsConcat(observations, first, calls, [call]);
  }

  lemma StatusCallsAcrossEqualObservations(
    before: Spec.NativeStatusInputs,
    after: Spec.NativeStatusInputs,
    first: nat,
    calls: seq<Spec.StatusCallEvidence>
  )
    requires before == after
    requires StatusCallsFor(before, first, calls)
    ensures StatusCallsFor(after, first, calls)
  {
    hide StatusCallsFor;
  }

  lemma StatusCallsAtEqualOrdinal(
    observations: Spec.NativeStatusInputs,
    first: nat,
    equalFirst: nat,
    calls: seq<Spec.StatusCallEvidence>
  )
    requires first == equalFirst
    requires StatusCallsFor(observations, first, calls)
    ensures StatusCallsFor(observations, equalFirst, calls)
  {
    hide StatusCallsFor;
  }

  lemma {:isolate_assertions} StatusCallsAppendObservedStep(
    before: Spec.NativeStatusInputs,
    after: Spec.NativeStatusInputs,
    first: nat,
    prefix: seq<Spec.StatusCallEvidence>,
    step: StepEvidence
  )
    requires before == after
    requires StatusCallsFor(before, first, prefix)
    requires step.firstStatus == first + |prefix|
    requires StatusCallsFor(after, step.firstStatus, step.statusCalls)
    ensures StatusCallsFor(after, first, prefix + step.statusCalls)
  {
    hide *;
    StatusCallsAcrossEqualObservations(before, after, first, prefix);
    StatusCallsAtEqualOrdinal(
      after, step.firstStatus, first + |prefix|, step.statusCalls);
    StatusCallsConcat(after, first, prefix, step.statusCalls);
  }

  lemma StatusCallPrefixSlice(
    left: seq<Spec.StatusCallEvidence>,
    right: seq<Spec.StatusCallEvidence>,
    lo: nat,
    hi: nat
  )
    requires lo <= hi <= |left|
    ensures (left + right)[lo..hi] == left[lo..hi]
  {
  }

  lemma StatusCallTail(
    left: seq<Spec.StatusCallEvidence>,
    right: seq<Spec.StatusCallEvidence>
  )
    ensures (left + right)[|left|..] == right
  {
  }

  lemma StatusCallConsIndex(
    first: Spec.StatusCallEvidence,
    tail: seq<Spec.StatusCallEvidence>,
    i: nat
  )
    requires 1 <= i <= |tail|
    ensures ([first] + tail)[i] == tail[i - 1]
  {
    hide *;
    StatusCallTail([first], tail);
  }

  lemma {:isolate_assertions} StatusBoundsSnoc(
    first: nat,
    prefixCalls: seq<Spec.StatusCallEvidence>,
    prefixBounds: seq<nat>,
    prefixSteps: seq<StepEvidence>,
    step: StepEvidence,
    nextCalls: seq<Spec.StatusCallEvidence>,
    nextBounds: seq<nat>,
    nextSteps: seq<StepEvidence>
  )
    requires |prefixBounds| == |prefixSteps| + 1
    requires prefixBounds[|prefixSteps|] == first + |prefixCalls|
    requires forall j: nat {:trigger prefixBounds[j]} | j < |prefixSteps| ::
               first <= prefixBounds[j] <= prefixBounds[j + 1] <=
               first + |prefixCalls| &&
               prefixSteps[j].firstStatus == prefixBounds[j] &&
               prefixBounds[j + 1] ==
               prefixBounds[j] + |prefixSteps[j].statusCalls| &&
               prefixCalls[prefixBounds[j] - first ..
               prefixBounds[j + 1] - first] ==
               prefixSteps[j].statusCalls
    requires step.firstStatus == first + |prefixCalls|
    requires nextCalls == prefixCalls + step.statusCalls
    requires nextBounds == prefixBounds + [first + |nextCalls|]
    requires nextSteps == prefixSteps + [step]
    ensures forall j: nat {:trigger nextBounds[j]} | j < |nextSteps| ::
              first <= nextBounds[j] <= nextBounds[j + 1] <=
              first + |nextCalls| &&
              nextSteps[j].firstStatus == nextBounds[j] &&
              nextBounds[j + 1] ==
              nextBounds[j] + |nextSteps[j].statusCalls| &&
              nextCalls[nextBounds[j] - first ..
              nextBounds[j + 1] - first] ==
              nextSteps[j].statusCalls
  {
    hide *;
    StatusCallTail(prefixCalls, step.statusCalls);
    forall j: nat {:trigger nextBounds[j]} | j < |nextSteps|
      ensures first <= nextBounds[j] <= nextBounds[j + 1] <=
              first + |nextCalls| &&
              nextSteps[j].firstStatus == nextBounds[j] &&
              nextBounds[j + 1] ==
              nextBounds[j] + |nextSteps[j].statusCalls| &&
              nextCalls[nextBounds[j] - first ..
              nextBounds[j + 1] - first] ==
              nextSteps[j].statusCalls
    {
      if j < |prefixSteps| {
        assert nextBounds[j] == prefixBounds[j];
        assert nextBounds[j + 1] == prefixBounds[j + 1];
        assert nextSteps[j] == prefixSteps[j];
        assert prefixBounds[j + 1] <= first + |prefixCalls|;
        StatusCallPrefixSlice(
          prefixCalls, step.statusCalls,
          prefixBounds[j] - first,
          prefixBounds[j + 1] - first);
      } else {
        assert j == |prefixSteps|;
        assert nextBounds[j] == first + |prefixCalls|;
        assert nextCalls[|prefixCalls|..] == step.statusCalls;
      }
    }
  }

  lemma StatusCallsSlice(
    observations: Spec.NativeStatusInputs,
    first: nat,
    calls: seq<Spec.StatusCallEvidence>,
    lo: nat,
    hi: nat
  )
    requires StatusCallsFor(observations, first, calls)
    requires lo <= hi <= |calls|
    ensures StatusCallsFor(observations, first + lo, calls[lo..hi])
  {
    forall i: nat | i < |calls[lo..hi]|
      ensures IOContract.ObservedNativeFileStatusContractFields(
                observations.times, observations.failures, first + lo + i,
                calls[lo..hi][i].fs, calls[lo..hi][i].path,
                calls[lo..hi][i].followSymlink,
                calls[lo..hi][i].ok, calls[lo..hi][i].status,
                calls[lo..hi][i].err)
    {
      assert calls[lo..hi][i] == calls[lo + i];
    }
  }

  ghost function MetadataStatusCall(
    fs: BenchWorld.FileSystem,
    path: string,
    followSymlink: bool,
    evidence: MetadataEvidence
  ): Spec.StatusCallEvidence
  {
    Spec.StatusCallEvidence(
      fs, path, followSymlink, evidence.ok, evidence.rawStatus, evidence.err
    )
  }

  datatype MetadataEvidence = MetadataEvidence(
    ghost ordinal: nat,
    ghost rawStatus: BenchWorld.FileStatus,
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
        decision: SameFileDecision
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
    backupFs: BenchWorld.FileSystem,
    ghost firstStatus: nat,
    ghost statusCalls: seq<Spec.StatusCallEvidence>,
    ghost inputs: Spec.NativeStatusInputs
  )

  datatype BatchEvidence = BatchEvidence(
    steps: seq<StepEvidence>,
    fsBounds: seq<BenchWorld.FileSystem>,
    outcomes: seq<Spec.MoveOutcome>,
    stdoutFragments: seq<BenchWorld.Bytes>,
    stderrFragments: seq<BenchWorld.Bytes>,
    ghost firstStatus: nat,
    ghost statusCalls: seq<Spec.StatusCallEvidence>,
    ghost statusBounds: seq<nat>
  )

  datatype DirectoryStatusEvidence =
    | FailedDirectoryStatus(call: Spec.StatusCallEvidence)
    | SuccessfulDirectoryStatus(
        call: Spec.StatusCallEvidence,
        batch: BatchEvidence
      )

  datatype RunStatusEvidence =
    | NoRunStatus
    | DirectoryRunStatus(value: DirectoryStatusEvidence)
    | DirectMoveStatus(step: StepEvidence)
    | ProbedMoveStatus(call: Spec.StatusCallEvidence, step: StepEvidence)

  datatype StatusTranscript = StatusTranscript(
    first: nat,
    calls: seq<Spec.StatusCallEvidence>,
    inputs: Spec.NativeStatusInputs
  )

  ghost predicate BatchStatusEvidenceFor(
    observations: Spec.NativeStatusInputs,
    evidence: BatchEvidence
  )
  {
    |evidence.statusBounds| == |evidence.steps| + 1 &&
    evidence.statusBounds[0] == evidence.firstStatus &&
    evidence.statusBounds[|evidence.steps|] ==
    evidence.firstStatus + |evidence.statusCalls| &&
    StatusCallsFor(observations, evidence.firstStatus, evidence.statusCalls) &&
    forall i: nat {:trigger evidence.statusBounds[i]} | i < |evidence.steps| ::
      evidence.firstStatus <= evidence.statusBounds[i] <=
      evidence.statusBounds[i + 1] <=
      evidence.firstStatus + |evidence.statusCalls| &&
      evidence.steps[i].inputs == observations &&
      evidence.steps[i].firstStatus == evidence.statusBounds[i] &&
      evidence.statusBounds[i + 1] ==
      evidence.statusBounds[i] + |evidence.steps[i].statusCalls| &&
      evidence.statusCalls[
      evidence.statusBounds[i] - evidence.firstStatus ..
      evidence.statusBounds[i + 1] - evidence.firstStatus
      ] == evidence.steps[i].statusCalls
  }

  lemma PackageBatchStatusEvidence(
    observations: Spec.NativeStatusInputs,
    evidence: BatchEvidence
  )
    requires |evidence.statusBounds| == |evidence.steps| + 1
    requires evidence.statusBounds[0] == evidence.firstStatus
    requires evidence.statusBounds[|evidence.steps|] ==
             evidence.firstStatus + |evidence.statusCalls|
    requires StatusCallsFor(observations, evidence.firstStatus,
                            evidence.statusCalls)
    requires forall i: nat {:trigger evidence.statusBounds[i]} | i < |evidence.steps| ::
               evidence.firstStatus <= evidence.statusBounds[i] <=
               evidence.statusBounds[i + 1] <=
               evidence.firstStatus + |evidence.statusCalls| &&
               evidence.steps[i].firstStatus == evidence.statusBounds[i] &&
               evidence.statusBounds[i + 1] ==
               evidence.statusBounds[i] + |evidence.steps[i].statusCalls| &&
               evidence.statusCalls[
               evidence.statusBounds[i] - evidence.firstStatus ..
               evidence.statusBounds[i + 1] - evidence.firstStatus
               ] == evidence.steps[i].statusCalls
    requires forall i: nat | i < |evidence.steps| :: evidence.steps[i].inputs == observations
    ensures BatchStatusEvidenceFor(observations, evidence)
  {
  }

  lemma {:induction false} BatchStatusEvidenceFromParts(
    observations: Spec.NativeStatusInputs,
    first: nat,
    calls: seq<Spec.StatusCallEvidence>,
    bounds: seq<nat>,
    steps: seq<StepEvidence>,
    fsBounds: seq<BenchWorld.FileSystem>,
    outcomes: seq<Spec.MoveOutcome>,
    stdoutFragments: seq<BenchWorld.Bytes>,
    stderrFragments: seq<BenchWorld.Bytes>
  )
    requires |bounds| == |steps| + 1
    requires bounds[0] == first
    requires bounds[|steps|] == first + |calls|
    requires StatusCallsFor(observations, first, calls)
    requires forall i: nat {:trigger bounds[i]} | i < |steps| ::
               first <= bounds[i] <= bounds[i + 1] <= first + |calls| &&
               steps[i].firstStatus == bounds[i] &&
               bounds[i + 1] == bounds[i] + |steps[i].statusCalls| &&
               calls[bounds[i] - first .. bounds[i + 1] - first] ==
               steps[i].statusCalls
    requires forall i: nat | i < |steps| :: steps[i].inputs == observations
    ensures BatchStatusEvidenceFor(
              observations,
              BatchEvidence(steps, fsBounds, outcomes, stdoutFragments,
                            stderrFragments, first, calls, bounds))
  {
    hide *;
    var evidence := BatchEvidence(steps, fsBounds, outcomes,
                                  stdoutFragments, stderrFragments, first, calls, bounds);
    assert forall i: nat {:trigger evidence.statusBounds[i]} | i < |evidence.steps| ::
        evidence.firstStatus <= evidence.statusBounds[i] <=
        evidence.statusBounds[i + 1] <=
        evidence.firstStatus + |evidence.statusCalls| &&
        evidence.steps[i].firstStatus == evidence.statusBounds[i] &&
        evidence.statusBounds[i + 1] ==
        evidence.statusBounds[i] + |evidence.steps[i].statusCalls| &&
        evidence.statusCalls[
        evidence.statusBounds[i] - evidence.firstStatus ..
        evidence.statusBounds[i + 1] - evidence.firstStatus
        ] == evidence.steps[i].statusCalls by {
      forall i: nat {:trigger evidence.statusBounds[i]} | i < |evidence.steps|
        ensures evidence.firstStatus <= evidence.statusBounds[i] <=
                evidence.statusBounds[i + 1] <=
                evidence.firstStatus + |evidence.statusCalls| &&
                evidence.steps[i].firstStatus == evidence.statusBounds[i] &&
                evidence.statusBounds[i + 1] ==
                evidence.statusBounds[i] + |evidence.steps[i].statusCalls| &&
                evidence.statusCalls[
                evidence.statusBounds[i] - evidence.firstStatus ..
                evidence.statusBounds[i + 1] - evidence.firstStatus
                ] == evidence.steps[i].statusCalls
      {
        assert bounds[i] == evidence.statusBounds[i];
        assert bounds[i + 1] == evidence.statusBounds[i + 1];
        assert steps[i] == evidence.steps[i];
        assert calls[bounds[i] - first .. bounds[i + 1] - first] ==
               steps[i].statusCalls;
      }
    }
    PackageBatchStatusEvidence(observations, evidence);
  }

  ghost predicate BatchMoveStatusEvidenceFor(
    sources: seq<string>,
    directory: string,
    cmd: Schema.MvCmd,
    observations: Spec.NativeStatusInputs,
    evidence: BatchEvidence
  )
  {
    BatchStatusEvidenceFor(observations, evidence) &&
    |evidence.steps| == |sources| &&
    (forall i: nat | i < |sources| ::
       var normalizedSource :=
         Spec.NormalizeSourceSpec(sources[i], cmd.stripTrailingSlashes);
       StepStatusEvidenceFor(
         normalizedSource,
         Spec.TargetInDirectorySpec(directory, normalizedSource),
         cmd,
         evidence.steps[i]
       ))
  }

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
    backupFs: BenchWorld.FileSystem,
    transcript: StatusTranscript
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
      backupFs,
      transcript.first,
      transcript.calls,
      transcript.inputs
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
    evidence.times.atimeSec == evidence.rawStatus.times.atimeSec &&
    evidence.times.atimeNsec == evidence.rawStatus.times.atimeNsec &&
    evidence.times.mtimeSec == evidence.rawStatus.times.mtimeSec &&
    evidence.times.mtimeNsec == evidence.rawStatus.times.mtimeNsec &&
    (evidence.ok ==>
       evidence.key == evidence.rawStatus.hostKey &&
       evidence.isDir == (evidence.rawStatus.kind == BenchWorld.DirectoryKind) &&
       evidence.isSymlink == (evidence.rawStatus.kind == BenchWorld.SymlinkKind) &&
       MetadataLinkCountValue(evidence) == evidence.rawStatus.linkCount) &&
    IOContract.FileStatusStructureContractFields(fs, path, followSymlink,
                                                 evidence.ok, evidence.rawStatus, evidence.err) &&
    if evidence.ok then
      match IOContract.GetFileStatusResultFields(fs, path, followSymlink)
      case Ok(expected) =>
        evidence.ok && evidence.err == 0 &&
        evidence.key == expected.hostKey &&
        evidence.links.LinkCountKnown? &&
        MetadataLinkCountValue(evidence) == expected.linkCount &&
        evidence.isDir == (expected.kind == BenchWorld.DirectoryKind) &&
        evidence.isSymlink == (expected.kind == BenchWorld.SymlinkKind)
      case Err(_) => false
    else evidence.err > 0
  }

  ghost predicate ObservedMetadataEvidenceFor(
    observations: Spec.NativeStatusInputs,
    fs: BenchWorld.FileSystem,
    path: string,
    followSymlink: bool,
    evidence: MetadataEvidence
  )
  {
    MetadataEvidenceFor(fs, path, followSymlink, evidence) &&
    var status := evidence.rawStatus;
    IOContract.ObservedNativeFileStatusContractFields(
      observations.times, observations.failures, evidence.ordinal, fs, path, followSymlink,
      evidence.ok, status, evidence.err
    ) &&
    (evidence.ok ==>
       evidence.key == status.hostKey &&
       evidence.isDir == (status.kind == BenchWorld.DirectoryKind) &&
       evidence.isSymlink == (status.kind == BenchWorld.SymlinkKind) &&
       MetadataLinkCountValue(evidence) == status.linkCount &&
       evidence.times.atimeSec == status.times.atimeSec &&
       evidence.times.atimeNsec == status.times.atimeNsec &&
       evidence.times.mtimeSec == status.times.mtimeSec &&
       evidence.times.mtimeNsec == status.times.mtimeNsec)
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
      (if sourceEntry.leaf == targetEntry.leaf &&
          (!sourceEntry.parentMetadata.ok || !targetEntry.parentMetadata.ok) then
         sourceFollowed == NoMetadataEvidence &&
         sourceReferentEntry == NoEntryNameEvidence &&
         decision == FailedParentStat(
           if !sourceEntry.parentMetadata.ok then sourceEntry.parent else targetEntry.parent,
           if !sourceEntry.parentMetadata.ok then sourceEntry.parentMetadata.err else targetEntry.parentMetadata.err)
       else (if sourceMetadata.isSymlink then
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
            if sourceReferentEntry.SomeEntryNameEvidence? &&
               sourceReferentEntry.value.leaf == targetEntry.leaf &&
               (!sourceReferentEntry.value.parentMetadata.ok || !targetEntry.parentMetadata.ok) then
              FailedParentStat(
                if !sourceReferentEntry.value.parentMetadata.ok then sourceReferentEntry.value.parent else targetEntry.parent,
                if !sourceReferentEntry.value.parentMetadata.ok then sourceReferentEntry.value.parentMetadata.err else targetEntry.parentMetadata.err)
            else if EvidenceNamesSame(sourceEntry, targetEntry) ||
                    (cmd.backupMode == Schema.BackupOff &&
                     ((sourceMetadata.ok &&
                       targetMetadata.ok &&
                       sourceMetadata.key == targetMetadata.key) ||
                      ReferentEvidenceNamesTarget(
                        sourceReferentEntry, targetEntry
                      )))
            then RejectSameFile
            else ContinueMove)
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
    decision: SameFileDecision
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
    requires sourceEntry.leaf == targetEntry.leaf ==>
               sourceEntry.parentMetadata.ok && targetEntry.parentMetadata.ok
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
             if sourceReferentEntry.SomeEntryNameEvidence? &&
                sourceReferentEntry.value.leaf == targetEntry.leaf &&
                (!sourceReferentEntry.value.parentMetadata.ok || !targetEntry.parentMetadata.ok) then
               FailedParentStat(
                 if !sourceReferentEntry.value.parentMetadata.ok then sourceReferentEntry.value.parent else targetEntry.parent,
                 if !sourceReferentEntry.value.parentMetadata.ok then sourceReferentEntry.value.parentMetadata.err else targetEntry.parentMetadata.err)
             else if EvidenceNamesSame(sourceEntry, targetEntry) ||
                     (cmd.backupMode == Schema.BackupOff &&
                      ((sourceMetadata.ok &&
                        targetMetadata.ok &&
                        sourceMetadata.key == targetMetadata.key) ||
                       ReferentEvidenceNamesTarget(
                         sourceReferentEntry, targetEntry
                       )))
             then RejectSameFile
             else ContinueMove
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
          MvPathSpec.SimpleBackupPathSpec(target, cmd.backupSuffix),
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
       checks[i].candidate == MvPathSpec.NumberedBackupPathSpec(target, start + i) &&
       Spec.StatusExistsOutcomeFields(
         fs,
         checks[i].candidate,
         false,
         checks[i].found,
         checks[i].err
       )) &&
    (forall i: nat | i + 1 < |checks| :: checks[i].found) &&
    !checks[|checks| - 1].found
  }

  ghost predicate BackupStatusSuffixFor(
    backupMode: Schema.BackupMode,
    fs: BenchWorld.FileSystem,
    target: string,
    calls: seq<Spec.StatusCallEvidence>
  )
  {
    if backupMode == Schema.BackupOff || backupMode == Schema.BackupSimple then
      |calls| == 0
    else if backupMode == Schema.BackupExisting then
      |calls| >= 1 &&
      Spec.StatusRequest(calls[0], fs, MvPathSpec.NumberedBackupPathSpec(target, 1), false) &&
      (if !calls[0].ok then
         |calls| == 1
       else
         |calls| >= 2 &&
         (forall i: nat | 1 <= i < |calls| ::
            Spec.StatusRequest(calls[i], fs, MvPathSpec.NumberedBackupPathSpec(target, i), false)) &&
         (forall i: nat | 1 <= i + 1 < |calls| :: calls[i].ok) &&
         !calls[|calls| - 1].ok)
    else
      |calls| >= 1 &&
      (forall i: nat | i < |calls| ::
         Spec.StatusRequest(calls[i], fs, MvPathSpec.NumberedBackupPathSpec(target, i + 1), false)) &&
      (forall i: nat | i + 1 < |calls| :: calls[i].ok) &&
      !calls[|calls| - 1].ok
  }

  ghost predicate BackupSelectionFromStatusCallsFor(
    backupMode: Schema.BackupMode, suffix: string, fs: BenchWorld.FileSystem,
    target: string, evidence: BackupSelectionEvidence, calls: seq<Spec.StatusCallEvidence>
  )
  {
    BackupStatusSuffixFor(backupMode, fs, target, calls) &&
    (if backupMode == Schema.BackupOff then evidence == NoBackupSelection
     else evidence.SelectedBackup? &&
          (if backupMode == Schema.BackupSimple ||
              (backupMode == Schema.BackupExisting && !calls[0].ok) then
             evidence.backupPath == MvPathSpec.SimpleBackupPathSpec(target, suffix)
           else if backupMode == Schema.BackupExisting then
             |calls| >= 2 && evidence.backupPath == MvPathSpec.NumberedBackupPathSpec(target, |calls| - 1)
           else |calls| >= 1 && evidence.backupPath == MvPathSpec.NumberedBackupPathSpec(target, |calls|)))
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
        backupPath == MvPathSpec.SimpleBackupPathSpec(target, suffix) &&
        |checks| == 0 &&
        !existingFirstCheckCalled
      else if backupMode == Schema.BackupExisting then
        existingFirstCheckCalled &&
        Spec.StatusExistsOutcomeFields(
          fs,
          MvPathSpec.NumberedBackupPathSpec(target, 1),
          false,
          existingFirstFound,
          existingFirstErr
        ) &&
        if existingFirstFound then
          BackupChecksFor(target, 1, fs, checks) &&
          backupPath == checks[|checks| - 1].candidate
        else
          |checks| == 0 &&
          backupPath == MvPathSpec.SimpleBackupPathSpec(target, suffix)
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
    targetWasFound: bool,
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
          Text.StepSuccessStdoutSpec(source, target, "", verbose, debug), [], false
        )
      else
        outcome == Spec.MoveOutcome(
          [],
          Spec.SourceRenameFailureMessageSpec(
            source,
            target,
            Spec.SourceRenameDiagnosticErrSpec(
              target, sourceIsDir, calls[0].err
            ),
            sourceIsDir && targetWasFound
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
            Text.StepSuccessStdoutSpec(
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
              Spec.SourceRenameDiagnosticErrSpec(
                target, sourceIsDir, calls[1].err
              ),
              false
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
          evidence.targetFound,
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

  ghost predicate SourceResolutionObservationFor(
    source: string, cwd: BenchWorld.Path, step: StepEvidence
  )
  {
    if step.sameFile.CheckedSameFile? && step.sameFile.source.isSymlink &&
       (!step.sameFile.decision.FailedParentStat? || step.sameFile.sourceReferentEntry.SomeEntryNameEvidence?) then
      match step.sameFile.sourceReferentEntry
      case FailedEntryNameEvidence(err) =>
        IOContract.ResolvePathIdentitySpec(step.beforeFs, cwd, step.inputs.failures,
                                           source, false, "", err)
      case SomeEntryNameEvidence(path, _) =>
        IOContract.ResolvePathIdentitySpec(step.beforeFs, cwd, step.inputs.failures,
                                           source, true, path, 0)
      case NoEntryNameEvidence => false
    else true
  }

  ghost predicate RenameNativeObservationsFor(
    source: string, target: string, step: StepEvidence
  )
  {
    |step.renames| <= 2 &&
    (if |step.renames| == 0 then true
     else if step.backup.NoBackupSelection? then
       |step.renames| == 1 &&
       IOContract.RenamePathSpec(step.beforeFs, step.inputs.now, step.inputs.failures,
                                 step.renames[0].afterFs, source, target, step.renames[0].ok, step.renames[0].err)
     else
       IOContract.RenamePathSpec(step.beforeFs, step.inputs.now, step.inputs.failures,
                                 step.renames[0].afterFs, target, step.backup.backupPath,
                                 step.renames[0].ok, step.renames[0].err) &&
       (|step.renames| == 2 ==>
          IOContract.RenamePathSpec(step.renames[0].afterFs, step.inputs.now, step.inputs.failures,
                                    step.renames[1].afterFs, source, target, step.renames[1].ok, step.renames[1].err)))
  }

  opaque ghost predicate StepEvidenceFor(
    source: string,
    target: string,
    cmd: Schema.MvCmd,
    preCwd: BenchWorld.Path,
    evidence: StepEvidence
  )
  {
    StatusCallsFor(evidence.inputs, evidence.firstStatus, evidence.statusCalls) &&
    StepStatusEvidenceFor(source, target, cmd, evidence) &&
    SourceResolutionObservationFor(source, preCwd, evidence) &&
    RenameNativeObservationsFor(source, target, evidence) &&
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
      Spec.StatusExistsOutcomeFields(
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
         )
       else if cmd.overwriteMode == Schema.OverwriteSkip then
         evidence.sameFile == NoSameFileCheck &&
         evidence.backup == NoBackupSelection &&
         |evidence.renames| == 0 &&
         evidence.afterFs == evidence.beforeFs &&
         evidence.outcome ==
         Spec.MoveOutcome(Text.SkipStdoutSpec(target, cmd.debug), [], false)
       else if cmd.updateMode == Schema.UpdateNone then
         evidence.sameFile == NoSameFileCheck &&
         evidence.backup == NoBackupSelection &&
         |evidence.renames| == 0 &&
         evidence.afterFs == evidence.beforeFs &&
         evidence.outcome ==
         Spec.MoveOutcome(Text.SkipStdoutSpec(target, cmd.debug), [], false)
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
           if decision.FailedParentStat? then
             evidence.backup == NoBackupSelection && |evidence.renames| == 0 &&
             evidence.afterFs == evidence.beforeFs &&
             evidence.outcome == Spec.MoveOutcome([], Spec.ParentStatFailureMessageSpec(
                                                    decision.path, decision.err), true)
           else if decision == RejectSameFile then
             evidence.backup == NoBackupSelection &&
             |evidence.renames| == 0 &&
             evidence.afterFs == evidence.beforeFs &&
             evidence.outcome == Spec.MoveOutcome(
               [], Spec.SameFileMessageSpec(source, target), true
             )
           else if cmd.updateMode == Schema.UpdateOlder then
             if !Spec.SourceNewerSpec(
                  sourceMetadata.times.mtimeSec,
                  sourceMetadata.times.mtimeNsec,
                  targetMetadata.times.mtimeSec,
                  targetMetadata.times.mtimeNsec
                ) then
               evidence.backup == NoBackupSelection &&
               |evidence.renames| == 0 &&
               evidence.afterFs == evidence.beforeFs &&
               evidence.outcome ==
               Spec.MoveOutcome(Text.SkipStdoutSpec(target, cmd.debug), [], false)
             else
               ExistingTargetRenameEvidenceFor(
                 source, target, cmd, preCwd, evidence
               )
           else
             ExistingTargetRenameEvidenceFor(
               source, target, cmd, preCwd, evidence
             ))
  }

  ghost predicate StepStatusEvidenceFor(
    source: string,
    target: string,
    cmd: Schema.MvCmd,
    evidence: StepEvidence
  )
  {
    var fs := evidence.beforeFs;
    var calls := evidence.statusCalls;
    |calls| >= 1 &&
    Spec.StatusRequest(calls[0], fs, source, false) &&
    calls[0].ok == evidence.sourceOk &&
    calls[0].err == evidence.sourceErr &&
    (evidence.sourceOk ==> evidence.sourceIsDir ==
                           (calls[0].status.kind == BenchWorld.DirectoryKind)) &&
    (if !evidence.sourceOk then
       |calls| == 1
     else
       |calls| >= 2 &&
       Spec.StatusRequest(calls[1], fs, target, false) &&
       calls[1].ok == evidence.targetFound &&
       calls[1].err == evidence.targetExistsErr &&
       (if !evidence.targetFound ||
           cmd.overwriteMode == Schema.OverwriteSkip ||
           cmd.updateMode == Schema.UpdateNone ||
           cmd.updateMode == Schema.UpdateNoneFail then
          |calls| == 2
        else
          match evidence.sameFile
          case NoSameFileCheck => false
          case CheckedSameFile(
            sourceMetadata, targetMetadata, sourceFollowed,
            sourceEntry, targetEntry, sourceReferentEntry,
            collision, decision
            ) =>
            |calls| >= 4 &&
            calls[0] == MetadataStatusCall(fs, source, false, sourceMetadata) &&
            calls[1] == MetadataStatusCall(fs, target, false, targetMetadata) &&
            calls[2] == MetadataStatusCall(
              fs, sourceEntry.parent, false, sourceEntry.parentMetadata
            ) &&
            calls[3] == MetadataStatusCall(
              fs, targetEntry.parent, false, targetEntry.parentMetadata
            ) &&
            (if decision.FailedParentStat? && sourceReferentEntry.NoEntryNameEvidence? then
               |calls| == 4
             else var afterEntries :=
                    if sourceMetadata.isSymlink then
                      (if sourceReferentEntry.SomeEntryNameEvidence? then 6 else 5)
                    else 4;
                  (if sourceMetadata.isSymlink then
                     |calls| >= 5 &&
                     (match sourceFollowed
                      case SomeMetadataEvidence(followed) =>
                        calls[4] == MetadataStatusCall(fs, source, true, followed)
                      case _ => false) &&
                     (match sourceReferentEntry
                      case SomeEntryNameEvidence(resolvedPath, referentEntry) =>
                        |calls| >= 6 &&
                        calls[5] == MetadataStatusCall(
                          fs, referentEntry.parent, false,
                          referentEntry.parentMetadata
                        )
                      case FailedEntryNameEvidence(_) => true
                      case NoEntryNameEvidence => false)
                   else
                     true) &&
                  (if decision.FailedParentStat? || decision == RejectSameFile ||
                      (cmd.updateMode == Schema.UpdateOlder &&
                       !Spec.SourceNewerSpec(
                         sourceMetadata.times.mtimeSec,
                         sourceMetadata.times.mtimeNsec,
                         targetMetadata.times.mtimeSec,
                         targetMetadata.times.mtimeNsec
                       )) then
                     |calls| == afterEntries
                   else
                     var collisionNeeded :=
                       (cmd.backupMode == Schema.BackupSimple ||
                        cmd.backupMode == Schema.BackupExisting) &&
                       sourceEntry.leaf == targetEntry.leaf + cmd.backupSuffix;
                     var afterCollision := afterEntries +
                                           (if collisionNeeded then 1 else 0);
                     afterCollision <= |calls| &&
                     (collisionNeeded ==>
                        (match collision
                         case CheckedBackupCollision(_, candidate) =>
                           calls[afterEntries] == MetadataStatusCall(
                             fs, MvPathSpec.SimpleBackupPathSpec(target, cmd.backupSuffix),
                             true, candidate
                           )
                         case _ => false)) &&
                     (if BackupCollisionDetected(collision) then
                        |calls| == afterCollision
                      else
                        BackupSelectionFromStatusCallsFor(
                          cmd.backupMode, cmd.backupSuffix, fs, target,
                          evidence.backup, calls[afterCollision..]
                        ))))))
  }

  lemma StepStatusEvidenceTransfer(
    source: string,
    target: string,
    cmd: Schema.MvCmd,
    from: StepEvidence,
    to: StepEvidence
  )
    requires StepStatusEvidenceFor(source, target, cmd, from)
    requires to.beforeFs == from.beforeFs
    requires to.sourceOk == from.sourceOk
    requires to.sourceIsDir == from.sourceIsDir
    requires to.sourceErr == from.sourceErr
    requires to.targetFound == from.targetFound
    requires to.targetExistsErr == from.targetExistsErr
    requires to.sameFile == from.sameFile
    requires to.backup == from.backup
    requires to.statusCalls == from.statusCalls
    ensures StepStatusEvidenceFor(source, target, cmd, to)
  {
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
    requires StatusCallsFor(evidence.inputs, evidence.firstStatus, evidence.statusCalls)
    requires StepStatusEvidenceFor(source, target, cmd, evidence)
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
    requires Spec.StatusExistsOutcomeFields(
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
             )
    requires RenameNativeObservationsFor(source, target, evidence)
    requires StatusCallsFor(evidence.inputs, evidence.firstStatus, evidence.statusCalls)
    requires StepStatusEvidenceFor(source, target, cmd, evidence)
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
    requires Spec.StatusExistsOutcomeFields(
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
             Spec.MoveOutcome(Text.SkipStdoutSpec(target, cmd.debug), [], false)
    requires StatusCallsFor(evidence.inputs, evidence.firstStatus, evidence.statusCalls)
    requires StepStatusEvidenceFor(source, target, cmd, evidence)
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
    requires Spec.StatusExistsOutcomeFields(
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
             Spec.MoveOutcome(Text.SkipStdoutSpec(target, cmd.debug), [], false)
    requires StatusCallsFor(evidence.inputs, evidence.firstStatus, evidence.statusCalls)
    requires StepStatusEvidenceFor(source, target, cmd, evidence)
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
    requires Spec.StatusExistsOutcomeFields(
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
    requires StatusCallsFor(evidence.inputs, evidence.firstStatus, evidence.statusCalls)
    requires StepStatusEvidenceFor(source, target, cmd, evidence)
    ensures StepEvidenceFor(source, target, cmd, preCwd, evidence)
  {
    reveal StepEvidenceFor();
  }

  lemma PackageParentMetadataFailureStep(
    source: string, target: string, cmd: Schema.MvCmd, cwd: BenchWorld.Path,
    sourceMetadata: MetadataEvidence, targetMetadata: MetadataEvidence,
    sourceEntry: EntryNameEvidence, targetEntry: EntryNameEvidence,
    step: StepEvidence
  )
    requires MetadataEvidenceFor(step.beforeFs, source, false, sourceMetadata) && sourceMetadata.ok
    requires MetadataEvidenceFor(step.beforeFs, target, false, targetMetadata) && targetMetadata.ok
    requires EntryNameEvidenceFor(step.beforeFs, source, sourceEntry)
    requires EntryNameEvidenceFor(step.beforeFs, target, targetEntry)
    requires sourceEntry.leaf == targetEntry.leaf
    requires !sourceEntry.parentMetadata.ok || !targetEntry.parentMetadata.ok
    requires step.sourceOk && step.targetExistsCalled && step.targetFound
    requires IOContract.IsDirectoryStrictContractFields(step.beforeFs, source, false,
                                                        step.sourceOk, step.sourceIsDir, step.sourceErr)
    requires Spec.StatusExistsOutcomeFields(step.beforeFs, target, false, true, step.targetExistsErr)
    requires cmd.overwriteMode != Schema.OverwriteSkip && cmd.updateMode != Schema.UpdateNone &&
             cmd.updateMode != Schema.UpdateNoneFail
    requires step.sameFile == CheckedSameFile(sourceMetadata, targetMetadata, NoMetadataEvidence,
                                              sourceEntry, targetEntry, NoEntryNameEvidence, NoBackupCollisionCheck,
                                              FailedParentStat(
                                                if !sourceEntry.parentMetadata.ok then sourceEntry.parent else targetEntry.parent,
                                                if !sourceEntry.parentMetadata.ok then sourceEntry.parentMetadata.err else targetEntry.parentMetadata.err))
    requires step.backup == NoBackupSelection && step.renames == [] && step.afterFs == step.beforeFs
    requires step.outcome == Spec.MoveOutcome([], Spec.ParentStatFailureMessageSpec(
                                                step.sameFile.decision.path, step.sameFile.decision.err), true)
    requires StatusCallsFor(step.inputs, step.firstStatus, step.statusCalls)
    requires StepStatusEvidenceFor(source, target, cmd, step)
    ensures StepEvidenceFor(source, target, cmd, cwd, step)
  {
    reveal StepEvidenceFor();
    reveal SameFileEvidenceFor();
  }

  lemma PackageReferentParentFailureStep(
    source: string, target: string, cmd: Schema.MvCmd, cwd: BenchWorld.Path,
    step: StepEvidence
  )
    requires IOContract.IsDirectoryStrictContractFields(step.beforeFs, source, false,
                                                        step.sourceOk, step.sourceIsDir, step.sourceErr)
    requires step.sourceOk && step.targetExistsCalled && step.targetFound
    requires Spec.StatusExistsOutcomeFields(step.beforeFs, target, false, true, step.targetExistsErr)
    requires cmd.overwriteMode != Schema.OverwriteSkip && cmd.updateMode != Schema.UpdateNone &&
             cmd.updateMode != Schema.UpdateNoneFail
    requires SameFileEvidenceFor(cmd, step.beforeFs, cwd, source, target, step.sameFile)
    requires step.sameFile.CheckedSameFile? && step.sameFile.decision.FailedParentStat?
    requires step.sameFile.sourceReferentEntry.SomeEntryNameEvidence?
    requires step.backup == NoBackupSelection && step.renames == [] && step.afterFs == step.beforeFs
    requires step.outcome == Spec.MoveOutcome([], Spec.ParentStatFailureMessageSpec(
                                                step.sameFile.decision.path, step.sameFile.decision.err), true)
    requires StatusCallsFor(step.inputs, step.firstStatus, step.statusCalls)
    requires StepStatusEvidenceFor(source, target, cmd, step)
    requires SourceResolutionObservationFor(source, cwd, step)
    ensures StepEvidenceFor(source, target, cmd, cwd, step)
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
    requires Spec.StatusExistsOutcomeFields(
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
    requires evidence.sameFile.decision == RejectSameFile
    requires evidence.backup == NoBackupSelection
    requires |evidence.renames| == 0
    requires evidence.afterFs == evidence.beforeFs
    requires evidence.outcome ==
             Spec.MoveOutcome([], Spec.SameFileMessageSpec(source, target), true)
    requires SourceResolutionObservationFor(source, preCwd, evidence)
    requires StatusCallsFor(evidence.inputs, evidence.firstStatus, evidence.statusCalls)
    requires StepStatusEvidenceFor(source, target, cmd, evidence)
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
    requires Spec.StatusExistsOutcomeFields(
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
    requires evidence.sameFile.decision == ContinueMove
    requires !Spec.SourceNewerSpec(
               evidence.sameFile.source.times.mtimeSec,
               evidence.sameFile.source.times.mtimeNsec,
               evidence.sameFile.target.times.mtimeSec,
               evidence.sameFile.target.times.mtimeNsec
             )
    requires evidence.backup == NoBackupSelection
    requires |evidence.renames| == 0
    requires evidence.afterFs == evidence.beforeFs
    requires evidence.outcome ==
             Spec.MoveOutcome(Text.SkipStdoutSpec(target, cmd.debug), [], false)
    requires SourceResolutionObservationFor(source, preCwd, evidence)
    requires StatusCallsFor(evidence.inputs, evidence.firstStatus, evidence.statusCalls)
    requires StepStatusEvidenceFor(source, target, cmd, evidence)
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
    requires Spec.StatusExistsOutcomeFields(
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
    requires evidence.sameFile.decision == ContinueMove
    requires cmd.updateMode != Schema.UpdateOlder ||
             Spec.SourceNewerSpec(
               evidence.sameFile.source.times.mtimeSec,
               evidence.sameFile.source.times.mtimeNsec,
               evidence.sameFile.target.times.mtimeSec,
               evidence.sameFile.target.times.mtimeNsec
             )
    requires ExistingTargetRenameEvidenceFor(
               source, target, cmd, preCwd, evidence
             )
    requires SourceResolutionObservationFor(source, preCwd, evidence)
    requires RenameNativeObservationsFor(source, target, evidence)
    requires StatusCallsFor(evidence.inputs, evidence.firstStatus, evidence.statusCalls)
    requires StepStatusEvidenceFor(source, target, cmd, evidence)
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
      Spec.NormalizeSourceSpec(source, cmd.stripTrailingSlashes);
    StepEvidenceFor(
      normalizedSource,
      Spec.TargetInDirectorySpec(directory, normalizedSource),
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

  lemma {:isolate_assertions} PackageBatchEvidenceFor(
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
    requires |evidence.steps| == |sources|
    requires |evidence.fsBounds| == |sources| + 1
    requires |evidence.outcomes| == |sources|
    requires |evidence.stdoutFragments| == |sources|
    requires |evidence.stderrFragments| == |sources|
    requires evidence.fsBounds[0] == beforeFs
    requires evidence.fsBounds[|evidence.fsBounds| - 1] == afterFs
    requires forall i: nat | i < |sources| ::
               BatchStepEvidenceFor(
                 sources[i], directory, cmd,
                 evidence.fsBounds[i], preCwd, evidence.fsBounds[i + 1],
                 evidence.outcomes[i], evidence.stdoutFragments[i],
                 evidence.stderrFragments[i], evidence.steps[i])
    requires Spec.ConcatenateFragments(evidence.stdoutFragments) == out
    requires Spec.ConcatenateFragments(evidence.stderrFragments) == err
    requires hadError <==>
             exists i: nat ::
               i < |evidence.outcomes| && evidence.outcomes[i].failed
    ensures BatchEvidenceFor(
              sources, directory, cmd, beforeFs, preCwd, afterFs,
              hadError, out, err, evidence)
  {
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

  lemma AppendBatchEvidence(
    sources: seq<string>,
    source: string,
    directory: string,
    cmd: Schema.MvCmd,
    beforeFs: BenchWorld.FileSystem,
    cwd: BenchWorld.Path,
    prefixError: bool,
    prefixOut: BenchWorld.Bytes,
    prefixErr: BenchWorld.Bytes,
    inputs: Spec.NativeStatusInputs,
    prefix: BatchEvidence,
    step: StepEvidence
  ) returns (next: BatchEvidence)
    requires BatchEvidenceFor(sources, directory, cmd, beforeFs, cwd, step.beforeFs,
                              prefixError, prefixOut, prefixErr, prefix)
    requires BatchMoveStatusEvidenceFor(sources, directory, cmd, inputs, prefix)
    requires StepEvidenceFor(Spec.NormalizeSourceSpec(source, cmd.stripTrailingSlashes),
                             Spec.TargetInDirectorySpec(directory, Spec.NormalizeSourceSpec(source, cmd.stripTrailingSlashes)), cmd, cwd, step)
    requires StepStatusEvidenceFor(Spec.NormalizeSourceSpec(source, cmd.stripTrailingSlashes),
                                   Spec.TargetInDirectorySpec(directory, Spec.NormalizeSourceSpec(source, cmd.stripTrailingSlashes)), cmd, step)
    requires step.inputs == inputs
    requires step.firstStatus == prefix.firstStatus + |prefix.statusCalls|
    requires StatusCallsFor(inputs, step.firstStatus, step.statusCalls)
    ensures BatchEvidenceFor(sources + [source], directory, cmd, beforeFs, cwd, step.afterFs,
                             prefixError || step.outcome.failed, prefixOut + step.outcome.stdoutFragment,
                             prefixErr + step.outcome.stderrFragment, next)
    ensures BatchMoveStatusEvidenceFor(sources + [source], directory, cmd, inputs, next)
    ensures next.firstStatus == prefix.firstStatus
    ensures next.statusCalls == prefix.statusCalls + step.statusCalls
  {
    hide *;
    reveal BatchEvidenceFor(), BatchMoveStatusEvidenceFor(), BatchStatusEvidenceFor();
    next := BatchEvidence(prefix.steps + [step], prefix.fsBounds + [step.afterFs],
                          prefix.outcomes + [step.outcome], prefix.stdoutFragments + [step.outcome.stdoutFragment],
                          prefix.stderrFragments + [step.outcome.stderrFragment], prefix.firstStatus,
                          prefix.statusCalls + step.statusCalls,
                          prefix.statusBounds + [prefix.firstStatus + |prefix.statusCalls + step.statusCalls|]);
    StatusCallsConcat(inputs, prefix.firstStatus, prefix.statusCalls, step.statusCalls);
    StatusBoundsSnoc(prefix.firstStatus, prefix.statusCalls, prefix.statusBounds,
                     prefix.steps, step, next.statusCalls, next.statusBounds, next.steps);
    ConcatenateFragmentsSnoc(prefix.stdoutFragments, step.outcome.stdoutFragment);
    ConcatenateFragmentsSnoc(prefix.stderrFragments, step.outcome.stderrFragment);
    FailureExistsSnoc(prefix.outcomes, step.outcome, prefixError);
    assert BatchStepEvidenceFor(source, directory, cmd, step.beforeFs, cwd, step.afterFs,
                                step.outcome, step.outcome.stdoutFragment, step.outcome.stderrFragment, step) by {
      reveal BatchStepEvidenceFor();
    }
    forall j: nat | j < |sources + [source]|
      ensures BatchStepEvidenceFor((sources + [source])[j], directory, cmd,
                                   next.fsBounds[j], cwd, next.fsBounds[j + 1], next.outcomes[j],
                                   next.stdoutFragments[j], next.stderrFragments[j], next.steps[j])
      ensures next.steps[j].inputs == inputs
      ensures
        var normalized := Spec.NormalizeSourceSpec((sources + [source])[j], cmd.stripTrailingSlashes);
        StepStatusEvidenceFor(normalized, Spec.TargetInDirectorySpec(directory, normalized), cmd, next.steps[j])
    {
      if j < |sources| {
        assert prefix.statusBounds[j] <= prefix.statusBounds[j + 1];
        assert prefix.steps[j].inputs == inputs;
        assert next.steps[j] == prefix.steps[j];
        assert next.fsBounds[j] == prefix.fsBounds[j];
        assert next.fsBounds[j + 1] == prefix.fsBounds[j + 1];
        assert next.outcomes[j] == prefix.outcomes[j];
        assert next.stdoutFragments[j] == prefix.stdoutFragments[j];
        assert next.stderrFragments[j] == prefix.stderrFragments[j];
      } else {
        assert j == |sources|;
        assert next.fsBounds[j] == step.beforeFs;
      }
    }
    PackageBatchStatusEvidence(inputs, next);
  }

  method FindUnusedNumberedBackupPath(
    target: string,
    index: nat,
    io: BenchIO.IO
  ) returns (path: string, ghost checks: seq<BackupCheckEvidence>, ghost calls: seq<Spec.StatusCallEvidence>)
    requires index >= 1
    modifies io.statusObservationsRegion
    ensures BackupChecksFor(target, index, old(io.fs()), checks)
    ensures path == checks[|checks| - 1].candidate
    ensures io.statusCursor() == old(io.statusCursor()) + |calls|
    ensures StatusCallsFor(Spec.NativeStatusInputs(io.statusObservations(), io.trustedNativeFailures(), io.now()), old(io.statusCursor()), calls)
    ensures |calls| == |checks|
    ensures forall i: nat | i < |calls| ::
              Spec.StatusRequest(
                calls[i], old(io.fs()), MvPathSpec.NumberedBackupPathSpec(target, index + i), false
              ) &&
              calls[i].ok == checks[i].found &&
              calls[i].err == checks[i].err
    decreases *
  {
    hide *;
    reveal BackupChecksFor();
    ghost var firstStatus := io.statusCursor();
    ghost var inputs := Spec.NativeStatusInputs(io.statusObservations(), io.trustedNativeFailures(), io.now());
    var candidate := MvPathSpec.NumberedBackupPathSpec(target, index);
    var metadata := CaptureMetadata(candidate, false, io);
    var found := metadata.ok;
    var err := metadata.err;
    ghost var check := BackupCheckEvidence(candidate, found, err);
    ghost var call := MetadataStatusCall(io.fs(), candidate, false, metadata);
    assert Spec.StatusRequest(call, io.fs(), candidate, false) by {
      reveal MetadataStatusCall(), Spec.StatusRequest();
    }
    assert call.ok == found && call.err == err by {
      reveal MetadataStatusCall();
    }
    assert StatusCallsFor(inputs, firstStatus, [call]);
    if found {
      ghost var tail: seq<BackupCheckEvidence>;
      ghost var tailCalls: seq<Spec.StatusCallEvidence>;
      path, tail, tailCalls := FindUnusedNumberedBackupPath(
        target, index + 1, io
      );
      checks := [check] + tail;
      calls := [call] + tailCalls;
      assert StatusCallsFor(inputs, firstStatus + 1, tailCalls);
      {
        hide *;
        StatusCallsConcat(inputs, firstStatus, [call], tailCalls);
      }
      assert Spec.StatusExistsOutcomeFields(
          old(io.fs()), candidate, false, true, err
        );
      assert forall i: nat | i < |checks| ::
          checks[i].candidate == MvPathSpec.NumberedBackupPathSpec(target, index + i) &&
          Spec.StatusExistsOutcomeFields(
            old(io.fs()),
            checks[i].candidate,
            false,
            checks[i].found,
            checks[i].err
          ) by {
        forall i: nat | i < |checks|
          ensures
            checks[i].candidate ==
            MvPathSpec.NumberedBackupPathSpec(target, index + i) &&
            Spec.StatusExistsOutcomeFields(
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
      forall i: nat | i < |calls|
        ensures Spec.StatusRequest(calls[i], old(io.fs()), MvPathSpec.NumberedBackupPathSpec(target, index + i), false)
        ensures calls[i].ok == checks[i].found && calls[i].err == checks[i].err
      {
        if i == 0 {
          assert calls[i] == call && checks[i] == check;
        } else {
          StatusCallConsIndex(call, tailCalls, i);
          assert checks[i] == tail[i - 1];
          assert index + i == index + 1 + (i - 1);
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
      calls := [call];
      assert Spec.StatusExistsOutcomeFields(old(io.fs()), candidate, false, false, err);
    }
    assert BackupChecksFor(target, index, old(io.fs()), checks);
  }

  method {:isolate_assertions} PickBackupPath(
    target: string,
    backupMode: Schema.BackupMode,
    suffix: string,
    io: BenchIO.IO
  ) returns (path: string, ghost evidence: BackupSelectionEvidence,
             ghost calls: seq<Spec.StatusCallEvidence>)
    modifies io.statusObservationsRegion
    ensures BackupSelectionEvidenceFor(
              target, backupMode, suffix, old(io.fs()), evidence
            )
    ensures backupMode != Schema.BackupOff ==>
              evidence.SelectedBackup? &&
              evidence.backupPath == path
    ensures io.statusCursor() == old(io.statusCursor()) + |calls|
    ensures StatusCallsFor(Spec.NativeStatusInputs(io.statusObservations(), io.trustedNativeFailures(), io.now()), old(io.statusCursor()), calls)
    ensures BackupStatusSuffixFor(backupMode, old(io.fs()), target, calls)
    ensures BackupSelectionFromStatusCallsFor(backupMode, suffix, old(io.fs()), target, evidence, calls)
    decreases *
  {
    hide StatusCallsFor(), Spec.StatusCallsFor();
    ghost var firstStatus := io.statusCursor();
    ghost var inputs := Spec.NativeStatusInputs(io.statusObservations(), io.trustedNativeFailures(), io.now());
    assert StatusCallsFor(inputs, firstStatus, []) by {
      reveal StatusCallsFor(), Spec.StatusCallsFor();
    }
    if backupMode == Schema.BackupOff {
      path := "";
      evidence := NoBackupSelection;
      calls := [];
    } else if backupMode == Schema.BackupSimple {
      path := MvPathSpec.SimpleBackupPathSpec(target, suffix);
      evidence := SelectedBackup(path, [], false, false, 0);
      calls := [];
    } else if backupMode == Schema.BackupExisting {
      var numberedSeed := MvPathSpec.NumberedBackupPathSpec(target, 1);
      var getFileStatusResult2 := io.GetFileStatus(numberedSeed, false);
      var rawMetadataOk5 := getFileStatusResult2.Ok?;
      var rawMetadataStatus5 := IOContract.ResultValue(getFileStatusResult2, BenchWorld.DEFAULT_FILE_STATUS);
      var rawMetadataErr5 := IOContract.ResultErrno(getFileStatusResult2);
      MetadataProof.FileStatusStructureImpliesMetadata(io.fs(), numberedSeed, false, rawMetadataOk5, rawMetadataStatus5, rawMetadataErr5);
      var found := rawMetadataOk5;
      var err := rawMetadataErr5;
      ghost var seedCall := Spec.StatusCallEvidence(old(io.fs()), numberedSeed, false,
                                                    rawMetadataOk5, rawMetadataStatus5, rawMetadataErr5);
      assert Spec.StatusRequest(seedCall, old(io.fs()), numberedSeed, false);
      assert StatusCallsFor(inputs, firstStatus, [seedCall]) by {
        reveal StatusCallsFor(), Spec.StatusCallsFor();
      }
      if !found {
        path := MvPathSpec.SimpleBackupPathSpec(target, suffix);
        evidence := SelectedBackup(path, [], true, found, err);
        calls := [seedCall];
        assert Spec.StatusExistsOutcomeFields(old(io.fs()), numberedSeed, false, false, err);
      } else {
        ghost var checks: seq<BackupCheckEvidence>;
        ghost var numberedCalls: seq<Spec.StatusCallEvidence>;
        path, checks, numberedCalls := FindUnusedNumberedBackupPath(target, 1, io);
        evidence := SelectedBackup(path, checks, true, found, err);
        calls := [seedCall] + numberedCalls;
        assert StatusCallsFor(inputs, firstStatus + 1, numberedCalls);
        {
          hide *;
          StatusCallsConcat(inputs, firstStatus, [seedCall], numberedCalls);
        }
        assert Spec.StatusExistsOutcomeFields(
            old(io.fs()), numberedSeed, false, true, err
          );
        assert BackupStatusSuffixFor(backupMode, old(io.fs()), target, calls) by {
          forall i: nat | 1 <= i < |calls|
            ensures Spec.StatusRequest(calls[i], old(io.fs()), MvPathSpec.NumberedBackupPathSpec(target, i), false)
          {
            StatusCallConsIndex(seedCall, numberedCalls, i);
            assert calls[i] == numberedCalls[i - 1];
          }
          forall i: nat | 1 <= i + 1 < |calls|
            ensures calls[i].ok
          {
            if i == 0 {
              assert calls[i] == seedCall;
            } else {
              StatusCallConsIndex(seedCall, numberedCalls, i);
              assert calls[i] == numberedCalls[i - 1];
              assert checks[i - 1].found;
            }
          }
          assert calls[|calls| - 1] == numberedCalls[|numberedCalls| - 1];
        }
      }
    } else {
      ghost var checks: seq<BackupCheckEvidence>;
      path, checks, calls := FindUnusedNumberedBackupPath(target, 1, io);
      evidence := SelectedBackup(path, checks, false, false, 0);
      assert BackupStatusSuffixFor(backupMode, old(io.fs()), target, calls) by {
        forall i: nat | i + 1 < |calls|
          ensures calls[i].ok
        {
          assert checks[i].found;
        }
      }
    }
    assert BackupSelectionEvidenceFor(target, backupMode, suffix, old(io.fs()), evidence);
    assert BackupStatusSuffixFor(backupMode, old(io.fs()), target, calls);
    assert BackupSelectionFromStatusCallsFor(backupMode, suffix, old(io.fs()), target, evidence, calls);
    assert StatusCallsFor(inputs, firstStatus, calls) by {
      hide *;
    }
    hide *;
  }

  method CaptureMetadata(
    path: string,
    followSymlink: bool,
    io: BenchIO.IO
  ) returns (evidence: MetadataEvidence)
    modifies io.statusObservationsRegion
    ensures MetadataEvidenceFor(
              old(io.fs()), path, followSymlink, evidence
            )
    ensures ObservedMetadataEvidenceFor(
              Spec.NativeStatusInputs(io.statusObservations(), io.trustedNativeFailures(), io.now()), old(io.fs()), path, followSymlink, evidence
            )
    ensures IOContract.IsDirectoryStrictContractFields(old(io.fs()), path, followSymlink,
                                                       evidence.ok, evidence.isDir, evidence.err)
    ensures Spec.StatusExistsOutcomeFields(old(io.fs()), path, followSymlink, evidence.ok, evidence.err)
    ensures IOContract.IsDirectoryContractFields(old(io.fs()), path, followSymlink,
                                                 evidence.ok, evidence.isDir, evidence.err)
    ensures evidence.isDir == (evidence.rawStatus.kind == BenchWorld.DirectoryKind)
    ensures StatusCallsFor(Spec.NativeStatusInputs(io.statusObservations(), io.trustedNativeFailures(), io.now()),
                           old(io.statusCursor()), [MetadataStatusCall(old(io.fs()), path, followSymlink, evidence)])
    ensures evidence.ok <==> evidence.err == 0
    ensures evidence.ordinal == old(io.statusCursor())
    ensures io.statusCursor() == old(io.statusCursor()) + 1
  {
    hide IOContract.IsDirectoryContractFields(), StatusCallsFor(), Spec.StatusCallsFor();
    ghost var ordinal := io.statusCursor();
    var getFileStatusResult3 := io.GetFileStatus(path, followSymlink);
    var ok := getFileStatusResult3.Ok?;
    var status := IOContract.ResultValue(getFileStatusResult3, BenchWorld.DEFAULT_FILE_STATUS);
    var err := IOContract.ResultErrno(getFileStatusResult3);
    assert IOContract.ObservedNativeFileStatusContractFields(io.statusObservations(), io.trustedNativeFailures(),
                                                             ordinal, io.fs(), path, followSymlink, ok, status, err) by {
      hide *;
      reveal IOContract.GetFileStatusSpec();
    }
    hide IOContract.GetFileStatusSpec(), IOContract.ObservedNativeFileStatusContractFields();
    MetadataProof.FileStatusStructureImpliesMetadata(io.fs(), path, followSymlink, ok, status, err);
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
      ordinal,
      status,
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
    assert StatusCallsFor(Spec.NativeStatusInputs(io.statusObservations(), io.trustedNativeFailures(), io.now()),
                          ordinal, [MetadataStatusCall(io.fs(), path, followSymlink, evidence)]) by {
      hide *;
      reveal StatusCallsFor(), Spec.StatusCallsFor(), MetadataStatusCall();
    }
  }

  method CaptureEntryName(
    path: string,
    io: BenchIO.IO
  ) returns (evidence: EntryNameEvidence)
    modifies io.statusObservationsRegion
    ensures EntryNameEvidenceFor(old(io.fs()), path, evidence)
    ensures io.statusCursor() == old(io.statusCursor()) + 1
    ensures evidence.parentMetadata.ordinal == old(io.statusCursor())
    ensures ObservedMetadataEvidenceFor(
              Spec.NativeStatusInputs(io.statusObservations(), io.trustedNativeFailures(), io.now()), old(io.fs()), evidence.parent,
              false, evidence.parentMetadata)
    ensures StatusCallsFor(Spec.NativeStatusInputs(io.statusObservations(), io.trustedNativeFailures(), io.now()),
                           old(io.statusCursor()), [MetadataStatusCall(old(io.fs()), evidence.parent, false, evidence.parentMetadata)])
    decreases *
  {
    var leaf := BasenameCore.ComputeBasenameValue(path);
    var parent := DirnameCore.ComputeDirnameValue(path);
    var parentMetadata := CaptureMetadata(parent, false, io);
    evidence := EntryNameEvidence(parent, leaf, parentMetadata);
  }

  ghost predicate TargetDirectoryCheckSummaryFields(directory: string, preFs: BenchWorld.FileSystem, ok: bool, err: int)
  {
    (exists statErr: int ::
       IOContract.IsDirectoryContractFields(preFs, directory, true, true, true, statErr) &&
       ok == true &&
       err == Text.TargetDirectoryErrSpec(true, true, statErr)) ||
    (exists statErr: int ::
       IOContract.IsDirectoryContractFields(preFs, directory, true, true, false, statErr) &&
       ok == false &&
       err == Text.TargetDirectoryErrSpec(true, false, statErr)) ||
    (exists statErr: int ::
       IOContract.IsDirectoryContractFields(preFs, directory, true, false, false, statErr) &&
       ok == false &&
       err == Text.TargetDirectoryErrSpec(false, false, statErr)) ||
    (exists statErr: int ::
       IOContract.IsDirectoryContractFields(preFs, directory, true, false, true, statErr) &&
       ok == false &&
       err == Text.TargetDirectoryErrSpec(false, true, statErr))
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
      Spec.NormalizeSourceSpec(cmd.operands[0], cmd.stripTrailingSlashes);
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

  ghost predicate DirectoryStatusEvidenceFor(
    sources: seq<string>,
    directory: string,
    cmd: Schema.MvCmd,
    beforeFs: BenchWorld.FileSystem,
    cwd: BenchWorld.Path,
    afterFs: BenchWorld.FileSystem,
    beforeStdout: BenchWorld.Bytes,
    afterStdout: BenchWorld.Bytes,
    beforeStderr: BenchWorld.Bytes,
    afterStderr: BenchWorld.Bytes,
    exit: int,
    observations: Spec.NativeStatusInputs,
    firstStatus: nat,
    calls: seq<Spec.StatusCallEvidence>,
    evidence: DirectoryStatusEvidence
  )
  {
    match evidence
    case FailedDirectoryStatus(call) =>
      calls == [call] &&
      Spec.StatusRequest(call, beforeFs, directory, true) &&
      (!call.ok || call.status.kind != BenchWorld.DirectoryKind) &&
      afterFs == beforeFs &&
      afterStdout == beforeStdout && exit == 1
    case SuccessfulDirectoryStatus(call, batch) =>
      calls == [call] + batch.statusCalls &&
      Spec.StatusRequest(call, beforeFs, directory, true) &&
      call.ok && call.status.kind == BenchWorld.DirectoryKind &&
      batch.firstStatus == firstStatus + 1 &&
      BatchMoveStatusEvidenceFor(
        sources, directory, cmd, observations, batch
      ) &&
      exists hadError: bool, out: BenchWorld.Bytes, err: BenchWorld.Bytes ::
        BatchEvidenceFor(
          sources, directory, cmd, beforeFs, cwd, afterFs,
          hadError, out, err, batch
        ) &&
        exit == (if hadError then 1 else 0) &&
        afterStdout == beforeStdout + out &&
        afterStderr == beforeStderr + err
  }

  opaque ghost predicate RunStatusEvidenceFor(
    raw: Schema.MvCmdRaw,
    beforeFs: BenchWorld.FileSystem,
    cwd: BenchWorld.Path,
    afterFs: BenchWorld.FileSystem,
    beforeStdout: BenchWorld.Bytes,
    afterStdout: BenchWorld.Bytes,
    beforeStderr: BenchWorld.Bytes,
    afterStderr: BenchWorld.Bytes,
    exit: int,
    observations: Spec.NativeStatusInputs,
    firstStatus: nat,
    afterStatus: nat,
    calls: seq<Spec.StatusCallEvidence>,
    evidence: RunStatusEvidence
  )
  {
    var cmd := Schema.Command(raw);
    afterStatus == firstStatus + |calls| &&
    StatusCallsFor(observations, firstStatus, calls) &&
    (if cmd.mode != Schema.ModeRun ||
        (cmd.targetDirectory != "" && cmd.noTargetDirectory) ||
        |cmd.operands| == 0 ||
        (cmd.targetDirectory == "" && |cmd.operands| == 1) ||
        (cmd.targetDirectory == "" && cmd.noTargetDirectory &&
         |cmd.operands| > 2) then
       evidence == NoRunStatus && |calls| == 0
     else if cmd.targetDirectory != "" then
       match evidence
       case DirectoryRunStatus(directoryEvidence) =>
         DirectoryStatusEvidenceFor(
           cmd.operands, cmd.targetDirectory, cmd,
           beforeFs, cwd, afterFs,
           beforeStdout, afterStdout, beforeStderr, afterStderr,
           exit, observations, firstStatus, calls, directoryEvidence
         )
       case _ => false
     else if |cmd.operands| == 2 then
       var source := Spec.NormalizeSourceSpec(
                       cmd.operands[0], cmd.stripTrailingSlashes
                     );
       var destination := cmd.operands[1];
       if cmd.noTargetDirectory then
         match evidence
         case DirectMoveStatus(step) =>
           step.inputs == observations &&
           calls == step.statusCalls &&
           step.firstStatus == firstStatus &&
           step.beforeFs == beforeFs && step.afterFs == afterFs &&
           StepEvidenceFor(source, destination, cmd, cwd, step) &&
           StepStatusEvidenceFor(source, destination, cmd, step) &&
           exit == (if step.outcome.failed then 1 else 0) &&
           afterStdout == beforeStdout + step.outcome.stdoutFragment &&
           afterStderr == beforeStderr + step.outcome.stderrFragment
         case _ => false
       else
         match evidence
         case ProbedMoveStatus(call, step) =>
           step.inputs == observations &&
           calls == [call] + step.statusCalls &&
           Spec.StatusRequest(call, beforeFs, destination, true) &&
           step.firstStatus == firstStatus + 1 &&
           step.beforeFs == beforeFs && step.afterFs == afterFs &&
           var target :=
             if call.ok && call.status.kind == BenchWorld.DirectoryKind then
               Spec.TargetInDirectorySpec(destination, source)
             else destination;
           StepEvidenceFor(source, target, cmd, cwd, step) &&
           StepStatusEvidenceFor(source, target, cmd, step) &&
           exit == (if step.outcome.failed then 1 else 0) &&
           afterStdout == beforeStdout + step.outcome.stdoutFragment &&
           afterStderr == beforeStderr + step.outcome.stderrFragment
         case _ => false
     else
       var directory := cmd.operands[|cmd.operands| - 1];
       var sources := cmd.operands[..|cmd.operands| - 1];
       match evidence
       case DirectoryRunStatus(directoryEvidence) =>
         DirectoryStatusEvidenceFor(
           sources, directory, cmd,
           beforeFs, cwd, afterFs,
           beforeStdout, afterStdout, beforeStderr, afterStderr,
           exit, observations, firstStatus, calls, directoryEvidence
         )
       case _ => false)
  }

  ghost predicate PreparedSummaryIO(
    raw: Schema.MvCmdRaw,
    preFs: BenchWorld.FileSystem,
    preCwd: BenchWorld.Path,
    preStdout: BenchWorld.Bytes,
    preStderr: BenchWorld.Bytes,
    io: BenchIO.IO,
    exit: int,
    plannedStdout: BenchWorld.Bytes,
    plannedStderr: BenchWorld.Bytes
  )
    reads io.fsRegion
  {
    var cmd := Schema.Command(raw);
    if cmd.mode == Schema.ModeInvalidBackup then
      io.fs() == preFs &&
      exit == 1 &&
      plannedStdout == preStdout &&
      plannedStderr == preStderr + Spec.InvalidBackupArgumentMessageSpec(cmd.invalidBackupArg)
    else if cmd.mode == Schema.ModeInvalidUpdate then
      io.fs() == preFs &&
      exit == 1 &&
      plannedStdout == preStdout &&
      plannedStderr == preStderr + Spec.InvalidUpdateArgumentMessageSpec(cmd.invalidUpdateArg)
    else if cmd.mode == Schema.ModeHelp then
      io.fs() == preFs &&
      exit == 0 &&
      plannedStdout == preStdout + Spec.HelpTextSpec() &&
      plannedStderr == preStderr
    else if cmd.mode == Schema.ModeVersion then
      io.fs() == preFs &&
      exit == 0 &&
      plannedStdout == preStdout + Spec.VersionTextSpec() &&
      plannedStderr == preStderr
    else if cmd.targetDirectory != "" && cmd.noTargetDirectory then
      io.fs() == preFs &&
      exit == 1 &&
      plannedStdout == preStdout &&
      plannedStderr == preStderr + Spec.TargetDirectoryConflictMessageSpec()
    else if |cmd.operands| == 0 then
      io.fs() == preFs &&
      exit == 1 &&
      plannedStdout == preStdout &&
      plannedStderr == preStderr + Spec.MissingFileOperandMessageSpec()
    else if cmd.targetDirectory != "" then
      RunIntoDirectoryEvidenceFields(cmd.operands, cmd.targetDirectory, true, cmd, preFs, preCwd, io.fs(), preStdout, preStderr, plannedStdout, plannedStderr, exit)
    else if |cmd.operands| == 1 then
      io.fs() == preFs &&
      exit == 1 &&
      plannedStdout == preStdout &&
      plannedStderr == preStderr + Spec.MissingDestinationMessageSpec(cmd.operands[0])
    else if cmd.noTargetDirectory && |cmd.operands| > 2 then
      io.fs() == preFs &&
      exit == 1 &&
      plannedStdout == preStdout &&
      plannedStderr == preStderr + Spec.ExtraOperandMessageSpec(cmd.operands[2])
    else if |cmd.operands| == 2 then
      RunTwoOperandEvidenceFields(cmd, preFs, preCwd, io.fs(), preStdout, preStderr, plannedStdout, plannedStderr, exit)
    else
      RunIntoDirectoryEvidenceFields(cmd.operands[..|cmd.operands| - 1], cmd.operands[|cmd.operands| - 1], false, cmd, preFs, preCwd, io.fs(), preStdout, preStderr, plannedStdout, plannedStderr, exit)
  }

  twostate predicate CandidateSummary(
    io: BenchIO.IO,
    raw: Schema.MvCmdRaw,
    exit: int,
    plannedStdout: BenchWorld.Bytes,
    plannedStderr: BenchWorld.Bytes
  )
    reads io.fsRegion
  {
    var cmd := Schema.Command(raw);
    if cmd.mode == Schema.ModeInvalidBackup then
      io.fs() == old(io.fs()) &&
      exit == 1 &&
      plannedStdout == [] &&
      plannedStderr == [] + Spec.InvalidBackupArgumentMessageSpec(cmd.invalidBackupArg)
    else if cmd.mode == Schema.ModeInvalidUpdate then
      io.fs() == old(io.fs()) &&
      exit == 1 &&
      plannedStdout == [] &&
      plannedStderr == [] + Spec.InvalidUpdateArgumentMessageSpec(cmd.invalidUpdateArg)
    else if cmd.mode == Schema.ModeHelp then
      io.fs() == old(io.fs()) &&
      exit == 0 &&
      plannedStdout == [] + Spec.HelpTextSpec() &&
      plannedStderr == []
    else if cmd.mode == Schema.ModeVersion then
      io.fs() == old(io.fs()) &&
      exit == 0 &&
      plannedStdout == [] + Spec.VersionTextSpec() &&
      plannedStderr == []
    else if cmd.targetDirectory != "" && cmd.noTargetDirectory then
      io.fs() == old(io.fs()) &&
      exit == 1 &&
      plannedStdout == [] &&
      plannedStderr == [] + Spec.TargetDirectoryConflictMessageSpec()
    else if |cmd.operands| == 0 then
      io.fs() == old(io.fs()) &&
      exit == 1 &&
      plannedStdout == [] &&
      plannedStderr == [] + Spec.MissingFileOperandMessageSpec()
    else if cmd.targetDirectory != "" then
      RunIntoDirectoryEvidenceFields(cmd.operands, cmd.targetDirectory, true, cmd, old(io.fs()), old(io.cwd()), io.fs(), [], [], plannedStdout, plannedStderr, exit)
    else if |cmd.operands| == 1 then
      io.fs() == old(io.fs()) &&
      exit == 1 &&
      plannedStdout == [] &&
      plannedStderr == [] + Spec.MissingDestinationMessageSpec(cmd.operands[0])
    else if cmd.noTargetDirectory && |cmd.operands| > 2 then
      io.fs() == old(io.fs()) &&
      exit == 1 &&
      plannedStdout == [] &&
      plannedStderr == [] + Spec.ExtraOperandMessageSpec(cmd.operands[2])
    else if |cmd.operands| == 2 then
      RunTwoOperandEvidenceFields(cmd, old(io.fs()), old(io.cwd()), io.fs(), [], [], plannedStdout, plannedStderr, exit)
    else
      RunIntoDirectoryEvidenceFields(cmd.operands[..|cmd.operands| - 1], cmd.operands[|cmd.operands| - 1], false, cmd, old(io.fs()), old(io.cwd()), io.fs(), [], [], plannedStdout, plannedStderr, exit)
  }

  twostate predicate RunIntoDirectorySummary(
    io: BenchIO.IO,
    sources: seq<string>,
    directory: string,
    explicitTargetDirectory: bool,
    cmd: Schema.MvCmd,
    plannedStdout: BenchWorld.Bytes,
    plannedStderr: BenchWorld.Bytes,
    exit: int
  )
    reads io.fsRegion
  {
    (exists
       hadError: bool,
       out: BenchWorld.Bytes,
       err: BenchWorld.Bytes,
       batch: BatchEvidence
       ::
         TargetDirectoryCheckSummaryFields(
           directory, old(io.fs()), true, 0
         ) &&
         BatchEvidenceFor(
           sources,
           directory,
           cmd,
           old(io.fs()),
           old(io.cwd()),
           io.fs(),
           hadError,
           out,
           err,
           batch
         ) &&
         exit == (if hadError then 1 else 0) &&
         plannedStdout == [] + out &&
         plannedStderr == [] + err) ||
    (exists directoryErr: int ::
       TargetDirectoryCheckSummaryFields(
         directory, old(io.fs()), false, directoryErr
       ) &&
       io.fs() == old(io.fs()) &&
       exit == 1 &&
       plannedStdout == [] &&
       plannedStderr == [] +
       Spec.TargetFailureMessageSpec(
         directory, explicitTargetDirectory, directoryErr
       ))
  }

  twostate predicate DirectoryStatusSummary(
    io: BenchIO.IO,
    sources: seq<string>,
    directory: string,
    cmd: Schema.MvCmd,
    plannedStdout: BenchWorld.Bytes,
    plannedStderr: BenchWorld.Bytes,
    exit: int,
    calls: seq<Spec.StatusCallEvidence>,
    evidence: DirectoryStatusEvidence
  )
    reads io.fsRegion, io.statusObservationsRegion, io.trustedNativeFailuresRegion, io.nowRegion
  {
    match evidence
    case FailedDirectoryStatus(call) =>
      calls == [call] &&
      Spec.StatusRequest(call, old(io.fs()), directory, true) &&
      (!call.ok || call.status.kind != BenchWorld.DirectoryKind) &&
      io.fs() == old(io.fs()) &&
      plannedStdout == [] && exit == 1
    case SuccessfulDirectoryStatus(call, batch) =>
      calls == [call] + batch.statusCalls &&
      Spec.StatusRequest(call, old(io.fs()), directory, true) &&
      call.ok && call.status.kind == BenchWorld.DirectoryKind &&
      batch.firstStatus == old(io.statusCursor()) + 1 &&
      BatchMoveStatusEvidenceFor(
        sources, directory, cmd, Spec.NativeStatusInputs(io.statusObservations(), io.trustedNativeFailures(), io.now()), batch
      ) &&
      exists hadError: bool, out: BenchWorld.Bytes, err: BenchWorld.Bytes ::
        BatchEvidenceFor(
          sources, directory, cmd, old(io.fs()), old(io.cwd()), io.fs(),
          hadError, out, err, batch
        ) &&
        exit == (if hadError then 1 else 0) &&
        plannedStdout == [] + out &&
        plannedStderr == [] + err
  }

  twostate predicate RunStatusSummary(
    io: BenchIO.IO,
    raw: Schema.MvCmdRaw,
    plannedStdout: BenchWorld.Bytes,
    plannedStderr: BenchWorld.Bytes,
    exit: int,
    calls: seq<Spec.StatusCallEvidence>,
    evidence: RunStatusEvidence
  )
    reads io.fsRegion, io.statusObservationsRegion, io.trustedNativeFailuresRegion, io.nowRegion
  {
    var cmd := Schema.Command(raw);
    io.statusCursor() == old(io.statusCursor()) + |calls| &&
    StatusCallsFor(Spec.NativeStatusInputs(io.statusObservations(), io.trustedNativeFailures(), io.now()), old(io.statusCursor()), calls) &&
    (if cmd.mode != Schema.ModeRun ||
        (cmd.targetDirectory != "" && cmd.noTargetDirectory) ||
        |cmd.operands| == 0 ||
        (cmd.targetDirectory == "" && |cmd.operands| == 1) ||
        (cmd.targetDirectory == "" && cmd.noTargetDirectory &&
         |cmd.operands| > 2) then
       evidence == NoRunStatus && |calls| == 0
     else if cmd.targetDirectory != "" then
       match evidence
       case DirectoryRunStatus(directoryEvidence) =>
         DirectoryStatusEvidenceFor(
           cmd.operands, cmd.targetDirectory, cmd,
           old(io.fs()), old(io.cwd()), io.fs(),
           [], plannedStdout, [], plannedStderr,
           exit, Spec.NativeStatusInputs(io.statusObservations(), io.trustedNativeFailures(), io.now()), old(io.statusCursor()), calls, directoryEvidence
         )
       case _ => false
     else if |cmd.operands| == 2 then
       var source := Spec.NormalizeSourceSpec(
                       cmd.operands[0], cmd.stripTrailingSlashes
                     );
       var destination := cmd.operands[1];
       if cmd.noTargetDirectory then
         match evidence
         case DirectMoveStatus(step) =>
           step.inputs == Spec.NativeStatusInputs(io.statusObservations(), io.trustedNativeFailures(), io.now()) &&
           calls == step.statusCalls &&
           step.firstStatus == old(io.statusCursor()) &&
           step.beforeFs == old(io.fs()) && step.afterFs == io.fs() &&
           StepEvidenceFor(source, destination, cmd, old(io.cwd()), step) &&
           StepStatusEvidenceFor(source, destination, cmd, step) &&
           exit == (if step.outcome.failed then 1 else 0) &&
           plannedStdout == [] + step.outcome.stdoutFragment &&
           plannedStderr == [] + step.outcome.stderrFragment
         case _ => false
       else
         match evidence
         case ProbedMoveStatus(call, step) =>
           step.inputs == Spec.NativeStatusInputs(io.statusObservations(), io.trustedNativeFailures(), io.now()) &&
           calls == [call] + step.statusCalls &&
           Spec.StatusRequest(call, old(io.fs()), destination, true) &&
           step.firstStatus == old(io.statusCursor()) + 1 &&
           step.beforeFs == old(io.fs()) && step.afterFs == io.fs() &&
           var target :=
             if call.ok && call.status.kind == BenchWorld.DirectoryKind then
               Spec.TargetInDirectorySpec(destination, source)
             else destination;
           StepEvidenceFor(source, target, cmd, old(io.cwd()), step) &&
           StepStatusEvidenceFor(source, target, cmd, step) &&
           exit == (if step.outcome.failed then 1 else 0) &&
           plannedStdout == [] + step.outcome.stdoutFragment &&
           plannedStderr == [] + step.outcome.stderrFragment
         case _ => false
     else
       var directory := cmd.operands[|cmd.operands| - 1];
       var sources := cmd.operands[..|cmd.operands| - 1];
       match evidence
       case DirectoryRunStatus(directoryEvidence) =>
         DirectoryStatusEvidenceFor(
           sources, directory, cmd,
           old(io.fs()), old(io.cwd()), io.fs(),
           [], plannedStdout, [], plannedStderr,
           exit, Spec.NativeStatusInputs(io.statusObservations(), io.trustedNativeFailures(), io.now()), old(io.statusCursor()), calls, directoryEvidence
         )
       case _ => false)
  }

  twostate predicate RenamePhase(
    io: BenchIO.IO,
    source: string,
    target: string,
    cmd: Schema.MvCmd,
    frame: RenameFrame,
    outcome: Spec.MoveOutcome,
    step: StepEvidence
  )
    reads io.fsRegion
  {
    StepEvidenceFor(source, target, cmd, old(io.cwd()), step) &&
    StepStatusEvidenceFor(source, target, cmd, step) &&
    step.beforeFs == old(io.fs()) && step.afterFs == io.fs() && step.outcome == outcome &&
    step.firstStatus == frame.firstStatus && step.inputs == frame.inputs &&
    step.statusCalls == frame.statusCalls && StatusCallsFor(frame.inputs, step.firstStatus, step.statusCalls)
  }

  opaque twostate predicate PreparedSummary(raw: Schema.MvCmdRaw, io: BenchIO.IO, exit: int, plannedStdout: BenchWorld.Bytes, plannedStderr: BenchWorld.Bytes)
    reads io.fsRegion, io.cwdRegion, io.statusObservationsRegion, io.trustedNativeFailuresRegion, io.nowRegion
  {
    CandidateSummary(io, raw, exit, plannedStdout, plannedStderr) &&
    exists calls: seq<Spec.StatusCallEvidence> ::
      io.statusCursor() == old(io.statusCursor()) + |calls| &&
      StatusCallsFor(Spec.NativeStatusInputs(io.statusObservations(), io.trustedNativeFailures(), io.now()), old(io.statusCursor()), calls)
  }

  method {:isolate_assertions} Prepare(
    raw: Schema.MvCmdRaw,
    io: BenchIO.IO
  ) returns (exit: int, ghost calls: seq<Spec.StatusCallEvidence>,
             ghost runEvidence: RunStatusEvidence,
             plannedStdout: BenchWorld.Bytes, plannedStderr: BenchWorld.Bytes)
    modifies io.fsRegion, io.statusObservationsRegion
    ensures PreparedSummary(raw, io, exit, plannedStdout, plannedStderr)
    ensures CandidateSummary(io, raw, exit, plannedStdout, plannedStderr)
    ensures io.statusCursor() == old(io.statusCursor()) + |calls|
    ensures StatusCallsFor(Spec.NativeStatusInputs(io.statusObservations(), io.trustedNativeFailures(), io.now()), old(io.statusCursor()), calls)
    ensures RunStatusSummary(io, raw, plannedStdout, plannedStderr, exit, calls, runEvidence)
    decreases *
  {
    hide *;
    reveal PreparedSummary(), CandidateSummary(), RunStatusSummary(), PreparedSummaryIO(), RunStatusEvidenceFor(), Spec.ConcatenateFragments();
    plannedStdout, plannedStderr := [], [];
    ghost var preFs := io.fs();
    ghost var preCwd := io.cwd();
    ghost var preStdout := plannedStdout;
    ghost var preStderr := plannedStderr;
    ghost var firstStatus := io.statusCursor();
    calls := [];
    runEvidence := NoRunStatus;
    assert StatusCallsFor(Spec.NativeStatusInputs(io.statusObservations(), io.trustedNativeFailures(), io.now()), firstStatus, calls) by {
      reveal StatusCallsFor(), Spec.StatusCallsFor();
    }
    StatusTranscriptWitness(Spec.NativeStatusInputs(io.statusObservations(), io.trustedNativeFailures(), io.now()),
                            firstStatus, io.statusCursor(), calls);
    var cmd := Schema.Command(raw);
    if cmd.mode == Schema.ModeInvalidBackup {
      var err := Spec.InvalidBackupArgumentMessageSpec(cmd.invalidBackupArg);
      plannedStderr := plannedStderr + err;
      exit := 1;
      assert PreparedSummaryIO(raw, preFs, preCwd, preStdout, preStderr, io, exit, plannedStdout, plannedStderr) by {
        hide *;
        reveal PreparedSummaryIO(), PreparedSummary(), CandidateSummary(),
               RunIntoDirectorySummary(), DirectoryStatusSummary(), RunStatusSummary(),
               RunIntoDirectoryEvidenceFields(), DirectoryStatusEvidenceFor(), RunStatusEvidenceFor();
      }
      return;
    }

    if cmd.mode == Schema.ModeInvalidUpdate {
      var err := Spec.InvalidUpdateArgumentMessageSpec(cmd.invalidUpdateArg);
      plannedStderr := plannedStderr + err;
      exit := 1;
      assert PreparedSummaryIO(raw, preFs, preCwd, preStdout, preStderr, io, exit, plannedStdout, plannedStderr) by {
        hide *;
        reveal PreparedSummaryIO(), PreparedSummary(), CandidateSummary(),
               RunIntoDirectorySummary(), DirectoryStatusSummary(), RunStatusSummary(),
               RunIntoDirectoryEvidenceFields(), DirectoryStatusEvidenceFor(), RunStatusEvidenceFor();
      }
      return;
    }

    if cmd.mode == Schema.ModeHelp {
      var out := Spec.HelpTextSpec();
      plannedStdout := plannedStdout + out;
      exit := 0;
      assert PreparedSummaryIO(raw, preFs, preCwd, preStdout, preStderr, io, exit, plannedStdout, plannedStderr) by {
        hide *;
        reveal PreparedSummaryIO(), PreparedSummary(), CandidateSummary(),
               RunIntoDirectorySummary(), DirectoryStatusSummary(), RunStatusSummary(),
               RunIntoDirectoryEvidenceFields(), DirectoryStatusEvidenceFor(), RunStatusEvidenceFor();
      }
      return;
    }

    if cmd.mode == Schema.ModeVersion {
      var out := Spec.VersionTextSpec();
      plannedStdout := plannedStdout + out;
      exit := 0;
      assert PreparedSummaryIO(raw, preFs, preCwd, preStdout, preStderr, io, exit, plannedStdout, plannedStderr) by {
        hide *;
        reveal PreparedSummaryIO(), PreparedSummary(), CandidateSummary(),
               RunIntoDirectorySummary(), DirectoryStatusSummary(), RunStatusSummary(),
               RunIntoDirectoryEvidenceFields(), DirectoryStatusEvidenceFor(), RunStatusEvidenceFor();
      }
      return;
    }

    if cmd.targetDirectory != "" && cmd.noTargetDirectory {
      var err := Spec.TargetDirectoryConflictMessageSpec();
      plannedStderr := plannedStderr + err;
      exit := 1;
      assert PreparedSummaryIO(raw, preFs, preCwd, preStdout, preStderr, io, exit, plannedStdout, plannedStderr) by {
        hide *;
        reveal PreparedSummaryIO(), PreparedSummary(), CandidateSummary(),
               RunIntoDirectorySummary(), DirectoryStatusSummary(), RunStatusSummary(),
               RunIntoDirectoryEvidenceFields(), DirectoryStatusEvidenceFor(), RunStatusEvidenceFor();
      }
      return;
    }

    if |cmd.operands| == 0 {
      var err := Spec.MissingFileOperandMessageSpec();
      plannedStderr := plannedStderr + err;
      exit := 1;
      assert PreparedSummaryIO(raw, preFs, preCwd, preStdout, preStderr, io, exit, plannedStdout, plannedStderr) by {
        hide *;
        reveal PreparedSummaryIO(), PreparedSummary(), CandidateSummary(),
               RunIntoDirectorySummary(), DirectoryStatusSummary(), RunStatusSummary(),
               RunIntoDirectoryEvidenceFields(), DirectoryStatusEvidenceFor(), RunStatusEvidenceFor();
      }
      return;
    }

    if cmd.targetDirectory != "" {
      ghost var directoryEvidence: DirectoryStatusEvidence;
      exit, calls, directoryEvidence, plannedStdout, plannedStderr := PrepareIntoDirectory(
        cmd.operands, cmd.targetDirectory, true, cmd, io
      );
      runEvidence := DirectoryRunStatus(directoryEvidence);
      assert PreparedSummaryIO(raw, preFs, preCwd, preStdout, preStderr, io, exit, plannedStdout, plannedStderr) by {
        hide *;
        reveal PreparedSummaryIO(), PreparedSummary(), CandidateSummary(),
               RunIntoDirectorySummary(), DirectoryStatusSummary(), RunStatusSummary(),
               RunIntoDirectoryEvidenceFields(), DirectoryStatusEvidenceFor(), RunStatusEvidenceFor();
      }
      assert cmd.mode == Schema.ModeRun;
      assert !cmd.noTargetDirectory;
      assert |cmd.operands| > 0;
      assert io.statusCursor() == firstStatus + |calls|;
      assert StatusCallsFor(
          Spec.NativeStatusInputs(io.statusObservations(), io.trustedNativeFailures(), io.now()), firstStatus, calls
        );
      assert DirectoryStatusEvidenceFor(
          cmd.operands, cmd.targetDirectory, cmd,
          preFs, preCwd, io.fs(),
          preStdout, plannedStdout, preStderr, plannedStderr,
          exit, Spec.NativeStatusInputs(io.statusObservations(), io.trustedNativeFailures(), io.now()), firstStatus,
          calls, directoryEvidence
        ) by {
        hide *;
        reveal PreparedSummaryIO(), PreparedSummary(), CandidateSummary(),
               RunIntoDirectorySummary(), DirectoryStatusSummary(), RunStatusSummary(),
               RunIntoDirectoryEvidenceFields(), DirectoryStatusEvidenceFor(), RunStatusEvidenceFor();
      }
      assert RunStatusEvidenceFor(
          raw, preFs, preCwd, io.fs(),
          preStdout, plannedStdout, preStderr, plannedStderr,
          exit, Spec.NativeStatusInputs(io.statusObservations(), io.trustedNativeFailures(), io.now()), firstStatus,
          io.statusCursor(), calls, runEvidence
        ) by {
        hide *;
        reveal PreparedSummaryIO(), PreparedSummary(), CandidateSummary(),
               RunIntoDirectorySummary(), DirectoryStatusSummary(), RunStatusSummary(),
               RunIntoDirectoryEvidenceFields(), DirectoryStatusEvidenceFor(), RunStatusEvidenceFor();
      }
      StatusTranscriptWitness(Spec.NativeStatusInputs(io.statusObservations(), io.trustedNativeFailures(), io.now()),
                              firstStatus, io.statusCursor(), calls);
      assert PreparedSummary(raw, io, exit, plannedStdout, plannedStderr);
      return;
    }

    if |cmd.operands| == 1 {
      var err := Spec.MissingDestinationMessageSpec(cmd.operands[0]);
      plannedStderr := plannedStderr + err;
      exit := 1;
      assert PreparedSummaryIO(raw, preFs, preCwd, preStdout, preStderr, io, exit, plannedStdout, plannedStderr) by {
        hide *;
        reveal PreparedSummaryIO(), PreparedSummary(), CandidateSummary(),
               RunIntoDirectorySummary(), DirectoryStatusSummary(), RunStatusSummary(),
               RunIntoDirectoryEvidenceFields(), DirectoryStatusEvidenceFor(), RunStatusEvidenceFor();
      }
      return;
    }

    if cmd.noTargetDirectory && |cmd.operands| > 2 {
      var err := Spec.ExtraOperandMessageSpec(cmd.operands[2]);
      plannedStderr := plannedStderr + err;
      exit := 1;
      assert PreparedSummaryIO(raw, preFs, preCwd, preStdout, preStderr, io, exit, plannedStdout, plannedStderr) by {
        hide *;
        reveal PreparedSummaryIO(), PreparedSummary(), CandidateSummary(),
               RunIntoDirectorySummary(), DirectoryStatusSummary(), RunStatusSummary(),
               RunIntoDirectoryEvidenceFields(), DirectoryStatusEvidenceFor(), RunStatusEvidenceFor();
      }
      return;
    }

    if |cmd.operands| == 2 {
      var source := Spec.NormalizeSourceSpec(cmd.operands[0], cmd.stripTrailingSlashes);
      var dest := cmd.operands[1];
      var target := dest;
      var dirOk := false;
      var isDir := false;
      var dirErr := 0;
      ghost var directoryCall := Spec.StatusCallEvidence(
        preFs, dest, true, false, BenchWorld.DEFAULT_FILE_STATUS, 0
      );
      if !cmd.noTargetDirectory {
        var metadata := CaptureMetadata(dest, true, io);
        directoryCall := MetadataStatusCall(preFs, dest, true, metadata);
        calls := [directoryCall];
        dirOk, isDir, dirErr := metadata.ok, metadata.isDir, metadata.err;
        assert dirOk == directoryCall.ok && isDir == (directoryCall.status.kind == BenchWorld.DirectoryKind) by {
          reveal MetadataStatusCall();
        }
        if dirOk && isDir {
          target := Spec.TargetInDirectorySpec(dest, source);
        }
      }
      assert StatusCallsFor(Spec.NativeStatusInputs(io.statusObservations(), io.trustedNativeFailures(), io.now()), firstStatus, calls) by {
        reveal StatusCallsFor(), Spec.StatusCallsFor();
      }
      ghost var preMoveFs := io.fs();
      var hadError, out, errOut, step := MoveOne(
        source, target, cmd, io
      );
      assert StatusCallsFor(Spec.NativeStatusInputs(io.statusObservations(), io.trustedNativeFailures(), io.now()), firstStatus, calls);
      assert step.firstStatus == firstStatus + |calls|;
      assert StatusCallsFor(
          Spec.NativeStatusInputs(io.statusObservations(), io.trustedNativeFailures(), io.now()), firstStatus + |calls|,
          step.statusCalls
        );
      StatusCallsConcat(Spec.NativeStatusInputs(io.statusObservations(), io.trustedNativeFailures(), io.now()), firstStatus,
                        calls, step.statusCalls);
      calls := calls + step.statusCalls;
      runEvidence :=
        if cmd.noTargetDirectory then DirectMoveStatus(step)
        else ProbedMoveStatus(directoryCall, step);
      ghost var movedFs := io.fs();
      plannedStdout := plannedStdout + out;
      plannedStderr := plannedStderr + errOut;
      exit := if hadError then 1 else 0;
      assert preMoveFs == preFs;
      assert (exit == 1) == hadError;
      assert step.beforeFs == preFs;
      assert step.afterFs == movedFs;
      assert step.outcome == Spec.MoveOutcome(out, errOut, hadError);
      assert io.fs() == movedFs;
      assert plannedStdout == preStdout + out;
      assert plannedStderr == preStderr + errOut;
      if !cmd.noTargetDirectory {
        if dirOk && isDir {
          assert target == Spec.TargetInDirectorySpec(dest, source);
          assert IOContract.IsDirectoryContractFields(preFs, dest, true, true, true, dirErr);
          ghost var batch := BatchEvidence(
            [step],
            [preFs, movedFs],
            [step.outcome],
            [step.outcome.stdoutFragment],
            [step.outcome.stderrFragment],
            step.firstStatus,
            step.statusCalls,
            [step.firstStatus, step.firstStatus + |step.statusCalls|]
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
          assert forall i: nat | i < 1 ::
              BatchStepEvidenceFor(
                [cmd.operands[0]][i], dest, cmd,
                batch.fsBounds[i], preCwd, batch.fsBounds[i + 1],
                batch.outcomes[i], batch.stdoutFragments[i],
                batch.stderrFragments[i], batch.steps[i]
              );
          assert step.outcome.failed == hadError;
          assert |batch.outcomes| == 1;
          assert batch.outcomes[0] == step.outcome;
          assert (exists i: nat :: (i < |batch.outcomes| &&
                                    batch.outcomes[i].failed)) <==> batch.outcomes[0].failed by {
            if exists i: nat :: (i < |batch.outcomes| &&
                                 batch.outcomes[i].failed) {
              var i: nat :| i < |batch.outcomes| &&
                            batch.outcomes[i].failed;
              assert i == 0;
            } else if batch.outcomes[0].failed {
              assert 0 < |batch.outcomes|;
            }
          }
          assert hadError <==>
                 exists i: nat :: i < |batch.outcomes| &&
                                  batch.outcomes[i].failed;
          assert BatchEvidenceFor([cmd.operands[0]], dest, cmd, preFs, preCwd,
                                  movedFs, hadError, out, errOut, batch) by {
            reveal BatchEvidenceFor();
          }
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
          assert plannedStdout ==
                 preStdout + batchOutcome.stdoutFragment;
          assert plannedStderr ==
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
            plannedStdout ==
            preStdout + batchOutcome.stdoutFragment &&
            plannedStderr ==
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
                plannedStdout == preStdout + outcome0.stdoutFragment &&
                plannedStderr == preStderr + outcome0.stderrFragment;
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
              plannedStdout == preStdout + step0.outcome.stdoutFragment &&
              plannedStderr == preStderr + step0.outcome.stderrFragment;
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
              plannedStdout == preStdout + step0.outcome.stdoutFragment &&
              plannedStderr == preStderr + step0.outcome.stderrFragment;
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
              plannedStdout == preStdout + step0.outcome.stdoutFragment &&
              plannedStderr == preStderr + step0.outcome.stderrFragment;
        }
      } else {
        assert target == dest;
        assert exists step0: StepEvidence ::
            StepEvidenceFor(source, dest, cmd, preCwd, step0) &&
            step0.beforeFs == preFs &&
            step0.afterFs == movedFs &&
            exit == (if step0.outcome.failed then 1 else 0) &&
            plannedStdout == preStdout + step0.outcome.stdoutFragment &&
            plannedStderr == preStderr + step0.outcome.stderrFragment;
      }
      assert RunTwoOperandEvidenceFields(
          cmd, preFs, preCwd, io.fs(),
          preStdout, preStderr, plannedStdout, plannedStderr, exit
        ) by {
        reveal RunTwoOperandEvidenceFields();
      }
      hide RunTwoOperandEvidenceFields();
      assert PreparedSummaryIO(raw, preFs, preCwd, preStdout, preStderr, io, exit, plannedStdout, plannedStderr) by {
        hide *;
        reveal PreparedSummaryIO(), PreparedSummary(), CandidateSummary(),
               RunIntoDirectorySummary(), DirectoryStatusSummary(), RunStatusSummary(),
               RunIntoDirectoryEvidenceFields(), DirectoryStatusEvidenceFor(), RunStatusEvidenceFor();
      }
      assert io.statusCursor() == firstStatus + |calls|;
      assert StatusCallsFor(
          Spec.NativeStatusInputs(io.statusObservations(), io.trustedNativeFailures(), io.now()), firstStatus, calls
        );
      if cmd.noTargetDirectory {
        assert calls == step.statusCalls;
        assert step.firstStatus == firstStatus;
        assert step.beforeFs == preFs && step.afterFs == io.fs();
      } else {
        assert calls == [directoryCall] + step.statusCalls;
        assert Spec.StatusRequest(directoryCall, preFs, dest, true) by {
          reveal Spec.StatusRequest(), MetadataStatusCall();
        }
        assert step.firstStatus == firstStatus + 1;
        assert step.beforeFs == preFs && step.afterFs == io.fs();
      }
      assert RunStatusEvidenceFor(
          raw, preFs, preCwd, io.fs(),
          preStdout, plannedStdout, preStderr, plannedStderr,
          exit, Spec.NativeStatusInputs(io.statusObservations(), io.trustedNativeFailures(), io.now()), firstStatus,
          io.statusCursor(), calls, runEvidence
        ) by {
        hide *;
        reveal PreparedSummaryIO(), PreparedSummary(), CandidateSummary(),
               RunIntoDirectorySummary(), DirectoryStatusSummary(), RunStatusSummary(),
               RunIntoDirectoryEvidenceFields(), DirectoryStatusEvidenceFor(), RunStatusEvidenceFor();
      }
      StatusTranscriptWitness(Spec.NativeStatusInputs(io.statusObservations(), io.trustedNativeFailures(), io.now()),
                              firstStatus, io.statusCursor(), calls);
      assert PreparedSummary(raw, io, exit, plannedStdout, plannedStderr);
      return;
    }

    var directory := cmd.operands[|cmd.operands| - 1];
    var sources := cmd.operands[..|cmd.operands| - 1];
    ghost var directoryEvidence: DirectoryStatusEvidence;
    exit, calls, directoryEvidence, plannedStdout, plannedStderr := PrepareIntoDirectory(
      sources, directory, false, cmd, io
    );
    runEvidence := DirectoryRunStatus(directoryEvidence);
    assert PreparedSummaryIO(raw, preFs, preCwd, preStdout, preStderr, io, exit, plannedStdout, plannedStderr) by {
      hide *;
      reveal PreparedSummaryIO(), PreparedSummary(), CandidateSummary(),
             RunIntoDirectorySummary(), DirectoryStatusSummary(), RunStatusSummary(),
             RunIntoDirectoryEvidenceFields(), DirectoryStatusEvidenceFor(), RunStatusEvidenceFor();
    }
    assert RunStatusEvidenceFor(
        raw, preFs, preCwd, io.fs(),
        preStdout, plannedStdout, preStderr, plannedStderr,
        exit, Spec.NativeStatusInputs(io.statusObservations(), io.trustedNativeFailures(), io.now()), firstStatus,
        io.statusCursor(), calls, runEvidence
      ) by {
      hide *;
      reveal PreparedSummaryIO(), PreparedSummary(), CandidateSummary(),
             RunIntoDirectorySummary(), DirectoryStatusSummary(), RunStatusSummary(),
             RunIntoDirectoryEvidenceFields(), DirectoryStatusEvidenceFor(), RunStatusEvidenceFor();
    }
    StatusTranscriptWitness(Spec.NativeStatusInputs(io.statusObservations(), io.trustedNativeFailures(), io.now()),
                            firstStatus, io.statusCursor(), calls);
    assert PreparedSummary(raw, io, exit, plannedStdout, plannedStderr);
  }

  method CheckTargetDirectory(directory: string, io: BenchIO.IO)
    returns (ok: bool, err: int, ghost call: Spec.StatusCallEvidence)
    modifies io.statusObservationsRegion
    ensures TargetDirectoryCheckSummaryFields(directory, old(io.fs()), ok, err)
    ensures Spec.StatusRequest(call, old(io.fs()), directory, true)
    ensures ok == (call.ok && call.status.kind == BenchWorld.DirectoryKind)
    ensures io.statusCursor() == old(io.statusCursor()) + 1
    ensures StatusCallsFor(Spec.NativeStatusInputs(io.statusObservations(), io.trustedNativeFailures(), io.now()), old(io.statusCursor()), [call])
  {
    var getFileStatusResult5 := io.GetFileStatus(directory, true);
    var rawMetadataOk3 := getFileStatusResult5.Ok?;
    var rawMetadataStatus3 := IOContract.ResultValue(getFileStatusResult5, BenchWorld.DEFAULT_FILE_STATUS);
    var rawMetadataErr3 := IOContract.ResultErrno(getFileStatusResult5);
    call := Spec.StatusCallEvidence(old(io.fs()), directory, true,
                                    rawMetadataOk3, rawMetadataStatus3, rawMetadataErr3);
    MetadataProof.FileStatusStructureImpliesMetadata(io.fs(), directory, true, rawMetadataOk3, rawMetadataStatus3, rawMetadataErr3);
    var statOk := rawMetadataOk3;
    var isDir := rawMetadataStatus3.kind == BenchWorld.DirectoryKind;
    var statErr := rawMetadataErr3;
    ok := statOk && isDir;
    if statOk && !isDir {
      err := Errno.ENOTDIR;
    } else {
      err := statErr;
    }
  }

  method {:isolate_assertions} PrepareIntoDirectory(
    sources: seq<string>,
    directory: string,
    explicitTargetDirectory: bool,
    cmd: Schema.MvCmd,
    io: BenchIO.IO
  ) returns (exit: int, ghost calls: seq<Spec.StatusCallEvidence>,
             ghost evidence: DirectoryStatusEvidence,
             plannedStdout: BenchWorld.Bytes, plannedStderr: BenchWorld.Bytes)
    modifies io.fsRegion, io.statusObservationsRegion
    ensures RunIntoDirectorySummary(io, sources, directory, explicitTargetDirectory, cmd, plannedStdout, plannedStderr, exit)
    ensures io.statusCursor() == old(io.statusCursor()) + |calls|
    ensures StatusCallsFor(Spec.NativeStatusInputs(io.statusObservations(), io.trustedNativeFailures(), io.now()), old(io.statusCursor()), calls)
    ensures DirectoryStatusSummary(io, sources, directory, cmd, plannedStdout, plannedStderr, exit, calls, evidence)
    decreases *
  {
    plannedStdout, plannedStderr := [], [];
    ghost var preFs := io.fs();
    ghost var preCwd := io.cwd();
    ghost var preStdout := plannedStdout;
    ghost var preStderr := plannedStderr;
    ghost var firstStatus := io.statusCursor();
    var dirOk, dirErr, dirCall := CheckTargetDirectory(directory, io);
    calls := [dirCall];
    assert StatusCallsFor(Spec.NativeStatusInputs(io.statusObservations(), io.trustedNativeFailures(), io.now()), firstStatus, calls);
    if !dirOk {
      evidence := FailedDirectoryStatus(dirCall);
      var err := Spec.TargetFailureMessageSpec(directory, explicitTargetDirectory, dirErr);
      plannedStderr := plannedStderr + err;
      exit := 1;
      assert TargetDirectoryCheckSummaryFields(directory, preFs, false, dirErr);
      assert RunIntoDirectoryEvidenceFields(
          sources, directory, explicitTargetDirectory, cmd,
          preFs, preCwd, io.fs(), preStdout, preStderr,
          plannedStdout, plannedStderr, exit
        );
      return;
    }

    var hadError, out, errOut, batch := MoveSourcesIntoDirectory(
      sources, directory, cmd, io
    );
    assert StatusCallsFor(Spec.NativeStatusInputs(io.statusObservations(), io.trustedNativeFailures(), io.now()), firstStatus, [dirCall]);
    assert batch.firstStatus == firstStatus + 1;
    assert StatusCallsFor(
        Spec.NativeStatusInputs(io.statusObservations(), io.trustedNativeFailures(), io.now()), firstStatus + 1, batch.statusCalls
      );
    {
      hide *;
      StatusCallsConcat(Spec.NativeStatusInputs(io.statusObservations(), io.trustedNativeFailures(), io.now()), firstStatus,
                        [dirCall], batch.statusCalls);
    }
    calls := [dirCall] + batch.statusCalls;
    evidence := SuccessfulDirectoryStatus(dirCall, batch);
    ghost var movedFs := io.fs();
    plannedStdout := plannedStdout + out;
    plannedStderr := plannedStderr + errOut;
    exit := if hadError then 1 else 0;
    assert dirErr == 0;
    assert (exit == 1) == hadError;
    assert TargetDirectoryCheckSummaryFields(directory, preFs, true, 0);
    assert io.fs() == movedFs;
    assert plannedStdout == preStdout + out;
    assert plannedStderr == preStderr + errOut;
    assert RunIntoDirectoryEvidenceFields(
        sources, directory, explicitTargetDirectory, cmd,
        preFs, preCwd, io.fs(), preStdout, preStderr,
        plannedStdout, plannedStderr, exit
      );
  }

  datatype RenameFrame = RenameFrame(
    sourceIsDir: bool, targetFound: bool, targetErr: int, backupPath: string,
    ghost sameFile: SameFileEvidence, ghost backup: BackupSelectionEvidence,
    ghost beforeFs: BenchWorld.FileSystem, ghost cwd: BenchWorld.Path,
    ghost firstStatus: nat, ghost inputs: Spec.NativeStatusInputs,
    ghost statusCalls: seq<Spec.StatusCallEvidence>
  )

  ghost function RenameFramePrototype(frame: RenameFrame): StepEvidence
  {
    MakeStepEvidence(frame.beforeFs, frame.beforeFs, [], [], false,
                     true, frame.sourceIsDir, 0, true, frame.targetFound, frame.targetErr,
                     frame.sameFile, frame.backup, [], frame.beforeFs,
                     StatusTranscript(frame.firstStatus, frame.statusCalls, frame.inputs))
  }

  lemma ExistingTargetNonempty(fs: BenchWorld.FileSystem, target: string)
    requires Spec.StatusExistsOutcomeFields(fs, target, false, true, 0)
    ensures target != ""
  {
    hide *;
    reveal Spec.StatusExistsOutcomeFields(), IOContract.PathExistsContractFields(), IOContract.ResolvePathForMetadataFields();
  }

  lemma SelectedBackupNonempty(target: string, mode: Schema.BackupMode, suffix: string,
                               fs: BenchWorld.FileSystem, evidence: BackupSelectionEvidence)
    requires BackupSelectionEvidenceFor(target, mode, suffix, fs, evidence)
    requires evidence.SelectedBackup? && target != ""
    ensures evidence.backupPath != ""
  {
    hide *;
    reveal BackupSelectionEvidenceFor(), BackupChecksFor();
    reveal MvPathSpec.SimpleBackupPathSpec(), MvPathSpec.NumberedBackupPathSpec();
  }

  ghost opaque predicate RenameFrameReady(
    source: string, target: string, cmd: Schema.MvCmd, frame: RenameFrame
  )
  {
    IOContract.IsDirectoryStrictContractFields(frame.beforeFs, source, false,
                                               true, frame.sourceIsDir, 0) &&
    Spec.StatusExistsOutcomeFields(frame.beforeFs, target, false, frame.targetFound, frame.targetErr) &&
    StatusCallsFor(frame.inputs, frame.firstStatus, frame.statusCalls) &&
    StepStatusEvidenceFor(source, target, cmd, RenameFramePrototype(frame)) &&
    SourceResolutionObservationFor(source, frame.cwd, RenameFramePrototype(frame)) &&
    if !frame.targetFound then
      frame.sameFile == NoSameFileCheck && frame.backup == NoBackupSelection && frame.backupPath == ""
    else
      cmd.overwriteMode != Schema.OverwriteSkip && cmd.updateMode != Schema.UpdateNone &&
      cmd.updateMode != Schema.UpdateNoneFail &&
      SameFileEvidenceFor(cmd, frame.beforeFs, frame.cwd, source, target, frame.sameFile) &&
      frame.sameFile.CheckedSameFile? && frame.sameFile.decision == ContinueMove &&
      (cmd.updateMode != Schema.UpdateOlder || Spec.SourceNewerSpec(
         frame.sameFile.source.times.mtimeSec, frame.sameFile.source.times.mtimeNsec,
         frame.sameFile.target.times.mtimeSec, frame.sameFile.target.times.mtimeNsec)) &&
      BackupCollisionEvidenceFor(cmd, frame.beforeFs, source, target, frame.sameFile.source,
                                 frame.sameFile.sourceEntry, frame.sameFile.targetEntry, frame.sameFile.backupCollision) &&
      !BackupCollisionDetected(frame.sameFile.backupCollision) &&
      (if cmd.backupMode == Schema.BackupOff then
         frame.backup == NoBackupSelection && frame.backupPath == ""
       else frame.backup.SelectedBackup? && frame.backup.backupPath == frame.backupPath &&
            frame.backupPath != "" &&
            BackupSelectionEvidenceFor(target, cmd.backupMode, cmd.backupSuffix, frame.beforeFs, frame.backup))
  }

  ghost opaque predicate RenamePhaseSummary(
    source: string, target: string, cmd: Schema.MvCmd, frame: RenameFrame,
    afterFs: BenchWorld.FileSystem, outcome: Spec.MoveOutcome, step: StepEvidence
  )
  {
    StepEvidenceFor(source, target, cmd, frame.cwd, step) &&
    StepStatusEvidenceFor(source, target, cmd, step) &&
    step.beforeFs == frame.beforeFs && step.afterFs == afterFs && step.outcome == outcome &&
    step.firstStatus == frame.firstStatus && step.inputs == frame.inputs &&
    step.statusCalls == frame.statusCalls && StatusCallsFor(frame.inputs, step.firstStatus, step.statusCalls)
  }

  lemma AssembleRenamedStep(
    source: string, target: string, cmd: Schema.MvCmd, frame: RenameFrame,
    afterFs: BenchWorld.FileSystem, outcome: Spec.MoveOutcome,
    calls: seq<RenameCallEvidence>, backupFs: BenchWorld.FileSystem
  ) returns (step: StepEvidence)
    requires RenameFrameReady(source, target, cmd, frame)
    requires RenameEvidenceFor(source, target, frame.sourceIsDir, frame.targetFound,
                               frame.backupPath, cmd.verbose, cmd.debug, frame.beforeFs, frame.cwd,
                               afterFs, outcome, calls, backupFs)
    requires RenameNativeObservationsFor(source, target,
                                         MakeStepEvidence(frame.beforeFs, afterFs, outcome.stdoutFragment, outcome.stderrFragment, outcome.failed,
                                                          true, frame.sourceIsDir, 0, true, frame.targetFound, frame.targetErr,
                                                          frame.sameFile, frame.backup, calls, backupFs,
                                                          StatusTranscript(frame.firstStatus, frame.statusCalls, frame.inputs)))
    ensures RenamePhaseSummary(source, target, cmd, frame, afterFs, outcome, step)
  {
    hide *;
    reveal RenameFrameReady(), RenameFramePrototype(), MakeStepEvidence();
    step := MakeStepEvidence(frame.beforeFs, afterFs, outcome.stdoutFragment, outcome.stderrFragment, outcome.failed,
                             true, frame.sourceIsDir, 0, true, frame.targetFound, frame.targetErr,
                             frame.sameFile, frame.backup, calls, backupFs,
                             StatusTranscript(frame.firstStatus, frame.statusCalls, frame.inputs));
    StepStatusEvidenceTransfer(source, target, cmd, RenameFramePrototype(frame), step);
    assert SourceResolutionObservationFor(source, frame.cwd, step) by {
      reveal SourceResolutionObservationFor();
    }
    if frame.targetFound {
      assert ExistingTargetRenameEvidenceFor(source, target, cmd, frame.cwd, step) by {
        reveal ExistingTargetRenameEvidenceFor();
      }
      PackageExistingTargetRenameStep(source, target, cmd, frame.cwd, step);
    } else {
      PackageMissingTargetStep(source, target, cmd, frame.cwd, step);
    }
    reveal RenamePhaseSummary(), RenamePhase();
  }

  method AttemptRename(source: string, target: string, io: BenchIO.IO)
    returns (ok: bool, err: int, ghost call: RenameCallEvidence)
    modifies io.fsRegion
    ensures call == RenameCallEvidence(ok, err, io.fs())
    ensures IOContract.RenamePathSpec(old(io.fs()), io.now(), io.trustedNativeFailures(),
                                      io.fs(), source, target, ok, err)
    ensures IOContract.RenamePathContractFields(old(io.fs()), source, target, ok, err, io.fs())
    ensures ok <==> err == 0
  {
    var result := io.RenamePath(source, target);
    ok := result.Ok?;
    err := IOContract.ResultErrno(result);
    call := RenameCallEvidence(ok, err, io.fs());
  }

  method RenameOriginalSource(
    source: string, target: string, backupPath: string, sourceIsDir: bool,
    targetWasFound: bool, cmd: Schema.MvCmd, io: BenchIO.IO
  ) returns (outcome: Spec.MoveOutcome, ghost call: RenameCallEvidence)
    modifies io.fsRegion
    ensures call.afterFs == io.fs()
    ensures IOContract.RenamePathSpec(old(io.fs()), io.now(), io.trustedNativeFailures(),
                                      io.fs(), source, target, call.ok, call.err)
    ensures IOContract.RenamePathContractFields(old(io.fs()), source, target, call.ok, call.err, io.fs())
    ensures if call.ok then outcome == Spec.MoveOutcome(
                                         Text.StepSuccessStdoutSpec(source, target, backupPath, cmd.verbose, cmd.debug), [], false)
            else outcome == Spec.MoveOutcome([], Spec.SourceRenameFailureMessageSpec(source, target,
                                                                                     Spec.SourceRenameDiagnosticErrSpec(target, sourceIsDir, call.err), sourceIsDir && targetWasFound), true)
  {
    var ok, err, actual := AttemptRename(source, target, io);
    call := actual;
    var output: BenchWorld.Bytes := [];
    var diagnostics: BenchWorld.Bytes := [];
    if ok {
      output := Spec.StepSuccessStdoutSpec(source, target, backupPath, cmd.verbose, cmd.debug);
    } else {
      diagnostics := Spec.SourceRenameFailureMessageSpec(source, target,
                                                         Spec.SourceRenameDiagnosticErrSpec(target, sourceIsDir, err),
                                                         sourceIsDir && targetWasFound);
    }
    outcome := Spec.MoveOutcome(output, diagnostics, !ok);
  }

  method ExecuteRenameFrame(source: string, target: string, cmd: Schema.MvCmd,
                            frame: RenameFrame, io: BenchIO.IO)
    returns (hadError: bool, out: BenchWorld.Bytes, errOut: BenchWorld.Bytes, ghost step: StepEvidence)
    requires RenameFrameReady(source, target, cmd, frame)
    requires io.fs() == frame.beforeFs && io.cwd() == frame.cwd
    requires Spec.NativeStatusInputs(io.statusObservations(), io.trustedNativeFailures(), io.now()) == frame.inputs
    requires io.statusCursor() == frame.firstStatus + |frame.statusCalls|
    modifies io.fsRegion
    ensures RenamePhase(io, source, target, cmd, frame, Spec.MoveOutcome(out, errOut, hadError), step)
  {
    reveal RenamePhaseSummary();
    hide IOContract.RenamePathSpec(), IOContract.RenamePathContractFields();
    hide StepStatusEvidenceFor(), StatusCallsFor(), Spec.StatusCallsFor();
    hide IOContract.IsDirectoryStrictContractFields(), Spec.StatusExistsOutcomeFields();
    hide IOContract.GetFileStatusResultFields(), IOContract.FileStatusStructureContractFields();
    hide SameFileEvidenceFor(), BackupSelectionEvidenceFor(), BackupCollisionEvidenceFor();
    reveal RenameFrameReady();
    assert (frame.backupPath == "") == frame.backup.NoBackupSelection?;
    assert frame.backupPath != "" ==> frame.backup.SelectedBackup?;
    var outcome: Spec.MoveOutcome;
    ghost var calls: seq<RenameCallEvidence>;
    ghost var backupFs := frame.beforeFs;
    if frame.backupPath != "" {
      var backupOk, backupErr, backupCall := AttemptRename(target, frame.backupPath, io);
      backupFs := io.fs();
      if !backupOk {
        var diagnostics := Spec.RenameFailureMessageSpec(source, target, backupErr);
        outcome := Spec.MoveOutcome([], diagnostics, true);
        calls := [backupCall];
      } else {
        ghost var sourceCall: RenameCallEvidence;
        outcome, sourceCall := RenameOriginalSource(source, target, frame.backupPath,
                                                    frame.sourceIsDir, false, cmd, io);
        calls := [backupCall, sourceCall];
      }
    } else {
      ghost var sourceCall: RenameCallEvidence;
      outcome, sourceCall := RenameOriginalSource(source, target, "", frame.sourceIsDir,
                                                  frame.targetFound, cmd, io);
      calls := [sourceCall];
    }
    assert RenameEvidenceFor(source, target, frame.sourceIsDir, frame.targetFound,
                             frame.backupPath, cmd.verbose, cmd.debug, frame.beforeFs, frame.cwd, io.fs(), outcome, calls, backupFs) by {
      reveal RenameEvidenceFor();
    }
    assert |calls| <= 2;
    if frame.backup.NoBackupSelection? {
      assert |calls| == 1;
      assert IOContract.RenamePathSpec(frame.beforeFs, frame.inputs.now, frame.inputs.failures,
                                       calls[0].afterFs, source, target, calls[0].ok, calls[0].err);
    } else {
      assert frame.backup.backupPath == frame.backupPath;
      assert IOContract.RenamePathSpec(frame.beforeFs, frame.inputs.now, frame.inputs.failures,
                                       calls[0].afterFs, target, frame.backup.backupPath, calls[0].ok, calls[0].err);
      if |calls| == 2 {
        assert IOContract.RenamePathSpec(calls[0].afterFs, frame.inputs.now, frame.inputs.failures,
                                         calls[1].afterFs, source, target, calls[1].ok, calls[1].err);
      }
    }
    assert RenameNativeObservationsFor(source, target,
                                       MakeStepEvidence(frame.beforeFs, io.fs(), outcome.stdoutFragment, outcome.stderrFragment, outcome.failed,
                                                        true, frame.sourceIsDir, 0, true, frame.targetFound, frame.targetErr, frame.sameFile, frame.backup,
                                                        calls, backupFs, StatusTranscript(frame.firstStatus, frame.statusCalls, frame.inputs))) by {
      hide *;
      reveal RenameNativeObservationsFor(), MakeStepEvidence();
    }
    step := AssembleRenamedStep(source, target, cmd, frame, io.fs(), outcome, calls, backupFs);
    hadError, out, errOut := outcome.failed, outcome.stdoutFragment, outcome.stderrFragment;
  }

  ghost opaque predicate ComparisonInputs(
    source: string, target: string, cmd: Schema.MvCmd,
    sourceMetadata: MetadataEvidence, targetMetadata: MetadataEvidence,
    frame: RenameFrame, io: BenchIO.IO
  )
    reads io.Footprint()
  {
    cmd.overwriteMode != Schema.OverwriteSkip && cmd.updateMode != Schema.UpdateNone &&
    cmd.updateMode != Schema.UpdateNoneFail &&
    sourceMetadata.ok && targetMetadata.ok && frame.targetFound && frame.targetErr == 0 &&
    MetadataEvidenceFor(frame.beforeFs, source, false, sourceMetadata) &&
    MetadataEvidenceFor(frame.beforeFs, target, false, targetMetadata) &&
    frame.sourceIsDir == sourceMetadata.isDir &&
    IOContract.IsDirectoryStrictContractFields(frame.beforeFs, source, false, true, frame.sourceIsDir, 0) &&
    Spec.StatusExistsOutcomeFields(frame.beforeFs, target, false, true, 0) &&
    frame.sameFile == NoSameFileCheck && frame.backup == NoBackupSelection && frame.backupPath == "" &&
    frame.statusCalls == [MetadataStatusCall(frame.beforeFs, source, false, sourceMetadata),
                          MetadataStatusCall(frame.beforeFs, target, false, targetMetadata)] &&
    StatusCallsFor(frame.inputs, frame.firstStatus, frame.statusCalls) &&
    frame.beforeFs == io.fs() && frame.cwd == io.cwd() &&
    frame.inputs == Spec.NativeStatusInputs(io.statusObservations(), io.trustedNativeFailures(), io.now()) &&
    io.statusCursor() == frame.firstStatus + 2
  }

  ghost opaque predicate ComparisonFrameFields(
    source: string, target: string, cmd: Schema.MvCmd, frame: RenameFrame
  )
  {
    cmd.overwriteMode != Schema.OverwriteSkip && cmd.updateMode != Schema.UpdateNone &&
    cmd.updateMode != Schema.UpdateNoneFail && frame.targetFound && frame.targetErr == 0 &&
    IOContract.IsDirectoryStrictContractFields(frame.beforeFs, source, false, true, frame.sourceIsDir, 0) &&
    Spec.StatusExistsOutcomeFields(frame.beforeFs, target, false, true, 0) &&
    frame.backup == NoBackupSelection && frame.backupPath == "" &&
    StatusCallsFor(frame.inputs, frame.firstStatus, frame.statusCalls) &&
    SameFileEvidenceFor(cmd, frame.beforeFs, frame.cwd, source, target, frame.sameFile) &&
    frame.sameFile.CheckedSameFile? && frame.sourceIsDir == frame.sameFile.source.isDir &&
    frame.sameFile.backupCollision == NoBackupCollisionCheck &&
    SourceResolutionObservationFor(source, frame.cwd, RenameFramePrototype(frame)) &&
    var same := frame.sameFile;
    var calls := frame.statusCalls;
    |calls| >= 4 &&
    calls[0] == MetadataStatusCall(frame.beforeFs, source, false, same.source) &&
    calls[1] == MetadataStatusCall(frame.beforeFs, target, false, same.target) &&
    calls[2] == MetadataStatusCall(frame.beforeFs, same.sourceEntry.parent, false, same.sourceEntry.parentMetadata) &&
    calls[3] == MetadataStatusCall(frame.beforeFs, same.targetEntry.parent, false, same.targetEntry.parentMetadata) &&
    (if same.decision.FailedParentStat? && same.sourceReferentEntry.NoEntryNameEvidence? then |calls| == 4
     else if same.source.isSymlink then
       |calls| >= 5 && same.sourceFollowed.SomeMetadataEvidence? &&
       calls[4] == MetadataStatusCall(frame.beforeFs, source, true, same.sourceFollowed.value) &&
       (match same.sourceReferentEntry
        case SomeEntryNameEvidence(_, value) => |calls| == 6 &&
                                                calls[5] == MetadataStatusCall(frame.beforeFs, value.parent, false, value.parentMetadata)
        case FailedEntryNameEvidence(_) => |calls| == 5
        case NoEntryNameEvidence => false)
     else |calls| == 4)
  }

  ghost function StoppedComparisonOutcome(source: string, target: string, cmd: Schema.MvCmd,
                                          frame: RenameFrame): Spec.MoveOutcome
    requires frame.sameFile.CheckedSameFile?
  {
    var decision := frame.sameFile.decision;
    if decision.FailedParentStat? then
      Spec.MoveOutcome([], Spec.ParentStatFailureMessageSpec(decision.path, decision.err), true)
    else if decision == RejectSameFile then
      Spec.MoveOutcome([], Spec.SameFileMessageSpec(source, target), true)
    else Spec.MoveOutcome(Text.SkipStdoutSpec(target, cmd.debug), [], false)
  }

  lemma AssembleStoppedComparison(
    source: string, target: string, cmd: Schema.MvCmd, frame: RenameFrame,
    outcome: Spec.MoveOutcome
  ) returns (step: StepEvidence)
    requires ComparisonFrameFields(source, target, cmd, frame)
    requires frame.sameFile.CheckedSameFile?
    requires frame.sameFile.decision.FailedParentStat? || frame.sameFile.decision == RejectSameFile ||
             (cmd.updateMode == Schema.UpdateOlder && !Spec.SourceNewerSpec(
                frame.sameFile.source.times.mtimeSec, frame.sameFile.source.times.mtimeNsec,
                frame.sameFile.target.times.mtimeSec, frame.sameFile.target.times.mtimeNsec))
    requires outcome == StoppedComparisonOutcome(source, target, cmd, frame)
    ensures RenamePhaseSummary(source, target, cmd, frame, frame.beforeFs, outcome, step)
  {
    hide *;
    reveal ComparisonFrameFields(), RenameFramePrototype(), MakeStepEvidence();
    reveal SameFileEvidenceFor(), MetadataEvidenceFor(), MetadataStatusCall(), Spec.StatusRequest();
    step := MakeStepEvidence(frame.beforeFs, frame.beforeFs, outcome.stdoutFragment, outcome.stderrFragment,
                             outcome.failed, true, frame.sourceIsDir, 0, true, true, 0, frame.sameFile, NoBackupSelection,
                             [], frame.beforeFs, StatusTranscript(frame.firstStatus, frame.statusCalls, frame.inputs));
    assert StepStatusEvidenceFor(source, target, cmd, step) by {
      reveal StepStatusEvidenceFor();
    }
    assert SourceResolutionObservationFor(source, frame.cwd, step) by {
      reveal SourceResolutionObservationFor();
    }
    assert RenameNativeObservationsFor(source, target, step) by {
      reveal RenameNativeObservationsFor();
    }
    reveal StoppedComparisonOutcome();
    reveal StepEvidenceFor();
    reveal RenamePhaseSummary(), RenamePhase();
  }

  method ResolveSourceIdentity(source: string, io: BenchIO.IO)
    returns (ok: bool, path: string, err: int)
    ensures IOContract.ResolvePathIdentitySpec(old(io.fs()), old(io.cwd()), io.trustedNativeFailures(),
                                               source, ok, path, err)
    ensures IOContract.ResolvePathIdentityContractFields(old(io.fs()), old(io.cwd()), source, ok, path, err)
    ensures ok <==> err == 0
  {
    var result := io.ResolvePathIdentity(source);
    ok := result.Ok?;
    path := IOContract.ResultValue(result, "");
    err := IOContract.ResultErrno(result);
  }

  method CaptureMoveComparison(source: string, target: string, cmd: Schema.MvCmd,
                               sourceMetadata: MetadataEvidence, targetMetadata: MetadataEvidence, frame: RenameFrame, io: BenchIO.IO)
    returns (same: SameFileEvidence, ghost resultFrame: RenameFrame)
    requires ComparisonInputs(source, target, cmd, sourceMetadata, targetMetadata, frame, io)
    modifies io.statusObservationsRegion
    ensures ComparisonFrameFields(source, target, cmd, resultFrame)
    ensures resultFrame.sourceIsDir == frame.sourceIsDir && resultFrame.targetFound == frame.targetFound &&
            resultFrame.targetErr == frame.targetErr && resultFrame.beforeFs == frame.beforeFs &&
            resultFrame.cwd == frame.cwd && resultFrame.firstStatus == frame.firstStatus && resultFrame.inputs == frame.inputs
    ensures resultFrame.sameFile == same && same.CheckedSameFile?
    ensures same.source == sourceMetadata && same.target == targetMetadata
    ensures io.statusCursor() == resultFrame.firstStatus + |resultFrame.statusCalls|
    decreases *
  {
    hide IOContract.GetFileStatusResultFields(), IOContract.FileStatusStructureContractFields();
    hide StatusCallsFor(), Spec.StatusCallsFor(), MetadataEvidenceFor(), ObservedMetadataEvidenceFor();
    hide EntryNameEvidenceFor(), IOContract.ResolvePathIdentitySpec(), IOContract.ResolvePathIdentityContractFields();
    reveal ComparisonInputs();
    ghost var preFs := frame.beforeFs;
    ghost var preCwd := frame.cwd;
    ghost var firstStatus := frame.firstStatus;
    ghost var statusCalls := frame.statusCalls;
    var sourceEntry := CaptureEntryName(source, io);
    ghost var nextStatusCall := MetadataStatusCall(preFs, sourceEntry.parent, false, sourceEntry.parentMetadata);
    assert StatusCallsFor(frame.inputs, firstStatus + |statusCalls|, [nextStatusCall]) by {
      hide *;
      reveal ComparisonInputs();
    }
    StatusCallsConcat(frame.inputs, firstStatus, statusCalls, [nextStatusCall]);
    statusCalls := statusCalls + [nextStatusCall];
    assert io.statusCursor() == firstStatus + |statusCalls|;
    var targetEntry := CaptureEntryName(target, io);
    nextStatusCall := MetadataStatusCall(preFs, targetEntry.parent, false, targetEntry.parentMetadata);
    assert StatusCallsFor(frame.inputs, firstStatus + |statusCalls|, [nextStatusCall]) by {
      hide *;
      reveal ComparisonInputs();
    }
    StatusCallsConcat(frame.inputs, firstStatus, statusCalls, [nextStatusCall]);
    statusCalls := statusCalls + [nextStatusCall];
    assert io.statusCursor() == firstStatus + |statusCalls|;
    if sourceEntry.leaf == targetEntry.leaf &&
       (!sourceEntry.parentMetadata.ok || !targetEntry.parentMetadata.ok) {
      var failedPath := if !sourceEntry.parentMetadata.ok then sourceEntry.parent else targetEntry.parent;
      var parentErr := if !sourceEntry.parentMetadata.ok then sourceEntry.parentMetadata.err else targetEntry.parentMetadata.err;
      same := CheckedSameFile(sourceMetadata, targetMetadata, NoMetadataEvidence,
                              sourceEntry, targetEntry, NoEntryNameEvidence, NoBackupCollisionCheck,
                              FailedParentStat(failedPath, parentErr));
      assert SameFileEvidenceFor(cmd, preFs, preCwd, source, target, same) by {
        hide *;
        reveal ComparisonInputs();
        reveal SameFileEvidenceFor();
      }
    } else {
      var sourceFollowed: OptionalMetadataEvidence := NoMetadataEvidence;
      var sourceReferentEntry: OptionalEntryNameEvidence := NoEntryNameEvidence;
      if sourceMetadata.isSymlink {
        var followed := CaptureMetadata(source, true, io);
        nextStatusCall := MetadataStatusCall(preFs, source, true, followed);
        assert StatusCallsFor(frame.inputs, firstStatus + |statusCalls|, [nextStatusCall]) by {
          hide *;
          reveal ComparisonInputs();
        }
        StatusCallsConcat(frame.inputs, firstStatus, statusCalls, [nextStatusCall]);
        statusCalls := statusCalls + [nextStatusCall];
        assert io.statusCursor() == firstStatus + |statusCalls|;
        sourceFollowed := SomeMetadataEvidence(followed);
        var resolveOk, resolvedSource, resolveErr := ResolveSourceIdentity(source, io);
        if resolveOk {
          var referentEntry := CaptureEntryName(resolvedSource, io);
          nextStatusCall := MetadataStatusCall(preFs, referentEntry.parent, false, referentEntry.parentMetadata);
          assert StatusCallsFor(frame.inputs, firstStatus + |statusCalls|, [nextStatusCall]) by {
            hide *;
            reveal ComparisonInputs();
          }
          StatusCallsConcat(frame.inputs, firstStatus, statusCalls, [nextStatusCall]);
          statusCalls := statusCalls + [nextStatusCall];
          assert io.statusCursor() == firstStatus + |statusCalls|;
          sourceReferentEntry := SomeEntryNameEvidence(resolvedSource, referentEntry);
        } else {
          sourceReferentEntry := FailedEntryNameEvidence(resolveErr);
        }
      }
      var decision: SameFileDecision;
      if sourceReferentEntry.SomeEntryNameEvidence? &&
         sourceReferentEntry.value.leaf == targetEntry.leaf &&
         (!sourceReferentEntry.value.parentMetadata.ok || !targetEntry.parentMetadata.ok) {
        var referentEntry := sourceReferentEntry.value;
        decision := FailedParentStat(
          if !referentEntry.parentMetadata.ok then referentEntry.parent else targetEntry.parent,
          if !referentEntry.parentMetadata.ok then referentEntry.parentMetadata.err else targetEntry.parentMetadata.err);
      } else {
        var sameEntry := sourceEntry.parentMetadata.ok && targetEntry.parentMetadata.ok &&
                         sourceEntry.parentMetadata.key == targetEntry.parentMetadata.key && sourceEntry.leaf == targetEntry.leaf;
        var referentSameEntry := false;
        if sourceReferentEntry.SomeEntryNameEvidence? {
          var referentEntry := sourceReferentEntry.value;
          referentSameEntry := referentEntry.parentMetadata.ok && targetEntry.parentMetadata.ok &&
                               referentEntry.parentMetadata.key == targetEntry.parentMetadata.key && referentEntry.leaf == targetEntry.leaf;
        }
        var rejectSameFile := sameEntry || (cmd.backupMode == Schema.BackupOff &&
                                            (sourceMetadata.key == targetMetadata.key || referentSameEntry));
        decision := if rejectSameFile then RejectSameFile else ContinueMove;
      }
      same := CheckedSameFile(sourceMetadata, targetMetadata, sourceFollowed,
                              sourceEntry, targetEntry, sourceReferentEntry, NoBackupCollisionCheck, decision);
      assert SameFileEvidenceFor(cmd, preFs, preCwd, source, target, same) by {
        hide *;
        reveal ComparisonInputs();
        reveal SameFileEvidenceFor(), EvidenceNamesSame(), ReferentEvidenceNamesTarget();
      }
    }
    resultFrame := frame.(sameFile := same, statusCalls := statusCalls);
    assert ComparisonFrameFields(source, target, cmd, resultFrame) by {
      hide *;
      reveal ComparisonInputs();
      reveal ComparisonFrameFields(), SourceResolutionObservationFor(), RenameFramePrototype(), MakeStepEvidence();
    }
  }

  ghost opaque predicate InitialStepInputs(
    source: string, target: string, cmd: Schema.MvCmd,
    sourceMetadata: MetadataEvidence, targetMetadata: OptionalMetadataEvidence, frame: RenameFrame,
    outcome: Spec.MoveOutcome
  )
  {
    MetadataEvidenceFor(frame.beforeFs, source, false, sourceMetadata) &&
    frame.sourceIsDir == sourceMetadata.isDir &&
    IOContract.IsDirectoryStrictContractFields(frame.beforeFs, source, false,
                                               sourceMetadata.ok, sourceMetadata.isDir, sourceMetadata.err) &&
    frame.sameFile == NoSameFileCheck && frame.backup == NoBackupSelection && frame.backupPath == "" &&
    StatusCallsFor(frame.inputs, frame.firstStatus, frame.statusCalls) &&
    |frame.statusCalls| >= 1 && frame.statusCalls[0] == MetadataStatusCall(frame.beforeFs, source, false, sourceMetadata) &&
    if !sourceMetadata.ok then
      targetMetadata == NoMetadataEvidence && !frame.targetFound && frame.targetErr == 0 &&
      |frame.statusCalls| == 1 && outcome == Spec.MoveOutcome([], Spec.SourceStatFailureMessageSpec(source, sourceMetadata.err), true)
    else
      targetMetadata.SomeMetadataEvidence? && targetMetadata.value.ok &&
      MetadataEvidenceFor(frame.beforeFs, target, false, targetMetadata.value) &&
      frame.targetFound && frame.targetErr == 0 && |frame.statusCalls| == 2 &&
      frame.statusCalls[1] == MetadataStatusCall(frame.beforeFs, target, false, targetMetadata.value) &&
      Spec.StatusExistsOutcomeFields(frame.beforeFs, target, false, true, 0) &&
      (if cmd.overwriteMode == Schema.OverwriteSkip || cmd.updateMode == Schema.UpdateNone then
         outcome == Spec.MoveOutcome(Text.SkipStdoutSpec(target, cmd.debug), [], false)
       else cmd.updateMode == Schema.UpdateNoneFail &&
            outcome == Spec.MoveOutcome([], Spec.NotReplacingMessageSpec(target), true))
  }

  lemma AssembleInitialMoveStep(
    source: string, target: string, cmd: Schema.MvCmd,
    sourceMetadata: MetadataEvidence, targetMetadata: OptionalMetadataEvidence,
    frame: RenameFrame, outcome: Spec.MoveOutcome
  ) returns (step: StepEvidence)
    requires InitialStepInputs(source, target, cmd, sourceMetadata, targetMetadata, frame, outcome)
    ensures RenamePhaseSummary(source, target, cmd, frame, frame.beforeFs, outcome, step)
  {
    hide *;
    reveal InitialStepInputs(), MakeStepEvidence(), MetadataStatusCall(), MetadataEvidenceFor(), Spec.StatusRequest();
    step := MakeStepEvidence(frame.beforeFs, frame.beforeFs, outcome.stdoutFragment, outcome.stderrFragment,
                             outcome.failed, sourceMetadata.ok, sourceMetadata.isDir, sourceMetadata.err,
                             sourceMetadata.ok, frame.targetFound, frame.targetErr, NoSameFileCheck, NoBackupSelection,
                             [], frame.beforeFs, StatusTranscript(frame.firstStatus, frame.statusCalls, frame.inputs));
    assert StepStatusEvidenceFor(source, target, cmd, step) by {
      reveal StepStatusEvidenceFor();
    }
    reveal SourceResolutionObservationFor(), RenameNativeObservationsFor(), StepEvidenceFor();
    reveal RenamePhaseSummary(), RenamePhase();
  }

  method CompleteComparedMove(source: string, target: string, cmd: Schema.MvCmd,
                              comparison: SameFileEvidence, ghost comparisonFrame: RenameFrame, io: BenchIO.IO)
    returns (hadError: bool, out: BenchWorld.Bytes, errOut: BenchWorld.Bytes, ghost step: StepEvidence)
    requires ComparisonFrameFields(source, target, cmd, comparisonFrame)
    requires comparison == comparisonFrame.sameFile && comparison.CheckedSameFile?
    requires io.fs() == comparisonFrame.beforeFs && io.cwd() == comparisonFrame.cwd
    requires Spec.NativeStatusInputs(io.statusObservations(), io.trustedNativeFailures(), io.now()) == comparisonFrame.inputs
    requires io.statusCursor() == comparisonFrame.firstStatus + |comparisonFrame.statusCalls|
    modifies io.fsRegion, io.statusObservationsRegion
    ensures StepEvidenceFor(source, target, cmd, comparisonFrame.cwd, step)
    ensures StepStatusEvidenceFor(source, target, cmd, step)
    ensures step.beforeFs == comparisonFrame.beforeFs && step.afterFs == io.fs()
    ensures step.outcome == Spec.MoveOutcome(out, errOut, hadError)
    ensures step.firstStatus == comparisonFrame.firstStatus && step.inputs == comparisonFrame.inputs
    ensures io.statusCursor() == step.firstStatus + |step.statusCalls|
    ensures StatusCallsFor(step.inputs, step.firstStatus, step.statusCalls)
    decreases *
  {
    hide StepStatusEvidenceFor(), StatusCallsFor(), Spec.StatusCallsFor();
    hide SourceResolutionObservationFor(), RenameNativeObservationsFor();
    hide IOContract.GetFileStatusResultFields(), IOContract.FileStatusStructureContractFields();
    hide IOContract.IsDirectoryStrictContractFields(), Spec.StatusExistsOutcomeFields();
    hide MetadataEvidenceFor(), ObservedMetadataEvidenceFor(), EntryNameEvidenceFor();
    hide IOContract.ResolvePathIdentitySpec(), IOContract.ResolvePathIdentityContractFields();
    reveal RenamePhaseSummary(), RenamePhase();
    ghost var preFs := comparisonFrame.beforeFs;
    ghost var preCwd := comparisonFrame.cwd;
    ghost var firstStatus := comparisonFrame.firstStatus;
    ghost var statusCalls := comparisonFrame.statusCalls;
    ghost var nextStatusCall: Spec.StatusCallEvidence;
    ghost var sameFileEvidence := comparison;
    ghost var backupEvidence: BackupSelectionEvidence := NoBackupSelection;
    ghost var renameCalls: seq<RenameCallEvidence> := [];
    ghost var backupFs := preFs;
    var sourceMetadata := comparison.source;
    var targetMetadata := comparison.target;
    var sourceOk := true;
    var sourceIsDir := sourceMetadata.isDir;
    var sourceErr := 0;
    var found := true;
    var existsErr := 0;
    hadError, out, errOut := false, [], [];
    reveal ComparisonFrameFields(), SameFileEvidenceFor();
    hide IOContract.GetFileStatusResultFields(), IOContract.FileStatusStructureContractFields();
    var sourceEntry := comparison.sourceEntry;
    var targetEntry := comparison.targetEntry;
    var sourceFollowed := comparison.sourceFollowed;
    var sourceReferentEntry := comparison.sourceReferentEntry;
    var sameFileDecision := comparison.decision;
    ghost var afterEntries := |statusCalls|;
    if sameFileDecision.FailedParentStat? || sameFileDecision == RejectSameFile ||
       (cmd.updateMode == Schema.UpdateOlder && !Spec.SourceNewerSpec(
          sourceMetadata.times.mtimeSec, sourceMetadata.times.mtimeNsec,
          targetMetadata.times.mtimeSec, targetMetadata.times.mtimeNsec)) {
      if sameFileDecision.FailedParentStat? {
        hadError := true;
        errOut := Text.ParentStatFailureMessageSpec(sameFileDecision.path, sameFileDecision.err);
      } else if sameFileDecision == RejectSameFile {
        hadError := true;
        errOut := Spec.SameFileMessageSpec(source, target);
      } else if cmd.debug {
        out := Spec.SkipStdoutSpec(target, true);
      }
      step := AssembleStoppedComparison(source, target, cmd, comparisonFrame,
                                        Spec.MoveOutcome(out, errOut, hadError));
      reveal RenamePhaseSummary(), RenamePhase();
      return;
    }
    assert sameFileDecision == ContinueMove;

    ghost var collisionEvidence: BackupCollisionEvidence :=
      NoBackupCollisionCheck;
    if (cmd.backupMode == Schema.BackupSimple ||
        cmd.backupMode == Schema.BackupExisting) &&
       sourceEntry.leaf ==
       targetEntry.leaf + cmd.backupSuffix
    {
      var candidateMetadata := CaptureMetadata(
        MvPathSpec.SimpleBackupPathSpec(target, cmd.backupSuffix), true, io
      );
      nextStatusCall := MetadataStatusCall(
        preFs, MvPathSpec.SimpleBackupPathSpec(target, cmd.backupSuffix), true,
        candidateMetadata);
      assert StatusCallsFor(comparisonFrame.inputs, firstStatus + |statusCalls|, [nextStatusCall]) by {
        hide *;
        reveal ComparisonFrameFields();
      }
      StatusCallsConcat(comparisonFrame.inputs, firstStatus,
                        statusCalls, [nextStatusCall]);
      statusCalls := statusCalls + [nextStatusCall];
      assert io.statusCursor() == firstStatus + |statusCalls|;
      assert |statusCalls| == afterEntries + 1;
      assert statusCalls[afterEntries] == MetadataStatusCall(
                                            preFs, MvPathSpec.SimpleBackupPathSpec(target, cmd.backupSuffix), true,
                                            candidateMetadata
                                          );
      collisionEvidence := CheckedBackupCollision(
        sourceMetadata, candidateMetadata
      );
      sameFileEvidence := comparison.(backupCollision := collisionEvidence);
      assert SameFileEvidenceFor(cmd, preFs, preCwd, source, target, sameFileEvidence) by {
        reveal SameFileEvidenceFor();
      }
      if candidateMetadata.ok &&
         candidateMetadata.key == sourceMetadata.key
      {
        assert BackupCollisionDetected(collisionEvidence);
        hadError := true;
        errOut :=
          Spec.BackupWouldDestroySourceMessageSpec(source, target);
        step := MakeStepEvidence(
          preFs, io.fs(), out, errOut, hadError,
          sourceOk, sourceIsDir, sourceErr,
          true, found, existsErr,
          sameFileEvidence, backupEvidence, renameCalls, backupFs,
          StatusTranscript(firstStatus, statusCalls, comparisonFrame.inputs)
        );
        assert StepStatusEvidenceFor(source, target, cmd, step) by {
          reveal StepStatusEvidenceFor(), MetadataEvidenceFor(), MetadataStatusCall(), Spec.StatusRequest();
        }
        assert SourceResolutionObservationFor(source, preCwd, step) by {
          reveal SourceResolutionObservationFor();
        }
        assert RenameNativeObservationsFor(source, target, step) by {
          reveal RenameNativeObservationsFor();
        }
        assert StepEvidenceFor(source, target, cmd, preCwd, step) by {
          reveal StepEvidenceFor(), ExistingTargetRenameEvidenceFor();
        }
        assert StepStatusEvidenceFor(source, target, cmd, step);
        assert step.firstStatus == firstStatus;
        assert step.statusCalls == statusCalls;
        assert io.statusCursor() == step.firstStatus + |step.statusCalls|;
        assert StatusCallsFor(comparisonFrame.inputs, step.firstStatus, step.statusCalls);
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
    ghost var collisionNeeded :=
      (cmd.backupMode == Schema.BackupSimple ||
       cmd.backupMode == Schema.BackupExisting) &&
      sourceEntry.leaf == targetEntry.leaf + cmd.backupSuffix;
    ghost var afterCollision := afterEntries +
    (if collisionNeeded then 1 else 0);
    assert |statusCalls| == afterCollision;
    assert io.statusCursor() == firstStatus + |statusCalls|;
    assert io.fs() == preFs;

    if cmd.backupMode != Schema.BackupOff {
      ghost var fsBeforeBackup := io.fs();
      var backupPath, selectedBackup, backupCalls := PickBackupPath(
        target, cmd.backupMode, cmd.backupSuffix, io
      );
      ExistingTargetNonempty(preFs, target);
      SelectedBackupNonempty(target, cmd.backupMode, cmd.backupSuffix, preFs, selectedBackup);
      assert backupPath != "";
      assert StatusCallsFor(comparisonFrame.inputs, firstStatus + |statusCalls|, backupCalls) by {
        hide *;
        reveal ComparisonFrameFields();
      }
      StatusCallsConcat(comparisonFrame.inputs, firstStatus,
                        statusCalls, backupCalls);
      statusCalls := statusCalls + backupCalls;
      assert io.statusCursor() == firstStatus + |statusCalls|;
      assert statusCalls[afterCollision..] == backupCalls;
      assert BackupStatusSuffixFor(
          cmd.backupMode, preFs, target, statusCalls[afterCollision..]
        );
      backupEvidence := selectedBackup;
      assert fsBeforeBackup == preFs;
      assert io.fs() == preFs;
      ghost var backupStatusTemplate := MakeStepEvidence(
        preFs, preFs, [], [], false,
        sourceOk, sourceIsDir, sourceErr,
        true, found, existsErr,
        sameFileEvidence, backupEvidence, [], preFs,
        StatusTranscript(firstStatus, statusCalls,
                         comparisonFrame.inputs)
      );
      assert StepStatusEvidenceFor(source, target, cmd, backupStatusTemplate) by {
        reveal StepStatusEvidenceFor(), MetadataEvidenceFor(), MetadataStatusCall(), Spec.StatusRequest();
      }
      var frame := RenameFrame(sourceIsDir, found, existsErr, backupPath,
                               sameFileEvidence, backupEvidence, preFs, preCwd, firstStatus,
                               comparisonFrame.inputs, statusCalls);
      assert backupStatusTemplate == RenameFramePrototype(frame);
      assert SourceResolutionObservationFor(source, preCwd, RenameFramePrototype(frame)) by {
        hide *;
        reveal ComparisonFrameFields(), RenameFramePrototype(), MakeStepEvidence(), SourceResolutionObservationFor();
      }
      assert RenameFrameReady(source, target, cmd, frame) by {
        hide *;
        reveal ComparisonFrameFields(), RenameFrameReady();
      }
      assert io.fs() == frame.beforeFs && io.cwd() == frame.cwd by {
        hide *;
      }
      assert Spec.NativeStatusInputs(io.statusObservations(), io.trustedNativeFailures(), io.now()) == frame.inputs by {
        hide *;
      }
      assert io.statusCursor() == frame.firstStatus + |frame.statusCalls|;
      hadError, out, errOut, step := ExecuteRenameFrame(source, target, cmd, frame, io);
      reveal RenamePhaseSummary(), RenamePhase();
      return;
    }

    assert cmd.backupMode == Schema.BackupOff;
    var frame := RenameFrame(sourceIsDir, found, existsErr, "", sameFileEvidence, backupEvidence,
                             preFs, preCwd, firstStatus, comparisonFrame.inputs, statusCalls);
    assert RenameFrameReady(source, target, cmd, frame) by {
      reveal RenameFrameReady(), RenameFramePrototype(), MakeStepEvidence();
      reveal StepStatusEvidenceFor(), MetadataEvidenceFor(), MetadataStatusCall(), Spec.StatusRequest();
    }
    hadError, out, errOut, step := ExecuteRenameFrame(source, target, cmd, frame, io);
    reveal RenamePhaseSummary(), RenamePhase();
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
    modifies io.fsRegion, io.statusObservationsRegion
    ensures StepEvidenceFor(source, target, cmd, old(io.cwd()), step)
    ensures StepStatusEvidenceFor(source, target, cmd, step)
    ensures step.beforeFs == old(io.fs())
    ensures step.afterFs == io.fs()
    ensures step.outcome == Spec.MoveOutcome(out, errOut, hadError)
    ensures step.firstStatus == old(io.statusCursor())
    ensures step.inputs == Spec.NativeStatusInputs(io.statusObservations(), io.trustedNativeFailures(), io.now())
    ensures io.statusCursor() == step.firstStatus + |step.statusCalls|
    ensures StatusCallsFor(Spec.NativeStatusInputs(io.statusObservations(), io.trustedNativeFailures(), io.now()), step.firstStatus, step.statusCalls)
    decreases *
  {
    hide *;
    reveal RenamePhaseSummary(), RenamePhase();
    ghost var preFs := io.fs();
    ghost var preCwd := io.cwd();
    ghost var firstStatus := io.statusCursor();
    ghost var statusCalls: seq<Spec.StatusCallEvidence> := [];
    assert StatusCallsFor(Spec.NativeStatusInputs(io.statusObservations(),
                                                  io.trustedNativeFailures(), io.now()), firstStatus, statusCalls) by {
      reveal StatusCallsFor(), Spec.StatusCallsFor();
    }
    hadError := false;
    out := [];
    errOut := [];
    ghost var sameFileEvidence: SameFileEvidence := NoSameFileCheck;
    ghost var backupEvidence: BackupSelectionEvidence :=
      NoBackupSelection;
    ghost var renameCalls: seq<RenameCallEvidence> := [];
    ghost var backupFs := preFs;

    var sourceMetadata := CaptureMetadata(source, false, io);
    ghost var nextStatusCall := MetadataStatusCall(preFs, source, false, sourceMetadata);
    StatusCallsConcat(Spec.NativeStatusInputs(io.statusObservations(), io.trustedNativeFailures(), io.now()),
                      firstStatus, statusCalls, [nextStatusCall]);
    statusCalls := statusCalls + [nextStatusCall];
    var sourceOk := sourceMetadata.ok;
    var sourceIsDir := sourceMetadata.isDir;
    var sourceErr := sourceMetadata.err;
    if !sourceOk {
      hadError := true;
      errOut := Spec.SourceStatFailureMessageSpec(source, sourceErr);
      var frame := RenameFrame(sourceIsDir, false, 0, "", NoSameFileCheck, NoBackupSelection,
                               preFs, preCwd, firstStatus,
                               Spec.NativeStatusInputs(io.statusObservations(), io.trustedNativeFailures(), io.now()), statusCalls);
      assert InitialStepInputs(source, target, cmd, sourceMetadata, NoMetadataEvidence, frame,
                               Spec.MoveOutcome(out, errOut, hadError)) by {
        reveal InitialStepInputs(), Text.SkipStdoutSpec();
      }
      step := AssembleInitialMoveStep(source, target, cmd, sourceMetadata, NoMetadataEvidence, frame,
                                      Spec.MoveOutcome(out, errOut, hadError));
      assert RenamePhaseSummary(source, target, cmd, frame, preFs, Spec.MoveOutcome(out, errOut, hadError), step);
      reveal RenamePhaseSummary(), RenamePhase();
      return;
    }

    var targetMetadata := CaptureMetadata(target, false, io);
    nextStatusCall := MetadataStatusCall(preFs, target, false, targetMetadata);
    StatusCallsConcat(Spec.NativeStatusInputs(io.statusObservations(), io.trustedNativeFailures(), io.now()),
                      firstStatus, statusCalls, [nextStatusCall]);
    statusCalls := statusCalls + [nextStatusCall];
    var found := targetMetadata.ok;
    var existsErr := targetMetadata.err;
    if found {
      if cmd.overwriteMode == Schema.OverwriteSkip || cmd.updateMode == Schema.UpdateNone ||
         cmd.updateMode == Schema.UpdateNoneFail {
        if cmd.overwriteMode != Schema.OverwriteSkip && cmd.updateMode == Schema.UpdateNoneFail {
          hadError := true;
          errOut := Spec.NotReplacingMessageSpec(target);
        } else if cmd.debug {
          out := Spec.SkipStdoutSpec(target, true);
        }
        var frame := RenameFrame(sourceIsDir, found, existsErr, "", NoSameFileCheck, NoBackupSelection,
                                 preFs, preCwd, firstStatus,
                                 Spec.NativeStatusInputs(io.statusObservations(), io.trustedNativeFailures(), io.now()), statusCalls);
        assert InitialStepInputs(source, target, cmd, sourceMetadata, SomeMetadataEvidence(targetMetadata), frame,
                                 Spec.MoveOutcome(out, errOut, hadError)) by {
          reveal InitialStepInputs(), Text.SkipStdoutSpec();
        }
        step := AssembleInitialMoveStep(source, target, cmd, sourceMetadata, SomeMetadataEvidence(targetMetadata), frame,
                                        Spec.MoveOutcome(out, errOut, hadError));
        reveal RenamePhaseSummary(), RenamePhase();
        return;
      }

      var initialComparisonFrame := RenameFrame(sourceIsDir, found, existsErr, "",
                                                NoSameFileCheck, NoBackupSelection, preFs, preCwd, firstStatus,
                                                Spec.NativeStatusInputs(io.statusObservations(), io.trustedNativeFailures(), io.now()), statusCalls);
      assert ComparisonInputs(source, target, cmd, sourceMetadata, targetMetadata, initialComparisonFrame, io) by {
        reveal ComparisonInputs();
      }
      var comparison, comparisonFrame := CaptureMoveComparison(source, target, cmd,
                                                               sourceMetadata, targetMetadata, initialComparisonFrame, io);
      hadError, out, errOut, step := CompleteComparedMove(source, target, cmd, comparison, comparisonFrame, io);
      return;
    }

    assert io.fs() == preFs;
    assert io.statusCursor() == firstStatus + |statusCalls|;
    var frame := RenameFrame(sourceIsDir, found, existsErr, "", sameFileEvidence, backupEvidence,
                             preFs, preCwd, firstStatus,
                             Spec.NativeStatusInputs(io.statusObservations(), io.trustedNativeFailures(), io.now()), statusCalls);
    assert RenameFrameReady(source, target, cmd, frame) by {
      reveal RenameFrameReady(), RenameFramePrototype(), MakeStepEvidence(), StepStatusEvidenceFor();
      reveal MetadataStatusCall(), Spec.StatusRequest(), SourceResolutionObservationFor(), MetadataEvidenceFor();
    }
    hadError, out, errOut, step := ExecuteRenameFrame(source, target, cmd, frame, io);
    reveal RenamePhaseSummary(), RenamePhase();
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
    modifies io.fsRegion, io.statusObservationsRegion
    ensures BatchEvidenceFor(
              sources, directory, cmd, old(io.fs()), old(io.cwd()), io.fs(),
              hadError, out, errOut, batch
            )
    ensures batch.firstStatus == old(io.statusCursor())
    ensures io.statusCursor() == batch.firstStatus + |batch.statusCalls|
    ensures StatusCallsFor(Spec.NativeStatusInputs(io.statusObservations(), io.trustedNativeFailures(), io.now()), batch.firstStatus, batch.statusCalls)
    ensures BatchStatusEvidenceFor(Spec.NativeStatusInputs(io.statusObservations(), io.trustedNativeFailures(), io.now()), batch)
    ensures BatchMoveStatusEvidenceFor(
              sources, directory, cmd, Spec.NativeStatusInputs(io.statusObservations(), io.trustedNativeFailures(), io.now()), batch)
    decreases *
  {
    hide *;
    ghost var preFs := io.fs();
    ghost var preCwd := io.cwd();
    ghost var inputs := Spec.NativeStatusInputs(io.statusObservations(), io.trustedNativeFailures(), io.now());
    ghost var firstStatus := io.statusCursor();
    batch := BatchEvidence([], [preFs], [], [], [], firstStatus, [], [firstStatus]);
    hadError := false;
    out := [];
    errOut := [];
    assert BatchEvidenceFor([], directory, cmd, preFs, preCwd, preFs, false, [], [], batch) by {
      reveal BatchEvidenceFor(), Spec.ConcatenateFragments();
    }
    assert BatchMoveStatusEvidenceFor([], directory, cmd, inputs, batch) by {
      reveal BatchMoveStatusEvidenceFor(), BatchStatusEvidenceFor(), StatusCallsFor(), Spec.StatusCallsFor();
    }
    var i := 0;
    while i < |sources|
      invariant 0 <= i <= |sources|
      invariant batch.firstStatus == firstStatus
      invariant io.statusCursor() == firstStatus + |batch.statusCalls|
      invariant BatchEvidenceFor(sources[..i], directory, cmd, preFs, preCwd, io.fs(),
                                 hadError, out, errOut, batch)
      invariant BatchMoveStatusEvidenceFor(sources[..i], directory, cmd, inputs, batch)
      decreases |sources| - i
    {
      var source := sources[i];
      var normalizedSource := Spec.NormalizeSourceSpec(source, cmd.stripTrailingSlashes);
      var target := Spec.TargetInDirectorySpec(directory, normalizedSource);
      var stepError, stepOut, stepErr, step := MoveOne(normalizedSource, target, cmd, io);
      assert Spec.NativeStatusInputs(io.statusObservations(), io.trustedNativeFailures(), io.now()) == inputs;
      ghost var next := AppendBatchEvidence(sources[..i], source, directory, cmd,
                                            preFs, preCwd, hadError, out, errOut, inputs, batch, step);
      hadError := hadError || stepError;
      out := out + stepOut;
      errOut := errOut + stepErr;
      batch := next;
      assert sources[..i] + [source] == sources[..i + 1];
      i := i + 1;
    }
    assert sources[..i] == sources;
    reveal BatchMoveStatusEvidenceFor(), BatchStatusEvidenceFor();
  }

  twostate predicate CoreSummary(raw: Schema.MvCmdRaw, io: BenchIO.IO, exit: int, plan: PlannedOutput)
    reads io.Footprint()
  {
    PreparedSummary(raw, io, plan.normalExit, plan.stdout, plan.stderr) &&
    Spec.Emit(io, plan.stdout, plan.stderr, plan.normalExit, exit)
  }

  method Flush(output: BenchWorld.Bytes, diagnostics: BenchWorld.Bytes,
               normalExit: int, io: BenchIO.IO) returns (exit: int)
    modifies io.stdoutRegion, io.stderrRegion
    ensures Spec.Emit(io, output, diagnostics, normalExit, exit)
  {
    var outErr := 0;
    if |output| != 0 {
      var result := io.WriteStdout(output);
      outErr := IOContract.ResultErrno(result);
    }
    var finalDiagnostics := diagnostics;
    if outErr != 0 {
      var reason := io.GetCLocaleErrnoText(outErr);
      finalDiagnostics := diagnostics + Text.WriteErrorText(reason);
    }
    assert finalDiagnostics == diagnostics + (if outErr == 0 then []
                                              else Spec.WriteErrorText(IOContract.CLocaleErrnoTextResult(outErr)));
    var errErr := 0;
    if |finalDiagnostics| != 0 {
      var result := io.WriteStderr(finalDiagnostics);
      errErr := IOContract.ResultErrno(result);
      assert IOContract.WriteStderrSpec(old(io.stderr()), io.trustedStreams(), io.stderr(),
                                        finalDiagnostics, IOContract.WriteResultCommitted(result), errErr);
    }
    exit := if outErr != 0 || errErr != 0 then 1 else normalExit;
  }

  method RunCore(raw: Schema.MvCmdRaw, io: BenchIO.IO)
    returns (exit: int, ghost calls: seq<Spec.StatusCallEvidence>,
             ghost evidence: RunStatusEvidence, ghost plan: PlannedOutput)
    modifies io.fsRegion, io.stdoutRegion, io.stderrRegion, io.statusObservationsRegion
    ensures CoreSummary(raw, io, exit, plan)
    ensures RunStatusSummary(io, raw, plan.stdout, plan.stderr, plan.normalExit, calls, evidence)
    decreases *
  {
    var normalExit, output, diagnostics;
    normalExit, calls, evidence, output, diagnostics := Prepare(raw, io);
    plan := PlannedOutput(output, diagnostics, normalExit);
    exit := Flush(output, diagnostics, normalExit, io);
    assert PreparedSummary(raw, io, normalExit, output, diagnostics) by {
      hide *;
    }
    assert Spec.Emit(io, output, diagnostics, normalExit, exit) by {
      hide *;
      reveal Spec.Emit();
    }
    assert CoreSummary(raw, io, exit, plan) by {
      hide *;
      reveal CoreSummary();
    }
  }
}
