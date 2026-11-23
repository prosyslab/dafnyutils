include "../../../core/Utf8.dfy"
include "../../../core/World.dfy"
include "../Spec/LsSpec.dfy"
include "LsTextCore.dfy"
include "../../../core/IO.dfy"
include "../../../core/IOContract.dfy"
include "../Spec/LsSchema.dfy"
include "LsNativeObservationCore.dfy"
include "../Proof/LsNativeObservationProof.dfy"
include "../Proof/LsNativeResourceProof.dfy"
include "../Proof/LsNativeDirectoryProof.dfy"
include "../Proof/LsDirectoryTraceProof.dfy"
include "../Proof/LsDirectoryPieceProof.dfy"
include "../Proof/LsRunNativeProof.dfy"

module LsCore {
  import Text = LsTextCore
  import WorldPath = BenchWorld
  import StreamWorld = BenchWorld
  import StreamContract = IOContract

  import Result = Results
  import BenchIO
  import Utf8 = Utf8Semantics
  import BenchWorld
  import IOContract
  import Schema = LsSchema
  import Spec = LsSpec
  import Native = LsNativeSpec
  import NativeIO = LsNativeCore
  import NativeObservation = LsNativeObservationSpec
  import NativeObserve = LsNativeObservationCore
  import NativeFrames = LsNativeObservationProof
  import NativeTrace = LsNativeProof
  import NativeResources = LsNativeResourceProof
  import NativeDirectory = LsNativeDirectorySpec
  import NativeEntries = LsNativeDirectoryProof
  import DirectoryTraceProof = LsDirectoryTraceProof
  import DirectoryPieceProof = LsDirectoryPieceProof
  import RunNativeProof = LsRunNativeProof

  opaque function InsertSortedCore(
    cmd: Schema.LsCmd,
    entry: Spec.EntryObservation,
    sorted: seq<Spec.EntryObservation>
  ): seq<Spec.EntryObservation>
    decreases |sorted|
  {
    if |sorted| == 0 then [entry]
    else if Spec.EntryBeforeSpec(cmd, entry, sorted[0]) then [entry] + sorted
    else [sorted[0]] + InsertSortedCore(cmd, entry, sorted[1..])
  }

  opaque function SortEntriesCore(
    cmd: Schema.LsCmd,
    entries: seq<Spec.EntryObservation>
  ): seq<Spec.EntryObservation>
    decreases |entries|
  {
    if |entries| == 0 then []
    else InsertSortedCore(cmd, entries[0], SortEntriesCore(cmd, entries[1..]))
  }

  opaque function InsertOperandSortedCore(
    cmd: Schema.LsCmd,
    observation: Spec.OperandObservation,
    sorted: seq<Spec.OperandObservation>
  ): seq<Spec.OperandObservation>
    decreases |sorted|
  {
    if |sorted| == 0 then [observation]
    else if Spec.OperandBeforeSpec(cmd, observation, sorted[0]) then
      [observation] + sorted
    else
      [sorted[0]] + InsertOperandSortedCore(cmd, observation, sorted[1..])
  }

  opaque function SortOperandsCore(
    cmd: Schema.LsCmd,
    observations: seq<Spec.OperandObservation>
  ): seq<Spec.OperandObservation>
    decreases |observations|
  {
    if |observations| == 0 then []
    else InsertOperandSortedCore(
           cmd, observations[0], SortOperandsCore(cmd, observations[1..]))
  }

  function DirectPositionsCore(
    sorted: seq<Spec.OperandObservation>, i: nat
  ): seq<nat>
    requires i <= |sorted|
    ensures forall k: nat :: k < |DirectPositionsCore(sorted, i)| ==>
                               DirectPositionsCore(sorted, i)[k] < |sorted|
    decreases |sorted| - i
  {
    if i == |sorted| then []
    else ((if sorted[i].operandClass == Spec.DirectOperand then [i] else []) +
          DirectPositionsCore(sorted, i + 1))
  }

  function DirectoryPositionsCore(
    sorted: seq<Spec.OperandObservation>, i: nat
  ): seq<nat>
    requires i <= |sorted|
    ensures forall k: nat :: k < |DirectoryPositionsCore(sorted, i)| ==>
                               DirectoryPositionsCore(sorted, i)[k] < |sorted|
    decreases |sorted| - i
  {
    if i == |sorted| then []
    else
      (if sorted[i].operandClass == Spec.ExpandedDirectory &&
          sorted[i].sectionAvailable then [i] else []) +
      DirectoryPositionsCore(sorted, i + 1)
  }

  function RenderOperandCore(cmd: Schema.LsCmd, observations: seq<Spec.OperandObservation>, index: nat): BenchWorld.Bytes
    requires index < |observations|
  {
    Spec.RenderAlignedEntrySpec(cmd, observations[index].renderName, observations[index].status,
                                Text.OperandWidthsSpec(cmd, observations))
  }

  function BodiesAtPositionsCore(
    cmd: Schema.LsCmd, sorted: seq<Spec.OperandObservation>, positions: seq<nat>
  ): BenchWorld.Bytes
    requires forall k: nat :: k < |positions| ==> positions[k] < |sorted|
  {
    BodiesAtPositionsPrefixCore(cmd, sorted, positions, |positions|)
  }

  function BodiesFragmentsPrefixCore(
    cmd: Schema.LsCmd, sorted: seq<Spec.OperandObservation>, positions: seq<nat>, processed: nat
  ): seq<BenchWorld.Bytes>
    requires processed <= |positions|
    requires forall k: nat :: k < |positions| ==> positions[k] < |sorted|
    ensures |BodiesFragmentsPrefixCore(cmd, sorted, positions, processed)| == processed
    ensures forall k: nat :: k < processed ==>
                               BodiesFragmentsPrefixCore(cmd, sorted, positions, processed)[k] ==
                               RenderOperandCore(cmd, sorted, positions[k])
    decreases processed
  {
    if processed == 0 then []
    else (BodiesFragmentsPrefixCore(cmd, sorted, positions, processed - 1) +
          [RenderOperandCore(cmd, sorted, positions[processed - 1])])
  }

  function OperandIndicesPrefixCore(
    sorted: seq<Spec.OperandObservation>, positions: seq<nat>, processed: nat
  ): seq<nat>
    requires processed <= |positions|
    requires forall k: nat :: k < |positions| ==> positions[k] < |sorted|
    ensures |OperandIndicesPrefixCore(sorted, positions, processed)| == processed
    ensures forall k: nat :: k < processed ==>
                               OperandIndicesPrefixCore(sorted, positions, processed)[k] ==
                               sorted[positions[k]].index
    decreases processed
  {
    if processed == 0 then []
    else (OperandIndicesPrefixCore(sorted, positions, processed - 1) +
          [sorted[positions[processed - 1]].index])
  }

  function BodiesAtPositionsPrefixCore(
    cmd: Schema.LsCmd, sorted: seq<Spec.OperandObservation>, positions: seq<nat>, processed: nat
  ): BenchWorld.Bytes
    requires processed <= |positions|
    requires forall k: nat :: k < |positions| ==> positions[k] < |sorted|
    decreases processed
  {
    if processed == 0 then []
    else (BodiesAtPositionsPrefixCore(cmd, sorted, positions, processed - 1) +
          RenderOperandCore(cmd, sorted, positions[processed - 1]))
  }

  function DirectoryGroupsCore(
    sorted: seq<Spec.OperandObservation>, positions: seq<nat>
  ): seq<Spec.OutputGroup>
    requires forall k: nat :: k < |positions| ==> positions[k] < |sorted|
  {
    DirectoryGroupsPrefixCore(sorted, positions, |positions|)
  }

  function DirectoryGroupsPrefixCore(
    sorted: seq<Spec.OperandObservation>, positions: seq<nat>, processed: nat
  ): seq<Spec.OutputGroup>
    requires processed <= |positions|
    requires forall k: nat :: k < |positions| ==> positions[k] < |sorted|
    decreases processed
  {
    if processed == 0 then []
    else (DirectoryGroupsPrefixCore(sorted, positions, processed - 1) +
          [Spec.OutputGroup(
             [sorted[positions[processed - 1]].index],
             sorted[positions[processed - 1]].body, true)])
  }

  function HasQueuedDirectoryCore(sorted: seq<Spec.OperandObservation>): bool
  {
    exists i: nat :: i < |sorted| && sorted[i].operandClass == Spec.ExpandedDirectory
  }

  function OutputGroupsCore(
    cmd: Schema.LsCmd, sorted: seq<Spec.OperandObservation>
  ): seq<Spec.OutputGroup>
  {
    var directPositions := DirectPositionsCore(sorted, 0);
    var directoryPositions := DirectoryPositionsCore(sorted, 0);
    (if |directPositions| == 0 then []
     else [Spec.OutputGroup(
             OperandIndicesPrefixCore(sorted, directPositions, |directPositions|),
             BodiesAtPositionsCore(cmd, sorted, directPositions) +
             (if |directoryPositions| == 0 && HasQueuedDirectoryCore(sorted)
              then "\n" else []), false)]) +
    DirectoryGroupsCore(sorted, directoryPositions)
  }

  function JoinOutputGroupsCore(groups: seq<Spec.OutputGroup>): BenchWorld.Bytes
  {
    JoinOutputGroupsPrefixCore(groups, |groups|)
  }

  function GroupFragmentsPrefixCore(
    groups: seq<Spec.OutputGroup>, processed: nat
  ): seq<BenchWorld.Bytes>
    requires processed <= |groups|
    ensures |GroupFragmentsPrefixCore(groups, processed)| == processed
    ensures forall i: nat :: i < processed ==>
                               GroupFragmentsPrefixCore(groups, processed)[i] ==
                               (if i == 0 then [] else "\n") + groups[i].body
    decreases processed
  {
    if processed == 0 then []
    else (GroupFragmentsPrefixCore(groups, processed - 1) +
          [(if processed == 1 then [] else "\n") + groups[processed - 1].body])
  }

  function JoinOutputGroupsPrefixCore(
    groups: seq<Spec.OutputGroup>, processed: nat
  ): BenchWorld.Bytes
    requires processed <= |groups|
    decreases processed
  {
    if processed == 0 then []
    else (JoinOutputGroupsPrefixCore(groups, processed - 1) +
          (if processed == 1 then [] else "\n") + groups[processed - 1].body)
  }

  function AccessErrorsCore(
    observations: seq<Spec.OperandObservation>
  ): BenchWorld.Bytes
  {
    AccessErrorsPrefixCore(observations, |observations|)
  }

  function AccessErrorFragmentsPrefixCore(
    observations: seq<Spec.OperandObservation>, processed: nat
  ): seq<BenchWorld.Bytes>
    requires processed <= |observations|
    ensures |AccessErrorFragmentsPrefixCore(observations, processed)| == processed
    ensures forall i: nat :: i < processed ==>
                               AccessErrorFragmentsPrefixCore(observations, processed)[i] ==
                               observations[i].accessErrors
    decreases processed
  {
    if processed == 0 then []
    else (AccessErrorFragmentsPrefixCore(observations, processed - 1) +
          [observations[processed - 1].accessErrors])
  }

  function AccessErrorsPrefixCore(
    observations: seq<Spec.OperandObservation>, processed: nat
  ): BenchWorld.Bytes
    requires processed <= |observations|
    decreases processed
  {
    if processed == 0 then []
    else (AccessErrorsPrefixCore(observations, processed - 1) +
          observations[processed - 1].accessErrors)
  }

  function SectionErrorsCore(
    observations: seq<Spec.OperandObservation>
  ): BenchWorld.Bytes
  {
    SectionErrorsPrefixCore(observations, |observations|)
  }

  function SectionErrorFragmentsPrefixCore(
    observations: seq<Spec.OperandObservation>, processed: nat
  ): seq<BenchWorld.Bytes>
    requires processed <= |observations|
    ensures |SectionErrorFragmentsPrefixCore(observations, processed)| == processed
    ensures forall i: nat :: i < processed ==>
                               SectionErrorFragmentsPrefixCore(observations, processed)[i] ==
                               observations[i].sectionErrors
    decreases processed
  {
    if processed == 0 then []
    else (SectionErrorFragmentsPrefixCore(observations, processed - 1) +
          [observations[processed - 1].sectionErrors])
  }

  function SectionErrorsPrefixCore(
    observations: seq<Spec.OperandObservation>, processed: nat
  ): BenchWorld.Bytes
    requires processed <= |observations|
    decreases processed
  {
    if processed == 0 then []
    else (SectionErrorsPrefixCore(observations, processed - 1) +
          observations[processed - 1].sectionErrors)
  }

  ghost predicate RawObservationPiecesSummary(
    cmd: Schema.LsCmd,
    observations: seq<Spec.EntryObservation>,
    outputFragments: seq<BenchWorld.Bytes>,
    errorFragments: seq<BenchWorld.Bytes>
  )
  {
    |outputFragments| == |observations| &&
    |errorFragments| == |observations| &&
    forall i: nat | i < |observations| ::
      outputFragments[i] ==
      (if observations[i].ok
       then Spec.RenderEntrySpec(cmd, observations[i].renderName, observations[i].status)
       else []) &&
      errorFragments[i] ==
      Spec.EntryErrorTextSpec(observations[i].displayName, observations[i])
  }

  ghost predicate ObservationPiecesSummary(
    cmd: Schema.LsCmd,
    observations: seq<Spec.EntryObservation>,
    outputFragments: seq<BenchWorld.Bytes>
  )
  {
    |outputFragments| == |observations| &&
    forall i: nat | i < |observations| ::
      outputFragments[i] ==
      (if observations[i].ok
       then Spec.RenderAlignedEntrySpec(cmd, observations[i].renderName, observations[i].status, Spec.ObservationWidthsSpec(cmd, observations))
       else Spec.RenderFailedEntrySpec(cmd, observations[i], Spec.ObservationWidthsSpec(cmd, observations)))
  }

  ghost opaque predicate DirectoryListingSummary(
    cmd: Schema.LsCmd,
    displayPath: BenchWorld.Path,
    fs: BenchWorld.FileSystem,
    path: BenchWorld.Path,
    firstStatus: nat,
    afterStatus: nat,
    observations: seq<Spec.EntryObservation>,
    readErr: int,
    output: BenchWorld.Bytes,
    errors: BenchWorld.Bytes,
    hadError: bool, nativeTrace: Spec.DirectoryTrace
  )
  {
    exists rawObservations: seq<Spec.EntryObservation>,
      outputFragments: seq<BenchWorld.Bytes>, outputCuts: seq<nat>,
      errorFragments: seq<BenchWorld.Bytes>, errorCuts: seq<nat>,
      entryOutput: BenchWorld.Bytes, entryErrors: BenchWorld.Bytes, closeErr: int,
      expectedEntries: set<BenchWorld.DirEntry> ::
      Spec.DirectoryCloseObservation(cmd, fs, path, readErr, closeErr) &&
      Spec.ReadCloseDirectoryTrace(cmd, fs, path, nativeTrace, readErr, closeErr) &&
      nativeTrace.raw == rawObservations && Spec.DirectoryExpectedEntries(nativeTrace,expectedEntries) &&
      Spec.DirectoryObservationRelation(cmd, fs, path, firstStatus, afterStatus,
                                        readErr == 0, rawObservations,expectedEntries) &&
      observations == SortEntriesCore(cmd, rawObservations) &&
      ObservationPiecesSummary(cmd, observations, outputFragments) &&
      Spec.ObservationErrorsRelation(displayPath, rawObservations, errorFragments) &&
      Spec.FragmentsConcatenate(outputFragments, entryOutput, outputCuts) &&
      output == Spec.TotalLineSpec(cmd, rawObservations) + entryOutput &&
      Spec.FragmentsConcatenate(errorFragments, entryErrors, errorCuts) &&
      errors == entryErrors +
      (if readErr == 0 then [] else Spec.ReadDirectoryErrorMessageSpec(displayPath, readErr)) +
      Spec.CloseDirectoryErrorMessageSpec(displayPath, closeErr) &&
      hadError == (readErr != 0 || closeErr != 0 ||
                   exists i: nat :: i < |observations| && Spec.ObservationFailedSpec(observations[i]))
  }

  function RecursiveChildOutputPrefixCore(
    observations: seq<Spec.EntryObservation>,
    children: map<nat, Spec.RecursiveWitness>, processed: nat
  ): BenchWorld.Bytes
    requires processed <= |observations|
    decreases processed
  {
    if processed == 0 then []
    else (RecursiveChildOutputPrefixCore(
            observations, children, processed - 1) +
          (if processed - 1 in children &&
              Spec.RecursiveNodeListed(children[processed - 1])
           then "\n" + children[processed - 1].output
           else []))
  }

  ghost function RecursiveChildErrorPrefixCore(
    displayPath: BenchWorld.Path, observations: seq<Spec.EntryObservation>,
    children: map<nat, Spec.RecursiveWitness>, cycles: set<nat>, processed: nat
  ): BenchWorld.Bytes
    requires processed <= |observations|
    decreases processed
  {
    if processed == 0 then []
    else (RecursiveChildErrorPrefixCore(
            displayPath, observations, children, cycles, processed - 1) +
          (if processed - 1 in cycles then
             Spec.RecursiveCycleMessageSpec(
               Spec.ChildDisplayPath(
                 displayPath, observations[processed - 1].displayName))
           else if processed - 1 in children
           then children[processed - 1].errors
           else []))
  }

  ghost opaque predicate RecursiveDirectorySummary(
    cmd: Schema.LsCmd,
    fs: BenchWorld.FileSystem,
    displayPath: BenchWorld.Path,
    accessPath: BenchWorld.Path,
    ancestors: set<BenchWorld.HostInodeKey>,
    tree: Spec.RecursiveWitness
  )
    decreases tree
  {
    Spec.RecursiveNativeDirectoryTrace(cmd, fs, accessPath, tree) &&
    Spec.RecursiveNativeCallsFields(cmd,fs,tree) &&
    cmd.statusContext.BoundStatusObservations? &&
    Spec.OpenDirectoryObservation(cmd, fs, accessPath, tree.openOk, tree.openErr) &&
    (tree.openOk ==> Spec.OpenedDirectoryStatusObservation(
         cmd, fs, accessPath, tree.firstStatus, tree.statusOk,
         tree.openedStatus, tree.statusErr)) &&
    (if !tree.openOk then
       tree.openErr > 0 && !tree.statusOk && !tree.cycle &&
       tree.listingFirstStatus == tree.firstStatus &&
       tree.listingAfterStatus == tree.firstStatus &&
       tree.afterStatus == tree.firstStatus &&
       tree.observations == [] && tree.children == map[] && tree.cycles == {} &&
       tree.output == [] &&
       tree.errors == Spec.OpenDirectoryErrorMessageSpec(displayPath, tree.openErr) &&
       tree.hadError
     else if !tree.statusOk then
       tree.openErr == 0 && tree.statusErr > 0 && !tree.cycle &&
       tree.listingFirstStatus == tree.firstStatus+1 &&
       tree.listingAfterStatus == tree.firstStatus+1 &&
       tree.afterStatus == tree.firstStatus+1 &&
       tree.observations == [] && tree.children == map[] && tree.cycles == {} &&
       tree.output == [] &&
       tree.errors == Spec.DirectoryIdentityErrorMessageSpec(displayPath, tree.statusErr) &&
       tree.hadError
     else
       tree.openErr == 0 && tree.statusErr == 0 &&
       tree.listingFirstStatus == tree.firstStatus + 1 &&
       tree.openedStatus.kind == BenchWorld.DirectoryKind &&
       (if tree.cycle then
          tree.openedStatus.hostKey in ancestors &&
          tree.listingAfterStatus == tree.listingFirstStatus &&
          tree.afterStatus == tree.listingFirstStatus &&
          tree.observations == [] && tree.children == map[] && tree.cycles == {} &&
          tree.output == [] && tree.errors == Spec.RecursiveCycleMessageSpec(displayPath) &&
          tree.hadError
        else
          tree.openedStatus.hostKey !in ancestors &&
          DirectoryListingSummary(
            cmd, displayPath, fs, accessPath, tree.listingFirstStatus,
            tree.listingAfterStatus,
            tree.observations, tree.readErr,
            tree.listingOutput, tree.listingErrors, tree.listingHadError, tree.nativeTrace) &&
          (exists statusCuts: seq<nat> ::
             |statusCuts| == |tree.observations| + 1 &&
             statusCuts[0] == tree.listingAfterStatus &&
             statusCuts[|tree.observations|] == tree.afterStatus &&
             (forall i: nat | i < |tree.observations| ::
                (if i in tree.children then
                   tree.children[i].firstStatus == statusCuts[i] &&
                   tree.children[i].afterStatus == statusCuts[i + 1]
                 else statusCuts[i] == statusCuts[i + 1]))) &&
          tree.cycles <= tree.children.Keys &&
          (forall i: nat :: i < |tree.observations| ==>
                              (i in tree.children <==> Spec.RecursiveEntryEligible(tree.observations[i])) &&
                              (i in tree.cycles <==> i in tree.children && tree.children[i].cycle)) &&
          (forall i: nat :: i in tree.children ==>
                              i < |tree.observations| &&
                              RecursiveDirectorySummary(
                                cmd, fs,
                                Spec.ChildDisplayPath(displayPath, tree.observations[i].displayName),
                                tree.observations[i].accessPath,
                                ancestors + {tree.openedStatus.hostKey}, tree.children[i])) &&
          tree.output == Spec.DirectoryHeaderSpec(displayPath) + tree.listingOutput +
          RecursiveChildOutputPrefixCore(
            tree.observations, tree.children, |tree.observations|) &&
          tree.errors == tree.listingErrors + RecursiveChildErrorPrefixCore(
            displayPath, tree.observations, tree.children, tree.cycles,
            |tree.observations|) &&
          tree.hadError ==
          (tree.listingHadError ||
           exists i: nat :: i in tree.children && tree.children[i].hadError)))
  }

  ghost opaque predicate OperandObservationSummary(
    cmd: Schema.LsCmd,
    fs: BenchWorld.FileSystem,
    cwd: BenchWorld.Path,
    observation: Spec.OperandObservation
  )
  {
    Spec.OperandNativeFields(cmd,fs,observation) &&
    observation.index < |cmd.operands| &&
    observation.operand == cmd.operands[observation.index] &&
    observation.path == Spec.OperandPathSpec(cmd, cwd, observation.operand) &&
    (observation.sectionAvailable ==>
       observation.operandClass == Spec.ExpandedDirectory &&
       Spec.OpenDirectoryObservation(cmd, fs, observation.path, true, 0)) &&
    (observation.operandClass == Spec.ExpandedDirectory ==>
       observation.nativeTrace.DirectoryTrace? &&
       Spec.BoundOpenDirectoryTrace(cmd, fs, observation.path, observation.nativeTrace,
                                    observation.sectionAvailable,
                                    if observation.sectionAvailable then 0 else observation.nativeTrace.openErr) &&
       (!observation.sectionAvailable ==>
          Spec.FailedOpenDirectoryTrace(cmd, fs, observation.path, observation.nativeTrace) &&
          observation.sectionErrors == Spec.OpenDirectoryErrorMessageSpec(
            observation.operand, observation.nativeTrace.openErr))) &&
    match Spec.ObservedOperandStatusResult(cmd,fs,observation)
    case Err(error) =>
      !observation.ok && !observation.sectionAvailable &&
      observation.err == IOContract.IOErrorErrno(error) &&
      observation.operandClass == Spec.AccessFailure &&
      observation.afterStatus == observation.firstStatus +
      Spec.ObservedOperandStatusCallCount(cmd,fs,observation) &&
      observation.body == [] &&
      observation.accessErrors == Spec.AccessErrorMessageSpec(
        observation.operand, observation.err) &&
      observation.sectionErrors == [] && observation.failed && !observation.hasCycle &&
      !observation.directoryFailed
    case Ok(status) =>
      observation.ok && observation.status == status && observation.err == 0 &&
      if status.kind == BenchWorld.DirectoryKind && !cmd.listDirectories then
        observation.accessErrors == [] &&
        observation.operandClass == Spec.ExpandedDirectory &&
        if observation.sectionAvailable then
          if cmd.recursive then
            exists tree: Spec.RecursiveWitness ::
              RecursiveDirectorySummary(
                cmd, fs, observation.operand, observation.path,
                {}, tree) &&
              tree.openOk && tree.nativeTrace == observation.nativeTrace &&
              observation.nativeCalls == observation.statusCalls+tree.nativeCalls &&
              tree.firstStatus == observation.firstStatus +
              Spec.ObservedOperandStatusCallCount(cmd,fs,observation) &&
              tree.afterStatus == observation.afterStatus &&
              observation.body == tree.output &&
              observation.sectionErrors == tree.errors &&
              observation.failed == tree.hadError &&
              observation.hasCycle == Spec.RecursiveHasCycle(tree) &&
              observation.directoryFailed == Spec.RecursiveRootFailed(tree)
          else
            !observation.hasCycle &&
            exists entries: seq<Spec.EntryObservation>, readErr: int,
              listingOutput: BenchWorld.Bytes
              {:trigger DirectoryListingSummary(
                cmd, observation.operand, fs, observation.path,
                observation.firstStatus + Spec.ObservedOperandStatusCallCount(cmd,fs,observation),
                observation.afterStatus, entries, readErr,
                listingOutput, observation.sectionErrors, observation.failed, observation.nativeTrace)} ::
              DirectoryListingSummary(
                cmd, observation.operand, fs, observation.path,
                observation.firstStatus + Spec.ObservedOperandStatusCallCount(cmd,fs,observation),
                observation.afterStatus, entries, readErr,
                listingOutput, observation.sectionErrors, observation.failed, observation.nativeTrace) &&
              observation.directoryFailed == Spec.DirectoryOperationFailed(observation.nativeTrace, readErr) &&
              observation.nativeCalls == observation.statusCalls+observation.nativeTrace.nativeCalls &&
              observation.body ==
              (if |cmd.operands| > 1
               then Spec.DirectoryHeaderSpec(observation.operand)
               else []) + listingOutput
        else
          observation.afterStatus == observation.firstStatus +
          Spec.ObservedOperandStatusCallCount(cmd,fs,observation) &&
          observation.body == [] &&
          observation.nativeCalls == observation.statusCalls+observation.nativeTrace.nativeCalls &&
          (exists openErr: int ::
             Spec.OpenDirectoryObservation(cmd, fs, observation.path, false, openErr) &&
             observation.sectionErrors == Spec.OpenDirectoryErrorMessageSpec(
               observation.operand, openErr)) &&
          observation.failed && !observation.hasCycle && observation.directoryFailed
      else
        observation.operandClass == Spec.DirectOperand &&
        observation.afterStatus == observation.firstStatus +
        Spec.ObservedOperandStatusCallCount(cmd,fs,observation) &&
        !observation.sectionAvailable &&
        Spec.DirectOperandRenderFields(cmd,fs,observation,status) &&
        observation.body == Spec.RenderEntrySpec(cmd,observation.renderName,status) &&
        observation.sectionErrors == [] && !observation.hasCycle && !observation.directoryFailed
  }

  lemma ExpandedRecursiveOperandSummary(
    cmd: Schema.LsCmd, fs: BenchWorld.FileSystem, cwd: BenchWorld.Path,
    observation: Spec.OperandObservation, tree: Spec.RecursiveWitness
  )
    requires Spec.OperandNativeFields(cmd,fs,observation)
    requires observation.index < |cmd.operands|
    requires observation.operand == cmd.operands[observation.index]
    requires observation.path == Spec.OperandPathSpec(cmd, cwd, observation.operand)
    requires observation.ok && observation.err == 0 &&
             observation.operandClass == Spec.ExpandedDirectory
    requires observation.status.kind == BenchWorld.DirectoryKind &&
             !cmd.listDirectories && cmd.recursive
    requires observation.accessErrors == []
    requires observation.sectionAvailable == tree.openOk
    requires observation.directoryFailed == Spec.RecursiveRootFailed(tree)
    requires observation.nativeCalls == observation.statusCalls+tree.nativeCalls
    requires observation.nativeTrace == tree.nativeTrace
    requires Spec.RecursiveNativeDirectoryTrace(cmd, fs, observation.path, tree)
    requires Spec.RecursiveNativeCallsFields(cmd,fs,tree)
    requires Spec.OpenDirectoryObservation(cmd,
                                           fs, observation.path, tree.openOk, tree.openErr)
    requires Spec.ObservedOperandStatusResult(cmd,fs,observation) ==
             Result.Ok(observation.status)
    requires if observation.sectionAvailable then
               RecursiveDirectorySummary(
                 cmd, fs, observation.operand, observation.path,
                 {}, tree) &&
               tree.firstStatus == observation.firstStatus +
               Spec.ObservedOperandStatusCallCount(cmd,fs,observation) &&
               tree.afterStatus == observation.afterStatus &&
               observation.body == tree.output &&
               observation.sectionErrors == tree.errors &&
               observation.failed == tree.hadError &&
               observation.hasCycle == Spec.RecursiveHasCycle(tree)
             else
               observation.afterStatus == observation.firstStatus +
               Spec.ObservedOperandStatusCallCount(cmd,fs,observation) &&
               observation.body == [] &&
               observation.sectionErrors == Spec.OpenDirectoryErrorMessageSpec(
                 observation.operand, tree.openErr) &&
               observation.failed && !observation.hasCycle
    ensures OperandObservationSummary(cmd, fs, cwd, observation)
  {
    hide *;
    reveal OperandObservationSummary(), Spec.RecursiveNativeDirectoryTrace();
    reveal Spec.BoundOpenDirectoryTrace(), Spec.RecursiveRootFailed();
    if observation.sectionAvailable {
      assert tree.openErr == 0 by {
        reveal RecursiveDirectorySummary();
      }
    } else {
      reveal Spec.RecursiveNativeCallsFields();
    }
  }

  lemma ExpandedFlatOperandSummary(
    cmd: Schema.LsCmd, fs: BenchWorld.FileSystem, cwd: BenchWorld.Path,
    observation: Spec.OperandObservation,
    entries: seq<Spec.EntryObservation>, readErr: int,
    listingOutput: BenchWorld.Bytes
  )
    requires Spec.OperandNativeFields(cmd,fs,observation)
    requires observation.index < |cmd.operands|
    requires observation.operand == cmd.operands[observation.index]
    requires observation.path == Spec.OperandPathSpec(cmd, cwd, observation.operand)
    requires observation.ok && observation.err == 0 &&
             observation.operandClass == Spec.ExpandedDirectory
    requires observation.status.kind == BenchWorld.DirectoryKind &&
             !cmd.listDirectories && !cmd.recursive
    requires observation.accessErrors == []
    requires Spec.OpenDirectoryObservation(cmd,
                                           fs, observation.path, observation.sectionAvailable,
                                           if observation.sectionAvailable then 0 else readErr)
    requires Spec.ObservedOperandStatusResult(cmd,fs,observation) ==
             Result.Ok(observation.status)
    requires Spec.BoundOpenDirectoryTrace(cmd, fs, observation.path, observation.nativeTrace,
                                          observation.sectionAvailable, if observation.sectionAvailable then 0 else readErr)
    requires observation.directoryFailed == Spec.DirectoryOperationFailed(observation.nativeTrace, readErr)
    requires observation.nativeCalls == observation.statusCalls+observation.nativeTrace.nativeCalls
    requires !observation.hasCycle
    requires !observation.sectionAvailable ==>
               Spec.FailedOpenDirectoryTrace(cmd, fs, observation.path, observation.nativeTrace)
    requires if observation.sectionAvailable then
               DirectoryListingSummary(
                 cmd, observation.operand, fs, observation.path,
                 observation.firstStatus + Spec.ObservedOperandStatusCallCount(cmd,fs,observation),
                 observation.afterStatus, entries, readErr,
                 listingOutput, observation.sectionErrors, observation.failed, observation.nativeTrace) &&
               observation.body ==
               (if |cmd.operands| > 1 then Spec.DirectoryHeaderSpec(observation.operand)
                else []) + listingOutput
             else
               observation.afterStatus == observation.firstStatus +
               Spec.ObservedOperandStatusCallCount(cmd,fs,observation) &&
               observation.body == [] &&
               observation.sectionErrors == Spec.OpenDirectoryErrorMessageSpec(
                 observation.operand, readErr) &&
               observation.failed && !observation.hasCycle
    ensures OperandObservationSummary(cmd, fs, cwd, observation)
  {
    hide *;
    reveal OperandObservationSummary();
    reveal Spec.BoundOpenDirectoryTrace(), Spec.DirectoryOperationFailed();
  }

  ghost predicate RunSummary(
    cmd: Schema.LsCmd,
    fs: BenchWorld.FileSystem,
    cwd: BenchWorld.Path,
    firstStatus: nat,
    afterStatus: nat,
    output: BenchWorld.Bytes,
    errors: BenchWorld.Bytes,
    exit: int, afterNative: seq<Native.State> := []
  )
  {
    exists observations: seq<Spec.OperandObservation>,
      sorted: seq<Spec.OperandObservation>, groups: seq<Spec.OutputGroup>,
      statusCuts: seq<nat> ::
      Spec.RunNativeFields(cmd,fs,firstStatus,afterStatus,observations,afterNative) &&
      |observations| == |cmd.operands| &&
      |statusCuts| == |observations| + 1 &&
      statusCuts[0] == firstStatus &&
      statusCuts[|observations|] == afterStatus &&
      (forall i: nat | i < |observations| ::
         observations[i].firstStatus == statusCuts[i] &&
         observations[i].afterStatus == statusCuts[i + 1]) &&
      (forall i: nat | i < |observations| ::
         observations[i].index == i &&
         OperandObservationSummary(cmd, fs, cwd, observations[i])) &&
      sorted == SortOperandsCore(cmd, observations) &&
      groups == OutputGroupsCore(cmd, sorted) &&
      output == JoinOutputGroupsCore(groups) &&
      errors == AccessErrorsCore(observations) + SectionErrorsCore(sorted) &&
      exit == Spec.OperandExitSpec(observations)
  }

  opaque twostate predicate PreparedSummary(raw: Schema.LsCmdRaw, io: BenchIO.IO, exit: int, plannedStdout: StreamWorld.Bytes, plannedStderr: StreamWorld.Bytes)
    reads io.fsRegion, io.cwdRegion, io.envRegion, io.nowRegion,
          io.statusObservationsRegion, io.trustedNativeFailuresRegion,
          io.dirHandlesRegion, io.directoryStateRegion
  {
    io.dirHandles() == old(io.dirHandles()) &&
    var cmd := Schema.WithStatusObservations(
                 Spec.EffectiveCommandSpec(raw, old(io.env()), old(io.now())),
                 io.statusObservations(), old(io.statusCursor()), io.trustedNativeFailures(),old(io.dirHandles()),old(io.cwd()),[old(NativeIO.Inputs(io))],[old(NativeIO.State(io))]);
    (cmd.mode != Schema.ModeRun ==> io.statusCursor() == old(io.statusCursor())) &&
    if cmd.mode == Schema.ModeHelp then
      plannedStdout == [] + Spec.HelpTextSpec &&
      plannedStderr == [] &&
      exit == 0
    else if cmd.mode == Schema.ModeVersion then
      plannedStdout == [] + Spec.VersionTextSpec &&
      plannedStderr == [] &&
      exit == 0
    else if cmd.mode != Schema.ModeRun then
      plannedStdout == [] &&
      plannedStderr == [] + Spec.InvalidModeMessageSpec(cmd.mode) &&
      exit == (if cmd.mode.ModeInvalidTime? then 1 else 2)
    else
      exists output: BenchWorld.Bytes, errors: BenchWorld.Bytes ::
        RunSummary(cmd, old(io.fs()), old(io.cwd()), old(io.statusCursor()),
                   io.statusCursor(),output,errors,exit,[NativeIO.State(io)]) &&
        plannedStdout == [] + output &&
        plannedStderr == [] + errors
  }

  twostate predicate CoreSummary(raw: Schema.LsCmdRaw, io: BenchIO.IO, exit: int)
    reads io.Footprint()
  {
    exists output: StreamWorld.Bytes, diagnostics: StreamWorld.Bytes, normalExit: int ::
      PreparedSummary(raw, io, normalExit, output, diagnostics) &&
      Spec.EmissionFields(old(io.stdout()), old(io.stderr()), io.stdout(), io.stderr(),
                          io.trustedStreams(), output, diagnostics, normalExit, exit)
  }

  lemma AppendFragment(
    fragments: seq<BenchWorld.Bytes>,
    combined: BenchWorld.Bytes,
    cuts: seq<nat>,
    tail: BenchWorld.Bytes
  )
    requires Spec.FragmentsConcatenate(fragments, combined, cuts)
    ensures Spec.FragmentsConcatenate(
              fragments + [tail], combined + tail, cuts + [|combined + tail|])
  {
    reveal Spec.FragmentsConcatenate();
    forall i: nat {:trigger (cuts + [|combined + tail|])[i]} |
      i < |fragments + [tail]|
      ensures (cuts + [|combined + tail|])[i] <=
              (cuts + [|combined + tail|])[i + 1] <= |combined + tail| &&
              (cuts + [|combined + tail|])[i + 1] ==
              (cuts + [|combined + tail|])[i] + |(fragments + [tail])[i]| &&
              (combined + tail)[
              (cuts + [|combined + tail|])[i]..
              (cuts + [|combined + tail|])[i + 1]
              ] == (fragments + [tail])[i]
    {
    }
  }

  lemma FailedOperandSnoc(
    observations: seq<Spec.OperandObservation>,
    observation: Spec.OperandObservation
  )
    ensures (exists j: nat ::
               j < |observations + [observation]| &&
               (observations + [observation])[j].failed) ==
            ((exists j: nat :: j < |observations| && observations[j].failed) ||
             observation.failed)
  {
    if exists j: nat ::
        j < |observations + [observation]| &&
        (observations + [observation])[j].failed {
      var j: nat :|
        j < |observations + [observation]| &&
        (observations + [observation])[j].failed;
      if j < |observations| {
        assert exists k: nat :: k < |observations| && observations[k].failed;
      } else {
        assert j == |observations|;
      }
    }
    if exists j: nat :: j < |observations| && observations[j].failed {
      var j: nat :| j < |observations| && observations[j].failed;
      assert (observations + [observation])[j] == observations[j];
    } else if observation.failed {
      assert (observations + [observation])[|observations|] == observation;
    }
  }

  method OperandExitCore(observations: seq<Spec.OperandObservation>) returns (exit: nat)
    ensures exit == Spec.OperandExitSpec(observations)
  {
    exit := 0;
    var i := 0;
    while i < |observations|
      invariant 0 <= i <= |observations|
      invariant forall j: nat | j < i :: Spec.OperandFailureExitSpec(observations[j]) <= exit
      invariant exit == 0 || exists j: nat :: j < i && Spec.OperandFailureExitSpec(observations[j]) == exit
      decreases |observations| - i
    {
      var severity := Spec.OperandFailureExitSpec(observations[i]);
      if severity > exit { exit := severity; }
      i := i + 1;
    }
    var values := set j: nat | j < |observations| :: Spec.OperandFailureExitSpec(observations[j]);
    var maximum := Text.MaximumWidth(values);
    if values != {} {
      assert maximum in values;
      assert maximum <= exit;
      if exit != 0 { assert exit in values; }
      assert exit <= maximum;
    } else {
      if exit != 0 {
        ghost var j: nat :| j < |observations| && Spec.OperandFailureExitSpec(observations[j]) == exit;
        assert exit in values;
      }
      assert exit == 0;
    }
    assert exit == maximum;
    assert Spec.OperandExitSpec(observations) == maximum;
  }

  lemma PackageOpenDirectoryObservation(cmd: Schema.LsCmd, fs: BenchWorld.FileSystem,
                                        path: BenchWorld.Path, call: Native.Call, ok: bool, err: int)
    requires Spec.NativeCommandFields(cmd,fs)
    requires Native.CallFields(cmd.nativeInputs[0],call)
    requires call.action.OpenAction? && call.action.path == path && call.action.dots
    requires call.action.openResult.Ok? == ok && IOContract.ResultErrno(call.action.openResult) == err
    ensures Spec.OpenDirectoryObservation(cmd,fs,path,ok,err)
  {
    hide *;
    reveal Spec.NativeCommandFields();
    NativeTrace.Single(cmd.nativeInputs[0],call);
    assert Spec.NativeCallsFields(cmd,fs,[call]) by { reveal Spec.NativeCallsFields(); }
    assert exists actual: Native.Call ::
        actual == call && Spec.NativeCallsFields(cmd,fs,[actual]) &&
        actual.action.OpenAction? && actual.action.path == path && actual.action.dots &&
        actual.action.openResult.Ok? == ok && IOContract.ResultErrno(actual.action.openResult) == err;
    reveal Spec.OpenDirectoryObservation();
  }

  lemma PackageOpenedDirectoryStatusObservation(cmd: Schema.LsCmd, fs: BenchWorld.FileSystem,
                                                path: BenchWorld.Path, call: Native.Call, ok: bool, status: BenchWorld.FileStatus, err: int)
    requires Spec.NativeCommandFields(cmd,fs)
    requires Native.CallFields(cmd.nativeInputs[0],call) && call.action.HandleStatusAction?
    requires NativeObservation.StatusFields(call.action.statusResult,ok,status,err)
    ensures Spec.OpenedDirectoryStatusObservation(cmd,fs,path,call.before.status,ok,status,err)
  {
    hide *;
    reveal Spec.NativeCommandFields();
    NativeTrace.Single(cmd.nativeInputs[0],call);
    assert Spec.NativeCallsFields(cmd,fs,[call]) by { reveal Spec.NativeCallsFields(); }
    assert exists actual: Native.Call ::
        actual == call && Spec.NativeCallsFields(cmd,fs,[actual]) &&
        actual.before.status == call.before.status && actual.action.HandleStatusAction? &&
        NativeObservation.StatusFields(actual.action.statusResult,ok,status,err);
    reveal Spec.OpenedDirectoryStatusObservation();
  }

  lemma PackageDirectoryCloseObservation(cmd: Schema.LsCmd, fs: BenchWorld.FileSystem,
                                         path: BenchWorld.Path, read: Native.Call, closed: Native.Call, readErr: int, closeErr: int)
    requires Spec.NativeCallsFields(cmd,fs,[read,closed])
    requires read.action.ReadAction? && closed.action.CloseAction?
    requires read.action.handle == closed.action.handle
    requires read.action.readResult.Err? || read.action.readResult.v.DirectoryEnd?
    requires IOContract.ResultErrno(read.action.readResult) == readErr
    requires IOContract.ResultErrno(closed.action.closeResult) == closeErr
    ensures Spec.DirectoryCloseObservation(cmd,fs,path,readErr,closeErr)
  {
    hide *;
    assert exists actualRead: Native.Call, actualClose: Native.Call ::
        actualRead == read && actualClose == closed && Spec.NativeCallsFields(cmd,fs,[actualRead,actualClose]) &&
        actualRead.action.ReadAction? && actualClose.action.CloseAction? &&
        actualRead.action.handle == actualClose.action.handle &&
        (actualRead.action.readResult.Err? || actualRead.action.readResult.v.DirectoryEnd?) &&
        IOContract.ResultErrno(actualRead.action.readResult) == readErr &&
        IOContract.ResultErrno(actualClose.action.closeResult) == closeErr;
    reveal Spec.DirectoryCloseObservation();
  }

  method RenderNameCore(
    cmd: Schema.LsCmd, displayName: string, path: BenchWorld.Path,
    followSymlink: bool, status: BenchWorld.FileStatus, io: BenchIO.IO
  ) returns (renderName: string, linkErr: int, ghost calls: seq<Native.Call>)
    requires cmd.statusContext.BoundStatusObservations?
    requires |cmd.nativeInputs| == 1 && cmd.nativeInputs[0] == NativeIO.Inputs(io)
    modifies io.directoryStateRegion
    ensures NativeIO.Inputs(io) == old(NativeIO.Inputs(io))
    ensures NativeObservation.RenderFields(cmd.nativeInputs[0],old(NativeIO.State(io)),
                                           NativeIO.State(io),displayName,path,followSymlink,cmd.numericLong,status,renderName,linkErr,calls)
  {
    renderName,linkErr,calls := NativeObserve.Render(displayName,path,followSymlink,
                                                     cmd.numericLong,status,io);
  }

  method ObservePath(
    cmd: Schema.LsCmd, displayName: string, entryKind: BenchWorld.DirectoryEntryKind,
    path: BenchWorld.Path, followSymlink: bool, io: BenchIO.IO
  ) returns (observation: Spec.EntryObservation, output: BenchWorld.Bytes,
             errors: BenchWorld.Bytes, hadError: bool)
    requires cmd.statusContext.BoundStatusObservations?
    requires cmd.statusContext.observations == io.statusObservations()
    requires cmd.statusContext.failures == io.trustedNativeFailures()
    requires |cmd.nativeInputs| == 1 && cmd.nativeInputs[0] == NativeIO.Inputs(io)
    modifies io.directoryStateRegion, io.statusObservationsRegion
    ensures NativeIO.Inputs(io) == old(NativeIO.Inputs(io))
    ensures Spec.MetadataObservationRelation(cmd,old(io.fs()),observation)
    ensures NativeIO.Inputs(io) == old(NativeIO.Inputs(io))
    ensures Native.TraceFields(cmd.nativeInputs[0],old(NativeIO.State(io)),NativeIO.State(io),observation.nativeCalls)
    ensures io.cwdContext().topology == old(io.cwdContext()).topology
    ensures io.cwdContext().capabilities == old(io.cwdContext()).capabilities
    ensures io.cwdContext().position == old(io.cwdContext()).position
    ensures io.cwdContext().hint == old(io.cwdContext()).hint
    ensures io.cwdContext().legacyHandles == old(io.cwdContext()).legacyHandles
    ensures io.cwdContext().legacyOrigins == old(io.cwdContext()).legacyOrigins
    ensures observation.statusOrdinal == old(io.statusCursor())
    ensures observation.source == Spec.StatusEntryEvidence(observation.statusOrdinal)
    ensures io.statusCursor() == old(io.statusCursor())+1
    ensures Native.TraceFields(cmd.nativeInputs[0],old(NativeIO.State(io)),NativeIO.State(io),
                               observation.nativeCalls)
    ensures output == (if observation.ok then Spec.RenderEntrySpec(cmd,observation.renderName,observation.status) else [])
    ensures errors == Spec.EntryErrorTextSpec(displayName,observation)
    ensures hadError == Spec.ObservationFailedSpec(observation)
    ensures observation.entryKind == entryKind && observation.displayName == displayName
    ensures observation.accessPath == path && observation.followSymlink == followSymlink
  {
    ghost var before := NativeIO.State(io);
    var ok,status,err,renderName,linkErr,calls := NativeObserve.Observe(displayName,path,
                                                                        followSymlink,cmd.numericLong,io);
    NativeFrames.PathFrame(cmd.nativeInputs[0],before,NativeIO.State(io),displayName,path,
                           followSymlink,cmd.numericLong,ok,status,err,renderName,linkErr,calls);
    observation := Spec.EntryObservation(displayName,renderName,path,followSymlink,ok,status,
                                         err,linkErr,entryKind,before.status,Spec.StatusEntryEvidence(before.status),calls);
    if ok {
      output := Spec.RenderEntrySpec(cmd,renderName,status);
      errors := Spec.ReadLinkErrorMessageSpec(displayName,linkErr);
      hadError := linkErr != 0;
    } else {
      output := [];
      errors := Spec.AccessErrorMessageSpec(displayName,err);
      hadError := true;
    }
    assert Spec.MetadataObservationRelation(cmd,io.fs(),observation) by {
      reveal Spec.MetadataObservationRelation(), Spec.NativeCommandFields();
    }
    assert Native.TraceFields(cmd.nativeInputs[0],before,NativeIO.State(io),calls) by {
      reveal NativeObservation.PathFields();
    }
  }

  method ObserveDirectoryEntry(
    cmd: Schema.LsCmd, name: string, path: BenchWorld.Path,
    kind: BenchWorld.DirectoryEntryKind, ghost entry: BenchWorld.DirEntry,
    io: BenchIO.IO
  ) returns (observation: Spec.EntryObservation, output: BenchWorld.Bytes,
             errors: BenchWorld.Bytes, hadError: bool)
    requires cmd.statusContext.BoundStatusObservations?
    requires cmd.statusContext.observations == io.statusObservations()
    requires cmd.statusContext.failures == io.trustedNativeFailures()
    requires |cmd.nativeInputs| == 1 && cmd.nativeInputs[0] == NativeIO.Inputs(io)
    requires entry.name == name
    requires IOContract.DirectoryEntryKindMatchesEntry(kind, entry)
    modifies io.directoryStateRegion, io.statusObservationsRegion
    ensures observation.displayName == name && observation.accessPath == path
    ensures observation.entryKind == kind
    ensures NativeIO.Inputs(io) == old(NativeIO.Inputs(io))
    ensures Native.TraceFields(cmd.nativeInputs[0],old(NativeIO.State(io)),NativeIO.State(io),observation.nativeCalls)
    ensures io.cwdContext().topology == old(io.cwdContext()).topology
    ensures io.cwdContext().capabilities == old(io.cwdContext()).capabilities
    ensures io.cwdContext().position == old(io.cwdContext()).position
    ensures io.cwdContext().hint == old(io.cwdContext()).hint
    ensures io.cwdContext().legacyHandles == old(io.cwdContext()).legacyHandles
    ensures io.cwdContext().legacyOrigins == old(io.cwdContext()).legacyOrigins
    ensures observation.statusOrdinal == old(io.statusCursor())
    ensures io.statusCursor() == old(io.statusCursor()) + Spec.EntryStatusCallCount(observation)
    ensures if Spec.EntryStatusRequiredSpec(cmd, Spec.ClassifiedDirentKindSpec(kind), name) then
              observation.source == Spec.StatusEntryEvidence(observation.statusOrdinal) &&
              Spec.MetadataObservationRelation(cmd, old(io.fs()), observation) &&
              observation.followSymlink ==
              (cmd.followMode == Schema.FollowAlways && Spec.EntryMetadataRequiredSpec(cmd))
            else
              observation.source == Spec.DirentEntryEvidence(entry, Spec.ClassifiedDirentKindSpec(kind)) &&
              Spec.DirentKindMatchesEntrySpec(Spec.ClassifiedDirentKindSpec(kind), entry) &&
              Spec.CanonicalDirentFields(observation)
    ensures !Spec.EntryStatusRequiredSpec(cmd,Spec.ClassifiedDirentKindSpec(kind),name) ==> observation.nativeCalls == []
    ensures output == (if observation.ok then Spec.RenderEntrySpec(cmd, observation.renderName, observation.status) else [])
    ensures errors == Spec.EntryErrorTextSpec(name, observation)
    ensures hadError == Spec.ObservationFailedSpec(observation)
  {
    if Spec.EntryStatusRequiredSpec(cmd, Spec.ClassifiedDirentKindSpec(kind), name) {
      observation, output, errors, hadError := ObservePath(
        cmd, name, kind, path,
        cmd.followMode == Schema.FollowAlways && Spec.EntryMetadataRequiredSpec(cmd), io);
    } else {
      observation := Spec.EntryObservation(
        name, name, path, false, true, BenchWorld.DEFAULT_FILE_STATUS, 0, 0, kind,
        io.statusCursor(), Spec.DirentEntryEvidence(entry, Spec.ClassifiedDirentKindSpec(kind)));
      output := Spec.RenderEntrySpec(cmd, name, BenchWorld.DEFAULT_FILE_STATUS);
      errors := [];
      hadError := false;
    }
  }

  method ObserveDotEntry(
    cmd: Schema.LsCmd, name: string, path: BenchWorld.Path, io: BenchIO.IO
  ) returns (observation: Spec.EntryObservation, output: BenchWorld.Bytes,
             errors: BenchWorld.Bytes, hadError: bool)
    requires cmd.statusContext.BoundStatusObservations?
    requires cmd.statusContext.observations == io.statusObservations()
    requires cmd.statusContext.failures == io.trustedNativeFailures()
    requires |cmd.nativeInputs| == 1 && cmd.nativeInputs[0] == NativeIO.Inputs(io)
    requires name == "." || name == ".."
    modifies io.directoryStateRegion, io.statusObservationsRegion
    ensures observation.displayName == name && observation.accessPath == path
    ensures observation.entryKind == BenchWorld.DirectoryDirentKind
    ensures NativeIO.Inputs(io) == old(NativeIO.Inputs(io))
    ensures Native.TraceFields(cmd.nativeInputs[0],old(NativeIO.State(io)),NativeIO.State(io),observation.nativeCalls)
    ensures io.cwdContext().topology == old(io.cwdContext()).topology
    ensures io.cwdContext().capabilities == old(io.cwdContext()).capabilities
    ensures io.cwdContext().position == old(io.cwdContext()).position
    ensures io.cwdContext().hint == old(io.cwdContext()).hint
    ensures io.cwdContext().legacyHandles == old(io.cwdContext()).legacyHandles
    ensures io.cwdContext().legacyOrigins == old(io.cwdContext()).legacyOrigins
    ensures observation.statusOrdinal == old(io.statusCursor())
    ensures io.statusCursor() == old(io.statusCursor()) + Spec.EntryStatusCallCount(observation)
    ensures if Spec.EntryRenderSortMetadataRequiredSpec(cmd) then
              observation.source == Spec.StatusEntryEvidence(observation.statusOrdinal) &&
              Spec.MetadataObservationRelation(cmd, old(io.fs()), observation) &&
              observation.followSymlink ==
              (cmd.followMode == Schema.FollowAlways && Spec.EntryMetadataRequiredSpec(cmd))
            else observation.source == Spec.ImpliedDotEntryEvidence && Spec.CanonicalDirentFields(observation)
    ensures !Spec.EntryRenderSortMetadataRequiredSpec(cmd) ==> observation.nativeCalls == []
    ensures output == (if observation.ok then Spec.RenderEntrySpec(cmd, observation.renderName, observation.status) else [])
    ensures errors == Spec.EntryErrorTextSpec(name, observation)
    ensures hadError == Spec.ObservationFailedSpec(observation)
  {
    if Spec.EntryRenderSortMetadataRequiredSpec(cmd) {
      observation, output, errors, hadError := ObservePath(
        cmd, name, BenchWorld.DirectoryDirentKind, path,
        cmd.followMode == Schema.FollowAlways && Spec.EntryMetadataRequiredSpec(cmd), io);
    } else {
      observation := Spec.EntryObservation(
        name, name, path, false, true, BenchWorld.DEFAULT_FILE_STATUS, 0, 0,
        BenchWorld.DirectoryDirentKind, io.statusCursor(), Spec.ImpliedDotEntryEvidence);
      output := Spec.RenderEntrySpec(cmd, name, BenchWorld.DEFAULT_FILE_STATUS);
      errors := [];
      hadError := false;
    }
  }

  method AddObservation(
    cmd: Schema.LsCmd,
    observation: Spec.EntryObservation,
    piece: BenchWorld.Bytes,
    errorPiece: BenchWorld.Bytes,
    observations: seq<Spec.EntryObservation>,
    outputFragments: seq<BenchWorld.Bytes>,
    outputCuts: seq<nat>,
    output: BenchWorld.Bytes,
    errorFragments: seq<BenchWorld.Bytes>,
    errorCuts: seq<nat>,
    errors: BenchWorld.Bytes
  ) returns (
      observations2: seq<Spec.EntryObservation>,
      outputFragments2: seq<BenchWorld.Bytes>,
      outputCuts2: seq<nat>,
      output2: BenchWorld.Bytes,
      errorFragments2: seq<BenchWorld.Bytes>,
      errorCuts2: seq<nat>,
      errors2: BenchWorld.Bytes
    )
    requires RawObservationPiecesSummary(cmd, observations, outputFragments, errorFragments)
    requires Spec.FragmentsConcatenate(outputFragments, output, outputCuts)
    requires Spec.FragmentsConcatenate(errorFragments, errors, errorCuts)
    requires piece ==
             (if observation.ok then Spec.RenderEntrySpec(cmd, observation.renderName, observation.status) else [])
    requires errorPiece ==
             Spec.EntryErrorTextSpec(observation.displayName, observation)
    ensures observations2 == observations + [observation]
    ensures RawObservationPiecesSummary(cmd, observations2, outputFragments2, errorFragments2)
    ensures Spec.FragmentsConcatenate(outputFragments2, output2, outputCuts2)
    ensures Spec.FragmentsConcatenate(errorFragments2, errors2, errorCuts2)
  {
    AppendFragment(outputFragments, output, outputCuts, piece);
    AppendFragment(errorFragments, errors, errorCuts, errorPiece);
    observations2 := observations + [observation];
    outputFragments2 := outputFragments + [piece];
    outputCuts2 := outputCuts + [|output + piece|];
    output2 := output + piece;
    errorFragments2 := errorFragments + [errorPiece];
    errorCuts2 := errorCuts + [|errors + errorPiece|];
    errors2 := errors + errorPiece;
  }

  method ContainsDisplayName(
    observations: seq<Spec.EntryObservation>,
    name: string
  ) returns (found: bool)
    ensures found == (exists i: nat :: i < |observations| && observations[i].displayName == name)
  {
    found := false;
    var i := 0;
    while i < |observations|
      invariant 0 <= i <= |observations|
      invariant found ==
                (exists j: nat :: j < i && observations[j].displayName == name)
      decreases |observations| - i
    {
      if observations[i].displayName == name {
        found := true;
      }
      i := i + 1;
    }
  }

  lemma DistinctEmpty()
    ensures Spec.DistinctDisplayNames([])
  {
    reveal Spec.DistinctDisplayNames();
  }

  lemma DistinctSnoc(
    observations: seq<Spec.EntryObservation>,
    observation: Spec.EntryObservation
  )
    requires Spec.DistinctDisplayNames(observations)
    requires !(exists i: nat ::
                 i < |observations| && observations[i].displayName == observation.displayName)
    ensures Spec.DistinctDisplayNames(observations + [observation])
  {
    reveal Spec.DistinctDisplayNames();
    assert (observations + [observation])[..|observations|] == observations;
    assert forall i: nat :: i < |observations| ==>
                              observations[i].displayName != observation.displayName by {
      forall i: nat | i < |observations|
        ensures observations[i].displayName != observation.displayName
      {
        assert !(exists k: nat ::
                   k < |observations| && observations[k].displayName == observation.displayName);
      }
    }
  }

  ghost opaque predicate ProcessedCoverage(
    cmd: Schema.LsCmd,
    expected: set<BenchWorld.DirEntry>,
    remaining: set<BenchWorld.DirEntry>,
    observations: seq<Spec.EntryObservation>
  )
  {
    forall entry: BenchWorld.DirEntry ::
      entry in expected - remaining && Spec.VisibleNameSpec(cmd, entry.name) ==>
        exists i: nat :: i < |observations| && observations[i].displayName == entry.name
  }

  lemma ProcessedCoverageInit(
    cmd: Schema.LsCmd,
    expected: set<BenchWorld.DirEntry>,
    observations: seq<Spec.EntryObservation>
  )
    ensures ProcessedCoverage(cmd, expected, expected, observations)
  {
    reveal ProcessedCoverage();
  }

  lemma ProcessedCoverageRemove(
    cmd: Schema.LsCmd,
    expected: set<BenchWorld.DirEntry>,
    beforeRemaining: set<BenchWorld.DirEntry>,
    entry: BenchWorld.DirEntry,
    before: seq<Spec.EntryObservation>,
    after: seq<Spec.EntryObservation>
  )
    requires ProcessedCoverage(cmd, expected, beforeRemaining, before)
    requires entry in beforeRemaining
    requires |before| <= |after| && after[..|before|] == before
    requires Spec.VisibleNameSpec(cmd, entry.name) ==>
               exists i: nat :: i < |after| && after[i].displayName == entry.name
    ensures ProcessedCoverage(cmd, expected, beforeRemaining - {entry}, after)
  {
    reveal ProcessedCoverage();
    forall candidate: BenchWorld.DirEntry |
      candidate in expected - (beforeRemaining - {entry}) &&
      Spec.VisibleNameSpec(cmd, candidate.name)
      ensures exists i: nat :: i < |after| && after[i].displayName == candidate.name
    {
      if candidate != entry {
        assert candidate in expected - beforeRemaining;
        var i: nat :| i < |before| && before[i].displayName == candidate.name;
        assert after[i] == before[i];
      }
    }
  }

  ghost predicate DirectoryStatusCuts(
    observations: seq<Spec.EntryObservation>, cuts: seq<nat>, firstStatus: nat, afterStatus: nat
  )
  {
    |cuts| == |observations| + 1 && cuts[0] == firstStatus &&
    cuts[|observations|] == afterStatus &&
    forall i: nat | i < |observations| ::
      observations[i].statusOrdinal == cuts[i] &&
      cuts[i + 1] == cuts[i] + Spec.EntryStatusCallCount(observations[i])
  }

  lemma DirectoryStatusCutsSnoc(
    observations: seq<Spec.EntryObservation>, cuts: seq<nat>,
    firstStatus: nat, beforeStatus: nat, afterStatus: nat, observation: Spec.EntryObservation
  )
    requires DirectoryStatusCuts(observations, cuts, firstStatus, beforeStatus)
    requires observation.statusOrdinal == beforeStatus
    requires afterStatus == beforeStatus + Spec.EntryStatusCallCount(observation)
    ensures DirectoryStatusCuts(observations + [observation], cuts + [afterStatus], firstStatus, afterStatus)
  {
    forall i: nat | i < |observations + [observation]|
      ensures (observations + [observation])[i].statusOrdinal == (cuts + [afterStatus])[i] &&
              (cuts + [afterStatus])[i + 1] == (cuts + [afterStatus])[i] +
              Spec.EntryStatusCallCount((observations + [observation])[i])
    {
      if i < |observations| { assert i + 1 < |cuts|; }
      else { assert i == |observations|; }
    }
  }

  lemma CompleteDirectoryObservations(
    cmd: Schema.LsCmd, fs: BenchWorld.FileSystem, path: BenchWorld.Path,
    expected: set<BenchWorld.DirEntry>, firstStatus: nat, afterStatus: nat,
    observations: seq<Spec.EntryObservation>, statusCuts: seq<nat>)
    requires cmd.statusContext.BoundStatusObservations?
    requires DirectoryStatusCuts(observations,statusCuts,firstStatus,afterStatus)
    requires BenchWorld.DirEntry(".",true,false) in expected
    requires BenchWorld.DirEntry("..",true,false) in expected
    requires Spec.DistinctDisplayNames(observations)
    requires forall i: nat | i < |observations| :: Spec.DirectorySourceRelation(cmd,fs,path,observations[i])
    requires ProcessedCoverage(cmd,expected,{},observations)
    ensures Spec.DirectoryObservationRelation(cmd,fs,path,firstStatus,afterStatus,true,observations,expected)
  {
    hide *;
    reveal Spec.DirectoryObservationRelation(), ProcessedCoverage(), DirectoryStatusCuts();
    reveal Spec.VisibleNameSpec();
  }

  lemma StatusOnlyDirectoryCuts(
    observations: seq<Spec.EntryObservation>, firstStatus: nat
  )
    requires forall i: nat :: i < |observations| ==>
                                observations[i].statusOrdinal == firstStatus + i &&
                                observations[i].source ==
                                Spec.StatusEntryEvidence(observations[i].statusOrdinal)
    ensures exists cuts: seq<nat> ::
              |cuts| == |observations| + 1 &&
              cuts[0] == firstStatus &&
              cuts[|observations|] == firstStatus + |observations| &&
              (forall i: nat | i < |observations| ::
                 observations[i].statusOrdinal == cuts[i] &&
                 cuts[i + 1] == cuts[i] + Spec.EntryStatusCallCount(observations[i]))
  {
    ghost var cuts := seq(|observations| + 1,
    i requires i < |observations| + 1 => firstStatus + i);
    assert |cuts| == |observations| + 1;
    assert cuts[0] == firstStatus;
    assert cuts[|observations|] == firstStatus + |observations|;
    assert forall i: nat | i < |observations| ::
        observations[i].statusOrdinal == cuts[i] &&
        cuts[i + 1] == cuts[i] + Spec.EntryStatusCallCount(observations[i]);
    assert |cuts| == |observations| + 1 &&
           cuts[0] == firstStatus &&
           cuts[|observations|] == firstStatus + |observations| &&
           (forall i: nat | i < |observations| ::
              observations[i].statusOrdinal == cuts[i] &&
              cuts[i + 1] == cuts[i] + Spec.EntryStatusCallCount(observations[i]));
    assert exists witnessCuts: seq<nat> ::
        |witnessCuts| == |observations| + 1 &&
        witnessCuts[0] == firstStatus &&
        witnessCuts[|observations|] == firstStatus + |observations| &&
        (forall i: nat | i < |observations| ::
           observations[i].statusOrdinal == witnessCuts[i] &&
           witnessCuts[i + 1] == witnessCuts[i] +
           Spec.EntryStatusCallCount(observations[i]));
  }

  method RenderObservationSequence(
    cmd: Schema.LsCmd,
    displayPath: BenchWorld.Path,
    observations: seq<Spec.EntryObservation>
  ) returns (
      output: BenchWorld.Bytes,
      errors: BenchWorld.Bytes,
      hadError: bool,
      ghost outputFragments: seq<BenchWorld.Bytes>,
      ghost outputCuts: seq<nat>,
      ghost errorFragments: seq<BenchWorld.Bytes>,
      ghost errorCuts: seq<nat>
    )
    ensures ObservationPiecesSummary(cmd, observations, outputFragments)
    ensures Spec.ObservationErrorsRelation(displayPath, observations, errorFragments)
    ensures Spec.FragmentsConcatenate(outputFragments, output, outputCuts)
    ensures Spec.FragmentsConcatenate(errorFragments, errors, errorCuts)
    ensures hadError ==
            (exists i: nat :: i < |observations| && Spec.ObservationFailedSpec(observations[i]))
  {
    hide *;
    output := [];
    errors := [];
    hadError := false;
    outputFragments := [];
    outputCuts := [0];
    errorFragments := [];
    errorCuts := [0];
    assert Spec.FragmentsConcatenate([], [], [0]) by {
      reveal Spec.FragmentsConcatenate();
    }
    var i := 0;
    while i < |observations|
      invariant 0 <= i <= |observations|
      invariant |outputFragments| == i
      invariant |errorFragments| == i
      invariant forall j: nat | j < i ::
                  outputFragments[j] == (if observations[j].ok then
                                           Spec.RenderAlignedEntrySpec(cmd, observations[j].renderName, observations[j].status,
                                                                       Spec.ObservationWidthsSpec(cmd, observations)) else Spec.RenderFailedEntrySpec(cmd, observations[j], Spec.ObservationWidthsSpec(cmd, observations))) &&
                  errorFragments[j] == Spec.EntryErrorTextSpec(Spec.EntryDiagnosticPathSpec(displayPath, observations[j].displayName), observations[j])
      invariant Spec.FragmentsConcatenate(outputFragments, output, outputCuts)
      invariant Spec.FragmentsConcatenate(errorFragments, errors, errorCuts)
      invariant hadError ==
                (exists j: nat :: j < i && Spec.ObservationFailedSpec(observations[j]))
      decreases |observations| - i
    {
      var observation := observations[i];
      assert (exists j: nat :: j < i + 1 && Spec.ObservationFailedSpec(observations[j])) ==
             (hadError || Spec.ObservationFailedSpec(observation)) by {
        if exists j: nat :: j < i + 1 && Spec.ObservationFailedSpec(observations[j]) {
          var j: nat :| j < i + 1 && Spec.ObservationFailedSpec(observations[j]);
          if j < i {
            assert exists k: nat :: k < i && Spec.ObservationFailedSpec(observations[k]);
          }
        }
        if hadError {
          var j: nat :| j < i && Spec.ObservationFailedSpec(observations[j]);
          assert j < i + 1 && Spec.ObservationFailedSpec(observations[j]);
        } else if Spec.ObservationFailedSpec(observation) {
          assert i < i + 1 && Spec.ObservationFailedSpec(observations[i]);
        }
      }
      var piece := if observation.ok
      then Spec.RenderAlignedEntrySpec(cmd, observation.renderName, observation.status, Text.ObservationWidthsSpec(cmd, observations))
      else Spec.RenderFailedEntrySpec(cmd, observation, Text.ObservationWidthsSpec(cmd, observations));
      var errorPiece := Spec.EntryErrorTextSpec(
        Spec.EntryDiagnosticPathSpec(displayPath, observation.displayName), observation);
      assert piece == (if observation.ok then
                         Spec.RenderAlignedEntrySpec(cmd, observation.renderName, observation.status,
                                                     Spec.ObservationWidthsSpec(cmd, observations))
                       else Spec.RenderFailedEntrySpec(cmd, observation, Spec.ObservationWidthsSpec(cmd, observations)));
      assert errorPiece == Spec.EntryErrorTextSpec(
                             Spec.EntryDiagnosticPathSpec(displayPath, observation.displayName), observation) by {
        reveal Spec.EntryDiagnosticPathSpec();
      }
      AppendFragment(outputFragments, output, outputCuts, piece);
      AppendFragment(errorFragments, errors, errorCuts, errorPiece);
      outputFragments := outputFragments + [piece];
      outputCuts := outputCuts + [|output + piece|];
      output := output + piece;
      errorFragments := errorFragments + [errorPiece];
      errorCuts := errorCuts + [|errors + errorPiece|];
      errors := errors + errorPiece;
      hadError := hadError || Spec.ObservationFailedSpec(observation);
      i := i + 1;
    }
    assert ObservationPiecesSummary(cmd, observations, outputFragments) by {
      reveal ObservationPiecesSummary();
    }
    assert Spec.ObservationErrorsRelation(displayPath, observations, errorFragments) by {
      reveal Spec.ObservationErrorsRelation();
    }
  }

  lemma BindOpenDirectoryTrace(cmd: Schema.LsCmd, fs: BenchWorld.FileSystem,
                               path: BenchWorld.Path, trace: Spec.DirectoryTrace)
    requires Spec.NativeCommandFields(cmd,fs) && trace.DirectoryTrace?
    requires |trace.openCalls| == 1 && Native.CallFields(cmd.nativeInputs[0],trace.openCalls[0])
    requires trace.openCalls[0].action.OpenAction? && trace.openCalls[0].action.path == path && trace.openCalls[0].action.dots
    requires trace.openCalls[0].action.openResult.Ok? == trace.openOk
    requires IOContract.ResultErrno(trace.openCalls[0].action.openResult) == trace.openErr
    requires IOContract.ResultValue(trace.openCalls[0].action.openResult,0) == trace.handle
    requires trace.openedHandles == trace.openCalls[0].after.context.capabilities
    ensures Spec.BoundOpenDirectoryTrace(cmd,fs,path,trace,trace.openOk,trace.openErr)
  {
    hide *;
    reveal Spec.NativeCommandFields();
    assert trace.openCalls == [trace.openCalls[0]];
    NativeTrace.Single(cmd.nativeInputs[0],trace.openCalls[0]);
    assert Spec.NativeCallsFields(cmd,fs,trace.openCalls) by { reveal Spec.NativeCallsFields(); }
    reveal Spec.BoundOpenDirectoryTrace();
  }

  lemma AppendDirectoryReadPrefix(cmd: Schema.LsCmd, fs: BenchWorld.FileSystem,
                                  openedHandles: map<int,BenchWorld.DirectoryCapabilityState>, handle: int,
                                  steps: seq<Spec.DirectoryReadStep>, step: Spec.DirectoryReadStep)
    requires Spec.DirectoryReadPrefix(cmd,fs,openedHandles,handle,steps,step.before)
    requires step.more && step.err == 0
    requires Spec.DirectoryReadStepFields(cmd,fs,handle,step)
    ensures Spec.DirectoryReadPrefix(cmd,fs,openedHandles,handle,steps+[step],step.after)
  {
    DirectoryTraceProof.AppendReadPrefix(cmd,fs,openedHandles,handle,steps,step);
  }

  lemma AppendDirectoryReadEvidence(cmd: Schema.LsCmd,
                                    steps: seq<Spec.DirectoryReadStep>, step: Spec.DirectoryReadStep,
                                    raw: seq<Spec.EntryObservation>, positions: seq<nat>,
                                    nextRaw: seq<Spec.EntryObservation>, nextPositions: seq<nat>)
    requires Spec.DirectoryReadEvidence(cmd, steps, raw, positions)
    requires (nextRaw == raw && nextPositions == positions) ||
             (|nextRaw| == |raw|+1 && nextRaw[..|raw|] == raw &&
              nextPositions == positions + [|steps|] &&
              nextRaw[|raw|].displayName == step.name &&
              nextRaw[|raw|].directoryRead == step.nativeCalls &&
              (nextRaw[|raw|].entryKind == step.kind ||
               ((step.name == "." || step.name == "..") &&
                nextRaw[|raw|].entryKind == BenchWorld.DirectoryDirentKind)))
    requires Spec.VisibleNameSpec(cmd, step.name) ==>
               exists j: nat :: j < |nextRaw| && nextRaw[j].displayName == step.name
    ensures Spec.DirectoryReadEvidence(cmd, steps + [step], nextRaw, nextPositions)
  {
    DirectoryTraceProof.AppendReadEvidence(cmd,steps,step,raw,positions,nextRaw,nextPositions);
  }

  method {:isolate_assertions} CollectDirectoryEntries(cmd: Schema.LsCmd, path: BenchWorld.Path,
                                 handle: int, io: BenchIO.IO)
    returns (observations: seq<Spec.EntryObservation>, readErr: int,
             ghost steps: seq<Spec.DirectoryReadStep>, ghost terminal: Spec.DirectoryReadStep,
             ghost positions: seq<nat>, ghost calls: seq<Native.Call>,
             ghost pieces: seq<seq<Native.Call>>, ghost cuts: seq<nat>)
    requires Spec.NativeCommandFields(cmd,io.fs()) && cmd.nativeInputs[0] == NativeIO.Inputs(io)
    requires handle in io.directoryCapabilities()
    requires IOContract.DirectoryCapabilityReadCurrentFields(io.directoryTopology(),io.directoryCapabilities()[handle])
    requires io.directoryCapabilities()[handle].includeDots
    requires io.directoryCapabilities()[handle].remaining == IOContract.DirectoryCapabilityNamesFields(
                                                               io.directoryTopology(),io.directoryCapabilities()[handle].position,true)
    modifies io.directoryStateRegion,io.statusObservationsRegion
    ensures NativeIO.Inputs(io) == old(NativeIO.Inputs(io))
    ensures io.dirHandles() == old(io.dirHandles()) && io.directoryOrigins() == old(io.directoryOrigins())
    ensures io.directoryTopology() == old(io.directoryTopology())
    ensures handle in io.directoryCapabilities()
    ensures io.directoryCapabilities()[handle].position == old(io.directoryCapabilities())[handle].position
    ensures io.directoryCapabilities()[handle].remaining <= old(io.directoryCapabilities())[handle].remaining
    ensures readErr == 0 ==> io.directoryCapabilities()[handle].remaining == {}
    ensures io.directoryCapabilities() - {handle} == old(io.directoryCapabilities()) - {handle}
    ensures Spec.DirectoryReadPrefix(cmd,old(io.fs()),old(io.directoryCapabilities()),handle,steps,terminal.before)
    ensures Spec.DirectoryReadEvidence(cmd,steps,observations,positions)
    ensures terminal.after == io.directoryCapabilities() && !terminal.more && terminal.err == readErr
    ensures terminal.name == "" && terminal.kind == BenchWorld.UnknownDirentKind
    ensures Spec.DirectoryReadStepFields(cmd,old(io.fs()),handle,terminal)
    ensures Spec.DirectoryObservationRelation(cmd,old(io.fs()),path,
                                              old(io.statusCursor()),io.statusCursor(),readErr == 0,observations,
                                              NativeDirectory.EntriesForNames(old(io.directoryTopology()),old(io.directoryCapabilities())[handle].position,
                                                                              old(io.directoryCapabilities())[handle].remaining))
    ensures Native.TraceFields(cmd.nativeInputs[0],old(NativeIO.State(io)),NativeIO.State(io),calls+terminal.nativeCalls)
    ensures Spec.NativeCallFragments(pieces,calls,cuts) && |pieces| == |steps|
    ensures forall i: nat | i < |steps| ::
              (if exists j: nat :: j < |positions| && positions[j] == i then
                 exists j: nat :: j < |positions| && j < |observations| && positions[j] == i &&
                                  pieces[i] == steps[i].nativeCalls+observations[j].nativeCalls
               else pieces[i] == steps[i].nativeCalls)
    decreases *
  {
    hide *;
    reveal Spec.NativeCommandFields(), Spec.EntryStatusCallCount();
    reveal IOContract.DirectoryCapabilityReadCurrentFields(), IOContract.DirectoryCapabilityAnchorCurrentFields();
    reveal IOContract.DirectoryCapabilityNamesFields();
    ghost var preFs := io.fs();
    ghost var before := NativeIO.State(io);
    ghost var topology := io.directoryTopology();
    ghost var openedHandles := io.directoryCapabilities();
    ghost var legacyHandles := io.dirHandles();
    ghost var legacyOrigins := io.directoryOrigins();
    ghost var position := openedHandles[handle].position;
    ghost var expectedNames := openedHandles[handle].remaining;
    assert position in topology.nodes && expectedNames <= topology.nodes[position].entries.Keys+{".",".."};
    assert IOContract.LiveDirectoryTopologyFields(preFs,topology) by { reveal IOContract.CwdContextFields(); }
    assert "." in expectedNames && ".." in expectedNames;
    ghost var expected := NativeDirectory.EntriesForNames(topology,position,expectedNames);
    ghost var statusCuts: seq<nat> := [before.status];
    observations := [];
    readErr := 0;
    steps := [];
    positions := [];
    calls := [];
    pieces := [];
    cuts := [0];
    terminal := Spec.DirectoryReadStep(openedHandles,openedHandles,false,"",BenchWorld.UnknownDirentKind,0);
    DistinctEmpty();
    ProcessedCoverageInit(cmd,expected,observations);
    assert Spec.DirectoryReadPrefix(cmd,preFs,openedHandles,handle,steps,openedHandles) by { reveal Spec.DirectoryReadPrefix(); }
    assert Spec.DirectoryReadEvidence(cmd,steps,observations,positions) by { reveal Spec.DirectoryReadEvidence(); }
    assert DirectoryStatusCuts(observations,statusCuts,before.status,io.statusCursor()) by { reveal DirectoryStatusCuts(); }
    assert Native.TraceFields(cmd.nativeInputs[0],before,NativeIO.State(io),calls) by { reveal Native.TraceFields(); }
    DirectoryTraceProof.EmptyNativeCallFragments();
    var finished := false;
    while !finished
      invariant NativeIO.Inputs(io) == cmd.nativeInputs[0]
      invariant io.dirHandles() == legacyHandles && io.directoryOrigins() == legacyOrigins
      invariant io.directoryTopology() == topology
      invariant handle in io.directoryCapabilities()
      invariant io.directoryCapabilities()[handle].position == position
      invariant io.directoryCapabilities()[handle].includeDots
      invariant IOContract.DirectoryCapabilityReadCurrentFields(topology,io.directoryCapabilities()[handle])
      invariant io.directoryCapabilities()[handle].remaining <= expectedNames
      invariant io.directoryCapabilities() - {handle} == openedHandles - {handle}
      invariant Spec.DirectoryReadPrefix(cmd,preFs,openedHandles,handle,steps,
                                         if finished then terminal.before else io.directoryCapabilities())
      invariant Spec.DirectoryReadEvidence(cmd,steps,observations,positions)
      invariant DirectoryStatusCuts(observations,statusCuts,before.status,io.statusCursor())
      invariant forall i: nat | i < |observations| :: Spec.DirectorySourceRelation(cmd,preFs,path,observations[i])
      invariant Spec.DistinctDisplayNames(observations)
      invariant readErr == 0 ==> ProcessedCoverage(cmd,expected,
                                                   NativeDirectory.EntriesForNames(topology,position,io.directoryCapabilities()[handle].remaining),observations)
      invariant !finished ==> readErr == 0
      invariant finished ==>
                  terminal.after == io.directoryCapabilities() &&
                  !terminal.more && terminal.name == "" && terminal.kind == BenchWorld.UnknownDirentKind && terminal.err == readErr &&
                  Spec.DirectoryReadStepFields(cmd,preFs,handle,terminal)
      invariant finished && readErr == 0 ==> io.directoryCapabilities()[handle].remaining == {}
      invariant Native.TraceFields(cmd.nativeInputs[0],before,NativeIO.State(io),
                                   if finished then calls+terminal.nativeCalls else calls)
      invariant Spec.NativeCallFragments(pieces,calls,cuts) && |pieces| == |steps|
      invariant forall i: nat | i < |steps| ::
                  (if exists j: nat :: j < |positions| && positions[j] == i then
                     exists j: nat :: j < |positions| && j < |observations| && positions[j] == i &&
                                      pieces[i] == steps[i].nativeCalls+observations[j].nativeCalls
                   else pieces[i] == steps[i].nativeCalls)
      decreases *
    {
      ghost var stepBefore := NativeIO.State(io);
      ghost var beforeRemaining := io.directoryCapabilities()[handle].remaining;
      ghost var beforeObservations := observations;
      ghost var beforeSteps := steps;
      ghost var beforePositions := positions;
      ghost var beforeCalls := calls;
      ghost var beforePieces := pieces;
      ghost var beforeCuts := cuts;
      assert IOContract.DirectoryOperationCapabilitiesCurrentFields(topology,io.directoryCapabilities(),
                                                                    BenchWorld.DirectoryReadNext,handle,0) by { reveal IOContract.DirectoryOperationCapabilitiesCurrentFields(); }
      var item,read := NativeIO.Read(handle,io);
      NativeResources.ReadFrame(cmd.nativeInputs[0],read);
      NativeTrace.Single(cmd.nativeInputs[0],read);
      var more := item.Ok? && item.v.DirectoryItem?;
      var name := if more then item.v.name else "";
      var kind := if more then item.v.kind else BenchWorld.UnknownDirentKind;
      var err := IOContract.ResultErrno(item);
      assert more ==> err == 0;
      ghost var step := Spec.DirectoryReadStep(read.before.context.capabilities,
                                               read.after.context.capabilities,more,name,kind,err,[read]);
      assert Spec.DirectoryReadStepFields(cmd,preFs,handle,step) by {
        reveal Spec.DirectoryReadStepFields(), Spec.NativeCallsFields();
      }
      if !more {
        terminal := step;
        readErr := err;
        finished := true;
        NativeTrace.Concat(cmd.nativeInputs[0],before,stepBefore,NativeIO.State(io),calls,[read]);
        if readErr == 0 {
          assert beforeRemaining == {} by {
            reveal Native.CallFields(), IOContract.ContextOperationSpec(), IOContract.DirectoryOperationSpec();
            reveal IOContract.DirectoryResponseFields(), IOContract.DirectoryReadResultFields();
          }
        }
      } else {
        NativeResources.ReadItem(cmd.nativeInputs[0],read);
        ghost var entry := NativeDirectory.EntryForName(topology,position,name);
        NativeEntries.RawKindMatchesEntry(preFs,topology,position,name,kind);
        NativeEntries.Membership(topology,position,beforeRemaining,entry);
        NativeEntries.RemoveName(topology,position,beforeRemaining,name);
        ghost var entryCalls: seq<Native.Call> := [];
        if Spec.VisibleNameSpec(cmd,name) {
          var seen := ContainsDisplayName(observations,name);
          if !seen {
            ghost var firstEntry := NativeIO.State(io);
            var childPath := WorldPath.AppendPath(path,name);
            var observation: Spec.EntryObservation;
            var piece: BenchWorld.Bytes;
            var errorPiece: BenchWorld.Bytes;
            var failed: bool;
            if name == "." || name == ".." {
              observation,piece,errorPiece,failed := ObserveDotEntry(cmd,name,childPath,io);
            } else {
              observation,piece,errorPiece,failed := ObserveDirectoryEntry(cmd,name,childPath,kind,entry,io);
            }
            ghost var metadataObservation := observation;
            observation := observation.(directoryRead := [read]);
            entryCalls := observation.nativeCalls;
            assert Spec.DirectorySourceRelation(cmd,preFs,path,observation) by {
              hide *;
              reveal Spec.DirectorySourceRelation(), Spec.NativeDirectoryReadFields(), Spec.NativeDirentEntryFields();
              reveal Spec.NativeCommandFields(), Spec.NativeCallsFields(), Spec.VisibleNameSpec();
              reveal Spec.EntryStatusRequiredSpec(), Spec.EntryRenderSortMetadataRequiredSpec();
              reveal Spec.MetadataObservationRelation(), Spec.CanonicalDirentFields();
            }
            DirectoryStatusCutsSnoc(observations,statusCuts,before.status,firstEntry.status,io.statusCursor(),observation);
            DistinctSnoc(observations,observation);
            observations := observations+[observation];
            positions := positions+[|beforeSteps|];
            statusCuts := statusCuts+[io.statusCursor()];
          }
        }
        if |observations| == |beforeObservations| {
          assert Native.TraceFields(cmd.nativeInputs[0],read.after,NativeIO.State(io),[]) by { reveal Native.TraceFields(); }
        }
        AppendDirectoryReadPrefix(cmd,preFs,openedHandles,handle,beforeSteps,step);
        AppendDirectoryReadEvidence(cmd,beforeSteps,step,beforeObservations,beforePositions,observations,positions);
        steps := beforeSteps+[step];
        ProcessedCoverageRemove(cmd,expected,
                                NativeDirectory.EntriesForNames(topology,position,beforeRemaining),entry,beforeObservations,observations);
        NativeTrace.Concat(cmd.nativeInputs[0],stepBefore,read.after,NativeIO.State(io),[read],entryCalls);
        NativeTrace.Concat(cmd.nativeInputs[0],before,stepBefore,NativeIO.State(io),beforeCalls,[read]+entryCalls);
        ghost var nativePiece := [read]+entryCalls;
        assert forall j: nat | j < |beforePositions| :: beforePositions[j] < |beforeSteps| by {
          reveal Spec.DirectoryReadEvidence();
        }
        DirectoryPieceProof.Append(beforeSteps,beforeObservations,beforePositions,beforePieces,
                                   step,observations,positions,nativePiece);
        calls := beforeCalls+nativePiece;
        pieces := beforePieces+[nativePiece];
        cuts := beforeCuts+[|calls|];
        // The fragment helper preserves each exact call slice; no native receipt is summarized away.
        DirectoryTraceProof.AppendNativeCallFragments(beforePieces,beforeCalls,beforeCuts,nativePiece);
      }
    }
    if readErr == 0 {
      NativeEntries.Empty(topology,position);
      reveal NativeDirectory.EntryForName();
      NativeEntries.Membership(topology,position,expectedNames,BenchWorld.DirEntry(".",true,false));
      NativeEntries.Membership(topology,position,expectedNames,BenchWorld.DirEntry("..",true,false));
      CompleteDirectoryObservations(cmd,preFs,path,expected,before.status,io.statusCursor(),observations,statusCuts);
    } else {
      reveal Spec.DirectoryObservationRelation(), DirectoryStatusCuts();
    }
  }

  method ReadOpenedDirectoryCore(
    cmd: Schema.LsCmd, displayPath: BenchWorld.Path, path: BenchWorld.Path,
    handle: int, ghost opening: Spec.DirectoryTrace, io: BenchIO.IO)
    returns (observations: seq<Spec.EntryObservation>, readErr: int,
             output: BenchWorld.Bytes, errors: BenchWorld.Bytes, hadError: bool,
             directoryFailed: bool, ghost nativeTrace: Spec.DirectoryTrace)
    requires Spec.NativeCommandFields(cmd,io.fs()) && cmd.nativeInputs[0] == NativeIO.Inputs(io)
    requires Spec.BoundOpenDirectoryTrace(cmd,io.fs(),path,opening,true,0)
    requires opening.handle == handle && opening.openedHandles == io.directoryCapabilities()
    requires handle in io.directoryCapabilities()
    requires IOContract.DirectoryCapabilityReadCurrentFields(io.directoryTopology(),io.directoryCapabilities()[handle])
    requires io.directoryCapabilities()[handle].includeDots
    requires io.directoryCapabilities()[handle].remaining == IOContract.DirectoryCapabilityNamesFields(
                                                               io.directoryTopology(),io.directoryCapabilities()[handle].position,true)
    requires Native.TraceFields(cmd.nativeInputs[0],opening.openCalls[0].before,NativeIO.State(io),opening.nativeCalls)
    requires opening.nativeCalls == opening.openCalls+opening.statusCalls
    requires Spec.DirectoryExpectedEntries(opening,NativeDirectory.EntriesForNames(io.directoryTopology(),
                                                                                   io.directoryCapabilities()[handle].position,io.directoryCapabilities()[handle].remaining))
    modifies io.directoryStateRegion,io.statusObservationsRegion
    ensures NativeIO.Inputs(io) == old(NativeIO.Inputs(io))
    ensures io.dirHandles() == old(io.dirHandles()) && io.directoryOrigins() == old(io.directoryOrigins())
    ensures DirectoryListingSummary(cmd,displayPath,old(io.fs()),path,
                                    old(io.statusCursor()),io.statusCursor(),observations,readErr,output,errors,hadError,nativeTrace)
    ensures directoryFailed == Spec.DirectoryOperationFailed(nativeTrace,readErr)
    ensures io.directoryCapabilities() == opening.openCalls[0].before.context.capabilities
    ensures nativeTrace.DirectoryTrace? && nativeTrace.openedHandles == opening.openedHandles &&
            nativeTrace.handle == opening.handle && nativeTrace.openOk && nativeTrace.openErr == 0
    ensures Native.TraceFields(cmd.nativeInputs[0],opening.openCalls[0].before,NativeIO.State(io),nativeTrace.nativeCalls)
    ensures nativeTrace.openCalls == opening.openCalls && nativeTrace.statusCalls == opening.statusCalls
    ensures Spec.BoundOpenDirectoryTrace(cmd,old(io.fs()),path,nativeTrace,true,0)
    decreases *
  {
    hide *;
    reveal Spec.NativeCommandFields();
    ghost var preFs := io.fs();
    ghost var preStatus := io.statusCursor();
    ghost var before := NativeIO.State(io);
    assert opening.DirectoryTrace? && |opening.openCalls| == 1 by {
      reveal Spec.BoundOpenDirectoryTrace();
    }
    assert IOContract.LiveDirectoryTopologyFields(preFs,io.directoryTopology()) by {
      reveal IOContract.CwdContextFields();
    }
    assert io.directoryCapabilities()[handle].position in io.directoryTopology().nodes &&
           io.directoryCapabilities()[handle].remaining <=
           io.directoryTopology().nodes[io.directoryCapabilities()[handle].position].entries.Keys+{".",".."} by {
      reveal IOContract.DirectoryCapabilityReadCurrentFields(), IOContract.DirectoryCapabilityAnchorCurrentFields();
      reveal IOContract.DirectoryCapabilityNamesFields();
    }
    ghost var expected := NativeDirectory.EntriesForNames(io.directoryTopology(),
                                                          io.directoryCapabilities()[handle].position,io.directoryCapabilities()[handle].remaining);
    var rawObservations,stepsReadErr,steps,terminal,positions,readCalls,nativePieces,nativeCuts :=
      CollectDirectoryEntries(cmd,path,handle,io);
    readErr := stepsReadErr;
    ghost var beforeClose := NativeIO.State(io);
    var closeResult,closed := NativeIO.Close(handle,io);
    NativeResources.CloseFrame(cmd.nativeInputs[0],closed);
    NativeTrace.Single(cmd.nativeInputs[0],closed);
    NativeTrace.Concat(cmd.nativeInputs[0],before,beforeClose,NativeIO.State(io),readCalls+terminal.nativeCalls,[closed]);
    NativeTrace.Concat(cmd.nativeInputs[0],opening.openCalls[0].before,before,NativeIO.State(io),
                       opening.nativeCalls,readCalls+terminal.nativeCalls+[closed]);
    assert Native.TraceFields(cmd.nativeInputs[0],opening.openCalls[0].before,NativeIO.State(io),
                              opening.nativeCalls+(readCalls+terminal.nativeCalls+[closed]));
    var closeErr := IOContract.ResultErrno(closeResult);
    assert |terminal.nativeCalls| == 1 && terminal.nativeCalls[0].after == beforeClose by {
      reveal Spec.DirectoryReadStepFields(), Native.TraceFields();
    }
    assert Native.CallFields(cmd.nativeInputs[0],terminal.nativeCalls[0]) by {
      reveal Spec.DirectoryReadStepFields(), Spec.NativeCallsFields(), Native.TraceFields();
    }
    NativeTrace.Single(cmd.nativeInputs[0],terminal.nativeCalls[0]);
    assert terminal.nativeCalls == [terminal.nativeCalls[0]];
    NativeTrace.Concat(cmd.nativeInputs[0],terminal.nativeCalls[0].before,beforeClose,
                       NativeIO.State(io),terminal.nativeCalls,[closed]);
    assert terminal.nativeCalls+[closed] == [terminal.nativeCalls[0],closed];
    assert Native.TraceFields(cmd.nativeInputs[0],terminal.nativeCalls[0].before,
                              closed.after,[terminal.nativeCalls[0],closed]);
    assert Spec.NativeCommandFields(cmd,preFs) by { reveal Spec.NativeCommandFields(); }
    assert Spec.NativeCallsFields(cmd,preFs,[terminal.nativeCalls[0],closed]) by {
      reveal Spec.NativeCallsFields();
    }
    assert terminal.nativeCalls[0].action.ReadAction? &&
           terminal.nativeCalls[0].action.handle == handle &&
           (terminal.nativeCalls[0].action.readResult.Err? ||
            terminal.nativeCalls[0].action.readResult.v.DirectoryEnd?) &&
           IOContract.ResultErrno(terminal.nativeCalls[0].action.readResult) == readErr by {
      reveal Spec.DirectoryReadStepFields();
    }
    nativeTrace := Spec.DirectoryTrace(opening.openedHandles,handle,true,0,steps,terminal,
                                       io.directoryCapabilities(),closeResult.Ok?,closeErr,rawObservations,positions,
                                       opening.openCalls,opening.statusCalls,[closed],readCalls,
                                       opening.openCalls+opening.statusCalls+readCalls+terminal.nativeCalls+[closed],nativePieces,nativeCuts);
    assert io.directoryCapabilities() == opening.openCalls[0].before.context.capabilities by {
      reveal Spec.BoundOpenDirectoryTrace(), Spec.NativeCallsFields(), Native.TraceFields();
      reveal Native.CallFields(), IOContract.OpenDirAtCwdSpec();
      reveal IOContract.OpenDirFromCwdTargetContractFields();
    }
    assert nativeTrace.nativeCalls == opening.nativeCalls+readCalls+terminal.nativeCalls+[closed];
    assert nativeTrace.nativeCalls == opening.nativeCalls+(readCalls+terminal.nativeCalls+[closed]);
    assert Native.TraceFields(cmd.nativeInputs[0],opening.openCalls[0].before,
                              NativeIO.State(io),nativeTrace.nativeCalls);
    assert Spec.BoundOpenDirectoryTrace(cmd,preFs,path,nativeTrace,true,0) by {
      reveal Spec.BoundOpenDirectoryTrace();
    }
    PackageDirectoryCloseObservation(cmd,preFs,path,terminal.nativeCalls[0],closed,readErr,closeErr);
    assert Spec.NativeCallsFields(cmd,preFs,[closed]) by { reveal Spec.NativeCallsFields(); }
    assert Spec.NativeCallsFields(cmd,preFs,nativeTrace.nativeCalls) by {
      reveal Spec.NativeCallsFields(), Native.TraceFields();
    }
    assert closeResult.Ok? <==> closeErr == 0 by {
      reveal Native.CallFields(), IOContract.ContextOperationSpec(), IOContract.DirectoryOperationSpec();
      reveal IOContract.DirectoryResponseFields(), IOContract.DirectoryUnitResultFields();
      reveal IOContract.ResultErrno(), IOContract.IOErrorErrno();
    }
    assert Spec.DirectoryCallPieces(nativeTrace) by { reveal Spec.DirectoryCallPieces(); }
    assert Spec.ReadCloseDirectoryTrace(cmd,preFs,path,nativeTrace,readErr,closeErr) by {
      reveal Spec.ReadCloseDirectoryTrace();
    }
    assert Spec.DirectoryExpectedEntries(nativeTrace,expected) by { reveal Spec.DirectoryExpectedEntries(); }
    observations := SortEntriesCore(cmd, rawObservations);
    ghost var renderedOutputs: seq<BenchWorld.Bytes>;
    ghost var renderedOutputCuts: seq<nat>;
    ghost var renderedErrors: seq<BenchWorld.Bytes>;
    ghost var renderedErrorCuts: seq<nat>;
    var entryOutput: BenchWorld.Bytes;
    var entryErrors: BenchWorld.Bytes;
    entryOutput, entryErrors, hadError, renderedOutputs, renderedOutputCuts,
    renderedErrors, renderedErrorCuts := RenderObservationSequence(cmd, displayPath, observations);
    var ignoredOutput: BenchWorld.Bytes;
    var ignoredFailure: bool;
    ghost var ignoredFragments: seq<BenchWorld.Bytes>;
    ghost var ignoredCuts: seq<nat>;
    ignoredOutput, entryErrors, ignoredFailure, ignoredFragments, ignoredCuts,
    renderedErrors, renderedErrorCuts := RenderObservationSequence(cmd, displayPath, rawObservations);
    output := Spec.TotalLineSpec(cmd, rawObservations) + entryOutput;
    errors := entryErrors + (if readErr == 0 then [] else Spec.ReadDirectoryErrorMessageSpec(displayPath, readErr)) +
    Spec.CloseDirectoryErrorMessageSpec(displayPath, closeErr);
    directoryFailed := readErr != 0 || closeErr != 0;
    hadError := hadError || directoryFailed;
    assert directoryFailed == Spec.DirectoryOperationFailed(nativeTrace,readErr) by {
      reveal Spec.DirectoryOperationFailed();
    }
    assert DirectoryListingSummary(cmd, displayPath, preFs, path, preStatus, io.statusCursor(),
                                   observations, readErr, output, errors, hadError, nativeTrace) by {
      hide *;
      reveal DirectoryListingSummary();
    }
  }

  method OpenDirectoryHandleCore(cmd: Schema.LsCmd, path: BenchWorld.Path, io: BenchIO.IO)
    returns (openOk: bool, handle: int, openErr: int, ghost nativeTrace: Spec.DirectoryTrace)
    requires Spec.NativeCommandFields(cmd,io.fs())
    requires cmd.nativeInputs[0] == NativeIO.Inputs(io)
    modifies io.directoryStateRegion
    ensures NativeIO.Inputs(io) == old(NativeIO.Inputs(io))
    ensures io.dirHandles() == old(io.dirHandles()) && io.directoryOrigins() == old(io.directoryOrigins())
    ensures Spec.OpenDirectoryObservation(cmd,old(io.fs()),path,openOk,openErr)
    ensures Spec.BoundOpenDirectoryTrace(cmd,old(io.fs()),path,nativeTrace,openOk,openErr)
    ensures !openOk ==> Spec.FailedOpenDirectoryTrace(cmd,old(io.fs()),path,nativeTrace)
    ensures nativeTrace.DirectoryTrace? && nativeTrace.handle == handle &&
            nativeTrace.openedHandles == io.directoryCapabilities() &&
            nativeTrace.openOk == openOk && nativeTrace.openErr == openErr
    ensures nativeTrace.readSteps == [] && nativeTrace.raw == [] && nativeTrace.positions == [] &&
            nativeTrace.closed == io.directoryCapabilities() && !nativeTrace.closeOk && nativeTrace.closeErr == 0
    ensures Native.TraceFields(cmd.nativeInputs[0],old(NativeIO.State(io)),NativeIO.State(io),nativeTrace.nativeCalls)
    ensures nativeTrace.nativeCalls == nativeTrace.openCalls && nativeTrace.statusCalls == [] &&
            nativeTrace.readCalls == [] && nativeTrace.closeCalls == [] &&
            nativeTrace.nativePieces == [] && nativeTrace.nativeCuts == [0]
    ensures |nativeTrace.openCalls| == 1 && nativeTrace.openCalls[0].before == old(NativeIO.State(io)) &&
            nativeTrace.openCalls[0].after == NativeIO.State(io)
    ensures !openOk ==> io.directoryCapabilities() == old(io.directoryCapabilities()) && openErr > 0
    ensures openOk ==>
              openErr == 0 && handle in io.directoryCapabilities() &&
              handle !in old(io.directoryCapabilities()) &&
              io.directoryCapabilities() - {handle} == old(io.directoryCapabilities()) &&
              io.directoryCapabilities()[handle].anchorTopology == io.directoryTopology() &&
              io.directoryCapabilities()[handle].anchorFs == io.fs() &&
              io.directoryCapabilities()[handle].includeDots &&
              io.directoryCapabilities()[handle].remaining ==
              IOContract.DirectoryCapabilityNamesFields(io.directoryTopology(),io.directoryCapabilities()[handle].position,true) &&
              IOContract.DirectoryCapabilityReadCurrentFields(io.directoryTopology(),io.directoryCapabilities()[handle])
  {
    hide *;
    reveal Spec.NativeCommandFields();
    var result,call := NativeIO.Open(path,true,io);
    NativeResources.OpenFrame(cmd.nativeInputs[0],call);
    NativeTrace.Single(cmd.nativeInputs[0],call);
    openOk := result.Ok?;
    handle := IOContract.ResultValue(result,0);
    openErr := IOContract.ResultErrno(result);
    PackageOpenDirectoryObservation(cmd,io.fs(),path,call,openOk,openErr);
    nativeTrace := Spec.DirectoryTrace(io.directoryCapabilities(),handle,openOk,openErr,[],
                                       Spec.DirectoryReadStep(io.directoryCapabilities(),io.directoryCapabilities(),false,"",BenchWorld.UnknownDirentKind,0),
                                       io.directoryCapabilities(),false,0,[],[],[call],[],[],[],[call],[],[0]);
    BindOpenDirectoryTrace(cmd,io.fs(),path,nativeTrace);
    if openOk {
      reveal Native.CallFields(), IOContract.OpenDirAtCwdSpec(), IOContract.OpenDirFromCwdTargetContractFields();
    } else {
      reveal Spec.FailedOpenDirectoryTrace();
    }
  }

  method OpenedDirectoryStatusCore(cmd: Schema.LsCmd, path: BenchWorld.Path,
                                   handle: int, io: BenchIO.IO)
    returns (statusOk: bool, openedStatus: BenchWorld.FileStatus, statusErr: int, ghost call: Native.Call)
    requires Spec.NativeCommandFields(cmd,io.fs())
    requires cmd.nativeInputs[0] == NativeIO.Inputs(io)
    requires handle in io.directoryCapabilities()
    requires IOContract.DirectoryCapabilityAnchorCurrentFields(io.directoryTopology(),io.directoryCapabilities()[handle])
    modifies io.directoryStateRegion,io.statusObservationsRegion
    ensures NativeIO.Inputs(io) == old(NativeIO.Inputs(io))
    ensures call.before == old(NativeIO.State(io)) && call.after == NativeIO.State(io)
    ensures Native.CallFields(cmd.nativeInputs[0],call) && call.action.HandleStatusAction? && call.action.handle == handle
    ensures NativeObservation.StatusFields(call.action.statusResult,statusOk,openedStatus,statusErr)
    ensures Spec.OpenedDirectoryStatusObservation(cmd,old(io.fs()),path,old(io.statusCursor()),statusOk,openedStatus,statusErr)
    ensures io.statusCursor() == old(io.statusCursor())+1
    ensures io.cwdContext() == old(io.cwdContext()).(ordinal := old(io.cwdContext()).ordinal+1)
    ensures if statusOk then statusErr == 0 && openedStatus.kind == BenchWorld.DirectoryKind else statusErr > 0
  {
    hide *;
    reveal Spec.NativeCommandFields();
    var result;
    result,call := NativeIO.HandleStatus(handle,io);
    statusOk := result.Ok?;
    openedStatus := IOContract.ResultValue(result,BenchWorld.DEFAULT_FILE_STATUS);
    statusErr := IOContract.ResultErrno(result);
    assert NativeObservation.StatusFields(call.action.statusResult,statusOk,openedStatus,statusErr) by {
      reveal NativeObservation.StatusFields();
    }
    PackageOpenedDirectoryStatusObservation(cmd,io.fs(),path,call,statusOk,openedStatus,statusErr);
    assert io.statusCursor() == call.before.status+1 &&
           call.after.context == call.before.context.(ordinal := call.before.context.ordinal+1) by {
      reveal Native.CallFields(), IOContract.GetOpenDirectoryCapabilityStatusSpec(), IOContract.CwdContextReadStepFields();
    }
    assert if statusOk then statusErr == 0 && openedStatus.kind == BenchWorld.DirectoryKind else statusErr > 0 by {
      reveal Native.CallFields(), IOContract.GetOpenDirectoryCapabilityStatusSpec();
      reveal IOContract.ObservedOpenDirectoryCapabilityResultFields(), IOContract.GetOpenDirectoryCapabilityResultFields();
      reveal IOContract.ResultValue(), IOContract.ResultErrno();
      if statusOk {
        ghost var context := call.before.context;
        assert handle in context.capabilities;
        assert context.capabilities[handle].position in context.topology.nodes by {
          reveal IOContract.CwdContextFields(), IOContract.LiveDirectoryCapabilitiesFields();
        }
        ghost var node := context.topology.nodes[context.capabilities[handle].position];
        assert node.status.kind == BenchWorld.DirectoryKind &&
               IOContract.LiveRecordStatusFields(context.topology.objects,node.status) by {
          reveal IOContract.CwdContextFields(), IOContract.LiveDirectoryTopologyFields();
        }
        reveal IOContract.LiveRecordStatusFields(), IOContract.DirectoryStatusSameStructure();
      }
    }
  }

  method {:vcs_split_on_every_assert} ReadDirectoryCore(
    cmd: Schema.LsCmd,
    displayPath: BenchWorld.Path,
    path: BenchWorld.Path,
    io: BenchIO.IO
  ) returns (
      observations: seq<Spec.EntryObservation>,
      readErr: int,
      wasOpened: bool,
      output: BenchWorld.Bytes,
      errors: BenchWorld.Bytes,
      hadError: bool, directoryFailed: bool, ghost nativeTrace: Spec.DirectoryTrace
    )
    requires Spec.NativeCommandFields(cmd,io.fs())
    requires cmd.statusContext.BoundStatusObservations?
    requires io.dirHandles() == cmd.directoryHandles
    requires cmd.statusContext.observations == io.statusObservations()
    requires cmd.statusContext.failures == io.trustedNativeFailures()
    requires |cmd.nativeInputs| == 1 && cmd.nativeInputs[0] == NativeIO.Inputs(io)
    modifies io.directoryStateRegion, io.statusObservationsRegion
    ensures Spec.OpenDirectoryObservation(cmd,
                                          old(io.fs()), path, wasOpened, if wasOpened then 0 else readErr)
    ensures wasOpened ==> DirectoryListingSummary(
                cmd, displayPath, old(io.fs()), path,
                old(io.statusCursor()), io.statusCursor(),
                observations, readErr, output, errors, hadError, nativeTrace)
    ensures Spec.BoundOpenDirectoryTrace(cmd, old(io.fs()), path, nativeTrace, wasOpened, if wasOpened then 0 else readErr)
    ensures !wasOpened ==> Spec.FailedOpenDirectoryTrace(cmd, old(io.fs()), path, nativeTrace)
    ensures !wasOpened ==>
              observations == [] &&
              readErr > 0 &&
              output == [] &&
              errors == Spec.OpenDirectoryErrorMessageSpec(displayPath, readErr) &&
              hadError && io.statusCursor() == old(io.statusCursor())
    ensures directoryFailed == Spec.DirectoryOperationFailed(nativeTrace, readErr)
    ensures io.dirHandles() == cmd.directoryHandles
    ensures NativeIO.Inputs(io) == old(NativeIO.Inputs(io))
    ensures io.directoryCapabilities() == old(io.directoryCapabilities())
    ensures Native.TraceFields(cmd.nativeInputs[0],old(NativeIO.State(io)),NativeIO.State(io),nativeTrace.nativeCalls)
    decreases *
  {
    hide *;
    reveal Spec.NativeCommandFields();
    var openOk: bool;
    var handle: int;
    var openErr: int;
    openOk, handle, openErr, nativeTrace := OpenDirectoryHandleCore(cmd, path, io);
    wasOpened := openOk;
    if !openOk {
      observations := [];
      readErr := openErr;
      output := [];
      errors := Spec.OpenDirectoryErrorMessageSpec(displayPath, openErr);
      hadError := true;
      directoryFailed := true;
      assert directoryFailed == Spec.DirectoryOperationFailed(nativeTrace,readErr) by {
        reveal Spec.DirectoryOperationFailed();
      }
      return;
    }
    ghost var openedState := NativeIO.State(io);
    assert IOContract.LiveDirectoryTopologyFields(io.fs(),io.directoryTopology()) by {
      reveal IOContract.CwdContextFields();
    }
    assert io.directoryCapabilities()[handle].position in io.directoryTopology().nodes &&
           io.directoryCapabilities()[handle].remaining <=
           io.directoryTopology().nodes[io.directoryCapabilities()[handle].position].entries.Keys+{".",".."} by {
      reveal IOContract.DirectoryCapabilityReadCurrentFields(), IOContract.DirectoryCapabilityAnchorCurrentFields();
      reveal IOContract.DirectoryCapabilityNamesFields();
    }
    assert Spec.DirectoryExpectedEntries(nativeTrace,NativeDirectory.EntriesForNames(io.directoryTopology(),
                                                                                     io.directoryCapabilities()[handle].position,io.directoryCapabilities()[handle].remaining)) by {
      reveal Spec.DirectoryExpectedEntries();
    }
    observations, readErr, output, errors, hadError, directoryFailed, nativeTrace :=
      ReadOpenedDirectoryCore(cmd, displayPath, path, handle, nativeTrace, io);
  }

  ghost predicate RecursivePrefixSummary(
    cmd: Schema.LsCmd,
    fs: BenchWorld.FileSystem,
    displayPath: BenchWorld.Path,
    ancestors: set<BenchWorld.HostInodeKey>,
    observations: seq<Spec.EntryObservation>,
    listing: BenchWorld.Bytes,
    listingErrors: BenchWorld.Bytes,
    listingHadError: bool,
    i: nat,
    children: map<nat, Spec.RecursiveWitness>,
    cycles: set<nat>,
    output: BenchWorld.Bytes,
    errors: BenchWorld.Bytes,
    hadError: bool
  )
  {
    i <= |observations| &&
    (forall j: nat :: j in children ==> j < i) &&
    (forall j: nat :: j in cycles ==> j < i) &&
    cycles <= children.Keys &&
    (forall j: nat :: j < i ==>
                        (j in children <==> Spec.RecursiveEntryEligible(observations[j])) &&
                        (j in cycles <==> j in children && children[j].cycle)) &&
    (forall j: nat :: j in children ==>
                        j < |observations| &&
                        RecursiveDirectorySummary(
                          cmd, fs,
                          Spec.ChildDisplayPath(displayPath, observations[j].displayName),
                          observations[j].accessPath,
                          ancestors, children[j])) &&
    output == Spec.DirectoryHeaderSpec(displayPath) + listing +
    RecursiveChildOutputPrefixCore(observations, children, i) &&
    errors == listingErrors + RecursiveChildErrorPrefixCore(
      displayPath, observations, children, cycles, i) &&
    hadError ==
    (listingHadError ||
     exists j: nat :: j in children && children[j].hadError)
  }

  lemma RecursivePrefixRanges(
    cmd: Schema.LsCmd, fs: BenchWorld.FileSystem,
    displayPath: BenchWorld.Path, ancestors: set<BenchWorld.HostInodeKey>,
    observations: seq<Spec.EntryObservation>, listing: BenchWorld.Bytes,
    listingErrors: BenchWorld.Bytes, listingHadError: bool, i: nat,
    children: map<nat, Spec.RecursiveWitness>, cycles: set<nat>,
    output: BenchWorld.Bytes, errors: BenchWorld.Bytes, hadError: bool
  )
    requires RecursivePrefixSummary(
               cmd, fs, displayPath, ancestors, observations, listing,
               listingErrors, listingHadError, i, children, cycles,
               output, errors, hadError)
    ensures forall j: nat :: j in children ==> j < i
    ensures forall j: nat :: j in cycles ==> j < i
  {
    reveal RecursivePrefixSummary(
           cmd, fs, displayPath, ancestors, observations, listing,
           listingErrors, listingHadError, i, children, cycles,
           output, errors, hadError);
  }

  lemma RecursivePrefixComplete(
    cmd: Schema.LsCmd, fs: BenchWorld.FileSystem,
    displayPath: BenchWorld.Path, accessPath: BenchWorld.Path,
    ancestors: set<BenchWorld.HostInodeKey>, tree: Spec.RecursiveWitness,
    statusCuts: seq<nat>
  )
    requires DirectoryListingSummary(
               cmd, displayPath, fs, accessPath, tree.listingFirstStatus,
               tree.listingAfterStatus,
               tree.observations, tree.readErr,
               tree.listingOutput, tree.listingErrors, tree.listingHadError, tree.nativeTrace)
    requires cmd.statusContext.BoundStatusObservations?
    requires Spec.RecursiveNativeDirectoryTrace(cmd, fs, accessPath, tree)
    requires tree.openOk && tree.openErr == 0 && tree.statusOk &&
             tree.statusErr == 0 && !tree.cycle
    requires tree.openedStatus.hostKey !in ancestors
    requires tree.listingFirstStatus == tree.firstStatus + 1
    requires tree.openedStatus.kind == BenchWorld.DirectoryKind
    requires Spec.RecursiveNativeCallsFields(cmd,fs,tree)
    requires Spec.OpenDirectoryObservation(cmd, fs, accessPath, true, 0)
    requires Spec.OpenedDirectoryStatusObservation(
               cmd, fs, accessPath, tree.firstStatus, true, tree.openedStatus, 0)
    requires |statusCuts| == |tree.observations| + 1
    requires statusCuts[0] == tree.listingAfterStatus
    requires statusCuts[|tree.observations|] == tree.afterStatus
    requires forall i: nat | i < |tree.observations| ::
               (if i in tree.children then
                  tree.children[i].firstStatus == statusCuts[i] &&
                  tree.children[i].afterStatus == statusCuts[i + 1]
                else statusCuts[i] == statusCuts[i + 1])
    requires RecursivePrefixSummary(
               cmd, fs, displayPath, ancestors + {tree.openedStatus.hostKey},
               tree.observations, tree.listingOutput,
               tree.listingErrors, tree.listingHadError, |tree.observations|,
               tree.children, tree.cycles, tree.output, tree.errors, tree.hadError)
    ensures RecursiveDirectorySummary(
              cmd, fs, displayPath, accessPath, ancestors, tree)
  {
    assert Spec.OpenDirectoryObservation(cmd, fs, accessPath, true, 0);
    hide *;
    reveal RecursivePrefixSummary(
           cmd, fs, displayPath, ancestors + {tree.openedStatus.hostKey},
           tree.observations, tree.listingOutput,
           tree.listingErrors, tree.listingHadError, |tree.observations|,
           tree.children, tree.cycles, tree.output, tree.errors, tree.hadError);
    reveal RecursiveDirectorySummary();
  }

  ghost opaque predicate StatusCutsPrefix(
    cuts: seq<nat>, children: map<nat, Spec.RecursiveWitness>, processed: nat
  )
  {
    |cuts| == processed + 1 &&
    forall j: nat | j < processed ::
      (if j in children then
         children[j].firstStatus == cuts[j] &&
         children[j].afterStatus == cuts[j + 1]
       else cuts[j] == cuts[j + 1])
  }

  lemma StatusCutsSnoc(
    beforeCuts: seq<nat>, beforeChildren: map<nat, Spec.RecursiveWitness>,
    afterChildren: map<nat, Spec.RecursiveWitness>, i: nat,
    afterStatus: nat, addedChild: bool
  )
    requires StatusCutsPrefix(beforeCuts, beforeChildren, i)
    requires |beforeCuts| == i + 1
    requires i !in beforeChildren
    requires if addedChild then
               i in afterChildren &&
               afterChildren == beforeChildren[i := afterChildren[i]] &&
               afterChildren[i].firstStatus == beforeCuts[i] &&
               afterChildren[i].afterStatus == afterStatus
             else afterChildren == beforeChildren && afterStatus == beforeCuts[i]
    ensures StatusCutsPrefix(beforeCuts + [afterStatus], afterChildren, i + 1)
  {
    reveal StatusCutsPrefix();
    forall j: nat | j < i + 1
      ensures (if j in afterChildren then
                 afterChildren[j].firstStatus == (beforeCuts + [afterStatus])[j] &&
                 afterChildren[j].afterStatus == (beforeCuts + [afterStatus])[j + 1]
               else (beforeCuts + [afterStatus])[j] ==
                    (beforeCuts + [afterStatus])[j + 1])
    {
      if j < i {
        assert j in afterChildren <==> j in beforeChildren;
        if j in afterChildren {
          assert afterChildren[j] == beforeChildren[j];
        }
        assert (beforeCuts + [afterStatus])[j] == beforeCuts[j];
        assert (beforeCuts + [afterStatus])[j + 1] == beforeCuts[j + 1];
      } else {
        assert j == i;
        assert (beforeCuts + [afterStatus])[j] == beforeCuts[i];
        assert (beforeCuts + [afterStatus])[j + 1] == afterStatus;
      }
    }
  }

  lemma RecursiveOutputPrefixAgreement(
    observations: seq<Spec.EntryObservation>,
    left: map<nat, Spec.RecursiveWitness>,
    right: map<nat, Spec.RecursiveWitness>,
    processed: nat
  )
    requires processed <= |observations|
    requires forall k: nat :: k < processed ==>
                                (k in left <==> k in right) &&
                                (k in left ==> left[k] == right[k])
    ensures RecursiveChildOutputPrefixCore(observations, left, processed) ==
            RecursiveChildOutputPrefixCore(observations, right, processed)
    decreases processed
  {
    if processed > 0 {
      RecursiveOutputPrefixAgreement(observations, left, right, processed - 1);
      reveal RecursiveChildOutputPrefixCore();
    }
  }

  lemma RecursiveErrorPrefixAgreement(
    displayPath: BenchWorld.Path,
    observations: seq<Spec.EntryObservation>,
    leftChildren: map<nat, Spec.RecursiveWitness>, leftCycles: set<nat>,
    rightChildren: map<nat, Spec.RecursiveWitness>, rightCycles: set<nat>,
    processed: nat
  )
    requires processed <= |observations|
    requires forall k: nat :: k < processed ==>
                                (k in leftCycles <==> k in rightCycles) &&
                                (k in leftChildren <==> k in rightChildren) &&
                                (k in leftChildren ==> leftChildren[k].errors == rightChildren[k].errors)
    ensures RecursiveChildErrorPrefixCore(
              displayPath, observations, leftChildren, leftCycles, processed) ==
            RecursiveChildErrorPrefixCore(
              displayPath, observations, rightChildren, rightCycles, processed)
    decreases processed
  {
    if processed > 0 {
      RecursiveErrorPrefixAgreement(
        displayPath, observations, leftChildren, leftCycles,
        rightChildren, rightCycles, processed - 1);
      reveal RecursiveChildErrorPrefixCore();
    }
  }

  lemma RecursiveOutputSnoc(
    displayPath: BenchWorld.Path, listing: BenchWorld.Bytes,
    observations: seq<Spec.EntryObservation>,
    beforeChildren: map<nat, Spec.RecursiveWitness>,
    afterChildren: map<nat, Spec.RecursiveWitness>, i: nat,
    beforeOutput: BenchWorld.Bytes, piece: BenchWorld.Bytes
  )
    requires i < |observations|
    requires beforeOutput == Spec.DirectoryHeaderSpec(displayPath) + listing +
                             RecursiveChildOutputPrefixCore(observations, beforeChildren, i)
    requires afterChildren == beforeChildren ||
             (i in afterChildren && afterChildren == beforeChildren[i := afterChildren[i]])
    requires piece ==
             (if i in afterChildren && Spec.RecursiveNodeListed(afterChildren[i])
              then "\n" + afterChildren[i].output else [])
    ensures beforeOutput + piece == Spec.DirectoryHeaderSpec(displayPath) + listing +
                                    RecursiveChildOutputPrefixCore(observations, afterChildren, i + 1)
  {
    assert forall k: nat :: k < i ==>
                              (k in beforeChildren <==> k in afterChildren) &&
                              (k in beforeChildren ==> beforeChildren[k] == afterChildren[k]) by {
      forall k: nat | k < i
        ensures (k in beforeChildren <==> k in afterChildren) &&
                (k in beforeChildren ==> beforeChildren[k] == afterChildren[k])
      {
        assert k != i;
      }
    }
    RecursiveOutputPrefixAgreement(observations, beforeChildren, afterChildren, i);
    reveal RecursiveChildOutputPrefixCore();
  }

  lemma RecursiveErrorSnoc(
    displayPath: BenchWorld.Path, listingErrors: BenchWorld.Bytes,
    observations: seq<Spec.EntryObservation>,
    beforeChildren: map<nat, Spec.RecursiveWitness>, beforeCycles: set<nat>,
    afterChildren: map<nat, Spec.RecursiveWitness>, afterCycles: set<nat>, i: nat,
    beforeErrors: BenchWorld.Bytes, piece: BenchWorld.Bytes
  )
    requires i < |observations|
    requires beforeErrors == listingErrors + RecursiveChildErrorPrefixCore(
                               displayPath, observations, beforeChildren, beforeCycles, i)
    requires afterChildren == beforeChildren ||
             (i in afterChildren && afterChildren == beforeChildren[i := afterChildren[i]])
    requires afterCycles == beforeCycles || afterCycles == beforeCycles + {i}
    requires piece ==
             (if i in afterCycles then
                Spec.RecursiveCycleMessageSpec(
                  Spec.ChildDisplayPath(displayPath, observations[i].displayName))
              else if i in afterChildren then afterChildren[i].errors else [])
    ensures beforeErrors + piece == listingErrors + RecursiveChildErrorPrefixCore(
                                      displayPath, observations, afterChildren, afterCycles, i + 1)
  {
    hide *;
    assert Spec.RecursiveCycleMessageSpec(
        Spec.ChildDisplayPath(displayPath, observations[i].displayName)) ==
           Spec.RecursiveCycleMessageSpec(
             Spec.ChildDisplayPath(displayPath, observations[i].displayName));
    assert forall k: nat :: k < i ==>
                              (k in beforeCycles <==> k in afterCycles) &&
                              (k in beforeChildren <==> k in afterChildren) &&
                              (k in beforeChildren ==> beforeChildren[k].errors == afterChildren[k].errors) by {
      forall k: nat | k < i
        ensures (k in beforeCycles <==> k in afterCycles) &&
                (k in beforeChildren <==> k in afterChildren) &&
                (k in beforeChildren ==> beforeChildren[k].errors == afterChildren[k].errors)
      {
        assert k != i;
      }
    }
    RecursiveErrorPrefixAgreement(
      displayPath, observations, beforeChildren, beforeCycles,
      afterChildren, afterCycles, i);
    reveal RecursiveChildErrorPrefixCore();
  }

  lemma FailedChildAfterUpdate(
    before: map<nat, Spec.RecursiveWitness>,
    index: nat,
    child: Spec.RecursiveWitness
  )
    requires index !in before
    ensures (exists j: nat {:trigger before[index := child][j]} ::
               j in before[index := child] && before[index := child][j].hadError) <==>
            (child.hadError || exists j: nat {:trigger before[j]} :: j in before && before[j].hadError)
  {
    assert (exists j: nat {:trigger before[index := child][j]} ::
              j in before[index := child] && before[index := child][j].hadError) ==>
        (child.hadError || exists j: nat {:trigger before[j]} ::
           j in before && before[j].hadError) by {
      if exists j: nat {:trigger before[index := child][j]} ::
          j in before[index := child] && before[index := child][j].hadError {
        var j: nat :| j in before[index := child] && before[index := child][j].hadError;
        if j != index {
          assert j in before;
          assert before[index := child][j] == before[j];
          assert exists k: nat {:trigger before[k]} :: k in before && before[k].hadError;
        }
      }
    }
    assert (child.hadError || exists j: nat {:trigger before[j]} ::
              j in before && before[j].hadError) ==>
        (exists j: nat {:trigger before[index := child][j]} ::
           j in before[index := child] && before[index := child][j].hadError) by {
      if child.hadError {
        assert index in before[index := child];
      } else if exists j: nat {:trigger before[j]} :: j in before && before[j].hadError {
        var j: nat :| j in before && before[j].hadError;
        assert j != index;
        assert before[index := child][j] == before[j];
      }
    }
  }

  lemma CompleteRecursiveChildUpdate(
    cmd: Schema.LsCmd, fs: BenchWorld.FileSystem, displayPath: BenchWorld.Path,
    childAncestors: set<BenchWorld.HostInodeKey>, observations: seq<Spec.EntryObservation>,
    beforeChildren: map<nat, Spec.RecursiveWitness>, beforeCycles: set<nat>,
    children: map<nat, Spec.RecursiveWitness>, cycles: set<nat>, i: nat
  )
    requires i < |observations|
    requires forall j: nat :: j in beforeChildren ==> j < i
    requires beforeCycles <= beforeChildren.Keys
    requires forall j: nat | j < i ::
               (j in beforeChildren <==> Spec.RecursiveEntryEligible(observations[j])) &&
               (j in beforeCycles <==> j in beforeChildren && beforeChildren[j].cycle)
    requires forall j: nat :: j in beforeChildren ==>
                                j < |observations| && RecursiveDirectorySummary(cmd, fs,
                                                                                Spec.ChildDisplayPath(displayPath, observations[j].displayName),
                                                                                observations[j].accessPath, childAncestors, beforeChildren[j])
    requires if Spec.RecursiveEntryEligible(observations[i]) then
               i in children && children == beforeChildren[i := children[i]] &&
               RecursiveDirectorySummary(cmd, fs,
                                         Spec.ChildDisplayPath(displayPath, observations[i].displayName),
                                         observations[i].accessPath, childAncestors, children[i])
             else children == beforeChildren
    requires cycles == (if i in children && children[i].cycle then beforeCycles + {i} else beforeCycles)
    ensures children == beforeChildren || (i in children && children == beforeChildren[i := children[i]])
    ensures cycles == beforeCycles || cycles == beforeCycles + {i}
    ensures i !in beforeChildren
    ensures children.Keys <= beforeChildren.Keys + {i}
    ensures cycles <= beforeCycles + {i}
    ensures forall j: nat :: j in children ==> j < i + 1
    ensures forall j: nat :: j in cycles ==> j < i + 1
    ensures cycles <= children.Keys
    ensures forall j: nat | j < i + 1 ::
              (j in children <==> Spec.RecursiveEntryEligible(observations[j])) &&
              (j in cycles <==> j in children && children[j].cycle)
    ensures forall j: nat :: j in children ==>
                               j < |observations| && RecursiveDirectorySummary(cmd, fs,
                                                                               Spec.ChildDisplayPath(displayPath, observations[j].displayName),
                                                                               observations[j].accessPath, childAncestors, children[j])
  {
    hide *;
    assert children == beforeChildren ||
           (i in children && children == beforeChildren[i := children[i]]);
    assert cycles == beforeCycles || cycles == beforeCycles + {i};
    assert i !in beforeChildren;
    assert children.Keys <= beforeChildren.Keys + {i};
    assert cycles <= beforeCycles + {i};
    assert forall j: nat :: j in children ==> j < i + 1 by {
      forall j: nat | j in children
        ensures j < i + 1
      {
        if j != i {
          assert j in beforeChildren.Keys;
          assert j < i;
        }
      }
    }
    assert forall j: nat :: j in cycles ==> j < i + 1 by {
      forall j: nat | j in cycles
        ensures j < i + 1
      {
        if j != i {
          assert j in beforeCycles;
          assert j < i;
        }
      }
    }
    assert cycles <= children.Keys;
    assert forall j: nat :: j < i + 1 ==>
                              (j in children <==> Spec.RecursiveEntryEligible(observations[j])) &&
                              (j in cycles <==> j in children && children[j].cycle) by {
      forall j: nat | j < i + 1
        ensures
          (j in children <==> Spec.RecursiveEntryEligible(observations[j])) &&
          (j in cycles <==> j in children && children[j].cycle)
      {
        if j < i {
          assert j in children <==> j in beforeChildren;
          assert j in cycles <==> j in beforeCycles;
        } else {
          assert j == i;
        }
      }
    }
    assert forall j: nat :: j in children ==>
                              j < |observations| &&
                              RecursiveDirectorySummary(
                                cmd, fs,
                                Spec.ChildDisplayPath(displayPath, observations[j].displayName),
                                observations[j].accessPath,
                                childAncestors, children[j]) by {
      forall j: nat | j in children
        ensures j < |observations| &&
                RecursiveDirectorySummary(
                  cmd, fs,
                  Spec.ChildDisplayPath(displayPath, observations[j].displayName),
                  observations[j].accessPath,
                  childAncestors, children[j])
      {
        if j != i {
          assert j in beforeChildren;
        }
      }
    }
  }

  lemma CompleteRecursivePrefixStep(
    cmd: Schema.LsCmd, fs: BenchWorld.FileSystem, displayPath: BenchWorld.Path,
    ancestors: set<BenchWorld.HostInodeKey>, observations: seq<Spec.EntryObservation>,
    listing: BenchWorld.Bytes, listingErrors: BenchWorld.Bytes, listingHadError: bool,
    i: nat, beforeChildren: map<nat, Spec.RecursiveWitness>, beforeCycles: set<nat>,
    children: map<nat, Spec.RecursiveWitness>, cycles: set<nat>,
    beforeOutput: BenchWorld.Bytes, beforeErrors: BenchWorld.Bytes, beforeHadError: bool,
    outputPiece: BenchWorld.Bytes, errorPiece: BenchWorld.Bytes, stepFailed: bool,
    beforeHasCycle: bool, afterHasCycle: bool
  )
    requires i < |observations|
    requires RecursivePrefixSummary(cmd,fs,displayPath,ancestors,observations,
                                    listing,listingErrors,listingHadError,i,beforeChildren,beforeCycles,
                                    beforeOutput,beforeErrors,beforeHadError)
    requires beforeHasCycle == (beforeCycles != {} ||
                                exists j: nat :: j in beforeChildren && Spec.RecursiveHasCycle(beforeChildren[j]))
    requires if Spec.RecursiveEntryEligible(observations[i]) then
               i in children && children == beforeChildren[i := children[i]] &&
               RecursiveDirectorySummary(cmd,fs,
                                         Spec.ChildDisplayPath(displayPath,observations[i].displayName),
                                         observations[i].accessPath,ancestors,children[i]) &&
               outputPiece == (if Spec.RecursiveNodeListed(children[i]) then "\n"+children[i].output else []) &&
               errorPiece == children[i].errors && stepFailed == children[i].hadError &&
               cycles == (if children[i].cycle then beforeCycles+{i} else beforeCycles) &&
               afterHasCycle == (beforeHasCycle || Spec.RecursiveHasCycle(children[i]))
             else children == beforeChildren && cycles == beforeCycles &&
                  outputPiece == [] && errorPiece == [] && !stepFailed && afterHasCycle == beforeHasCycle
    ensures RecursivePrefixSummary(cmd,fs,displayPath,ancestors,observations,
                                   listing,listingErrors,listingHadError,i+1,children,cycles,
                                   beforeOutput+outputPiece,beforeErrors+errorPiece,beforeHadError || stepFailed)
    ensures afterHasCycle == (cycles != {} ||
                              exists j: nat :: j in children && Spec.RecursiveHasCycle(children[j]))
  {
    hide *;
    reveal RecursivePrefixSummary(cmd,fs,displayPath,ancestors,observations,
           listing,listingErrors,listingHadError,i,beforeChildren,beforeCycles,
           beforeOutput,beforeErrors,beforeHadError);
    CompleteRecursiveChildUpdate(cmd,fs,displayPath,ancestors,observations,
                                 beforeChildren,beforeCycles,children,cycles,i);
    assert outputPiece ==
           (if i in children && Spec.RecursiveNodeListed(children[i]) then "\n"+children[i].output else []);
    RecursiveOutputSnoc(displayPath,listing,observations,beforeChildren,children,i,beforeOutput,outputPiece);
    if i in cycles {
      assert i in children;
      assert children[i].errors == Spec.RecursiveCycleMessageSpec(
                                     Spec.ChildDisplayPath(displayPath,observations[i].displayName)) by {
        reveal RecursiveDirectorySummary(cmd,fs,
               Spec.ChildDisplayPath(displayPath,observations[i].displayName),
               observations[i].accessPath,ancestors,children[i]);
      }
    }
    assert errorPiece ==
           (if i in cycles then Spec.RecursiveCycleMessageSpec(
                                  Spec.ChildDisplayPath(displayPath,observations[i].displayName))
            else if i in children then children[i].errors else []);
    RecursiveErrorSnoc(displayPath,listingErrors,observations,beforeChildren,beforeCycles,
                       children,cycles,i,beforeErrors,errorPiece);
    assert (beforeHadError || stepFailed) ==
           (listingHadError || exists j: nat :: j in children && children[j].hadError) by {
      if Spec.RecursiveEntryEligible(observations[i]) {
        FailedChildAfterUpdate(beforeChildren,i,children[i]);
      } else {
        assert children == beforeChildren && !stepFailed;
      }
    }
    if Spec.RecursiveEntryEligible(observations[i]) {
      assert (exists j: nat {:trigger children[j]} ::
                j in children && Spec.RecursiveHasCycle(children[j])) <==>
             (Spec.RecursiveHasCycle(children[i]) ||
              exists j: nat {:trigger beforeChildren[j]} ::
                j in beforeChildren && Spec.RecursiveHasCycle(beforeChildren[j])) by {
        if exists j: nat {:trigger children[j]} ::
            j in children && Spec.RecursiveHasCycle(children[j]) {
          var j: nat :| j in children && Spec.RecursiveHasCycle(children[j]);
          if j != i {
            assert j in beforeChildren;
            assert children[j] == beforeChildren[j];
            assert exists k: nat {:trigger beforeChildren[k]} ::
                k in beforeChildren && Spec.RecursiveHasCycle(beforeChildren[k]);
          }
        }
        if Spec.RecursiveHasCycle(children[i]) {
          assert exists j: nat {:trigger children[j]} ::
              j in children && Spec.RecursiveHasCycle(children[j]);
        } else if exists j: nat {:trigger beforeChildren[j]} ::
            j in beforeChildren && Spec.RecursiveHasCycle(beforeChildren[j]) {
          var j: nat :| j in beforeChildren && Spec.RecursiveHasCycle(beforeChildren[j]);
          assert j != i;
          assert j in children && children[j] == beforeChildren[j];
          assert exists k: nat {:trigger children[k]} ::
              k in children && Spec.RecursiveHasCycle(children[k]);
        }
      }
      assert children[i].cycle ==> Spec.RecursiveHasCycle(children[i]) by {
        reveal Spec.RecursiveHasCycle(children[i]);
      }
      assert (cycles != {}) == (beforeCycles != {} || children[i].cycle);
    }
    reveal RecursivePrefixSummary(cmd,fs,displayPath,ancestors,observations,
           listing,listingErrors,listingHadError,i+1,children,cycles,
           beforeOutput+outputPiece,beforeErrors+errorPiece,beforeHadError || stepFailed);
  }

  lemma CompleteRecursiveClose(
    inputs: Native.Inputs, before: Native.State, openedState: Native.State,
    closed: Native.Call, prefix: seq<Native.Call>, handle: int
  )
    requires Native.CallFields(inputs,closed)
    requires closed.action.CloseAction? && closed.action.handle == handle
    requires Native.TraceFields(inputs,before,closed.before,prefix)
    requires closed.before.context.capabilities == openedState.context.capabilities
    requires openedState.context.capabilities - {handle} == before.context.capabilities
    ensures Native.TraceFields(inputs,before,closed.after,prefix+[closed])
    ensures closed.after.context.topology == closed.before.context.topology
    ensures closed.after.context.position == closed.before.context.position
    ensures closed.after.context.hint == closed.before.context.hint
    ensures closed.after.context.legacyHandles == closed.before.context.legacyHandles
    ensures closed.after.context.legacyOrigins == closed.before.context.legacyOrigins
    ensures closed.after.context.capabilities == before.context.capabilities
    ensures closed.action.closeResult.Ok? <==> IOContract.ResultErrno(closed.action.closeResult) == 0
  {
    hide *;
    NativeResources.CloseFrame(inputs,closed);
    NativeTrace.Single(inputs,closed);
    NativeTrace.Concat(inputs,before,closed.before,closed.after,prefix,[closed]);
    assert closed.action.closeResult.Ok? <==> IOContract.ResultErrno(closed.action.closeResult) == 0 by {
      reveal Native.CallFields(), IOContract.DirectoryUnitResultFields();
      reveal IOContract.ResultErrno(), IOContract.IOErrorErrno();
    }
  }

  method {:vcs_split_on_every_assert} WalkDirectoryRecursive(
    cmd: Schema.LsCmd,
    displayPath: BenchWorld.Path,
    accessPath: BenchWorld.Path,
    ancestors: set<BenchWorld.HostInodeKey>,
    io: BenchIO.IO
  ) returns (
      wasOpened: bool,
      wasListed: bool,
      output: BenchWorld.Bytes,
      errors: BenchWorld.Bytes,
      hadError: bool,
      hasCycle: bool,
      directoryFailed: bool,
      ghost tree: Spec.RecursiveWitness
    )
    requires Spec.NativeCommandFields(cmd,io.fs())
    requires cmd.statusContext.BoundStatusObservations?
    requires io.dirHandles() == cmd.directoryHandles
    requires cmd.statusContext.observations == io.statusObservations()
    requires cmd.statusContext.failures == io.trustedNativeFailures()
    requires |cmd.nativeInputs| == 1 && cmd.nativeInputs[0] == NativeIO.Inputs(io)
    modifies io.directoryStateRegion, io.statusObservationsRegion
    ensures RecursiveDirectorySummary(
              cmd, old(io.fs()), displayPath, accessPath, ancestors, tree)
    ensures directoryFailed == Spec.RecursiveRootFailed(tree)
    ensures wasOpened == tree.openOk
    ensures Spec.RecursiveNativeDirectoryTrace(cmd, old(io.fs()), accessPath, tree)
    ensures Spec.OpenDirectoryObservation(cmd,
                                          old(io.fs()), accessPath, wasOpened, tree.openErr)
    ensures !wasOpened ==>
              errors == Spec.OpenDirectoryErrorMessageSpec(
                displayPath, tree.openErr) &&
              hadError && io.statusCursor() == old(io.statusCursor())
    ensures !wasOpened ==> !hasCycle
    ensures hasCycle == Spec.RecursiveHasCycle(tree)
    ensures wasListed == Spec.RecursiveNodeListed(tree)
    ensures output == tree.output && errors == tree.errors && hadError == tree.hadError
    ensures tree.firstStatus == old(io.statusCursor())
    ensures tree.afterStatus == io.statusCursor()
    ensures io.dirHandles() == cmd.directoryHandles
    ensures NativeIO.Inputs(io) == old(NativeIO.Inputs(io))
    ensures io.directoryCapabilities() == old(io.directoryCapabilities())
    ensures Native.TraceFields(cmd.nativeInputs[0],old(NativeIO.State(io)),NativeIO.State(io),tree.nativeCalls)
    decreases *
  {
    hide *;
    reveal Spec.NativeCommandFields();
    reveal Spec.RecursiveHasCycle(), Spec.RecursiveNodeListed();
    reveal Spec.RecursiveRootFailed(), Spec.DirectoryOperationFailed();
    ghost var before := NativeIO.State(io);
    ghost var preFs := io.fs();
    ghost var preStatus := io.statusCursor();
    var openOk: bool;
    var handle: int;
    var openErr: int;
    ghost var nativeTrace: Spec.DirectoryTrace;
    openOk, handle, openErr, nativeTrace := OpenDirectoryHandleCore(cmd, accessPath, io);
    wasOpened := openOk;
    ghost var openedState := NativeIO.State(io);
    if !openOk {
      wasListed := false;
      output := [];
      errors := Spec.OpenDirectoryErrorMessageSpec(displayPath, openErr);
      hadError := true;
      hasCycle := false;
      directoryFailed := true;
      tree := Spec.RecursiveWitness(
        [], 0, [], [], false, map[], {}, output, errors, hadError,
        false, openErr, false, BenchWorld.DEFAULT_FILE_STATUS, 0, false,
        preStatus, preStatus, preStatus, preStatus, nativeTrace,[],nativeTrace.nativeCalls,[],[0]);
      assert Spec.RecursiveNativeDirectoryTrace(cmd, preFs, accessPath, tree) by {
        hide *;
        reveal Spec.RecursiveNativeDirectoryTrace(), Spec.FailedOpenDirectoryTrace(), Spec.BoundOpenDirectoryTrace();
        reveal Spec.NativeCallsFields(), Native.TraceFields();
      }
      assert RecursiveDirectorySummary(
          cmd, preFs, displayPath, accessPath, ancestors, tree) by {
        reveal RecursiveDirectorySummary(), Spec.RecursiveNativeCallsFields(), Spec.NativeCallsFields();
      }
      return;
    }
    var statusOk: bool;
    var openedStatus: BenchWorld.FileStatus;
    var statusErr: int;
    ghost var statusCall: Native.Call;
    assert IOContract.DirectoryCapabilityAnchorCurrentFields(io.directoryTopology(),io.directoryCapabilities()[handle]) by {
      reveal IOContract.DirectoryCapabilityReadCurrentFields();
    }
    statusOk,openedStatus,statusErr,statusCall := OpenedDirectoryStatusCore(cmd,accessPath,handle,io);
    assert io.cwdContext().legacyHandles == openedState.context.legacyHandles;
    assert io.directoryCapabilities() == openedState.context.capabilities;
    NativeTrace.Single(cmd.nativeInputs[0],statusCall);
    assert Spec.NativeCallsFields(cmd,preFs,[statusCall]) by {
      reveal Spec.NativeCallsFields();
    }
    NativeTrace.Concat(cmd.nativeInputs[0],before,statusCall.before,NativeIO.State(io),nativeTrace.nativeCalls,[statusCall]);
    nativeTrace := nativeTrace.(statusCalls := [statusCall],nativeCalls := nativeTrace.nativeCalls+[statusCall]);
    assert Spec.BoundOpenDirectoryTrace(cmd,preFs,accessPath,nativeTrace,true,0) by {
      reveal Spec.BoundOpenDirectoryTrace();
    }
    if !statusOk {
      wasListed := false;
      var closeResult,closed := NativeIO.Close(handle,io);
      CompleteRecursiveClose(cmd.nativeInputs[0],before,openedState,closed,nativeTrace.nativeCalls,handle);
      var closeFailed := closeResult.Err?;
      nativeTrace := nativeTrace.(closed := io.directoryCapabilities(),closeOk := closeResult.Ok?,
      closeErr := IOContract.ResultErrno(closeResult),closeCalls := [closed],
      nativeCalls := nativeTrace.nativeCalls+[closed]);
      output := [];
      errors := Spec.DirectoryIdentityErrorMessageSpec(displayPath, statusErr);
      hadError := !statusOk || closeFailed;
      hasCycle := false;
      directoryFailed := true;
      tree := Spec.RecursiveWitness(
        [], 0, [], [], false, map[], {}, output, errors, hadError,
        true, 0, false, openedStatus, statusErr, false,
        preStatus,preStatus+1,preStatus+1,preStatus+1,nativeTrace,[statusCall],nativeTrace.nativeCalls,[],[0]);
      assert Spec.RecursiveNativeDirectoryTrace(cmd, preFs, accessPath, tree) by {
        hide *;
        reveal Spec.RecursiveNativeDirectoryTrace(), Spec.FailedOpenDirectoryTrace(), Spec.BoundOpenDirectoryTrace();
        reveal Spec.NativeCallsFields(), Native.TraceFields();
      }
      assert RecursiveDirectorySummary(
          cmd, preFs, displayPath, accessPath, ancestors, tree) by {
        reveal RecursiveDirectorySummary(), Spec.RecursiveNativeCallsFields(), Spec.NativeCallsFields();
      }
      return;
    }
    ghost var listingFirst := io.statusCursor();
    assert listingFirst == preStatus + 1;
    if openedStatus.hostKey in ancestors {
      wasListed := false;
      var closeResult,closed := NativeIO.Close(handle,io);
      CompleteRecursiveClose(cmd.nativeInputs[0],before,openedState,closed,nativeTrace.nativeCalls,handle);
      var closeFailed := closeResult.Err?;
      nativeTrace := nativeTrace.(closed := io.directoryCapabilities(),closeOk := closeResult.Ok?,
      closeErr := IOContract.ResultErrno(closeResult),closeCalls := [closed],
      nativeCalls := nativeTrace.nativeCalls+[closed]);
      output := [];
      errors := Spec.RecursiveCycleMessageSpec(displayPath);
      hadError := openedStatus.hostKey in ancestors || closeFailed;
      hasCycle := true;
      directoryFailed := closeFailed;
      tree := Spec.RecursiveWitness(
        [], 0, [], [], false, map[], {}, output, errors, hadError,
        true, 0, true, openedStatus, 0, true,
        preStatus,listingFirst,listingFirst,listingFirst,nativeTrace,[statusCall],nativeTrace.nativeCalls,[],[0]);
      assert Spec.RecursiveNativeDirectoryTrace(cmd, preFs, accessPath, tree) by {
        hide *;
        reveal Spec.RecursiveNativeDirectoryTrace(), Spec.FailedOpenDirectoryTrace(), Spec.BoundOpenDirectoryTrace();
        reveal Spec.NativeCallsFields(), Native.TraceFields();
      }
      assert RecursiveDirectorySummary(
          cmd, preFs, displayPath, accessPath, ancestors, tree) by {
        reveal RecursiveDirectorySummary(), Spec.RecursiveNativeCallsFields(), Spec.NativeCallsFields();
      }
      return;
    }
    var observations: seq<Spec.EntryObservation>;
    var readErr: int;
    var listing: BenchWorld.Bytes;
    var listingErrors: BenchWorld.Bytes;
    var listingHadError: bool;
    assert Spec.DirectoryExpectedEntries(nativeTrace,NativeDirectory.EntriesForNames(io.directoryTopology(),
                                                                                     io.directoryCapabilities()[handle].position,io.directoryCapabilities()[handle].remaining)) by {
      reveal Spec.DirectoryExpectedEntries();
      reveal IOContract.DirectoryCapabilityReadCurrentFields(), IOContract.DirectoryCapabilityAnchorCurrentFields();
      reveal IOContract.DirectoryCapabilityNamesFields();
    }
    observations, readErr, listing, listingErrors, listingHadError, directoryFailed, nativeTrace :=
      ReadOpenedDirectoryCore(cmd, displayPath, accessPath, handle, nativeTrace, io);
    wasListed := true;
    assert |nativeTrace.nativeCalls| > 0 by {
      reveal DirectoryListingSummary(), Spec.ReadCloseDirectoryTrace(), Spec.BoundOpenDirectoryTrace();
    }
    ghost var listingAfter := io.statusCursor();
    ghost var allCalls := nativeTrace.nativeCalls;
    ghost var childCalls: seq<Native.Call> := [];
    ghost var childPieces: seq<seq<Native.Call>> := [];
    ghost var childCuts: seq<nat> := [0];
    errors := listingErrors;
    hadError := listingHadError;
    hasCycle := false;
    output := Spec.DirectoryHeaderSpec(displayPath) + listing;
    ghost var children: map<nat, Spec.RecursiveWitness> := map[];
    ghost var cycles: set<nat> := {};
    var childAncestors := ancestors + {openedStatus.hostKey};
    ghost var statusCuts: seq<nat> := [listingAfter];
    DirectoryTraceProof.EmptyNativeCallFragments();
    assert StatusCutsPrefix(statusCuts, children, 0) by {
      reveal StatusCutsPrefix();
    }
    var i := 0;
    assert RecursivePrefixSummary(
        cmd, preFs, displayPath, childAncestors, observations, listing,
        listingErrors, listingHadError, i, children, cycles,
        output, errors, hadError) by {
      reveal RecursiveChildOutputPrefixCore(), RecursiveChildErrorPrefixCore();
      reveal RecursivePrefixSummary(
             cmd, preFs, displayPath, childAncestors, observations, listing,
             listingErrors, listingHadError, i, children, cycles,
             output, errors, hadError);
    }
    while i < |observations|
      invariant hasCycle == (cycles != {} || exists j: nat :: j in children && Spec.RecursiveHasCycle(children[j]))
      invariant io.dirHandles() == cmd.directoryHandles
      invariant NativeIO.Inputs(io) == cmd.nativeInputs[0]
      invariant io.directoryCapabilities() == before.context.capabilities
      invariant Native.TraceFields(cmd.nativeInputs[0],before,NativeIO.State(io),allCalls)
      invariant allCalls == nativeTrace.nativeCalls+childCalls
      invariant Spec.NativeCallFragments(childPieces,childCalls,childCuts)
      invariant |childPieces| == i
      invariant forall j: nat | j < i :: childPieces[j] == (if j in children then children[j].nativeCalls else [])
      invariant 0 <= i <= |observations|
      invariant |statusCuts| == i + 1
      invariant statusCuts[0] == listingAfter
      invariant statusCuts[i] == io.statusCursor()
      invariant StatusCutsPrefix(statusCuts, children, i)
      invariant RecursivePrefixSummary(
                  cmd, preFs, displayPath, childAncestors, observations, listing,
                  listingErrors, listingHadError, i, children, cycles,
                  output, errors, hadError)
      decreases *
    {
      reveal RecursivePrefixSummary(
             cmd, preFs, displayPath, childAncestors, observations, listing,
             listingErrors, listingHadError, i, children, cycles,
             output, errors, hadError);
      ghost var stepBefore := NativeIO.State(io);
      ghost var beforeAllCalls := allCalls;
      ghost var beforeChildCalls := childCalls;
      ghost var beforeChildPieces := childPieces;
      ghost var beforeChildCuts := childCuts;
      ghost var nativePiece: seq<Native.Call> := [];
      ghost var beforeChildren := children;
      ghost var beforeCycles := cycles;
      ghost var beforeStatus := io.statusCursor();
      ghost var beforeCuts := statusCuts;
      var beforeOutput := output;
      var beforeErrors := errors;
      var beforeHadError := hadError;
      ghost var beforeHasCycle := hasCycle;
      assert beforeOutput == Spec.DirectoryHeaderSpec(displayPath) + listing +
                             RecursiveChildOutputPrefixCore(observations, beforeChildren, i);
      assert beforeErrors == listingErrors + RecursiveChildErrorPrefixCore(
                               displayPath, observations, beforeChildren, beforeCycles, i);
      assert beforeHadError ==
             (listingHadError ||
              exists j: nat :: j in beforeChildren && beforeChildren[j].hadError);
      RecursivePrefixRanges(
        cmd, preFs, displayPath, childAncestors, observations, listing,
        listingErrors, listingHadError, i, children, cycles,
        output, errors, hadError);
      var observation := observations[i];
      var outputPiece: BenchWorld.Bytes := [];
      var errorPiece: BenchWorld.Bytes := [];
      var stepFailed := false;
      ghost var addedChild := false;
      ghost var addedCycle := false;
      if Spec.RecursiveEntryEligible(observation)
      {
        var childDisplay := Spec.ChildDisplayPath(displayPath, observation.displayName);
        var descendantOutput: BenchWorld.Bytes;
        var descendantErrors: BenchWorld.Bytes;
        var childFailed: bool;
        var childHasCycle: bool;
        var childListed: bool;
        var childDirectoryFailed: bool;
        ghost var childTree: Spec.RecursiveWitness;
        var childOpened: bool;
        childOpened, childListed, descendantOutput, descendantErrors, childFailed, childHasCycle, childDirectoryFailed, childTree := WalkDirectoryRecursive(
          cmd, childDisplay, observation.accessPath, childAncestors, io);
        nativePiece := childTree.nativeCalls;
        outputPiece := if childListed then "\n" + descendantOutput else [];
        errorPiece := descendantErrors;
        assert i !in children;
        children := children[i := childTree];
        if childTree.cycle {
          cycles := cycles + {i};
          addedCycle := true;
        }
        hasCycle := hasCycle || childHasCycle;
        stepFailed := childFailed;
        addedChild := true;
      }
      if !addedChild {
        assert Native.TraceFields(cmd.nativeInputs[0],stepBefore,NativeIO.State(io),[]) by { reveal Native.TraceFields(); }
      }
      NativeTrace.Concat(cmd.nativeInputs[0],before,stepBefore,NativeIO.State(io),beforeAllCalls,nativePiece);
      allCalls := beforeAllCalls+nativePiece;
      childCalls := beforeChildCalls+nativePiece;
      childPieces := beforeChildPieces+[nativePiece];
      childCuts := beforeChildCuts+[|childCalls|];
      DirectoryTraceProof.AppendNativeCallFragments(beforeChildPieces,beforeChildCalls,beforeChildCuts,nativePiece);
      output := output + outputPiece;
      errors := errors + errorPiece;
      hadError := hadError || stepFailed;
      statusCuts := statusCuts + [io.statusCursor()];
      StatusCutsSnoc(beforeCuts, beforeChildren, children, i,
                     io.statusCursor(), addedChild);
      CompleteRecursivePrefixStep(cmd,preFs,displayPath,childAncestors,observations,
                                  listing,listingErrors,listingHadError,i,beforeChildren,beforeCycles,children,cycles,
                                  beforeOutput,beforeErrors,beforeHadError,outputPiece,errorPiece,stepFailed,beforeHasCycle,hasCycle);
      i := i + 1;
    }
    reveal RecursivePrefixSummary(
           cmd, preFs, displayPath, childAncestors, observations, listing,
           listingErrors, listingHadError, i, children, cycles,
           output, errors, hadError);
    tree := Spec.RecursiveWitness(
      observations, readErr, listing, listingErrors, listingHadError,
      children, cycles, output, errors, hadError,
      true, 0, true, openedStatus, 0, false,
      preStatus,listingFirst,listingAfter,io.statusCursor(),nativeTrace,[statusCall],allCalls,childPieces,childCuts);
    assert Spec.RecursiveNativeDirectoryTrace(cmd, preFs, accessPath, tree) by {
      hide *;
      reveal Spec.RecursiveNativeDirectoryTrace();
    }
    assert Spec.RecursiveNativeCallsFields(cmd,preFs,tree) by {
      hide *;
      reveal Spec.RecursiveNativeCallsFields(), Spec.NativeCallsFields(), Native.TraceFields();
    }
    reveal StatusCutsPrefix();
    RecursivePrefixComplete(
      cmd, preFs, displayPath, accessPath, ancestors, tree, statusCuts);
  }

  method OperandStatusCore(cmd: Schema.LsCmd, path: BenchWorld.Path, io: BenchIO.IO)
    returns (ok: bool, status: BenchWorld.FileStatus, err: int, ghost calls: seq<Native.Call>)
    requires Spec.NativeCommandFields(cmd,io.fs()) && cmd.nativeInputs[0] == NativeIO.Inputs(io)
    modifies io.directoryStateRegion,io.statusObservationsRegion
    ensures NativeIO.Inputs(io) == old(NativeIO.Inputs(io))
    ensures NativeObservation.OperandFields(cmd.nativeInputs[0],old(NativeIO.State(io)),NativeIO.State(io),
                                            path,Spec.ImplicitDirectoryFollowSpec(cmd),Spec.ExplicitCommandLineFollowSpec(cmd),ok,status,err,calls)
    ensures Native.TraceFields(cmd.nativeInputs[0],old(NativeIO.State(io)),NativeIO.State(io),calls)
    ensures 1 <= |calls| <= 2 && calls[0].before == old(NativeIO.State(io))
    ensures io.statusCursor() == old(io.statusCursor())+|calls|
    ensures io.cwdContext() == old(io.cwdContext()).(ordinal := old(io.cwdContext()).ordinal+|calls|)
    ensures if ok then err == 0 else err > 0
  {
    ghost var before := NativeIO.State(io);
    ok,status,err,calls := NativeObserve.Operand(path,Spec.ImplicitDirectoryFollowSpec(cmd),
                                                 Spec.ExplicitCommandLineFollowSpec(cmd),io);
    NativeFrames.OperandFrame(cmd.nativeInputs[0],before,NativeIO.State(io),path,
                              Spec.ImplicitDirectoryFollowSpec(cmd),Spec.ExplicitCommandLineFollowSpec(cmd),ok,status,err,calls);
    reveal NativeObservation.OperandFields(), Native.TraceFields(), Native.CallFields();
    reveal NativeObservation.StatusFields(), IOContract.GetFileStatusAtCwdSpec();
  }

  method {:vcs_split_on_every_assert} ObserveOperand(
    index: nat, cmd: Schema.LsCmd, ghost cwd: BenchWorld.Path, io: BenchIO.IO
  ) returns (observation: Spec.OperandObservation)
    requires index < |cmd.operands|
    requires Spec.NativeCommandFields(cmd,io.fs()) && cmd.nativeInputs[0] == NativeIO.Inputs(io)
    requires io.dirHandles() == cmd.directoryHandles
    modifies io.directoryStateRegion,io.statusObservationsRegion
    ensures observation.index == index
    ensures OperandObservationSummary(cmd,old(io.fs()),cwd,observation)
    ensures observation.firstStatus == old(io.statusCursor()) && observation.afterStatus == io.statusCursor()
    ensures NativeIO.Inputs(io) == old(NativeIO.Inputs(io))
    ensures io.dirHandles() == cmd.directoryHandles
    ensures io.directoryCapabilities() == old(io.directoryCapabilities())
    ensures Native.TraceFields(cmd.nativeInputs[0],old(NativeIO.State(io)),NativeIO.State(io),observation.nativeCalls)
    decreases *
  {
    hide *;
    reveal Spec.NativeCommandFields(), Spec.OperandPathSpec(), Spec.ObservedOperandStatusCallCount();
    ghost var preFs := io.fs();
    ghost var before := NativeIO.State(io);
    var operand := cmd.operands[index];
    var path := operand;
    var ok,status,err,statusCalls := OperandStatusCore(cmd,path,io);
    ghost var afterStatus := NativeIO.State(io);
    NativeFrames.SelectedResult(cmd.nativeInputs[0],before,afterStatus,path,
                                Spec.ImplicitDirectoryFollowSpec(cmd),Spec.ExplicitCommandLineFollowSpec(cmd),
                                ok,status,err,statusCalls);
    assert statusCalls[|statusCalls|-1].after == afterStatus by {
      reveal Native.TraceFields();
    }
    assert path == Spec.OperandPathSpec(cmd,cwd,operand);
    if !ok {
      observation := Spec.OperandObservation(index,operand,operand,path,false,status,err,Spec.AccessFailure,
                                             false,[],Spec.AccessErrorMessageSpec(operand,err),[],true,false,false,
                                             before.status,io.statusCursor(),Spec.NoDirectoryTrace,statusCalls,[],statusCalls,0);
      assert Spec.OperandNativeFields(cmd,preFs,observation) by {
        reveal Spec.OperandNativeFields(), Spec.NativeCallsFields(), Spec.NativeCommandFields(), Native.TraceFields();
      }
      assert OperandObservationSummary(cmd,preFs,cwd,observation) by {
        hide *;
        reveal OperandObservationSummary(), Spec.ObservedOperandStatusResult(), Spec.ObservedOperandStatusCallCount();
        reveal Spec.OperandNativeFields(), NativeObservation.OperandFields(), NativeObservation.StatusFields();
        reveal Spec.OperandPathSpec(), Spec.NativeCommandFields(), IOContract.ResultErrno();
      }
    } else if status.kind == BenchWorld.DirectoryKind && !cmd.listDirectories {
      var wasOpened: bool;
      var body: BenchWorld.Bytes;
      var sectionErrors: BenchWorld.Bytes;
      var failed: bool;
      var directoryFailed: bool;
      if cmd.recursive {
        var wasListed: bool;
        var hasCycle: bool;
        ghost var recursiveTree: Spec.RecursiveWitness;
        wasOpened,wasListed,body,sectionErrors,failed,hasCycle,directoryFailed,recursiveTree :=
          WalkDirectoryRecursive(cmd,operand,path,{},io);
        NativeTrace.Concat(cmd.nativeInputs[0],before,afterStatus,NativeIO.State(io),statusCalls,recursiveTree.nativeCalls);
        observation := Spec.OperandObservation(index,operand,operand,path,true,status,0,Spec.ExpandedDirectory,
                                               wasOpened,if wasOpened then body else [],[],sectionErrors,failed,hasCycle,directoryFailed,
                                               before.status,io.statusCursor(),recursiveTree.nativeTrace,statusCalls,[],statusCalls+recursiveTree.nativeCalls,0);
        assert Spec.OperandNativeFields(cmd,preFs,observation) by {
          reveal Spec.OperandNativeFields(), Spec.NativeCallsFields(), Spec.NativeCommandFields(), Native.TraceFields();
        }
        assert Spec.ObservedOperandStatusResult(cmd,preFs,observation) == Result.Ok(status) by {
          reveal Spec.ObservedOperandStatusResult(), Spec.NativeCommandFields();
        }
        assert Spec.RecursiveNativeCallsFields(cmd,preFs,recursiveTree) by {
          reveal RecursiveDirectorySummary();
        }
        ExpandedRecursiveOperandSummary(cmd,preFs,cwd,observation,recursiveTree);
      } else {
        var entries: seq<Spec.EntryObservation>;
        var readErr: int;
        var listingOutput: BenchWorld.Bytes;
        ghost var nativeTrace: Spec.DirectoryTrace;
        entries,readErr,wasOpened,listingOutput,sectionErrors,failed,directoryFailed,nativeTrace :=
          ReadDirectoryCore(cmd,operand,path,io);
        assert nativeTrace.DirectoryTrace? by { reveal Spec.BoundOpenDirectoryTrace(); }
        body := listingOutput;
        if |cmd.operands| > 1 { body := Spec.DirectoryHeaderSpec(operand)+body; }
        NativeTrace.Concat(cmd.nativeInputs[0],before,afterStatus,NativeIO.State(io),statusCalls,nativeTrace.nativeCalls);
        observation := Spec.OperandObservation(index,operand,operand,path,true,status,0,Spec.ExpandedDirectory,
                                               wasOpened,if wasOpened then body else [],[],sectionErrors,failed,false,directoryFailed,
                                               before.status,io.statusCursor(),nativeTrace,statusCalls,[],statusCalls+nativeTrace.nativeCalls,0);
        assert Spec.OperandNativeFields(cmd,preFs,observation) by {
          reveal Spec.OperandNativeFields(), Spec.NativeCallsFields(), Spec.NativeCommandFields(), Native.TraceFields();
        }
        assert Spec.ObservedOperandStatusResult(cmd,preFs,observation) == Result.Ok(status) by {
          reveal Spec.ObservedOperandStatusResult(), Spec.NativeCommandFields();
        }
        ExpandedFlatOperandSummary(cmd,preFs,cwd,observation,entries,readErr,listingOutput);
      }
    } else {
      var renderName,linkErr,renderCalls := RenderNameCore(cmd,operand,path,
                                                           Spec.ExplicitCommandLineFollowSpec(cmd),status,io);
      NativeFrames.RenderFrame(cmd.nativeInputs[0],afterStatus,NativeIO.State(io),operand,path,
                               Spec.ExplicitCommandLineFollowSpec(cmd),cmd.numericLong,status,renderName,linkErr,renderCalls);
      NativeTrace.Concat(cmd.nativeInputs[0],before,afterStatus,NativeIO.State(io),statusCalls,renderCalls);
      observation := Spec.OperandObservation(index,operand,renderName,path,true,status,0,Spec.DirectOperand,
                                             false,Spec.RenderEntrySpec(cmd,renderName,status),Spec.ReadLinkErrorMessageSpec(operand,linkErr),[],
                                             linkErr != 0,false,false,before.status,io.statusCursor(),Spec.NoDirectoryTrace,
                                             statusCalls,renderCalls,statusCalls+renderCalls,linkErr);
      assert Spec.OperandNativeFields(cmd,preFs,observation) by {
        reveal Spec.OperandNativeFields(), Spec.NativeCallsFields(), Spec.NativeCommandFields(), Native.TraceFields();
      }
      assert OperandObservationSummary(cmd,preFs,cwd,observation) by {
        hide *;
        reveal OperandObservationSummary(), Spec.ObservedOperandStatusResult(), Spec.ObservedOperandStatusCallCount();
        reveal Spec.DirectOperandRenderFields(), Spec.OperandNativeFields();
        reveal NativeObservation.OperandFields(), NativeObservation.StatusFields(), Spec.OperandPathSpec(), Spec.NativeCommandFields();
      }
    }
  }

  function PositiveEnvironmentResult(result: BenchWorld.IOResult<string>): nat
  {
    match result
    case Ok(value) => Spec.ParsedPositiveOrZeroSpec(value)
    case Err(_) => 0
  }

  method ResolveEnvironmentBlockSize(io: BenchIO.IO) returns (
      blockSize: nat,
      fileSizeBlockSize: nat
    )
    ensures blockSize == Spec.EnvironmentBlockSizeSpec(old(io.env()))
    ensures fileSizeBlockSize == Spec.EnvironmentFileSizeBlockSizeSpec(old(io.env()))
    ensures blockSize > 0
    ensures fileSizeBlockSize > 0
  {
    ghost var preEnv := io.env();
    var lsValue := io.GetEnv("LS_BLOCK_SIZE");
    var blockValue := io.GetEnv("BLOCK_SIZE");
    var legacyValue := io.GetEnv("BLOCKSIZE");
    var lsSize := PositiveEnvironmentResult(lsValue);
    var genericSize := PositiveEnvironmentResult(blockValue);
    var legacySize := PositiveEnvironmentResult(legacyValue);
    blockSize := if lsSize > 0 then lsSize
    else if genericSize > 0 then genericSize
    else if legacySize > 0 then legacySize
    else 1024;
    fileSizeBlockSize := if lsSize > 0 then lsSize
    else if genericSize > 0 then genericSize
    else 1;
    reveal IOContract.GetEnvContractFields();
  }

  method {:vcs_split_on_every_assert} Prepare(raw: Schema.LsCmdRaw, io: BenchIO.IO) returns (exit: int, plannedStdout: StreamWorld.Bytes, plannedStderr: StreamWorld.Bytes)
    modifies io.directoryStateRegion, io.statusObservationsRegion
    ensures PreparedSummary(raw, io, exit, plannedStdout, plannedStderr)
    decreases *
  {
    hide *;
    reveal Spec.EffectiveCommandSpec(), Schema.WithBlockSize(), Schema.WithReferenceNow();
    reveal Schema.Command(), Schema.WithStatusObservations(), IOContract.NowSpec();
    ghost var emissionBeforeOut: StreamWorld.Bytes := [];
    ghost var emissionBeforeErr: StreamWorld.Bytes := [];
    plannedStdout := [];
    plannedStderr := [];
    ghost var nativeBefore := NativeIO.State(io);
    ghost var nativeInputs := NativeIO.Inputs(io);
    ghost var preFs := io.fs();
    ghost var preCwd := io.cwd();
    ghost var preEnv := io.env();
    ghost var preNow := io.now();
    ghost var preStatus := io.statusCursor();
    ghost var preDirHandles := io.dirHandles();
    ghost var preStatusObservations := io.statusObservations();
    ghost var preStdout := (emissionBeforeOut + plannedStdout);
    ghost var preStderr := (emissionBeforeErr + plannedStderr);
    var parsedCmd := Schema.Command(raw);
    var cmd := parsedCmd;
    if parsedCmd.mode == Schema.ModeHelp {
      plannedStdout := plannedStdout + Spec.HelpTextSpec;
      exit := 0;
      assert PreparedSummary(raw, io, exit, plannedStdout, plannedStderr) by {
        reveal PreparedSummary();
      }
      return;
    }
    if parsedCmd.mode == Schema.ModeVersion {
      plannedStdout := plannedStdout + Spec.VersionTextSpec;
      exit := 0;
      assert PreparedSummary(raw, io, exit, plannedStdout, plannedStderr) by {
        reveal PreparedSummary();
      }
      return;
    }
    if parsedCmd.mode != Schema.ModeRun {
      plannedStderr := plannedStderr + (Spec.InvalidModeMessageSpec(parsedCmd.mode));
      exit := if parsedCmd.mode.ModeInvalidTime? then 1 else 2;
      assert PreparedSummary(raw, io, exit, plannedStdout, plannedStderr) by {
        reveal PreparedSummary();
      }
      return;
    }

    var blockSize := parsedCmd.cliBlockSize;
    var fileSizeBlockSize := parsedCmd.fileSizeBlockSize;
    if blockSize == 0 {
      blockSize, fileSizeBlockSize := ResolveEnvironmentBlockSize(io);
    }
    var referenceNow := io.Now();
    cmd := Schema.WithReferenceNow(
      Schema.WithBlockSize(parsedCmd, blockSize, fileSizeBlockSize), referenceNow);
    assert cmd == Spec.EffectiveCommandSpec(raw, preEnv, preNow);
    cmd := Schema.WithStatusObservations(cmd, preStatusObservations, preStatus, io.trustedNativeFailures(),preDirHandles,preCwd,[nativeInputs],[nativeBefore]);
    assert cmd == Schema.WithStatusObservations(
                    Spec.EffectiveCommandSpec(raw, preEnv, preNow), preStatusObservations, preStatus, io.trustedNativeFailures(),preDirHandles,preCwd,[nativeInputs],[nativeBefore]);

    ghost var cwd := io.cwd();
    var output: BenchWorld.Bytes := [];
    var errors: BenchWorld.Bytes := [];
    var hadError := false;
    var observations: seq<Spec.OperandObservation> := [];
    ghost var statusCuts: seq<nat> := [preStatus];
    ghost var nativeCalls: seq<Native.Call> := [];
    ghost var nativePieces: seq<seq<Native.Call>> := [];
    ghost var nativeCuts: seq<nat> := [0];
    assert Spec.NativeCommandFields(cmd,preFs) by { reveal Spec.NativeCommandFields(); }
    assert Native.TraceFields(nativeInputs,nativeBefore,NativeIO.State(io),nativeCalls) by {
      reveal Native.TraceFields();
    }
    DirectoryTraceProof.EmptyNativeCallFragments();
    var i := 0;
    while i < |cmd.operands|
      invariant io.dirHandles() == preDirHandles
      invariant NativeIO.Inputs(io) == nativeInputs
      invariant io.directoryCapabilities() == nativeBefore.context.capabilities
      invariant Native.TraceFields(nativeInputs,nativeBefore,NativeIO.State(io),nativeCalls)
      invariant Spec.NativeCallFragments(nativePieces,nativeCalls,nativeCuts)
      invariant |nativePieces| == i
      invariant 0 <= i <= |cmd.operands|
      invariant |observations| == i
      invariant forall j: nat | j < i :: nativePieces[j] == observations[j].nativeCalls
      invariant |statusCuts| == i + 1
      invariant statusCuts[0] == preStatus
      invariant statusCuts[i] == io.statusCursor()
      invariant io.statusObservations() == preStatusObservations
      invariant forall j: nat | j < i ::
                  observations[j].firstStatus == statusCuts[j] &&
                  observations[j].afterStatus == statusCuts[j + 1]
      invariant (emissionBeforeOut + plannedStdout) == preStdout
      invariant (emissionBeforeErr + plannedStderr) == preStderr
      invariant cwd == preCwd
      invariant forall j: nat :: j < i ==>
                                   observations[j].index == j &&
                                   OperandObservationSummary(cmd, preFs, preCwd, observations[j])
      invariant output == []
      invariant errors == []
      invariant hadError ==
                (exists j: nat :: j < i && observations[j].failed)
      decreases |cmd.operands| - i
    {
      ghost var stepBefore := NativeIO.State(io);
      var observation := ObserveOperand(i,cmd,cwd,io);
      NativeTrace.Concat(nativeInputs,nativeBefore,stepBefore,NativeIO.State(io),nativeCalls,observation.nativeCalls);
      ghost var beforePieces := nativePieces;
      ghost var beforeCalls := nativeCalls;
      ghost var beforeCuts := nativeCuts;
      nativeCalls := beforeCalls+observation.nativeCalls;
      nativePieces := beforePieces+[observation.nativeCalls];
      nativeCuts := beforeCuts+[|nativeCalls|];
      DirectoryTraceProof.AppendNativeCallFragments(beforePieces,beforeCalls,beforeCuts,observation.nativeCalls);
      ghost var beforeObservations := observations;
      FailedOperandSnoc(beforeObservations, observation);
      observations := observations + [observation];
      statusCuts := statusCuts + [io.statusCursor()];
      hadError := hadError || observation.failed;
      assert observations[i] == observation;
      i := i + 1;
    }
    var sorted := SortOperandsCore(cmd, observations);
    var groups := OutputGroupsCore(cmd, sorted);
    output := JoinOutputGroupsCore(groups);
    errors := AccessErrorsCore(observations) + SectionErrorsCore(sorted);
    plannedStdout := plannedStdout + (output);
    plannedStderr := plannedStderr + (errors);
    exit := OperandExitCore(observations);
    assert seq(|observations|,i requires 0 <= i < |observations| => observations[i].nativeCalls) == nativePieces;
    RunNativeProof.RunWitness(cmd,preFs,preStatus,io.statusCursor(),observations,
                              [NativeIO.State(io)],nativeCalls,nativeCuts);
    assert RunSummary(cmd,preFs,preCwd,preStatus,io.statusCursor(),output,errors,exit,[NativeIO.State(io)]) by {
      reveal RunSummary();
    }
    assert PreparedSummary(raw, io, exit, plannedStdout, plannedStderr) by {
      reveal PreparedSummary();
    }
  }


  method Flush(output: StreamWorld.Bytes, diagnostics: StreamWorld.Bytes,
               normalExit: int, io: BenchIO.IO) returns (exit: int)
    modifies io.stdoutRegion, io.stderrRegion
    ensures Spec.EmissionFields(old(io.stdout()), old(io.stderr()), io.stdout(), io.stderr(),
                                io.trustedStreams(), output, diagnostics, normalExit, exit)
  {
    var committed: nat := 0;
    var outErr := 0;
    if |output| != 0 {
      var result := io.WriteStdout(output);
      committed := StreamContract.WriteResultCommitted(result);
      outErr := StreamContract.ResultErrno(result);
    }
    var finalDiagnostics := diagnostics;
    if outErr != 0 {
      var reason := io.GetCLocaleErrnoText(outErr);
      finalDiagnostics := diagnostics + Spec.WriteErrorText(reason);
    }
    assert finalDiagnostics == diagnostics + (if outErr == 0 then []
                                              else Spec.WriteErrorText(StreamContract.CLocaleErrnoTextResult(outErr)));
    var errCommitted: nat := 0;
    var errErr := 0;
    if |finalDiagnostics| != 0 {
      var result := io.WriteStderr(finalDiagnostics);
      errCommitted := StreamContract.WriteResultCommitted(result);
      errErr := StreamContract.ResultErrno(result);
      assert StreamContract.WriteStderrSpec(old(io.stderr()), io.trustedStreams(), io.stderr(),
                                            finalDiagnostics, errCommitted, errErr);
    }
    exit := if outErr != 0 || errErr != 0 then 2 else normalExit;
    assert Spec.EmissionOutcomeFields(old(io.stdout()), old(io.stderr()), io.stdout(), io.stderr(),
                                      io.trustedStreams(), output, diagnostics, normalExit, exit, committed, outErr, errCommitted, errErr);
  }

  method RunCore(raw: Schema.LsCmdRaw, io: BenchIO.IO) returns (exit: int)
    modifies io.stdoutRegion, io.stderrRegion, io.directoryStateRegion, io.statusObservationsRegion
    ensures CoreSummary(raw, io, exit)
    decreases *
  {
    var normalExit, output, diagnostics := Prepare(raw, io);
    assert PreparedSummary(raw, io, normalExit, output, diagnostics);
    exit := Flush(output, diagnostics, normalExit, io);
    assert PreparedSummary(raw, io, normalExit, output, diagnostics);
    assert Spec.EmissionFields(old(io.stdout()), old(io.stderr()), io.stdout(), io.stderr(),
                               io.trustedStreams(), output, diagnostics, normalExit, exit);
    assert exists emitted: StreamWorld.Bytes, reported: StreamWorld.Bytes, preparedExit: int ::
        PreparedSummary(raw, io, preparedExit, emitted, reported) &&
        Spec.EmissionFields(old(io.stdout()), old(io.stderr()), io.stdout(), io.stderr(),
                            io.trustedStreams(), emitted, reported, preparedExit, exit);
  }
}
