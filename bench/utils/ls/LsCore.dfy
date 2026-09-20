include "../../core/World.dfy"
include "../../core/IO.dfy"
include "../../core/IOContract.dfy"
include "LsSchema.dfy"
include "LsSpec.dfy"
include "LsTime.dfy"

module LsCore {
  import BenchIO
  import Utf8 = Utf8Semantics
  import BenchWorld
  import IOContract
  import Schema = LsSchema
  import Spec = LsSpec
  import Time = LsTime

  function DigitCharCore(d: nat): char
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
  }

  function NatTextCore(n: nat): string
    decreases n
  {
    if n < 10 then [DigitCharCore(n)]
    else NatTextCore(n / 10) + [DigitCharCore(n % 10)]
  }

  function IntTextCore(n: int): string
  {
    if n < 0 then "-" + NatTextCore((-n) as nat) else NatTextCore(n as nat)
  }

  function PermissionCharCore(mode: bv32, bit: bv32, present: char): char
  {
    if (mode & bit) != 0 as bv32 then present else '-'
  }

  function ExecuteCharCore(
    mode: bv32,
    executeBit: bv32,
    specialBit: bv32,
    specialExecute: char,
    specialNoExecute: char
  ): char
  {
    if (mode & specialBit) != 0 as bv32 then
      if (mode & executeBit) != 0 as bv32 then specialExecute else specialNoExecute
    else
      PermissionCharCore(mode, executeBit, 'x')
  }

  function KindCharCore(kind: BenchWorld.FileKind): char
  {
    match kind
    case RegularKind => '-'
    case DirectoryKind => 'd'
    case SymlinkKind => 'l'
    case BlockDeviceKind => 'b'
    case CharacterDeviceKind => 'c'
    case FifoKind => 'p'
    case SocketKind => 's'
  }

  function ModeTextCore(status: BenchWorld.FileStatus): string
  {
    [KindCharCore(status.kind),
     PermissionCharCore(status.mode, 256 as bv32, 'r'),
     PermissionCharCore(status.mode, 128 as bv32, 'w'),
     ExecuteCharCore(status.mode, 64 as bv32, 2048 as bv32, 's', 'S'),
     PermissionCharCore(status.mode, 32 as bv32, 'r'),
     PermissionCharCore(status.mode, 16 as bv32, 'w'),
     ExecuteCharCore(status.mode, 8 as bv32, 1024 as bv32, 's', 'S'),
     PermissionCharCore(status.mode, 4 as bv32, 'r'),
     PermissionCharCore(status.mode, 2 as bv32, 'w'),
     ExecuteCharCore(status.mode, 1 as bv32, 512 as bv32, 't', 'T')]
  }

  function RenderEntryCore(
    cmd: Schema.LsCmd,
    displayName: string,
    status: BenchWorld.FileStatus
  ): BenchWorld.Bytes
  {
    var blockPrefix := if cmd.showBlocks then
                         NatTextCore(Spec.DisplayedBlocksSpec(status.storage.allocatedBlocks, cmd.cliBlockSize)) + " "
                       else "";
    Utf8.Encode(blockPrefix + if !cmd.numericLong then
      displayName + "\n"
    else
      ModeTextCore(status) + " " +
      NatTextCore(status.linkCount) + " " +
      NatTextCore(status.ownership.uid) + " " +
      NatTextCore(status.ownership.gid) + " " +
      NatTextCore(Spec.DisplayedFileSizeSpec(
                    status.storage.size, cmd.fileSizeBlockSize)) + " " +
      TimeTextCore(cmd, SelectedSecondsCore(cmd, status),
                   SelectedNanosecondsCore(cmd, status)) + " " +
      displayName + "\n")
  }

  function TimeTextCore(cmd: Schema.LsCmd, seconds: int, nanoseconds: int): string
  {
    match cmd.timeStyle
    case EpochSeconds => IntTextCore(seconds)
    case FullIso => Time.FullIso(seconds, nanoseconds)
    case LongIso => Time.LongIso(seconds)
    case Iso => Time.Iso(seconds, nanoseconds, cmd.referenceNow)
    case DefaultC => Time.DefaultC(seconds, nanoseconds, cmd.referenceNow)
  }

  function AllocatedBlocksSumCore(observations: seq<Spec.EntryObservation>): nat
    decreases |observations|
  {
    if |observations| == 0 then 0
    else
      (if observations[0].ok then observations[0].status.storage.allocatedBlocks else 0) +
      AllocatedBlocksSumCore(observations[1..])
  }

  function TotalLineCore(cmd: Schema.LsCmd, observations: seq<Spec.EntryObservation>): BenchWorld.Bytes
  {
    if cmd.numericLong || cmd.showBlocks then
      Utf8.Encode("total " + NatTextCore(
        Spec.DisplayedBlocksSpec(AllocatedBlocksSumCore(observations), cmd.cliBlockSize)) + "\n")
    else
      []
  }

  opaque function StringLessFromCore(left: string, right: string, i: nat): bool
    requires i <= |left| && i <= |right|
    decreases |left| + |right| - 2 * i
  {
    if i == |left| then i < |right|
    else if i == |right| then false
    else if left[i] == right[i] then StringLessFromCore(left, right, i + 1)
    else left[i] < right[i]
  }

  opaque function StringLessCore(left: string, right: string): bool
  {
    StringLessFromCore(left, right, 0)
  }

  function SelectedSecondsCore(cmd: Schema.LsCmd, status: BenchWorld.FileStatus): int
  {
    match cmd.timeField
    case ModificationTime => status.times.mtimeSec
    case AccessTime => status.times.atimeSec
    case ChangeTime => status.times.ctimeSec
  }

  function SelectedNanosecondsCore(cmd: Schema.LsCmd, status: BenchWorld.FileStatus): int
  {
    match cmd.timeField
    case ModificationTime => status.times.mtimeNsec
    case AccessTime => status.times.atimeNsec
    case ChangeTime => status.times.ctimeNsec
  }

  opaque function BaseEntryBeforeCore(
    cmd: Schema.LsCmd,
    left: Spec.EntryObservation,
    right: Spec.EntryObservation
  ): bool
  {
    if left.ok != right.ok then left.ok
    else if !left.ok then StringLessCore(left.displayName, right.displayName)
    else if cmd.sortMode == Schema.SortSize &&
            left.status.storage.size != right.status.storage.size then
      left.status.storage.size > right.status.storage.size
    else if cmd.sortMode == Schema.SortTime && left.ok && right.ok &&
            SelectedSecondsCore(cmd, left.status) != SelectedSecondsCore(cmd, right.status) then
      SelectedSecondsCore(cmd, left.status) > SelectedSecondsCore(cmd, right.status)
    else if cmd.sortMode == Schema.SortTime && left.ok && right.ok &&
            SelectedNanosecondsCore(cmd, left.status) != SelectedNanosecondsCore(cmd, right.status) then
      SelectedNanosecondsCore(cmd, left.status) > SelectedNanosecondsCore(cmd, right.status)
    else
      StringLessCore(left.displayName, right.displayName)
  }

  opaque function EntryBeforeCore(
    cmd: Schema.LsCmd,
    left: Spec.EntryObservation,
    right: Spec.EntryObservation
  ): bool
  {
    if cmd.reverse then BaseEntryBeforeCore(cmd, right, left)
    else BaseEntryBeforeCore(cmd, left, right)
  }

  opaque function InsertSortedCore(
    cmd: Schema.LsCmd,
    entry: Spec.EntryObservation,
    sorted: seq<Spec.EntryObservation>
  ): seq<Spec.EntryObservation>
    decreases |sorted|
  {
    if |sorted| == 0 then [entry]
    else if EntryBeforeCore(cmd, entry, sorted[0]) then [entry] + sorted
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

  opaque function OperandBeforeCore(
    cmd: Schema.LsCmd,
    left: Spec.OperandObservation,
    right: Spec.OperandObservation
  ): bool
  {
    if left.operandClass != right.operandClass then
      Spec.OperandClassRank(left.operandClass) <
      Spec.OperandClassRank(right.operandClass)
    else
      EntryBeforeCore(cmd, Spec.OperandAsEntry(left), Spec.OperandAsEntry(right))
  }

  opaque function InsertOperandSortedCore(
    cmd: Schema.LsCmd,
    observation: Spec.OperandObservation,
    sorted: seq<Spec.OperandObservation>
  ): seq<Spec.OperandObservation>
    decreases |sorted|
  {
    if |sorted| == 0 then [observation]
    else if OperandBeforeCore(cmd, observation, sorted[0]) then
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

  function BodiesAtPositionsCore(
    sorted: seq<Spec.OperandObservation>, positions: seq<nat>
  ): BenchWorld.Bytes
    requires forall k: nat :: k < |positions| ==> positions[k] < |sorted|
  {
    BodiesAtPositionsPrefixCore(sorted, positions, |positions|)
  }

  function BodiesFragmentsPrefixCore(
    sorted: seq<Spec.OperandObservation>, positions: seq<nat>, processed: nat
  ): seq<BenchWorld.Bytes>
    requires processed <= |positions|
    requires forall k: nat :: k < |positions| ==> positions[k] < |sorted|
    ensures |BodiesFragmentsPrefixCore(sorted, positions, processed)| == processed
    ensures forall k: nat :: k < processed ==>
                               BodiesFragmentsPrefixCore(sorted, positions, processed)[k] ==
                               sorted[positions[k]].body
    decreases processed
  {
    if processed == 0 then []
    else (BodiesFragmentsPrefixCore(sorted, positions, processed - 1) +
          [sorted[positions[processed - 1]].body])
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
    sorted: seq<Spec.OperandObservation>, positions: seq<nat>, processed: nat
  ): BenchWorld.Bytes
    requires processed <= |positions|
    requires forall k: nat :: k < |positions| ==> positions[k] < |sorted|
    decreases processed
  {
    if processed == 0 then []
    else (BodiesAtPositionsPrefixCore(sorted, positions, processed - 1) +
          sorted[positions[processed - 1]].body)
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

  function OutputGroupsCore(
    sorted: seq<Spec.OperandObservation>
  ): seq<Spec.OutputGroup>
  {
    var directPositions := DirectPositionsCore(sorted, 0);
    var directoryPositions := DirectoryPositionsCore(sorted, 0);
    (if |directPositions| == 0 then []
     else [Spec.OutputGroup(
             OperandIndicesPrefixCore(sorted, directPositions, |directPositions|),
             BodiesAtPositionsCore(sorted, directPositions), false)]) +
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

  ghost predicate ObservationPiecesSummary(
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
       then RenderEntryCore(cmd, observations[i].renderName, observations[i].status)
       else []) &&
      errorFragments[i] ==
      (if observations[i].ok
       then []
       else Spec.AccessErrorMessageSpec(observations[i].displayName, observations[i].err))
  }

  ghost predicate DirectoryListingSummary(
    cmd: Schema.LsCmd,
    fs: BenchWorld.FileSystem,
    path: BenchWorld.Path,
    observations: seq<Spec.EntryObservation>,
    readErr: int,
    output: BenchWorld.Bytes,
    errors: BenchWorld.Bytes,
    hadError: bool
  )
  {
    exists rawObservations: seq<Spec.EntryObservation>,
      outputFragments: seq<BenchWorld.Bytes>, outputCuts: seq<nat>,
      errorFragments: seq<BenchWorld.Bytes>, errorCuts: seq<nat>,
      entryOutput: BenchWorld.Bytes, entryErrors: BenchWorld.Bytes ::
      Spec.DirectoryObservationRelation(cmd, fs, path, readErr == 0, rawObservations) &&
      observations == SortEntriesCore(cmd, rawObservations) &&
      ObservationPiecesSummary(cmd, observations, outputFragments, errorFragments) &&
      Spec.FragmentsConcatenate(outputFragments, entryOutput, outputCuts) &&
      output == TotalLineCore(cmd, rawObservations) + entryOutput &&
      Spec.FragmentsConcatenate(errorFragments, entryErrors, errorCuts) &&
      errors == entryErrors +
      (if readErr == 0 then [] else Spec.ReadDirectoryErrorMessageSpec(path, readErr)) &&
      hadError == (readErr != 0 ||
                   exists i: nat :: i < |observations| && !observations[i].ok)
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
          (if processed - 1 in children
           then "\n" + children[processed - 1].output
           else []))
  }

  function RecursiveChildErrorPrefixCore(
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

  ghost predicate RecursiveDirectorySummary(
    cmd: Schema.LsCmd,
    fs: BenchWorld.FileSystem,
    displayPath: BenchWorld.Path,
    accessPath: BenchWorld.Path,
    ancestors: set<BenchWorld.HostInodeKey>,
    tree: Spec.RecursiveWitness
  )
    decreases tree
  {
    DirectoryListingSummary(
      cmd, fs, accessPath, tree.observations, tree.readErr,
      tree.listingOutput, tree.listingErrors, tree.listingHadError) &&
    tree.children.Keys !! tree.cycles &&
    (forall i: nat :: i in tree.cycles ==> i < |tree.observations|) &&
    (forall i: nat :: i < |tree.observations| ==>
                        var observation := tree.observations[i];
                        var eligible := observation.ok &&
                                        observation.status.kind == BenchWorld.DirectoryKind &&
                                        observation.displayName != "." && observation.displayName != "..";
                        (i in tree.cycles <==> eligible && observation.status.hostKey in ancestors) &&
                        (i in tree.children <==> eligible && observation.status.hostKey !in ancestors)) &&
    (forall i: nat :: i in tree.children ==>
                        i < |tree.observations| &&
                        RecursiveDirectorySummary(
                          cmd, fs,
                          Spec.ChildDisplayPath(displayPath, tree.observations[i].displayName),
                          tree.observations[i].accessPath,
                          ancestors + {tree.observations[i].status.hostKey},
                          tree.children[i])) &&
    tree.output == displayPath + ":\n" + tree.listingOutput +
    RecursiveChildOutputPrefixCore(
      tree.observations, tree.children, |tree.observations|) &&
    tree.errors == tree.listingErrors + RecursiveChildErrorPrefixCore(
      displayPath, tree.observations, tree.children, tree.cycles, |tree.observations|) &&
    tree.hadError ==
    (tree.listingHadError || |tree.cycles| > 0 ||
     exists i: nat :: i in tree.children && tree.children[i].hadError)
  }

  ghost opaque predicate OperandObservationSummary(
    cmd: Schema.LsCmd,
    fs: BenchWorld.FileSystem,
    cwd: BenchWorld.Path,
    observation: Spec.OperandObservation
  )
  {
    observation.index < |cmd.operands| &&
    observation.operand == cmd.operands[observation.index] &&
    observation.path == Spec.MakeAbsoluteSpec(cwd, observation.operand) &&
    observation.sectionAvailable ==
    (observation.operandClass == Spec.ExpandedDirectory &&
     IOContract.OpenDirFailureErrFields(fs, observation.path) == 0) &&
    match Spec.OperandStatusResultSpec(cmd, fs, observation.path)
    case Err(error) =>
      !observation.ok &&
      observation.err == IOContract.IOErrorErrno(error) &&
      observation.operandClass == Spec.AccessFailure &&
      observation.body == [] &&
      observation.accessErrors == Spec.AccessErrorMessageSpec(
        observation.operand, observation.err) &&
      observation.sectionErrors == [] && observation.failed
    case Ok(status) =>
      observation.ok && observation.status == status && observation.err == 0 &&
      observation.accessErrors == [] &&
      if status.kind == BenchWorld.DirectoryKind && !cmd.listDirectories then
        observation.operandClass == Spec.ExpandedDirectory &&
        if observation.sectionAvailable then
          if cmd.recursive then
            exists tree: Spec.RecursiveWitness ::
              RecursiveDirectorySummary(
                cmd, fs, observation.operand, observation.path,
                {status.hostKey}, tree) &&
              observation.body == tree.output &&
              observation.sectionErrors == tree.errors &&
              observation.failed == tree.hadError
          else
            exists entries: seq<Spec.EntryObservation>, readErr: int,
              listingOutput: BenchWorld.Bytes ::
              DirectoryListingSummary(
                cmd, fs, observation.path, entries, readErr,
                listingOutput, observation.sectionErrors, observation.failed) &&
              observation.body ==
              (if |cmd.operands| > 1
               then observation.operand + ":\n"
               else []) + listingOutput
        else
          observation.body == [] &&
          observation.sectionErrors == Spec.ReadDirectoryErrorMessageSpec(
            observation.path,
            IOContract.OpenDirFailureErrFields(fs, observation.path)) &&
          observation.failed
      else
        observation.operandClass == Spec.DirectOperand &&
        !observation.sectionAvailable &&
        observation.body == RenderEntryCore(
          cmd,
          Spec.RenderNameSpec(
            fs, observation.operand, observation.path,
            Spec.ExplicitCommandLineFollowSpec(cmd), cmd.numericLong, status),
          status) &&
        observation.sectionErrors == [] && !observation.failed
  }

  ghost predicate RunSummary(
    cmd: Schema.LsCmd,
    fs: BenchWorld.FileSystem,
    cwd: BenchWorld.Path,
    output: BenchWorld.Bytes,
    errors: BenchWorld.Bytes,
    exit: int
  )
  {
    exists observations: seq<Spec.OperandObservation>,
      sorted: seq<Spec.OperandObservation>, groups: seq<Spec.OutputGroup> ::
      |observations| == |cmd.operands| &&
      (forall i: nat | i < |observations| ::
         observations[i].index == i &&
         OperandObservationSummary(cmd, fs, cwd, observations[i])) &&
      sorted == SortOperandsCore(cmd, observations) &&
      groups == OutputGroupsCore(sorted) &&
      output == JoinOutputGroupsCore(groups) &&
      errors == AccessErrorsCore(observations) + SectionErrorsCore(sorted) &&
      exit == (if exists i: nat ::
                    i < |observations| && observations[i].failed then 2 else 0)
  }

  opaque twostate predicate CoreSummary(raw: Schema.LsCmdRaw, io: BenchIO.IO, exit: int)
    reads io.fsRegion, io.cwdRegion, io.envRegion, io.nowRegion, io.stdoutRegion, io.stderrRegion
  {
    var cmd := Spec.EffectiveCommandSpec(raw, old(io.env()), old(io.now()));
    if cmd.mode == Schema.ModeHelp then
      io.stdout() == old(io.stdout()) + Spec.HelpTextSpec() &&
      io.stderr() == old(io.stderr()) &&
      exit == 0
    else if cmd.mode == Schema.ModeVersion then
      io.stdout() == old(io.stdout()) + Spec.VersionTextSpec() &&
      io.stderr() == old(io.stderr()) &&
      exit == 0
    else if cmd.mode != Schema.ModeRun then
      io.stdout() == old(io.stdout()) &&
      io.stderr() == old(io.stderr()) + Spec.InvalidModeMessageSpec(cmd.mode) &&
      exit == (if cmd.mode.ModeInvalidTime? then 1 else 2)
    else
      exists output: BenchWorld.Bytes, errors: BenchWorld.Bytes ::
        RunSummary(cmd, old(io.fs()), old(io.cwd()), output, errors, exit) &&
        io.stdout() == old(io.stdout()) + output &&
        io.stderr() == old(io.stderr()) + errors
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

  method ObservePath(
    cmd: Schema.LsCmd,
    displayName: string,
    path: BenchWorld.Path,
    followSymlink: bool,
    io: BenchIO.IO
  ) returns (
      observation: Spec.EntryObservation,
      output: BenchWorld.Bytes,
      errors: BenchWorld.Bytes,
      hadError: bool
    )
    ensures Spec.MetadataObservationRelation(old(io.fs()), observation)
    ensures output ==
            (if observation.ok then RenderEntryCore(cmd, observation.renderName, observation.status) else [])
    ensures errors ==
            (if observation.ok then [] else Spec.AccessErrorMessageSpec(displayName, observation.err))
    ensures hadError == !observation.ok
    ensures observation.displayName == displayName
    ensures observation.accessPath == path
    ensures observation.followSymlink == followSymlink
  {
    ghost var preFs := io.fs();
    var ok, status, err := io.GetFileStatus(path, followSymlink);
    var renderName := displayName;
    if ok && status.kind == BenchWorld.SymlinkKind && !followSymlink && cmd.numericLong {
      var linkResult := io.ReadLink(path);
      match linkResult
      case Ok(target) => renderName := displayName + " -> " + target;
      case Err(_) =>
    }
    observation := Spec.EntryObservation(
      displayName, renderName, path, followSymlink, ok, status, err);
    if ok {
      output := RenderEntryCore(cmd, renderName, status);
      errors := [];
      hadError := false;
    } else {
      output := [];
      errors := Spec.AccessErrorMessageSpec(displayName, err);
      hadError := true;
    }
    reveal IOContract.GetFileStatusContractFields();
    reveal Spec.MetadataObservationRelation();
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
    requires ObservationPiecesSummary(cmd, observations, outputFragments, errorFragments)
    requires Spec.FragmentsConcatenate(outputFragments, output, outputCuts)
    requires Spec.FragmentsConcatenate(errorFragments, errors, errorCuts)
    requires piece ==
             (if observation.ok then RenderEntryCore(cmd, observation.renderName, observation.status) else [])
    requires errorPiece ==
             (if observation.ok then [] else Spec.AccessErrorMessageSpec(observation.displayName, observation.err))
    ensures observations2 == observations + [observation]
    ensures ObservationPiecesSummary(cmd, observations2, outputFragments2, errorFragments2)
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

  ghost opaque predicate DotCoverage(
    cmd: Schema.LsCmd,
    observations: seq<Spec.EntryObservation>
  )
  {
    cmd.hiddenMode == Schema.All ==>
      (exists i: nat :: i < |observations| && observations[i].displayName == ".") &&
      (exists i: nat :: i < |observations| && observations[i].displayName == "..")
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

  lemma DotCoverageInit(cmd: Schema.LsCmd, observations: seq<Spec.EntryObservation>)
    requires cmd.hiddenMode == Schema.All ==>
               (exists i: nat :: i < |observations| && observations[i].displayName == ".") &&
               (exists i: nat :: i < |observations| && observations[i].displayName == "..")
    ensures DotCoverage(cmd, observations)
  {
    reveal DotCoverage();
  }

  lemma DotCoveragePrefix(
    cmd: Schema.LsCmd,
    before: seq<Spec.EntryObservation>,
    after: seq<Spec.EntryObservation>
  )
    requires DotCoverage(cmd, before)
    requires |before| <= |after|
    requires after[..|before|] == before
    ensures DotCoverage(cmd, after)
  {
    reveal DotCoverage();
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

  lemma CompleteDirectoryObservations(
    cmd: Schema.LsCmd,
    fs: BenchWorld.FileSystem,
    path: BenchWorld.Path,
    resolved: BenchWorld.Path,
    expected: set<BenchWorld.DirEntry>,
    observations: seq<Spec.EntryObservation>
  )
    requires IOContract.ResolvePathForMetadataFields(fs, path, true) == BenchWorld.Ok(resolved)
    requires BenchWorld.FsContainsPath(fs, resolved)
    requires expected == IOContract.DirectoryEntriesForPathFields(fs, resolved)
    requires Spec.DistinctDisplayNames(observations)
    requires forall i: nat :: i < |observations| ==>
                                Spec.DirectorySourceRelation(cmd, fs, path, observations[i])
    requires DotCoverage(cmd, observations)
    requires ProcessedCoverage(cmd, expected, {}, observations)
    ensures Spec.DirectoryObservationRelation(cmd, fs, path, true, observations)
  {
    reveal Spec.DirectoryObservationRelation();
    reveal DotCoverage();
    reveal ProcessedCoverage();
  }

  method RenderObservationSequence(
    cmd: Schema.LsCmd,
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
    ensures ObservationPiecesSummary(cmd, observations, outputFragments, errorFragments)
    ensures Spec.FragmentsConcatenate(outputFragments, output, outputCuts)
    ensures Spec.FragmentsConcatenate(errorFragments, errors, errorCuts)
    ensures hadError ==
            (exists i: nat :: i < |observations| && !observations[i].ok)
  {
    output := [];
    errors := [];
    hadError := false;
    outputFragments := [];
    outputCuts := [0];
    errorFragments := [];
    errorCuts := [0];
    var i := 0;
    while i < |observations|
      invariant 0 <= i <= |observations|
      invariant |outputFragments| == i
      invariant |errorFragments| == i
      invariant ObservationPiecesSummary(
                  cmd, observations[..i], outputFragments, errorFragments)
      invariant Spec.FragmentsConcatenate(outputFragments, output, outputCuts)
      invariant Spec.FragmentsConcatenate(errorFragments, errors, errorCuts)
      invariant hadError ==
                (exists j: nat :: j < i && !observations[j].ok)
      decreases |observations| - i
    {
      var observation := observations[i];
      assert (exists j: nat :: j < i + 1 && !observations[j].ok) ==
             (hadError || !observation.ok) by {
        if exists j: nat :: j < i + 1 && !observations[j].ok {
          var j: nat :| j < i + 1 && !observations[j].ok;
          if j < i {
            assert exists k: nat :: k < i && !observations[k].ok;
          }
        }
        if hadError {
          var j: nat :| j < i && !observations[j].ok;
          assert j < i + 1 && !observations[j].ok;
        } else if !observation.ok {
          assert i < i + 1 && !observations[i].ok;
        }
      }
      var piece := if observation.ok
      then RenderEntryCore(cmd, observation.renderName, observation.status)
      else [];
      var errorPiece := if observation.ok
      then []
      else Spec.AccessErrorMessageSpec(observation.displayName, observation.err);
      AppendFragment(outputFragments, output, outputCuts, piece);
      AppendFragment(errorFragments, errors, errorCuts, errorPiece);
      outputFragments := outputFragments + [piece];
      outputCuts := outputCuts + [|output + piece|];
      output := output + piece;
      errorFragments := errorFragments + [errorPiece];
      errorCuts := errorCuts + [|errors + errorPiece|];
      errors := errors + errorPiece;
      hadError := hadError || !observation.ok;
      i := i + 1;
      assert observations[..i] == observations[..i - 1] + [observations[i - 1]];
    }
  }

  method {:vcs_split_on_every_assert} ReadDirectoryCore(
    cmd: Schema.LsCmd,
    path: BenchWorld.Path,
    io: BenchIO.IO
  ) returns (
      observations: seq<Spec.EntryObservation>,
      readErr: int,
      wasOpened: bool,
      output: BenchWorld.Bytes,
      errors: BenchWorld.Bytes,
      hadError: bool
    )
    modifies io.dirHandlesRegion
    ensures DirectoryListingSummary(
              cmd, old(io.fs()), path, observations, readErr, output, errors, hadError)
    ensures wasOpened == (IOContract.OpenDirFailureErrFields(old(io.fs()), path) == 0)
    ensures !wasOpened ==>
              observations == [] &&
              readErr == IOContract.OpenDirFailureErrFields(old(io.fs()), path) &&
              errors == Spec.ReadDirectoryErrorMessageSpec(path, readErr) && hadError
    decreases *
  {
    ghost var preFs := io.fs();
    observations := [];
    readErr := 0;
    wasOpened := false;
    output := [];
    errors := [];
    hadError := false;
    var outputFragments: seq<BenchWorld.Bytes> := [];
    var outputCuts: seq<nat> := [0];
    var errorFragments: seq<BenchWorld.Bytes> := [];
    var errorCuts: seq<nat> := [0];
    assert ObservationPiecesSummary(cmd, observations, outputFragments, errorFragments);
    assert Spec.FragmentsConcatenate(outputFragments, output, outputCuts);
    assert Spec.FragmentsConcatenate(errorFragments, errors, errorCuts);
    DistinctEmpty();

    var openOk, handle, openErr := io.OpenDir(path);
    reveal IOContract.OpenDirContractFields();
    if !openOk {
      readErr := openErr;
      output := TotalLineCore(cmd, []);
      errors := Spec.ReadDirectoryErrorMessageSpec(path, readErr);
      hadError := true;
      assert Spec.DirectoryObservationRelation(cmd, preFs, path, false, observations);
      assert observations == SortEntriesCore(cmd, []) by {
        reveal SortEntriesCore();
      }
      assert DirectoryListingSummary(cmd, preFs, path, observations, readErr, output, errors, hadError);
      return;
    }
    wasOpened := true;
    ghost var expected := io.dirHandles()[handle].remaining;
    ghost var resolved: BenchWorld.Path :|
      IOContract.ResolvePathForMetadataFields(preFs, path, true) == BenchWorld.Ok(resolved);
    assert BenchWorld.FsContainsPath(preFs, resolved);
    assert expected == IOContract.DirectoryEntriesForPathFields(preFs, resolved);

    if cmd.hiddenMode == Schema.All {
      var beforeDot := observations;
      var current := BenchWorld.AppendPath(path, ".");
      var dot, dotOut, dotErr, dotFailed := ObservePath(
        cmd, ".", current,
        cmd.followMode == Schema.FollowAlways && Spec.EntryMetadataRequiredSpec(cmd), io);
      observations, outputFragments, outputCuts, output,
      errorFragments, errorCuts, errors :=
        AddObservation(
          cmd, dot, dotOut, dotErr, observations,
          outputFragments, outputCuts, output,
          errorFragments, errorCuts, errors);
      DistinctSnoc(beforeDot, dot);
      hadError := hadError || dotFailed;
      assert Spec.DirectorySourceRelation(cmd, preFs, path, dot);
      var parent := BenchWorld.AppendPath(path, "..");
      var beforeDotdot := observations;
      var dotdot, dotdotOut, dotdotErr, dotdotFailed := ObservePath(
        cmd, "..", parent,
        cmd.followMode == Schema.FollowAlways && Spec.EntryMetadataRequiredSpec(cmd), io);
      observations, outputFragments, outputCuts, output,
      errorFragments, errorCuts, errors :=
        AddObservation(
          cmd, dotdot, dotdotOut, dotdotErr, observations,
          outputFragments, outputCuts, output,
          errorFragments, errorCuts, errors);
      assert !(exists i: nat ::
                 i < |beforeDotdot| && beforeDotdot[i].displayName == "..");
      DistinctSnoc(beforeDotdot, dotdot);
      hadError := hadError || dotdotFailed;
      assert Spec.DirectorySourceRelation(cmd, preFs, path, dotdot);
    }

    var finished := false;
    assert Spec.DistinctDisplayNames(observations);
    assert cmd.hiddenMode == Schema.All ==>
        (exists i: nat :: i < |observations| && observations[i].displayName == ".") &&
        (exists i: nat :: i < |observations| && observations[i].displayName == "..");
    DotCoverageInit(cmd, observations);
    ProcessedCoverageInit(cmd, expected, observations);
    while !finished
      invariant handle in io.dirHandles()
      invariant io.dirHandles()[handle].remaining <= expected
      invariant finished ==> io.dirHandles()[handle].remaining == {}
      invariant ObservationPiecesSummary(cmd, observations, outputFragments, errorFragments)
      invariant Spec.FragmentsConcatenate(outputFragments, output, outputCuts)
      invariant Spec.FragmentsConcatenate(errorFragments, errors, errorCuts)
      invariant forall i: nat :: i < |observations| ==>
                                   Spec.DirectorySourceRelation(cmd, preFs, path, observations[i])
      invariant Spec.DistinctDisplayNames(observations)
      invariant DotCoverage(cmd, observations)
      invariant ProcessedCoverage(
                  cmd, expected, io.dirHandles()[handle].remaining, observations)
      invariant readErr == 0
      decreases *
    {
      ghost var beforeHandles := io.dirHandles();
      ghost var beforeRemaining := io.dirHandles()[handle].remaining;
      ghost var beforeObservations := observations;
      ghost var visibleCovered := false;
      ghost var visibleIndex: nat := 0;
      var hasMore, name, isDir, isSymlink, err := io.ReadDir(handle);
      reveal IOContract.ReadDirContractFields();
      if err != 0 {
        readErr := err;
        finished := true;
        io.CloseDir(handle);
        var rawObservations := observations;
        assert Spec.DirectoryObservationRelation(cmd, preFs, path, false, rawObservations);
        observations := SortEntriesCore(cmd, rawObservations);
        var entryErrors: BenchWorld.Bytes;
        var renderedHadError: bool;
        ghost var renderedOutputs: seq<BenchWorld.Bytes>;
        ghost var renderedOutputCuts: seq<nat>;
        ghost var renderedErrors: seq<BenchWorld.Bytes>;
        ghost var renderedErrorCuts: seq<nat>;
        output, entryErrors, renderedHadError,
        renderedOutputs, renderedOutputCuts,
        renderedErrors, renderedErrorCuts :=
          RenderObservationSequence(cmd, observations);
        var entryOutput := output;
        output := TotalLineCore(cmd, rawObservations) + entryOutput;
        errors := entryErrors + Spec.ReadDirectoryErrorMessageSpec(path, readErr);
        hadError := true;
        assert DirectoryListingSummary(cmd, preFs, path, observations, readErr, output, errors, hadError);
        return;
      }
      if !hasMore {
        assert io.dirHandles()[handle].remaining == {};
        finished := true;
      } else if Spec.VisibleNameSpec(cmd, name) {
        var alreadyObserved := ContainsDisplayName(observations, name);
        if alreadyObserved {
          visibleIndex :| visibleIndex < |observations| &&
                          observations[visibleIndex].displayName == name;
          visibleCovered := true;
        } else {
          var beforeObservation := observations;
          var childPath := BenchWorld.AppendPath(path, name);
          var observation, piece, errorPiece, failed := ObservePath(
            cmd, name, childPath,
            cmd.followMode == Schema.FollowAlways && Spec.EntryMetadataRequiredSpec(cmd), io);
          observations, outputFragments, outputCuts, output,
          errorFragments, errorCuts, errors :=
            AddObservation(
              cmd, observation, piece, errorPiece, observations,
              outputFragments, outputCuts, output,
              errorFragments, errorCuts, errors);
          DistinctSnoc(beforeObservation, observation);
          hadError := hadError || failed;
          assert Spec.DirectorySourceRelation(cmd, preFs, path, observation);
          assert observation.displayName == name;
          visibleIndex := |beforeObservation|;
          assert observations[visibleIndex] == observation;
          visibleCovered := true;
        }
      }
      if hasMore {
        ghost var entry := BenchWorld.DirEntry(name, isDir, isSymlink);
        assert entry in beforeRemaining;
        assert io.dirHandles()[handle].remaining == beforeRemaining - {entry};
        assert |beforeObservations| <= |observations|;
        assert observations[..|beforeObservations|] == beforeObservations;
        if Spec.VisibleNameSpec(cmd, name) {
          assert visibleCovered;
          assert visibleIndex < |observations| &&
                 observations[visibleIndex].displayName == name;
        }
        DotCoveragePrefix(cmd, beforeObservations, observations);
        ProcessedCoverageRemove(
          cmd, expected, beforeRemaining, entry, beforeObservations, observations);
      }
    }
    assert io.dirHandles()[handle].remaining == {};
    var rawObservations := observations;
    CompleteDirectoryObservations(
      cmd, preFs, path, resolved, expected, rawObservations);
    io.CloseDir(handle);
    observations := SortEntriesCore(cmd, rawObservations);
    ghost var renderedOutputs: seq<BenchWorld.Bytes>;
    ghost var renderedOutputCuts: seq<nat>;
    ghost var renderedErrors: seq<BenchWorld.Bytes>;
    ghost var renderedErrorCuts: seq<nat>;
    output, errors, hadError,
    renderedOutputs, renderedOutputCuts,
    renderedErrors, renderedErrorCuts :=
      RenderObservationSequence(cmd, observations);
    var entryOutput := output;
    output := TotalLineCore(cmd, rawObservations) + entryOutput;
    assert DirectoryListingSummary(cmd, preFs, path, observations, readErr, output, errors, hadError);
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
    children.Keys !! cycles &&
    (forall j: nat :: j < i ==>
                        var observation := observations[j];
                        var eligible := observation.ok &&
                                        observation.status.kind == BenchWorld.DirectoryKind &&
                                        observation.displayName != "." && observation.displayName != "..";
                        (j in cycles <==> eligible && observation.status.hostKey in ancestors) &&
                        (j in children <==> eligible && observation.status.hostKey !in ancestors)) &&
    (forall j: nat :: j in children ==>
                        j < |observations| &&
                        RecursiveDirectorySummary(
                          cmd, fs,
                          Spec.ChildDisplayPath(displayPath, observations[j].displayName),
                          observations[j].accessPath,
                          ancestors + {observations[j].status.hostKey}, children[j])) &&
    output == displayPath + ":\n" + listing +
    RecursiveChildOutputPrefixCore(observations, children, i) &&
    errors == listingErrors + RecursiveChildErrorPrefixCore(
      displayPath, observations, children, cycles, i) &&
    hadError ==
    (listingHadError || |cycles| > 0 ||
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
    ancestors: set<BenchWorld.HostInodeKey>, tree: Spec.RecursiveWitness
  )
    requires DirectoryListingSummary(
               cmd, fs, accessPath, tree.observations, tree.readErr,
               tree.listingOutput, tree.listingErrors, tree.listingHadError)
    requires RecursivePrefixSummary(
               cmd, fs, displayPath, ancestors, tree.observations, tree.listingOutput,
               tree.listingErrors, tree.listingHadError, |tree.observations|,
               tree.children, tree.cycles, tree.output, tree.errors, tree.hadError)
    ensures RecursiveDirectorySummary(
              cmd, fs, displayPath, accessPath, ancestors, tree)
  {
    reveal RecursivePrefixSummary(
           cmd, fs, displayPath, ancestors, tree.observations, tree.listingOutput,
           tree.listingErrors, tree.listingHadError, |tree.observations|,
           tree.children, tree.cycles, tree.output, tree.errors, tree.hadError);
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
                                (k in left ==> left[k].output == right[k].output)
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
    requires beforeOutput == displayPath + ":\n" + listing +
                             RecursiveChildOutputPrefixCore(observations, beforeChildren, i)
    requires afterChildren == beforeChildren ||
             (i in afterChildren && afterChildren == beforeChildren[i := afterChildren[i]])
    requires piece ==
             (if i in afterChildren then "\n" + afterChildren[i].output else [])
    ensures beforeOutput + piece == displayPath + ":\n" + listing +
                                    RecursiveChildOutputPrefixCore(observations, afterChildren, i + 1)
  {
    assert forall k: nat :: k < i ==>
                              (k in beforeChildren <==> k in afterChildren) &&
                              (k in beforeChildren ==> beforeChildren[k].output == afterChildren[k].output) by {
      forall k: nat | k < i
        ensures (k in beforeChildren <==> k in afterChildren) &&
                (k in beforeChildren ==> beforeChildren[k].output == afterChildren[k].output)
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

  method {:vcs_split_on_every_assert} WalkDirectoryRecursive(
    cmd: Schema.LsCmd,
    displayPath: BenchWorld.Path,
    accessPath: BenchWorld.Path,
    ancestors: set<BenchWorld.HostInodeKey>,
    io: BenchIO.IO
  ) returns (
      wasOpened: bool,
      output: BenchWorld.Bytes,
      errors: BenchWorld.Bytes,
      hadError: bool,
      ghost tree: Spec.RecursiveWitness
    )
    modifies io.dirHandlesRegion
    ensures RecursiveDirectorySummary(
              cmd, old(io.fs()), displayPath, accessPath, ancestors, tree)
    ensures wasOpened ==
            (IOContract.OpenDirFailureErrFields(old(io.fs()), accessPath) == 0)
    ensures !wasOpened ==>
              errors == Spec.ReadDirectoryErrorMessageSpec(
                accessPath, IOContract.OpenDirFailureErrFields(old(io.fs()), accessPath)) &&
              hadError
    ensures output == tree.output && errors == tree.errors && hadError == tree.hadError
    decreases *
  {
    ghost var preFs := io.fs();
    var observations: seq<Spec.EntryObservation>;
    var readErr: int;
    var listing: BenchWorld.Bytes;
    var listingErrors: BenchWorld.Bytes;
    var listingHadError: bool;
    observations, readErr, wasOpened, listing, listingErrors, listingHadError :=
      ReadDirectoryCore(cmd, accessPath, io);
    errors := listingErrors;
    hadError := listingHadError;
    output := displayPath + ":\n" + listing;
    ghost var children: map<nat, Spec.RecursiveWitness> := map[];
    ghost var cycles: set<nat> := {};
    var i := 0;
    assert RecursivePrefixSummary(
        cmd, preFs, displayPath, ancestors, observations, listing,
        listingErrors, listingHadError, i, children, cycles,
        output, errors, hadError) by {
      reveal RecursivePrefixSummary(
             cmd, preFs, displayPath, ancestors, observations, listing,
             listingErrors, listingHadError, i, children, cycles,
             output, errors, hadError);
    }
    while i < |observations|
      invariant 0 <= i <= |observations|
      invariant !wasOpened ==>
                  observations == [] && i == 0 && errors == listingErrors &&
                  hadError == listingHadError
      invariant RecursivePrefixSummary(
                  cmd, preFs, displayPath, ancestors, observations, listing,
                  listingErrors, listingHadError, i, children, cycles,
                  output, errors, hadError)
      decreases *
    {
      reveal RecursivePrefixSummary(
             cmd, preFs, displayPath, ancestors, observations, listing,
             listingErrors, listingHadError, i, children, cycles,
             output, errors, hadError);
      ghost var beforeChildren := children;
      ghost var beforeCycles := cycles;
      var beforeOutput := output;
      var beforeErrors := errors;
      var beforeHadError := hadError;
      assert beforeOutput == displayPath + ":\n" + listing +
                             RecursiveChildOutputPrefixCore(observations, beforeChildren, i);
      assert beforeErrors == listingErrors + RecursiveChildErrorPrefixCore(
                               displayPath, observations, beforeChildren, beforeCycles, i);
      assert beforeHadError ==
             (listingHadError || |beforeCycles| > 0 ||
              exists j: nat :: j in beforeChildren && beforeChildren[j].hadError);
      RecursivePrefixRanges(
        cmd, preFs, displayPath, ancestors, observations, listing,
        listingErrors, listingHadError, i, children, cycles,
        output, errors, hadError);
      var observation := observations[i];
      var outputPiece: BenchWorld.Bytes := [];
      var errorPiece: BenchWorld.Bytes := [];
      var stepFailed := false;
      ghost var addedChild := false;
      ghost var addedCycle := false;
      if observation.ok &&
         observation.status.kind == BenchWorld.DirectoryKind &&
         observation.displayName != "." && observation.displayName != ".."
      {
        var childDisplay := if displayPath == "." then "./" + observation.displayName
        else displayPath + "/" + observation.displayName;
        if observation.status.hostKey in ancestors {
          errorPiece := Spec.RecursiveCycleMessageSpec(childDisplay);
          cycles := cycles + {i};
          stepFailed := true;
          addedCycle := true;
        } else {
          var descendantOutput: BenchWorld.Bytes;
          var descendantErrors: BenchWorld.Bytes;
          var childFailed: bool;
          ghost var childTree: Spec.RecursiveWitness;
          var childOpened: bool;
          childOpened, descendantOutput, descendantErrors, childFailed, childTree := WalkDirectoryRecursive(
            cmd,
            childDisplay,
            observation.accessPath,
            ancestors + {observation.status.hostKey},
            io
          );
          outputPiece := "\n" + descendantOutput;
          errorPiece := descendantErrors;
          children := children[i := childTree];
          stepFailed := childFailed;
          addedChild := true;
        }
      }
      output := output + outputPiece;
      errors := errors + errorPiece;
      hadError := hadError || stepFailed;
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
      assert children.Keys !! cycles;
      assert forall j: nat :: j < i + 1 ==>
                                var candidate := observations[j];
                                var eligible := candidate.ok &&
                                                candidate.status.kind == BenchWorld.DirectoryKind &&
                                                candidate.displayName != "." && candidate.displayName != "..";
                                (j in cycles <==> eligible && candidate.status.hostKey in ancestors) &&
                                (j in children <==> eligible && candidate.status.hostKey !in ancestors) by {
        forall j: nat | j < i + 1
          ensures
            var candidate := observations[j];
            var eligible := candidate.ok &&
                            candidate.status.kind == BenchWorld.DirectoryKind &&
                            candidate.displayName != "." && candidate.displayName != "..";
            (j in cycles <==> eligible && candidate.status.hostKey in ancestors) &&
            (j in children <==> eligible && candidate.status.hostKey !in ancestors)
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
                                  cmd, preFs,
                                  Spec.ChildDisplayPath(displayPath, observations[j].displayName),
                                  observations[j].accessPath,
                                  ancestors + {observations[j].status.hostKey}, children[j]) by {
        forall j: nat | j in children
          ensures j < |observations| &&
                  RecursiveDirectorySummary(
                    cmd, preFs,
                    Spec.ChildDisplayPath(displayPath, observations[j].displayName),
                    observations[j].accessPath,
                    ancestors + {observations[j].status.hostKey}, children[j])
        {
          if j != i {
            assert j in beforeChildren;
          }
        }
      }
      assert outputPiece ==
             (if i in children then "\n" + children[i].output else []);
      RecursiveOutputSnoc(
        displayPath, listing, observations, beforeChildren, children, i,
        beforeOutput, outputPiece);
      assert output == beforeOutput + outputPiece;
      assert errorPiece ==
             (if i in cycles then
                Spec.RecursiveCycleMessageSpec(
                  Spec.ChildDisplayPath(displayPath, observations[i].displayName))
              else if i in children then children[i].errors else []);
      RecursiveErrorSnoc(
        displayPath, listingErrors, observations, beforeChildren, beforeCycles,
        children, cycles, i, beforeErrors, errorPiece);
      assert errors == beforeErrors + errorPiece;
      assert hadError ==
             (listingHadError || |cycles| > 0 ||
              exists j: nat :: j in children && children[j].hadError) by {
        if addedChild {
          assert i in children;
          assert children == beforeChildren[i := children[i]];
          assert stepFailed == children[i].hadError;
          FailedChildAfterUpdate(beforeChildren, i, children[i]);
        } else if addedCycle {
          assert cycles == beforeCycles + {i};
          assert |cycles| > 0;
        } else {
          assert children == beforeChildren;
          assert cycles == beforeCycles;
          assert !stepFailed;
        }
      }
      i := i + 1;
      assert RecursivePrefixSummary(
          cmd, preFs, displayPath, ancestors, observations, listing,
          listingErrors, listingHadError, i, children, cycles,
          output, errors, hadError) by {
        reveal RecursivePrefixSummary(
               cmd, preFs, displayPath, ancestors, observations, listing,
               listingErrors, listingHadError, i, children, cycles,
               output, errors, hadError);
      }
    }
    reveal RecursivePrefixSummary(
           cmd, preFs, displayPath, ancestors, observations, listing,
           listingErrors, listingHadError, i, children, cycles,
           output, errors, hadError);
    tree := Spec.RecursiveWitness(
      observations, readErr, listing, listingErrors, listingHadError,
      children, cycles, output, errors, hadError);
    RecursivePrefixComplete(
      cmd, preFs, displayPath, accessPath, ancestors, tree);
  }

  method {:vcs_split_on_every_assert} ObserveOperand(
    index: nat,
    cmd: Schema.LsCmd,
    cwd: BenchWorld.Path,
    io: BenchIO.IO
  ) returns (observation: Spec.OperandObservation)
    requires index < |cmd.operands|
    modifies io.dirHandlesRegion
    ensures observation.index == index
    ensures OperandObservationSummary(cmd, old(io.fs()), cwd, observation)
    decreases *
  {
    ghost var preFs := io.fs();
    var operand := cmd.operands[index];
    var path := if BenchWorld.IsAbsolutePath(operand)
    then BenchWorld.NormalizePath(operand)
    else BenchWorld.NormalizePath(BenchWorld.AppendPath(cwd, operand));
    var follow := Spec.ExplicitCommandLineFollowSpec(cmd);
    var ok, status, err := io.GetFileStatus(path, follow);
    reveal IOContract.GetFileStatusContractFields();
    if ok && Spec.ImplicitDirectoryFollowSpec(cmd) &&
       status.kind == BenchWorld.SymlinkKind {
      var targetOk, targetStatus, targetErr := io.GetFileStatus(path, true);
      reveal IOContract.GetFileStatusContractFields();
      if targetOk && targetStatus.kind == BenchWorld.DirectoryKind {
        status := targetStatus;
      }
    }
    assert match Spec.OperandStatusResultSpec(cmd, preFs, path)
           case Ok(expected) => ok && status == expected && err == 0
           case Err(error) => !ok && err == IOContract.IOErrorErrno(error) by {
      reveal IOContract.GetFileStatusContractFields();
    }
    if !ok {
      observation := Spec.OperandObservation(
        index, operand, path, false, status, err, Spec.AccessFailure,
        false, [], Spec.AccessErrorMessageSpec(operand, err), [], true);
      assert OperandObservationSummary(cmd, preFs, cwd, observation) by {
        reveal OperandObservationSummary();
      }
    } else if status.kind == BenchWorld.DirectoryKind && !cmd.listDirectories {
      var wasOpened: bool;
      var body: BenchWorld.Bytes;
      var sectionErrors: BenchWorld.Bytes;
      var failed: bool;
      if cmd.recursive {
        ghost var recursiveTree: Spec.RecursiveWitness;
        wasOpened, body, sectionErrors, failed, recursiveTree := WalkDirectoryRecursive(
          cmd, operand, path, {status.hostKey}, io);
        observation := Spec.OperandObservation(
          index, operand, path, true, status, 0, Spec.ExpandedDirectory,
          wasOpened, if wasOpened then body else [], [], sectionErrors, failed);
        assert OperandObservationSummary(cmd, preFs, cwd, observation) by {
          reveal OperandObservationSummary();
        }
      } else {
        var observations: seq<Spec.EntryObservation>;
        var readErr: int;
        var listingOutput: BenchWorld.Bytes;
        observations, readErr, wasOpened, listingOutput, sectionErrors, failed :=
          ReadDirectoryCore(cmd, path, io);
        body := listingOutput;
        if |cmd.operands| > 1 {
          body := operand + ":\n" + body;
        }
        observation := Spec.OperandObservation(
          index, operand, path, true, status, 0, Spec.ExpandedDirectory,
          wasOpened, if wasOpened then body else [], [], sectionErrors, failed);
        if wasOpened {
          assert observation.body ==
                 (if |cmd.operands| > 1 then operand + ":\n" else []) + listingOutput by {
            assert observation.body == body;
            if |cmd.operands| > 1 {
            } else {
            }
          }
          assert exists entries: seq<Spec.EntryObservation>,
              listingReadErr: int,
              rendered: BenchWorld.Bytes ::
              DirectoryListingSummary(
                cmd, preFs, path, entries, listingReadErr,
                rendered, observation.sectionErrors, observation.failed) &&
              observation.body ==
              (if |cmd.operands| > 1 then operand + ":\n" else []) + rendered by {
            assert DirectoryListingSummary(
                cmd, preFs, path, observations, readErr,
                listingOutput, sectionErrors, failed);
          }
        }
        assert OperandObservationSummary(cmd, preFs, cwd, observation) by {
          assert Spec.OperandStatusResultSpec(cmd, preFs, path) == BenchWorld.Ok(status);
          assert observation.sectionAvailable == wasOpened;
          assert wasOpened ==
                 (IOContract.OpenDirFailureErrFields(preFs, path) == 0);
          reveal OperandObservationSummary();
          if wasOpened {
            assert exists entries: seq<Spec.EntryObservation>,
                listingReadErr: int,
                rendered: BenchWorld.Bytes ::
                DirectoryListingSummary(
                  cmd, preFs, path, entries, listingReadErr,
                  rendered, observation.sectionErrors, observation.failed) &&
                observation.body ==
                (if |cmd.operands| > 1 then operand + ":\n" else []) + rendered;
          } else {
            assert observation.body == [];
            assert observation.sectionErrors == Spec.ReadDirectoryErrorMessageSpec(
                                                  path, IOContract.OpenDirFailureErrFields(preFs, path));
            assert observation.failed;
          }
        }
      }
    } else {
      var renderName := operand;
      if status.kind == BenchWorld.SymlinkKind && !follow && cmd.numericLong {
        var linkResult := io.ReadLink(path);
        match linkResult
        case Ok(target) => renderName := operand + " -> " + target;
        case Err(_) =>
      }
      observation := Spec.OperandObservation(
        index, operand, path, true, status, 0, Spec.DirectOperand,
        false, RenderEntryCore(cmd, renderName, status), [], [], false);
      assert OperandObservationSummary(cmd, preFs, cwd, observation) by {
        reveal OperandObservationSummary();
      }
    }
  }

  function PositiveEnvironmentResult(result: BenchWorld.Result<string>): nat
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

  method {:vcs_split_on_every_assert} RunCore(raw: Schema.LsCmdRaw, io: BenchIO.IO) returns (exit: int)
    modifies io.stdoutRegion, io.stderrRegion, io.dirHandlesRegion
    ensures CoreSummary(raw, io, exit)
    decreases *
  {
    ghost var preFs := io.fs();
    ghost var preCwd := io.cwd();
    ghost var preEnv := io.env();
    ghost var preNow := io.now();
    ghost var preStdout := io.stdout();
    ghost var preStderr := io.stderr();
    var parsedCmd := Schema.Command(raw);
    var cmd := parsedCmd;
    if parsedCmd.mode == Schema.ModeHelp {
      io.AppendStdout(Spec.HelpTextSpec());
      exit := 0;
      assert CoreSummary(raw, io, exit) by {
        reveal CoreSummary();
      }
      return;
    }
    if parsedCmd.mode == Schema.ModeVersion {
      io.AppendStdout(Spec.VersionTextSpec());
      exit := 0;
      assert CoreSummary(raw, io, exit) by {
        reveal CoreSummary();
      }
      return;
    }
    if parsedCmd.mode != Schema.ModeRun {
      io.AppendStderr(Spec.InvalidModeMessageSpec(parsedCmd.mode));
      exit := if parsedCmd.mode.ModeInvalidTime? then 1 else 2;
      assert CoreSummary(raw, io, exit) by {
        reveal CoreSummary();
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

    var cwd := io.GetCwd();
    var output: BenchWorld.Bytes := [];
    var errors: BenchWorld.Bytes := [];
    var hadError := false;
    var observations: seq<Spec.OperandObservation> := [];
    var i := 0;
    while i < |cmd.operands|
      invariant 0 <= i <= |cmd.operands|
      invariant io.stdout() == preStdout
      invariant io.stderr() == preStderr
      invariant cwd == preCwd
      invariant |observations| == i
      invariant forall j: nat :: j < i ==>
                                   observations[j].index == j &&
                                   OperandObservationSummary(cmd, preFs, preCwd, observations[j])
      invariant output == []
      invariant errors == []
      invariant hadError ==
                (exists j: nat :: j < i && observations[j].failed)
      decreases |cmd.operands| - i
    {
      var observation := ObserveOperand(i, cmd, cwd, io);
      ghost var beforeObservations := observations;
      FailedOperandSnoc(beforeObservations, observation);
      observations := observations + [observation];
      hadError := hadError || observation.failed;
      assert observations[i] == observation;
      i := i + 1;
    }
    var sorted := SortOperandsCore(cmd, observations);
    var groups := OutputGroupsCore(sorted);
    output := JoinOutputGroupsCore(groups);
    errors := AccessErrorsCore(observations) + SectionErrorsCore(sorted);
    io.AppendStdout(output);
    io.AppendStderr(errors);
    exit := if hadError then 2 else 0;
    assert CoreSummary(raw, io, exit) by {
      reveal CoreSummary();
    }
  }
}
