include "../../core/World.dfy"
include "../../core/IO.dfy"
include "../../core/IOContract.dfy"
include "LsSchema.dfy"
include "LsTime.dfy"

module LsSpec {
  import BenchIO
  import Utf8 = Utf8Semantics
  import BenchWorld
  import IOContract
  import Schema = LsSchema
  import Time = LsTime

  datatype EntryObservation = EntryObservation(
    displayName: string,
    renderName: string,
    accessPath: BenchWorld.Path,
    followSymlink: bool,
    ok: bool,
    status: BenchWorld.FileStatus,
    err: int
  )

  datatype OperandClass = AccessFailure | DirectOperand | ExpandedDirectory

  datatype OperandObservation = OperandObservation(
    index: nat,
    operand: BenchWorld.Path,
    path: BenchWorld.Path,
    ok: bool,
    status: BenchWorld.FileStatus,
    err: int,
    operandClass: OperandClass,
    sectionAvailable: bool,
    body: BenchWorld.Bytes,
    accessErrors: BenchWorld.Bytes,
    sectionErrors: BenchWorld.Bytes,
    failed: bool
  )

  datatype OutputGroup = OutputGroup(
    indices: seq<nat>,
    body: BenchWorld.Bytes,
    isDirectoryBundle: bool
  )

  datatype RecursiveWitness = RecursiveWitness(
    observations: seq<EntryObservation>,
    readErr: int,
    listingOutput: BenchWorld.Bytes,
    listingErrors: BenchWorld.Bytes,
    listingHadError: bool,
    children: map<nat, RecursiveWitness>,
    cycles: set<nat>,
    output: BenchWorld.Bytes,
    errors: BenchWorld.Bytes,
    hadError: bool
  )

  function HelpTextSpec(): BenchWorld.Bytes
  {
    "Usage: ls [OPTION]... [FILE]...\n"
    + "List information about FILEs (the current directory by default).\n"
    + "\n"
    + "  -a, --all             do not ignore entries starting with .\n"
    + "  -A, --almost-all      do not list implied . and ..\n"
    + "  -d, --directory       list directories themselves, not their contents\n"
    + "  -n, --numeric-uid-gid use numeric user and group IDs in a long listing\n"
    + "  -s, --size            print the allocated size of each file, in blocks\n"
    + "      --block-size=SIZE scale sizes by the positive integer SIZE\n"
    + "  -S                    sort by apparent file size, largest first\n"
    + "  -t                    sort by the selected time, newest first\n"
    + "  -r, --reverse         reverse the complete sort order\n"
    + "  -u                    select access time\n"
    + "  -c                    select status-change time\n"
    + "      --time=WORD       select atime, ctime, or mtime\n"
    + "      --time-style=STYLE select the numeric-long timestamp style\n"
    + "  -H, --dereference-command-line follow command-line symbolic links\n"
    + "  -L, --dereference     follow symbolic links while listing\n"
    + "  -R, --recursive       list subdirectories recursively\n"
    + "      --help            display this help and exit\n"
    + "      --version         output version information and exit\n"
    + "\n"
    + "This benchmark prints one entry per line. Numeric long listings support\n"
    + "UTC default, full-iso, long-iso, iso, and +%s timestamp styles. Columns,\n"
    + "colors, human-readable sizes, and locale collation are outside this slice.\n"
    + "\n"
    + "Report bugs to: bug-coreutils@gnu.org\n"
    + "GNU coreutils home page: <https://www.gnu.org/software/coreutils/>\n"
    + "Full documentation <https://www.gnu.org/software/coreutils/ls>\n"
    + "or available locally via: info '(coreutils) ls invocation'\n"
  }

  function VersionTextSpec(): BenchWorld.Bytes
  {
    "ls (GNU coreutils) 9.10.13-2cf49\n"
    + "Copyright (C) 2026 Free Software Foundation, Inc.\n"
    + "License GPLv3+: GNU GPL version 3 or later <https://gnu.org/licenses/gpl.html>.\n"
    + "This is free software: you are free to change and redistribute it.\n"
    + "There is NO WARRANTY, to the extent permitted by law.\n"
    + "\n"
    + "Written by Richard M. Stallman and David MacKenzie.\n"
  }

  function ErrnoTextSpec(err: int): string
  {
    if err == 2 then "No such file or directory"
    else if err == 13 then "Permission denied"
    else if err == 20 then "Not a directory"
    else if err == 40 then "Too many levels of symbolic links"
    else "I/O error"
  }

  function AccessErrorMessageSpec(path: BenchWorld.Path, err: int): BenchWorld.Bytes
  {
    "ls: cannot access '" + path + "': " + ErrnoTextSpec(err) + "\n"
  }

  function ReadDirectoryErrorMessageSpec(path: BenchWorld.Path, err: int): BenchWorld.Bytes
  {
    "ls: reading directory '" + path + "': " + ErrnoTextSpec(err) + "\n"
  }

  function InvalidModeMessageSpec(mode: Schema.LsMode): BenchWorld.Bytes
  {
    match mode
    case ModeInvalidBlockSize(value) =>
      "ls: invalid --block-size argument '" + value + "'\n"
    case ModeInvalidTime(value) =>
      "ls: invalid argument '" + value + "' for '--time'\n" +
      "Valid arguments are:\n" +
      "  - 'atime', 'access', 'use'\n" +
      "  - 'ctime', 'status'\n" +
      "  - 'mtime', 'modification'\n" +
      "Try 'ls --help' for more information.\n"
    case ModeInvalidTimeStyle(value) =>
      "ls: invalid argument '" + value + "' for 'time style'\n" +
      "Valid arguments are:\n" +
      "  - [posix-]full-iso\n" +
      "  - [posix-]long-iso\n" +
      "  - [posix-]iso\n" +
      "  - [posix-]locale\n" +
      "  - +FORMAT (e.g., +%H:%M) for a 'date'-style format\n" +
      "Try 'ls --help' for more information.\n"
    case _ => []
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
  }

  function NatTextSpec(n: nat): string
    decreases n
  {
    if n < 10 then [DigitChar(n)]
    else NatTextSpec(n / 10) + [DigitChar(n % 10)]
  }

  function IntTextSpec(n: int): string
  {
    if n < 0 then "-" + NatTextSpec((-n) as nat) else NatTextSpec(n as nat)
  }

  function ParsedPositiveOrZeroSpec(text: string): nat
  {
    match Schema.ParsePositive(text)
    case PositiveNat(value) => value
    case InvalidPositiveNat => 0
  }

  function EnvironmentBlockSizeSpec(env: map<string, string>): nat
  {
    if "LS_BLOCK_SIZE" in env && ParsedPositiveOrZeroSpec(env["LS_BLOCK_SIZE"]) > 0 then
      ParsedPositiveOrZeroSpec(env["LS_BLOCK_SIZE"])
    else if "BLOCK_SIZE" in env && ParsedPositiveOrZeroSpec(env["BLOCK_SIZE"]) > 0 then
      ParsedPositiveOrZeroSpec(env["BLOCK_SIZE"])
    else if "BLOCKSIZE" in env && ParsedPositiveOrZeroSpec(env["BLOCKSIZE"]) > 0 then
      ParsedPositiveOrZeroSpec(env["BLOCKSIZE"])
    else
      1024
  }

  function EnvironmentFileSizeBlockSizeSpec(env: map<string, string>): nat
  {
    if "LS_BLOCK_SIZE" in env && ParsedPositiveOrZeroSpec(env["LS_BLOCK_SIZE"]) > 0 then
      ParsedPositiveOrZeroSpec(env["LS_BLOCK_SIZE"])
    else if "BLOCK_SIZE" in env && ParsedPositiveOrZeroSpec(env["BLOCK_SIZE"]) > 0 then
      ParsedPositiveOrZeroSpec(env["BLOCK_SIZE"])
    else
      1
  }

  function EffectiveCommandSpec(
    raw: Schema.LsCmdRaw, env: map<string, string>, referenceNow: int
  ): Schema.LsCmd
  {
    var cmd := Schema.Command(raw);
    Schema.WithReferenceNow(Schema.WithBlockSize(
                              cmd,
                              if cmd.cliBlockSize > 0 then cmd.cliBlockSize else EnvironmentBlockSizeSpec(env),
                              if cmd.cliBlockSize > 0 then cmd.cliBlockSize
                              else EnvironmentFileSizeBlockSizeSpec(env)
                            ), referenceNow)
  }

  function DisplayedBlocksSpec(blocks512: nat, blockSize: nat): nat
  {
    if blockSize == 0 then 0 else (blocks512 * 512 + blockSize - 1) / blockSize
  }

  function DisplayedFileSizeSpec(size: nat, blockSize: nat): nat
  {
    if blockSize == 0 then 0 else (size + blockSize - 1) / blockSize
  }

  function HasModeBitSpec(mode: bv32, bit: bv32): bool
  {
    (mode & bit) != 0 as bv32
  }

  function PermissionCharSpec(mode: bv32, bit: bv32, present: char): char
  {
    if HasModeBitSpec(mode, bit) then present else '-'
  }

  function ExecuteCharSpec(
    mode: bv32,
    executeBit: bv32,
    specialBit: bv32,
    specialExecute: char,
    specialNoExecute: char
  ): char
  {
    if HasModeBitSpec(mode, specialBit) then
      if HasModeBitSpec(mode, executeBit) then specialExecute else specialNoExecute
    else
      PermissionCharSpec(mode, executeBit, 'x')
  }

  function KindCharSpec(kind: BenchWorld.FileKind): char
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

  function ModeTextSpec(status: BenchWorld.FileStatus): string
  {
    [KindCharSpec(status.kind),
     PermissionCharSpec(status.mode, 256 as bv32, 'r'),
     PermissionCharSpec(status.mode, 128 as bv32, 'w'),
     ExecuteCharSpec(status.mode, 64 as bv32, 2048 as bv32, 's', 'S'),
     PermissionCharSpec(status.mode, 32 as bv32, 'r'),
     PermissionCharSpec(status.mode, 16 as bv32, 'w'),
     ExecuteCharSpec(status.mode, 8 as bv32, 1024 as bv32, 's', 'S'),
     PermissionCharSpec(status.mode, 4 as bv32, 'r'),
     PermissionCharSpec(status.mode, 2 as bv32, 'w'),
     ExecuteCharSpec(status.mode, 1 as bv32, 512 as bv32, 't', 'T')]
  }

  function RenderEntrySpec(
    cmd: Schema.LsCmd,
    displayName: string,
    status: BenchWorld.FileStatus
  ): BenchWorld.Bytes
  {
    var blockPrefix := if cmd.showBlocks then
                         NatTextSpec(DisplayedBlocksSpec(status.storage.allocatedBlocks, cmd.cliBlockSize)) + " "
                       else "";
    Utf8.Encode(blockPrefix + if !cmd.numericLong then
      displayName + "\n"
    else
      ModeTextSpec(status) + " " +
      NatTextSpec(status.linkCount) + " " +
      NatTextSpec(status.ownership.uid) + " " +
      NatTextSpec(status.ownership.gid) + " " +
      NatTextSpec(DisplayedFileSizeSpec(
                    status.storage.size, cmd.fileSizeBlockSize)) + " " +
      TimeTextSpec(cmd, SelectedSecondsSpec(cmd, status),
                   SelectedNanosecondsSpec(cmd, status)) + " " +
      displayName + "\n")
  }

  function TimeTextSpec(cmd: Schema.LsCmd, seconds: int, nanoseconds: int): string
  {
    match cmd.timeStyle
    case EpochSeconds => IntTextSpec(seconds)
    case FullIso => Time.FullIso(seconds, nanoseconds)
    case LongIso => Time.LongIso(seconds)
    case Iso => Time.Iso(seconds, nanoseconds, cmd.referenceNow)
    case DefaultC => Time.DefaultC(seconds, nanoseconds, cmd.referenceNow)
  }

  function AllocatedBlocksSumSpec(observations: seq<EntryObservation>): nat
    decreases |observations|
  {
    if |observations| == 0 then 0
    else
      (if observations[0].ok then observations[0].status.storage.allocatedBlocks else 0) +
      AllocatedBlocksSumSpec(observations[1..])
  }

  function TotalLineSpec(cmd: Schema.LsCmd, observations: seq<EntryObservation>): BenchWorld.Bytes
  {
    if cmd.numericLong || cmd.showBlocks then
      Utf8.Encode("total " + NatTextSpec(
        DisplayedBlocksSpec(AllocatedBlocksSumSpec(observations), cmd.cliBlockSize)) + "\n")
    else
      []
  }

  function MakeAbsoluteSpec(cwd: BenchWorld.Path, path: BenchWorld.Path): BenchWorld.Path
  {
    if BenchWorld.IsAbsolutePath(path) then BenchWorld.NormalizePath(path)
    else BenchWorld.NormalizePath(BenchWorld.AppendPath(cwd, path))
  }

  function VisibleNameSpec(cmd: Schema.LsCmd, name: string): bool
  {
    if name == "." || name == ".." then cmd.hiddenMode == Schema.All
    else cmd.hiddenMode != Schema.HideDotFiles || |name| == 0 || name[0] != '.'
  }

  function ExplicitCommandLineFollowSpec(cmd: Schema.LsCmd): bool
  {
    cmd.followMode == Schema.FollowAlways ||
    cmd.followMode == Schema.FollowCommandLine
  }

  function EntryMetadataRequiredSpec(cmd: Schema.LsCmd): bool
  {
    cmd.numericLong || cmd.showBlocks ||
    cmd.sortMode != Schema.SortName || cmd.recursive
  }

  function ImplicitDirectoryFollowSpec(cmd: Schema.LsCmd): bool
  {
    cmd.followMode == Schema.FollowNever &&
    !cmd.numericLong && !cmd.listDirectories
  }

  function OperandStatusResultSpec(
    cmd: Schema.LsCmd,
    fs: BenchWorld.FileSystem,
    path: BenchWorld.Path
  ): BenchWorld.Result<BenchWorld.FileStatus>
  {
    if ExplicitCommandLineFollowSpec(cmd) then
      IOContract.GetFileStatusResultFields(fs, path, true)
    else
      match IOContract.GetFileStatusResultFields(fs, path, false)
      case Err(error) => BenchWorld.Err(error)
      case Ok(status) =>
        if !ImplicitDirectoryFollowSpec(cmd) ||
           status.kind != BenchWorld.SymlinkKind then
          BenchWorld.Ok(status)
        else
          match IOContract.GetFileStatusResultFields(fs, path, true)
          case Ok(targetStatus) =>
            if targetStatus.kind == BenchWorld.DirectoryKind then
              BenchWorld.Ok(targetStatus)
            else
              BenchWorld.Ok(status)
          case Err(_) => BenchWorld.Ok(status)
  }

  function RenderNameSpec(
    fs: BenchWorld.FileSystem,
    displayName: string,
    path: BenchWorld.Path,
    followSymlink: bool,
    showTarget: bool,
    status: BenchWorld.FileStatus
  ): string
  {
    if status.kind != BenchWorld.SymlinkKind || followSymlink || !showTarget then displayName
    else
      match IOContract.ReadLinkResultFields(fs, path)
      case Ok(target) => displayName + " -> " + target
      case Err(_) => displayName
  }

  opaque function StringLessSpec(left: string, right: string): bool
    decreases |left|
  {
    if |left| == 0 then |right| > 0
    else if |right| == 0 then false
    else if left[0] == right[0] then StringLessSpec(left[1..], right[1..])
    else left[0] < right[0]
  }

  function SelectedSecondsSpec(cmd: Schema.LsCmd, status: BenchWorld.FileStatus): int
  {
    match cmd.timeField
    case ModificationTime => status.times.mtimeSec
    case AccessTime => status.times.atimeSec
    case ChangeTime => status.times.ctimeSec
  }

  function SelectedNanosecondsSpec(cmd: Schema.LsCmd, status: BenchWorld.FileStatus): int
  {
    match cmd.timeField
    case ModificationTime => status.times.mtimeNsec
    case AccessTime => status.times.atimeNsec
    case ChangeTime => status.times.ctimeNsec
  }

  opaque function BaseEntryBeforeSpec(
    cmd: Schema.LsCmd,
    left: EntryObservation,
    right: EntryObservation
  ): bool
  {
    if left.ok != right.ok then left.ok
    else if !left.ok then StringLessSpec(left.displayName, right.displayName)
    else if cmd.sortMode == Schema.SortSize &&
            left.status.storage.size != right.status.storage.size then
      left.status.storage.size > right.status.storage.size
    else if cmd.sortMode == Schema.SortTime && left.ok && right.ok &&
            SelectedSecondsSpec(cmd, left.status) != SelectedSecondsSpec(cmd, right.status) then
      SelectedSecondsSpec(cmd, left.status) > SelectedSecondsSpec(cmd, right.status)
    else if cmd.sortMode == Schema.SortTime && left.ok && right.ok &&
            SelectedNanosecondsSpec(cmd, left.status) != SelectedNanosecondsSpec(cmd, right.status) then
      SelectedNanosecondsSpec(cmd, left.status) > SelectedNanosecondsSpec(cmd, right.status)
    else
      StringLessSpec(left.displayName, right.displayName)
  }

  opaque function EntryBeforeSpec(
    cmd: Schema.LsCmd,
    left: EntryObservation,
    right: EntryObservation
  ): bool
  {
    if cmd.reverse then BaseEntryBeforeSpec(cmd, right, left)
    else BaseEntryBeforeSpec(cmd, left, right)
  }

  ghost predicate EntriesOrderedRelation(cmd: Schema.LsCmd, entries: seq<EntryObservation>)
  {
    forall i: nat, j: nat | i < j < |entries| ::
      !EntryBeforeSpec(cmd, entries[j], entries[i])
  }

  ghost predicate EntrySortingRelation(
    cmd: Schema.LsCmd,
    input: seq<EntryObservation>,
    output: seq<EntryObservation>
  )
  {
    multiset(output) == multiset(input) && EntriesOrderedRelation(cmd, output)
  }

  ghost opaque predicate MetadataObservationRelation(
    fs: BenchWorld.FileSystem,
    observation: EntryObservation
  )
  {
    match IOContract.GetFileStatusResultFields(
        fs, observation.accessPath, observation.followSymlink)
    case Ok(expected) =>
      observation.ok && observation.status == expected && observation.err == 0
    case Err(error) =>
      !observation.ok && observation.err == IOContract.IOErrorErrno(error) &&
      observation.renderName == observation.displayName
  }

  ghost predicate DirectorySourceRelation(
    cmd: Schema.LsCmd,
    fs: BenchWorld.FileSystem,
    path: BenchWorld.Path,
    observation: EntryObservation
  )
  {
    MetadataObservationRelation(fs, observation) &&
    observation.followSymlink ==
    (cmd.followMode == Schema.FollowAlways && EntryMetadataRequiredSpec(cmd)) &&
    VisibleNameSpec(cmd, observation.displayName) &&
    ((cmd.hiddenMode == Schema.All && observation.displayName == "." &&
      observation.accessPath == BenchWorld.AppendPath(path, ".")) ||
     (cmd.hiddenMode == Schema.All && observation.displayName == ".." &&
      observation.accessPath == BenchWorld.AppendPath(path, "..")) ||
     (observation.accessPath == BenchWorld.AppendPath(path, observation.displayName) &&
      exists resolved: BenchWorld.Path, entry: BenchWorld.DirEntry ::
        IOContract.ResolvePathForMetadataFields(fs, path, true) == BenchWorld.Ok(resolved) &&
        BenchWorld.FsContainsPath(fs, resolved) &&
        entry in IOContract.DirectoryEntriesForPathFields(fs, resolved) &&
        entry.name == observation.displayName))
  }

  ghost opaque predicate DistinctDisplayNames(observations: seq<EntryObservation>)
    decreases |observations|
  {
    |observations| == 0 ||
    (DistinctDisplayNames(observations[..|observations| - 1]) &&
     forall i: nat :: i < |observations| - 1 ==>
                        observations[i].displayName != observations[|observations| - 1].displayName)
  }

  ghost predicate DirectoryObservationRelation(
    cmd: Schema.LsCmd,
    fs: BenchWorld.FileSystem,
    path: BenchWorld.Path,
    complete: bool,
    observations: seq<EntryObservation>
  )
  {
    DistinctDisplayNames(observations) &&
    (forall i: nat :: i < |observations| ==>
                        DirectorySourceRelation(cmd, fs, path, observations[i])) &&
    (complete ==>
       (cmd.hiddenMode == Schema.All ==>
          (exists i: nat :: i < |observations| && observations[i].displayName == ".") &&
          (exists i: nat :: i < |observations| && observations[i].displayName == "..")) &&
       match IOContract.ResolvePathForMetadataFields(fs, path, true)
       case Err(_) => true
       case Ok(resolved) =>
         BenchWorld.FsContainsPath(fs, resolved) ==>
           forall entry: BenchWorld.DirEntry ::
             entry in IOContract.DirectoryEntriesForPathFields(fs, resolved) &&
             VisibleNameSpec(cmd, entry.name) ==>
               exists i: nat ::
                 i < |observations| && observations[i].displayName == entry.name)
  }

  ghost predicate FragmentsConcatenate(
    fragments: seq<BenchWorld.Bytes>,
    combined: BenchWorld.Bytes,
    cuts: seq<nat>
  )
  {
    |cuts| == |fragments| + 1 &&
    cuts[0] == 0 &&
    cuts[|cuts| - 1] == |combined| &&
    forall i: nat {:trigger cuts[i]} | i < |fragments| ::
      cuts[i] <= cuts[i + 1] <= |combined| &&
      cuts[i + 1] == cuts[i] + |fragments[i]| &&
      combined[cuts[i]..cuts[i + 1]] == fragments[i]
  }

  ghost predicate ObservationPiecesRelation(
    cmd: Schema.LsCmd,
    observations: seq<EntryObservation>,
    outputFragments: seq<BenchWorld.Bytes>,
    errorFragments: seq<BenchWorld.Bytes>
  )
  {
    |outputFragments| == |observations| &&
    |errorFragments| == |observations| &&
    forall i: nat | i < |observations| ::
      outputFragments[i] ==
      (if observations[i].ok
       then RenderEntrySpec(cmd, observations[i].renderName, observations[i].status)
       else []) &&
      errorFragments[i] ==
      (if observations[i].ok
       then []
       else AccessErrorMessageSpec(observations[i].displayName, observations[i].err))
  }

  ghost predicate DirectoryListingRelation(
    cmd: Schema.LsCmd,
    fs: BenchWorld.FileSystem,
    path: BenchWorld.Path,
    observations: seq<EntryObservation>,
    readErr: int,
    output: BenchWorld.Bytes,
    errors: BenchWorld.Bytes,
    hadError: bool
  )
  {
    exists rawObservations: seq<EntryObservation>,
      outputFragments: seq<BenchWorld.Bytes>, outputCuts: seq<nat>,
      errorFragments: seq<BenchWorld.Bytes>, errorCuts: seq<nat>,
      entryOutput: BenchWorld.Bytes, entryErrors: BenchWorld.Bytes ::
      DirectoryObservationRelation(cmd, fs, path, readErr == 0, rawObservations) &&
      EntrySortingRelation(cmd, rawObservations, observations) &&
      ObservationPiecesRelation(cmd, observations, outputFragments, errorFragments) &&
      FragmentsConcatenate(outputFragments, entryOutput, outputCuts) &&
      output == TotalLineSpec(cmd, rawObservations) + entryOutput &&
      FragmentsConcatenate(errorFragments, entryErrors, errorCuts) &&
      errors == entryErrors +
      (if readErr == 0 then [] else ReadDirectoryErrorMessageSpec(path, readErr)) &&
      hadError == (readErr != 0 ||
                   exists i: nat :: i < |observations| && !observations[i].ok)
  }

  function ChildDisplayPath(displayPath: BenchWorld.Path, name: string): BenchWorld.Path
  {
    if displayPath == "." then "./" + name else displayPath + "/" + name
  }

  function RecursiveCycleMessageSpec(displayPath: BenchWorld.Path): BenchWorld.Bytes
  {
    "ls: " + displayPath + ": not listing already-listed directory\n"
  }

  function RecursiveOutputFragments(tree: RecursiveWitness): seq<BenchWorld.Bytes>
  {
    seq(|tree.observations|, i requires i < |tree.observations| =>
      if i in tree.children then "\n" + tree.children[i].output else [])
  }

  function RecursiveErrorFragments(
    displayPath: BenchWorld.Path, tree: RecursiveWitness
  ): seq<BenchWorld.Bytes>
  {
    seq(|tree.observations|, i requires i < |tree.observations| =>
      if i in tree.cycles then
        RecursiveCycleMessageSpec(
          ChildDisplayPath(displayPath, tree.observations[i].displayName))
      else if i in tree.children then tree.children[i].errors
      else [])
  }

  ghost predicate RecursiveDirectoryRelation(
    cmd: Schema.LsCmd,
    fs: BenchWorld.FileSystem,
    displayPath: BenchWorld.Path,
    accessPath: BenchWorld.Path,
    ancestors: set<BenchWorld.HostInodeKey>,
    tree: RecursiveWitness
  )
    decreases tree
  {
    DirectoryListingRelation(
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
                        RecursiveDirectoryRelation(
                          cmd, fs,
                          ChildDisplayPath(displayPath, tree.observations[i].displayName),
                          tree.observations[i].accessPath,
                          ancestors + {tree.observations[i].status.hostKey},
                          tree.children[i])) &&
    (exists outputCuts: seq<nat>, errorCuts: seq<nat>,
       childOutput: BenchWorld.Bytes, childErrors: BenchWorld.Bytes ::
       FragmentsConcatenate(RecursiveOutputFragments(tree), childOutput, outputCuts) &&
       FragmentsConcatenate(
         RecursiveErrorFragments(displayPath, tree), childErrors, errorCuts) &&
       tree.output == displayPath + ":\n" + tree.listingOutput + childOutput &&
       tree.errors == tree.listingErrors + childErrors) &&
    tree.hadError ==
    (tree.listingHadError || |tree.cycles| > 0 ||
     exists i: nat :: i in tree.children && tree.children[i].hadError)
  }

  function OperandAsEntry(observation: OperandObservation): EntryObservation
  {
    EntryObservation(
      observation.operand, observation.operand, observation.path, false,
      observation.ok, observation.status, observation.err)
  }

  function OperandClassRank(kind: OperandClass): nat
  {
    match kind
    case DirectOperand => 0
    case ExpandedDirectory => 1
    case AccessFailure => 2
  }

  opaque function OperandBeforeSpec(
    cmd: Schema.LsCmd, left: OperandObservation, right: OperandObservation
  ): bool
  {
    if left.operandClass != right.operandClass then
      OperandClassRank(left.operandClass) < OperandClassRank(right.operandClass)
    else
      EntryBeforeSpec(cmd, OperandAsEntry(left), OperandAsEntry(right))
  }

  ghost predicate OperandSortingRelation(
    cmd: Schema.LsCmd,
    input: seq<OperandObservation>,
    output: seq<OperandObservation>
  )
  {
    multiset(output) == multiset(input) &&
    OperandObservationsOrdered(cmd, output)
  }

  ghost predicate OperandObservationsOrdered(
    cmd: Schema.LsCmd, observations: seq<OperandObservation>
  )
  {
    forall i: nat, j: nat | i < j < |observations| ::
      !OperandBeforeSpec(cmd, observations[j], observations[i])
  }

  ghost predicate OperandObservationRelation(
    cmd: Schema.LsCmd,
    fs: BenchWorld.FileSystem,
    cwd: BenchWorld.Path,
    observation: OperandObservation
  )
  {
    observation.index < |cmd.operands| &&
    observation.operand == cmd.operands[observation.index] &&
    observation.path == MakeAbsoluteSpec(cwd, observation.operand) &&
    observation.sectionAvailable ==
    (observation.operandClass == ExpandedDirectory &&
     IOContract.OpenDirFailureErrFields(fs, observation.path) == 0) &&
    match OperandStatusResultSpec(cmd, fs, observation.path)
    case Err(error) =>
      !observation.ok &&
      observation.err == IOContract.IOErrorErrno(error) &&
      observation.operandClass == AccessFailure &&
      observation.body == [] &&
      observation.accessErrors == AccessErrorMessageSpec(
        observation.operand, observation.err) &&
      observation.sectionErrors == [] && observation.failed
    case Ok(status) =>
      observation.ok && observation.status == status && observation.err == 0 &&
      observation.accessErrors == [] &&
      if status.kind == BenchWorld.DirectoryKind && !cmd.listDirectories then
        observation.operandClass == ExpandedDirectory &&
        if observation.sectionAvailable then
          if cmd.recursive then
            exists tree: RecursiveWitness ::
              RecursiveDirectoryRelation(
                cmd, fs, observation.operand, observation.path,
                {status.hostKey}, tree) &&
              observation.body == tree.output &&
              observation.sectionErrors == tree.errors &&
              observation.failed == tree.hadError
          else
            exists entries: seq<EntryObservation>, readErr: int,
              listingOutput: BenchWorld.Bytes ::
              DirectoryListingRelation(
                cmd, fs, observation.path, entries, readErr,
                listingOutput, observation.sectionErrors, observation.failed) &&
              observation.body ==
              (if |cmd.operands| > 1
               then observation.operand + ":\n"
               else []) + listingOutput
        else
          observation.body == [] &&
          observation.sectionErrors == ReadDirectoryErrorMessageSpec(
            observation.path,
            IOContract.OpenDirFailureErrFields(fs, observation.path)) &&
          observation.failed
      else
        observation.operandClass == DirectOperand &&
        !observation.sectionAvailable &&
        observation.body == RenderEntrySpec(
          cmd,
          RenderNameSpec(
            fs, observation.operand, observation.path,
            ExplicitCommandLineFollowSpec(cmd), cmd.numericLong, status),
          status) &&
        observation.sectionErrors == [] && !observation.failed
  }

  ghost predicate DirectPositionRelation(
    sorted: seq<OperandObservation>, positions: seq<nat>
  )
  {
    (forall k: nat :: k < |positions| ==> positions[k] < |sorted|) &&
    (forall k: nat :: k + 1 < |positions| ==> positions[k] < positions[k + 1]) &&
    (forall i: nat :: i < |sorted| ==>
                        (sorted[i].operandClass == DirectOperand <==>
                         exists k: nat :: k < |positions| && positions[k] == i))
  }

  ghost predicate DirectoryPositionRelation(
    sorted: seq<OperandObservation>, positions: seq<nat>
  )
  {
    (forall k: nat :: k < |positions| ==> positions[k] < |sorted|) &&
    (forall k: nat :: k + 1 < |positions| ==> positions[k] < positions[k + 1]) &&
    (forall i: nat :: i < |sorted| ==>
                        (sorted[i].operandClass == ExpandedDirectory && sorted[i].sectionAvailable <==>
                         exists k: nat :: k < |positions| && positions[k] == i))
  }

  ghost predicate OutputGroupsWitnessRelation(
    sorted: seq<OperandObservation>, groups: seq<OutputGroup>,
    directPositions: seq<nat>, directoryPositions: seq<nat>,
    directIndices: seq<nat>, directFragments: seq<BenchWorld.Bytes>,
    directCuts: seq<nat>, directBody: BenchWorld.Bytes
  )
  {
    DirectPositionRelation(sorted, directPositions) &&
    DirectoryPositionRelation(sorted, directoryPositions) &&
    |directFragments| == |directPositions| &&
    (forall k: nat :: k < |directPositions| ==>
                        directFragments[k] == sorted[directPositions[k]].body) &&
    FragmentsConcatenate(directFragments, directBody, directCuts) &&
    |directIndices| == |directPositions| &&
    (forall k: nat :: k < |directPositions| ==>
                        directIndices[k] == sorted[directPositions[k]].index) &&
    |groups| == |directoryPositions| + (if |directPositions| == 0 then 0 else 1) &&
    (|directPositions| > 0 ==>
       groups[0] == OutputGroup(
         directIndices, directBody, false)) &&
    (forall k: nat :: k < |directoryPositions| ==>
                        var offset := if |directPositions| == 0 then 0 else 1;
                        groups[k + offset] == OutputGroup(
                          [sorted[directoryPositions[k]].index],
                          sorted[directoryPositions[k]].body, true))
  }

  ghost predicate OutputGroupsRelation(
    sorted: seq<OperandObservation>,
    groups: seq<OutputGroup>
  )
  {
    exists directPositions: seq<nat>, directoryPositions: seq<nat>,
      directIndices: seq<nat>,
      directFragments: seq<BenchWorld.Bytes>, directCuts: seq<nat>,
      directBody: BenchWorld.Bytes ::
      OutputGroupsWitnessRelation(
        sorted, groups, directPositions, directoryPositions, directIndices,
        directFragments, directCuts, directBody)
  }

  ghost predicate SeparatedGroupsRelation(
    groups: seq<OutputGroup>, output: BenchWorld.Bytes
  )
  {
    exists fragments: seq<BenchWorld.Bytes>, cuts: seq<nat> ::
      |fragments| == |groups| &&
      (forall i: nat :: i < |groups| ==>
                          fragments[i] == (if i == 0 then [] else "\n") + groups[i].body) &&
      FragmentsConcatenate(fragments, output, cuts)
  }

  ghost predicate OperandErrorsRelation(
    observations: seq<OperandObservation>, sorted: seq<OperandObservation>,
    errors: BenchWorld.Bytes
  )
  {
    exists accessFragments: seq<BenchWorld.Bytes>, accessCuts: seq<nat>,
      sectionFragments: seq<BenchWorld.Bytes>, sectionCuts: seq<nat>,
      accessErrors: BenchWorld.Bytes, sectionErrors: BenchWorld.Bytes ::
      |accessFragments| == |observations| &&
      (forall i: nat :: i < |observations| ==>
                          accessFragments[i] == observations[i].accessErrors) &&
      FragmentsConcatenate(accessFragments, accessErrors, accessCuts) &&
      |sectionFragments| == |sorted| &&
      (forall i: nat :: i < |sorted| ==>
                          sectionFragments[i] == sorted[i].sectionErrors) &&
      FragmentsConcatenate(sectionFragments, sectionErrors, sectionCuts) &&
      errors == accessErrors + sectionErrors
  }

  ghost predicate RunRelation(
    cmd: Schema.LsCmd,
    fs: BenchWorld.FileSystem,
    cwd: BenchWorld.Path,
    output: BenchWorld.Bytes,
    errors: BenchWorld.Bytes,
    exit: int
  )
  {
    exists observations: seq<OperandObservation>,
      sorted: seq<OperandObservation>, groups: seq<OutputGroup> ::
      |observations| == |cmd.operands| &&
      (forall i: nat | i < |observations| ::
         observations[i].index == i &&
         OperandObservationRelation(cmd, fs, cwd, observations[i])) &&
      OperandSortingRelation(cmd, observations, sorted) &&
      OutputGroupsRelation(sorted, groups) &&
      SeparatedGroupsRelation(groups, output) &&
      OperandErrorsRelation(observations, sorted, errors) &&
      exit == (if exists i: nat ::
                    i < |observations| && observations[i].failed then 2 else 0)
  }

  twostate predicate Spec(raw: Schema.LsCmdRaw, io: BenchIO.IO, exit: int)
    reads io.fsRegion, io.cwdRegion, io.envRegion, io.nowRegion, io.stdoutRegion, io.stderrRegion
  {
    var cmd := EffectiveCommandSpec(raw, old(io.env()), old(io.now()));
    if cmd.mode == Schema.ModeHelp then
      io.stdout() == old(io.stdout()) + HelpTextSpec() &&
      io.stderr() == old(io.stderr()) &&
      exit == 0
    else if cmd.mode == Schema.ModeVersion then
      io.stdout() == old(io.stdout()) + VersionTextSpec() &&
      io.stderr() == old(io.stderr()) &&
      exit == 0
    else if cmd.mode != Schema.ModeRun then
      io.stdout() == old(io.stdout()) &&
      io.stderr() == old(io.stderr()) + InvalidModeMessageSpec(cmd.mode) &&
      exit == (if cmd.mode.ModeInvalidTime? then 1 else 2)
    else
      exists output: BenchWorld.Bytes, errors: BenchWorld.Bytes ::
        RunRelation(cmd, old(io.fs()), old(io.cwd()), output, errors, exit) &&
        io.stdout() == old(io.stdout()) + output &&
        io.stderr() == old(io.stderr()) + errors
  }
}
