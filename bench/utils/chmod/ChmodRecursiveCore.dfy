include "../../core/World.dfy"
include "../../core/WorldFileSystemProof.dfy"
include "../../core/IO.dfy"
include "../../core/IOContract.dfy"
include "ChmodSchema.dfy"
include "ChmodCore.dfy"
include "ChmodRecursiveSpec.dfy"

module ChmodRecursiveCore {
  import BenchWorld
  import WorldProof = WorldFileSystemProof
  import BenchIO
  import IOContract
  import Schema = ChmodSchema
  import Base = ChmodCore
  import Spec = ChmodRecursiveSpec

  datatype RecursiveTerminal = RecursiveEof | RecursiveReadError(err: int)

  datatype RecursiveFailureKind =
    RecursiveAccess | RecursiveDangling | RecursiveDereference

  datatype RecursiveIdentity = RecursiveIdentity(
    displayPath: string,
    accessPath: BenchWorld.Path,
    resolvedPath: BenchWorld.Path,
    isTopLevel: bool,
    isSymlink: bool,
    isDirectory: bool
  )

  datatype RecursiveVisit =
    | RecursiveSkip(identity: RecursiveIdentity)
    | RecursiveAccessFailure(
        identity: RecursiveIdentity,
        err: int,
        failureKind: RecursiveFailureKind
      )
    | RecursivePreserveRoot(identity: RecursiveIdentity, alias: bool)
    | RecursiveNode(
        identity: RecursiveIdentity,
        children: seq<RecursiveVisit>,
        terminal: RecursiveTerminal
      )

  datatype RecursiveResult = RecursiveResult(
    fs: BenchWorld.FileSystem,
    stdoutChunk: BenchWorld.Bytes,
    stderrChunk: BenchWorld.Bytes,
    allOk: bool
  )

  function VisitSizeCore(visit: RecursiveVisit): nat
    decreases visit
  {
    match visit
    case RecursiveSkip(_) | RecursiveAccessFailure(_, _, _) |
      RecursivePreserveRoot(_, _) => 1
    case RecursiveNode(_, children, _) => 1 + VisitsSizeCore(children)
  }

  function VisitsSizeCore(visits: seq<RecursiveVisit>): nat
    decreases visits
  {
    if |visits| == 0 then 0
    else VisitSizeCore(visits[0]) + VisitsSizeCore(visits[1..])
  }

  function TraversalFollowCore(cmd: Schema.ChmodCmd, isTopLevel: bool): bool
  {
    cmd.traversalMode == 2 || (cmd.traversalMode == 1 && isTopLevel)
  }

  function ChmodFollowCore(cmd: Schema.ChmodCmd, isTopLevel: bool): bool
  {
    if cmd.dereferenceMode == 1 then true
    else if cmd.dereferenceMode == 0 then false
    else TraversalFollowCore(cmd, isTopLevel)
  }

  function RootPreserveMessageCore(displayPath: string, alias: bool): BenchWorld.Bytes
  {
    Spec.RootPreserveMessageSpec(displayPath, alias)
  }

  function ReadDirectoryMessageCore(path: string, err: int): BenchWorld.Bytes
  {
    Spec.ReadDirectoryMessageSpec(path, err)
  }

  function DanglingSymlinkMessageCore(path: string): BenchWorld.Bytes
  {
    Spec.DanglingSymlinkMessageSpec(path)
  }

  function CannotDereferenceMessageCore(path: string, err: int): BenchWorld.Bytes
  {
    Spec.CannotDereferenceMessageSpec(path, err)
  }

  function NeitherChangedMessageCore(path: string): BenchWorld.Bytes
  {
    Spec.NeitherChangedMessageSpec(path)
  }

  function RecursiveDereferenceRequirementMessageCore(): BenchWorld.Bytes
  {
    Spec.RecursiveDereferenceRequirementMessageSpec()
  }

  function RecursiveAccessStdoutCore(cmd: Schema.ChmodCmd, path: string): BenchWorld.Bytes
  {
    if cmd.verbose then Base.AccessFailureMessageCore(path) else []
  }

  function RecursiveAccessStderrCore(
    cmd: Schema.ChmodCmd,
    path: string,
    err: int,
    failureKind: RecursiveFailureKind
  ): BenchWorld.Bytes
  {
    if cmd.silent then []
    else if failureKind.RecursiveDangling? then DanglingSymlinkMessageCore(path)
    else if failureKind.RecursiveDereference? then
      CannotDereferenceMessageCore(path, err)
    else Base.AccessErrorMessageCore(path, Base.ErrnoTextCore(err))
  }

  function ResolutionFailureKindCore(
    cmd: Schema.ChmodCmd,
    isTopLevel: bool,
    isSymlink: bool,
    err: int
  ): RecursiveFailureKind
  {
    if isSymlink && !TraversalFollowCore(cmd, isTopLevel) &&
       ChmodFollowCore(cmd, isTopLevel) then
      RecursiveDereference
    else if Base.CoreIsDanglingSymlinkFailure(isSymlink, err) then
      RecursiveDangling
    else
      RecursiveAccess
  }

  function RecursiveSkipStdoutCore(cmd: Schema.ChmodCmd, path: string): BenchWorld.Bytes
  {
    if cmd.verbose then NeitherChangedMessageCore(path) else []
  }

  function RecursiveReadStdoutCore(
    cmd: Schema.ChmodCmd,
    path: string,
    terminal: RecursiveTerminal
  ): BenchWorld.Bytes
  {
    match terminal
    case RecursiveEof => []
    case RecursiveReadError(_) =>
      if cmd.verbose then Base.AccessFailureMessageCore(path) else []
  }

  function RecursiveReadStderrCore(
    cmd: Schema.ChmodCmd,
    path: string,
    terminal: RecursiveTerminal
  ): BenchWorld.Bytes
  {
    match terminal
    case RecursiveEof => []
    case RecursiveReadError(err) =>
      if cmd.silent then [] else ReadDirectoryMessageCore(path, err)
  }

  function ApplyResolvedCore(
    cmd: Schema.ChmodCmd,
    plan: Base.CoreModePlan,
    identity: RecursiveIdentity,
    fs: BenchWorld.FileSystem,
    now: int
  ): Base.CorePathResult
  {
    if identity.isSymlink && !ChmodFollowCore(cmd, identity.isTopLevel) then
      Base.CorePathResult(
        fs,
        RecursiveSkipStdoutCore(cmd, identity.displayPath),
        [],
        true,
        Base.CorePathRetained(0 as bv32)
      )
    else if !BenchWorld.FsContainsPath(fs, identity.resolvedPath) then
      Base.CorePathResult(
        fs,
        RecursiveAccessStdoutCore(cmd, identity.displayPath),
        RecursiveAccessStderrCore(
          cmd, identity.displayPath, 2, RecursiveAccess
        ),
        false,
        Base.CorePathAccessFailed(2)
      )
    else
      var node := BenchWorld.FsNodeAt(fs, identity.resolvedPath);
      var before := BenchWorld.NodeMode(node);
      var desired := Base.CorePlannedMode(plan, before, identity.isDirectory);
      var next := Base.CoreModeSetFs(
                    fs,
                    true,
                    identity.resolvedPath,
                    desired,
                    now
                  );
      var after := BenchWorld.NormalizeMode(desired);
      Base.CoreSuccessfulChangeResult(
        cmd,
        plan,
        identity.displayPath,
        identity.accessPath,
        true,
        before,
        after,
        identity.isDirectory,
        next
      )
  }

  function EvalChildrenCore(
    cmd: Schema.ChmodCmd,
    plan: Base.CoreModePlan,
    visits: seq<RecursiveVisit>,
    i: nat,
    activeResolved: set<seq<string>>,
    fs: BenchWorld.FileSystem,
    now: int
  ): RecursiveResult
    decreases if i <= |visits| then VisitsSizeCore(visits[i..]) else 0, 1
  {
    if i >= |visits| then
      RecursiveResult(fs, [], [], true)
    else
      var step := EvalVisitCore(
                    cmd, plan, visits[i], activeResolved, fs, now
                  );
      var rest := EvalChildrenCore(
                    cmd, plan, visits, i + 1, activeResolved, step.fs, now
                  );
      RecursiveResult(
        rest.fs,
        step.stdoutChunk + rest.stdoutChunk,
        step.stderrChunk + rest.stderrChunk,
        step.allOk && rest.allOk
      )
  }

  function EvalVisitCore(
    cmd: Schema.ChmodCmd,
    plan: Base.CoreModePlan,
    visit: RecursiveVisit,
    activeResolved: set<seq<string>>,
    fs: BenchWorld.FileSystem,
    now: int
  ): RecursiveResult
    decreases VisitSizeCore(visit), 0
  {
    match visit
    case RecursiveSkip(identity) =>
      RecursiveResult(
        fs,
        RecursiveSkipStdoutCore(cmd, identity.displayPath),
        [],
        true
      )
    case RecursiveAccessFailure(identity, err, failureKind) =>
      RecursiveResult(
        fs,
        RecursiveAccessStdoutCore(cmd, identity.displayPath),
        RecursiveAccessStderrCore(cmd, identity.displayPath, err, failureKind),
        false
      )
    case RecursivePreserveRoot(identity, alias) =>
      RecursiveResult(
        fs,
        [],
        RootPreserveMessageCore(identity.displayPath, alias),
        false
      )
    case RecursiveNode(identity, children, terminal) =>
      var parent := ApplyResolvedCore(cmd, plan, identity, fs, now);
      if BenchWorld.PathSegments(identity.resolvedPath) in activeResolved then
        RecursiveResult(
          parent.fs,
          parent.stdoutChunk,
          parent.stderrChunk,
          parent.ok
        )
      else
        var descendants := EvalChildrenCore(
                             cmd,
                             plan,
                             children,
                             0,
                             activeResolved + {BenchWorld.PathSegments(identity.resolvedPath)},
                             parent.fs,
                             now
                           );
        RecursiveResult(
          descendants.fs,
          parent.stdoutChunk + descendants.stdoutChunk +
          RecursiveReadStdoutCore(cmd, identity.displayPath, terminal),
          parent.stderrChunk + descendants.stderrChunk +
          RecursiveReadStderrCore(cmd, identity.displayPath, terminal),
          parent.ok && descendants.allOk && terminal.RecursiveEof?
        )
  }

  predicate DuplicateFreePrefix(entries: seq<BenchWorld.DirEntry>)
  {
    forall i, j :: 0 <= i < j < |entries| ==> entries[i] != entries[j]
  }

  function EntriesSet(entries: seq<BenchWorld.DirEntry>): set<BenchWorld.DirEntry>
  {
    set i | 0 <= i < |entries| :: entries[i]
  }

  lemma SnocConsDecomposition<T>(xs: seq<T>, last: T)
    requires |xs| > 0
    ensures xs + [last] == [xs[0]] + (xs[1..] + [last])
    ensures (xs + [last])[0] == xs[0]
    ensures (xs + [last])[1..] == xs[1..] + [last]
  {
  }

  lemma ConsTailIndex<T>(head: T, tail: seq<T>, index: nat)
    requires 0 < index <= |tail|
    ensures ([head] + tail)[index] == tail[index - 1]
  {
  }

  lemma EntriesSetCons(
    entry: BenchWorld.DirEntry,
    entries: seq<BenchWorld.DirEntry>
  )
    ensures EntriesSet([entry] + entries) == {entry} + EntriesSet(entries)
  {
    assert forall candidate: BenchWorld.DirEntry ::
        candidate in EntriesSet([entry] + entries) <==>
                     candidate in {entry} + EntriesSet(entries) by {
      forall candidate: BenchWorld.DirEntry
        ensures candidate in EntriesSet([entry] + entries) <==>
                candidate in {entry} + EntriesSet(entries)
      {
        if candidate in EntriesSet([entry] + entries) {
          var i :| 0 <= i < |[entry] + entries| &&
                   candidate == ([entry] + entries)[i];
          if i == 0 {
            assert candidate == entry;
          } else {
            assert 0 <= i - 1 < |entries|;
            assert candidate == entries[i - 1];
          }
        } else if candidate == entry {
          assert candidate == ([entry] + entries)[0];
        } else if candidate in EntriesSet(entries) {
          var i :| 0 <= i < |entries| && candidate == entries[i];
          assert candidate == ([entry] + entries)[i + 1];
        }
      }
    }
  }

  lemma RemainingAfterCons(
    snapshot: set<BenchWorld.DirEntry>,
    entry: BenchWorld.DirEntry,
    entries: seq<BenchWorld.DirEntry>
  )
    requires entry in snapshot
    ensures snapshot - EntriesSet([entry] + entries) ==
            (snapshot - {entry}) - EntriesSet(entries)
  {
    EntriesSetCons(entry, entries);
  }

  lemma EntriesSetSnoc(
    entries: seq<BenchWorld.DirEntry>,
    entry: BenchWorld.DirEntry
  )
    ensures EntriesSet(entries + [entry]) == EntriesSet(entries) + {entry}
  {
    assert forall candidate: BenchWorld.DirEntry ::
        candidate in EntriesSet(entries + [entry]) <==>
                     candidate in EntriesSet(entries) + {entry} by {
      forall candidate: BenchWorld.DirEntry
        ensures candidate in EntriesSet(entries + [entry]) <==>
                candidate in EntriesSet(entries) + {entry}
      {
        if candidate in EntriesSet(entries + [entry]) {
          var i :| 0 <= i < |entries + [entry]| &&
                   candidate == (entries + [entry])[i];
          if i < |entries| {
            assert candidate == entries[i];
          } else {
            assert i == |entries|;
            assert candidate == entry;
          }
        } else if candidate in EntriesSet(entries) {
          var i :| 0 <= i < |entries| && candidate == entries[i];
          assert candidate == (entries + [entry])[i];
        } else if candidate == entry {
          assert candidate == (entries + [entry])[|entries|];
        }
      }
    }
  }

  lemma DuplicateFreeSnoc(
    entries: seq<BenchWorld.DirEntry>,
    entry: BenchWorld.DirEntry
  )
    requires DuplicateFreePrefix(entries)
    requires entry !in EntriesSet(entries)
    ensures DuplicateFreePrefix(entries + [entry])
  {
  }

  predicate ValidOpenSchedule(
    snapshot: set<BenchWorld.DirEntry>,
    entries: seq<BenchWorld.DirEntry>,
    terminal: RecursiveTerminal
  )
  {
    (terminal.RecursiveReadError? ==> terminal.err != 0) &&
    DuplicateFreePrefix(entries) &&
    (forall i :: 0 <= i < |entries| ==> entries[i] in snapshot) &&
    (terminal.RecursiveEof? ==>
       (set i | 0 <= i < |entries| :: entries[i]) == snapshot)
  }

  lemma ValidOpenScheduleCons(
    snapshot: set<BenchWorld.DirEntry>,
    entry: BenchWorld.DirEntry,
    entries: seq<BenchWorld.DirEntry>,
    terminal: RecursiveTerminal
  )
    requires entry in snapshot
    requires ValidOpenSchedule(snapshot - {entry}, entries, terminal)
    ensures ValidOpenSchedule(
              snapshot, [entry] + entries, terminal
            )
  {
    EntriesSetCons(entry, entries);
    assert entry !in EntriesSet(entries) by {
      if entry in EntriesSet(entries) {
        var i :| 0 <= i < |entries| && entry == entries[i];
        assert entries[i] in snapshot - {entry};
      }
    }
    assert DuplicateFreePrefix([entry] + entries) by {
      forall i, j | 0 <= i < j < |[entry] + entries|
        ensures ([entry] + entries)[i] != ([entry] + entries)[j]
      {
        if i == 0 {
          assert ([entry] + entries)[i] == entry;
          assert ([entry] + entries)[j] == entries[j - 1];
          assert entries[j - 1] in snapshot - {entry};
        } else {
          assert ([entry] + entries)[i] == entries[i - 1];
          assert ([entry] + entries)[j] == entries[j - 1];
        }
      }
    }
    assert forall i :: 0 <= i < |[entry] + entries| ==>
                         ([entry] + entries)[i] in snapshot by {
      forall i | 0 <= i < |[entry] + entries|
        ensures ([entry] + entries)[i] in snapshot
      {
        if i > 0 {
          assert ([entry] + entries)[i] == entries[i - 1];
          assert entries[i - 1] in snapshot - {entry};
        }
      }
    }
    if terminal.RecursiveEof? {
      assert EntriesSet(entries) == snapshot - {entry};
      assert {entry} + EntriesSet(entries) == snapshot;
    }
  }

  predicate ActiveAncestryCycle(
    activeResolved: set<seq<string>>,
    resolved: BenchWorld.Path
  )
  {
    BenchWorld.PathSegments(resolved) in activeResolved
  }

  lemma RemainingUniverseDecreases(
    universe: set<seq<string>>,
    activeResolved: set<seq<string>>,
    resolved: seq<string>
  )
    requires activeResolved <= universe
    requires resolved in universe - activeResolved
    ensures |universe - (activeResolved + {resolved})| <
            |universe - activeResolved|
  {
  }

  predicate OwnedHandles(
    base: map<int, BenchWorld.DirHandleState>,
    current: map<int, BenchWorld.DirHandleState>,
    owned: set<int>
  )
  {
    owned !! base.Keys &&
    current.Keys == base.Keys + owned &&
    forall h :: h in base ==> current[h] == base[h]
  }

  lemma EmptyOwnedRestores(
    base: map<int, BenchWorld.DirHandleState>,
    current: map<int, BenchWorld.DirHandleState>
  )
    requires OwnedHandles(base, current, {})
    ensures current == base
  {
    assert current.Keys == base.Keys;
    assert forall h :: h in base ==> current[h] == base[h];
  }

  function VisitIdentityCore(visit: RecursiveVisit): RecursiveIdentity
  {
    match visit
    case RecursiveSkip(identity) => identity
    case RecursiveAccessFailure(identity, _, _) => identity
    case RecursivePreserveRoot(identity, _) => identity
    case RecursiveNode(identity, _, _) => identity
  }

  ghost predicate IdentityResolvesCore(
    fs: BenchWorld.FileSystem,
    identity: RecursiveIdentity
  )
  {
    match IOContract.ResolvePathForMetadataFields(
        fs, identity.accessPath, false
      )
    case Err(_) => false
    case Ok(rawResolved) =>
      BenchWorld.FsContainsPath(fs, rawResolved) &&
      identity.isSymlink == BenchWorld.FsNodeAt(fs, rawResolved).Symlink? &&
      match IOContract.ResolvePathForMetadataFields(
          fs, identity.accessPath, true
        )
      case Err(_) => false
      case Ok(resolved) =>
        identity.resolvedPath == resolved &&
        BenchWorld.FsContainsPath(fs, resolved) &&
        identity.isDirectory ==
        BenchWorld.FsNodeAt(fs, resolved).Directory?
  }

  ghost predicate VisitMatchesEntryCore(
    parent: RecursiveIdentity,
    entry: BenchWorld.DirEntry,
    visit: RecursiveVisit
  )
  {
    var child := VisitIdentityCore(visit);
    child.displayPath == BenchWorld.AppendPath(parent.displayPath, entry.name) &&
    child.accessPath == BenchWorld.AppendPath(parent.resolvedPath, entry.name) &&
    !child.isTopLevel
  }

  ghost predicate SkipVisitCore(
    cmd: Schema.ChmodCmd,
    identity: RecursiveIdentity,
    fs: BenchWorld.FileSystem
  )
  {
    match IOContract.ResolvePathForMetadataFields(
        fs, identity.accessPath, false
      )
    case Err(_) => false
    case Ok(rawResolved) =>
      BenchWorld.FsContainsPath(fs, rawResolved) &&
      BenchWorld.FsNodeAt(fs, rawResolved).Symlink? &&
      identity.isSymlink &&
      identity.resolvedPath == "" &&
      !identity.isDirectory &&
      !ChmodFollowCore(cmd, identity.isTopLevel) &&
      (!TraversalFollowCore(cmd, identity.isTopLevel) ||
       match IOContract.ResolvePathForMetadataFields(
           fs, identity.accessPath, true
         )
       case Err(error) => Base.CoreIsDanglingSymlinkFailure(
         identity.isSymlink, IOContract.IOErrorErrno(error)
       )
       case Ok(_) => false)
  }

  ghost predicate FollowAccessFailureVisitCore(
    cmd: Schema.ChmodCmd,
    identity: RecursiveIdentity,
    isLink: bool,
    err: int,
    failureKind: RecursiveFailureKind,
    fs: BenchWorld.FileSystem
  )
  {
    match IOContract.ResolvePathForMetadataFields(
        fs, identity.accessPath, true
      )
    case Err(error) =>
      err == IOContract.IOErrorErrno(error) &&
      failureKind == ResolutionFailureKindCore(
        cmd, identity.isTopLevel, isLink, err
      )
    case Ok(_) => false
  }

  ghost predicate AccessFailureVisitCore(
    cmd: Schema.ChmodCmd,
    identity: RecursiveIdentity,
    err: int,
    failureKind: RecursiveFailureKind,
    fs: BenchWorld.FileSystem
  )
  {
    match IOContract.ResolvePathForMetadataFields(
        fs, identity.accessPath, false
      )
    case Err(error) =>
      err == IOContract.IOErrorErrno(error) &&
      failureKind.RecursiveAccess? &&
      !identity.isSymlink &&
      identity.resolvedPath == "" &&
      !identity.isDirectory
    case Ok(rawResolved) =>
      if !BenchWorld.FsContainsPath(fs, rawResolved) then
        err == IOContract.MetadataFailureErrFields(
          fs, identity.accessPath, false
        ) &&
        failureKind.RecursiveAccess? &&
        !identity.isSymlink &&
        identity.resolvedPath == "" &&
        !identity.isDirectory
      else
        var isLink := BenchWorld.FsNodeAt(fs, rawResolved).Symlink?;
        identity.isSymlink == isLink &&
        identity.resolvedPath == "" &&
        !identity.isDirectory &&
        (!isLink || ChmodFollowCore(cmd, identity.isTopLevel) ||
         (TraversalFollowCore(cmd, identity.isTopLevel) &&
          !Base.CoreIsDanglingSymlinkFailure(isLink, err))) &&
        FollowAccessFailureVisitCore(
          cmd, identity, isLink, err, failureKind, fs
        )
  }

  opaque ghost predicate ValidVisitCore(
    cmd: Schema.ChmodCmd,
    plan: Base.CoreModePlan,
    visit: RecursiveVisit,
    activeResolved: set<seq<string>>,
    fs: BenchWorld.FileSystem,
    now: int
  )
    decreases VisitSizeCore(visit), 0
  {
    var identity := VisitIdentityCore(visit);
    match visit
    case RecursiveSkip(_) =>
      SkipVisitCore(cmd, identity, fs)
    case RecursiveAccessFailure(_, err, failureKind) =>
      AccessFailureVisitCore(cmd, identity, err, failureKind, fs)
    case RecursivePreserveRoot(_, alias) =>
      IdentityResolvesCore(fs, identity) &&
      (!identity.isSymlink ||
       TraversalFollowCore(cmd, identity.isTopLevel) ||
       ChmodFollowCore(cmd, identity.isTopLevel)) &&
      cmd.preserveRoot &&
      identity.isDirectory &&
      identity.resolvedPath == "/" &&
      alias == (identity.accessPath != "/")
    case RecursiveNode(_, children, terminal) =>
      IdentityResolvesCore(fs, identity) &&
      (!identity.isSymlink ||
       TraversalFollowCore(cmd, identity.isTopLevel) ||
       ChmodFollowCore(cmd, identity.isTopLevel)) &&
      !(cmd.preserveRoot && identity.isDirectory &&
        identity.resolvedPath == "/") &&
      if identity.isSymlink &&
         !TraversalFollowCore(cmd, identity.isTopLevel) then
        |children| == 0 && terminal.RecursiveEof?
      else
      if BenchWorld.PathSegments(identity.resolvedPath) in activeResolved then
        |children| == 0 && terminal.RecursiveEof?
      else
        var parent := ApplyResolvedCore(cmd, plan, identity, fs, now);
        if !identity.isDirectory then
          |children| == 0 && terminal.RecursiveEof?
        else
          BenchWorld.FsContainsPath(parent.fs, identity.resolvedPath) &&
          exists entries: seq<BenchWorld.DirEntry> ::
            |entries| == |children| &&
            ValidOpenSchedule(
              IOContract.DirectoryEntriesForPathFields(
                parent.fs,
                identity.resolvedPath
              ),
              entries,
              terminal
            ) &&
            (forall j :: 0 <= j < |children| ==>
                           VisitMatchesEntryCore(identity, entries[j], children[j])) &&
            ValidVisitsCore(
              cmd,
              plan,
              children,
              0,
              activeResolved + {
                BenchWorld.PathSegments(identity.resolvedPath)
              },
              parent.fs,
              now
            )
  }

  ghost predicate ValidVisitsCore(
    cmd: Schema.ChmodCmd,
    plan: Base.CoreModePlan,
    visits: seq<RecursiveVisit>,
    i: nat,
    activeResolved: set<seq<string>>,
    fs: BenchWorld.FileSystem,
    now: int
  )
    requires i <= |visits|
    decreases VisitsSizeCore(visits[i..]), 1
  {
    if i == |visits| then
      true
    else
      ValidVisitCore(cmd, plan, visits[i], activeResolved, fs, now) &&
      ValidVisitsCore(
        cmd,
        plan,
        visits,
        i + 1,
        activeResolved,
        EvalVisitCore(cmd, plan, visits[i], activeResolved, fs, now).fs,
        now
      )
  }

  ghost predicate TopLevelVisitsCore(
    cmd: Schema.ChmodCmd,
    plan: Base.CoreModePlan,
    cwd: BenchWorld.Path,
    visits: seq<RecursiveVisit>,
    fs: BenchWorld.FileSystem,
    now: int
  )
  {
    |visits| == |cmd.files| &&
    (forall i :: 0 <= i < |visits| ==>
                   var identity := VisitIdentityCore(visits[i]);
                   identity.displayPath == cmd.files[i] &&
                   identity.accessPath == Base.MakeAbsoluteCore(cwd, cmd.files[i]) &&
                   identity.isTopLevel) &&
    ValidVisitsCore(cmd, plan, visits, 0, {}, fs, now)
  }

  ghost predicate RecursivePlanCore(
    cmd: Schema.ChmodCmd,
    fs: BenchWorld.FileSystem,
    cwd: BenchWorld.Path,
    props: map<string, string>,
    plan: Base.CoreModePlan
  )
  {
    if !cmd.seenReference then
      plan == Base.CoreGeneralModePlan(
        cmd.modeExpr,
        IOContract.GetUmaskResultFields(props)
      )
    else
      exists referenceMode: bv32 ::
        IOContract.GetFileModeContractFields(
          fs,
          Base.MakeAbsoluteCore(cwd, cmd.referenceFile),
          true,
          true,
          referenceMode,
          0
        ) &&
        plan == Base.CoreReferenceModePlan(referenceMode)
  }

  lemma {:isolate_assertions} EvalChildrenSnocCore(
    cmd: Schema.ChmodCmd,
    plan: Base.CoreModePlan,
    visits: seq<RecursiveVisit>,
    child: RecursiveVisit,
    activeResolved: set<seq<string>>,
    fs: BenchWorld.FileSystem,
    now: int
  )
    ensures var prefix := EvalChildrenCore(
                            cmd, plan, visits, 0, activeResolved, fs, now
                          );
            var childResult := EvalVisitCore(
                                 cmd, plan, child, activeResolved, prefix.fs, now
                               );
            EvalChildrenCore(
              cmd, plan, visits + [child], 0, activeResolved, fs, now
            ) == RecursiveResult(
              childResult.fs,
              prefix.stdoutChunk + childResult.stdoutChunk,
              prefix.stderrChunk + childResult.stderrChunk,
              prefix.allOk && childResult.allOk
            )
    decreases |visits|
  {
    if |visits| > 0 {
      var first := EvalVisitCore(
        cmd, plan, visits[0], activeResolved, fs, now
      );
      EvalChildrenSnocCore(
        cmd,
        plan,
        visits[1..],
        child,
        activeResolved,
        first.fs,
        now
      );
      SnocConsDecomposition(visits, child);
      EvalChildrenSliceCore(
        cmd, plan, visits, 1, activeResolved, first.fs, now
      );
      EvalChildrenSliceCore(
        cmd, plan, visits + [child], 1, activeResolved, first.fs, now
      );
      var rest := EvalChildrenCore(
        cmd, plan, visits[1..], 0, activeResolved, first.fs, now
      );
      var prefix := EvalChildrenCore(
        cmd, plan, visits, 0, activeResolved, fs, now
      );
      assert prefix == RecursiveResult(
                         rest.fs,
                         first.stdoutChunk + rest.stdoutChunk,
                         first.stderrChunk + rest.stderrChunk,
                         first.allOk && rest.allOk
                       );
      var childResult := EvalVisitCore(
        cmd, plan, child, activeResolved, rest.fs, now
      );
      var extendedRest := EvalChildrenCore(
        cmd,
        plan,
        visits[1..] + [child],
        0,
        activeResolved,
        first.fs,
        now
      );
      assert extendedRest == RecursiveResult(
                               childResult.fs,
                               rest.stdoutChunk + childResult.stdoutChunk,
                               rest.stderrChunk + childResult.stderrChunk,
                               rest.allOk && childResult.allOk
                             );
      EvalChildrenConsCore(
        cmd,
        plan,
        visits[0],
        visits[1..] + [child],
        activeResolved,
        fs,
        now
      );
      var extended := EvalChildrenCore(
        cmd, plan, visits + [child], 0, activeResolved, fs, now
      );
      assert extended.fs == childResult.fs by {
        calc {
          extended.fs;
        ==
          extendedRest.fs;
        ==
          childResult.fs;
        }
      }
      assert extended.stdoutChunk ==
             prefix.stdoutChunk + childResult.stdoutChunk by {
        calc {
          extended.stdoutChunk;
        ==
          first.stdoutChunk + extendedRest.stdoutChunk;
        ==
          first.stdoutChunk +
          (rest.stdoutChunk + childResult.stdoutChunk);
        == {
          Base.AppendAssociative(
            first.stdoutChunk,
            rest.stdoutChunk,
            childResult.stdoutChunk
          );
        }
          (first.stdoutChunk + rest.stdoutChunk) +
          childResult.stdoutChunk;
        ==
          prefix.stdoutChunk + childResult.stdoutChunk;
        }
      }
      Base.AppendAssociative(
        first.stderrChunk,
        rest.stderrChunk,
        childResult.stderrChunk
      );
      assert extended.stderrChunk ==
             prefix.stderrChunk + childResult.stderrChunk by {
        calc {
          extended.stderrChunk;
        ==
          first.stderrChunk + extendedRest.stderrChunk;
        ==
          first.stderrChunk +
          (rest.stderrChunk + childResult.stderrChunk);
        ==
          (first.stderrChunk + rest.stderrChunk) +
          childResult.stderrChunk;
        ==
          prefix.stderrChunk + childResult.stderrChunk;
        }
      }
      assert extended.allOk ==
             (prefix.allOk && childResult.allOk) by {
        calc {
          extended.allOk;
        ==
          first.allOk && extendedRest.allOk;
        ==
          first.allOk && (rest.allOk && childResult.allOk);
        ==
          (first.allOk && rest.allOk) && childResult.allOk;
        ==
          prefix.allOk && childResult.allOk;
        }
      }
      assert extended == RecursiveResult(
                           childResult.fs,
                           prefix.stdoutChunk + childResult.stdoutChunk,
                           prefix.stderrChunk + childResult.stderrChunk,
                           prefix.allOk && childResult.allOk
                         );
    } else {
      assert visits == [];
      var prefix := EvalChildrenCore(
        cmd, plan, visits, 0, activeResolved, fs, now
      );
      assert prefix == RecursiveResult(fs, [], [], true);
      var childResult := EvalVisitCore(
        cmd, plan, child, activeResolved, prefix.fs, now
      );
      EvalChildrenConsCore(
        cmd, plan, child, [], activeResolved, fs, now
      );
      assert EvalChildrenCore(
          cmd, plan, visits + [child], 0, activeResolved, fs, now
        ) == RecursiveResult(
                    childResult.fs,
                    prefix.stdoutChunk + childResult.stdoutChunk,
                    prefix.stderrChunk + childResult.stderrChunk,
                    prefix.allOk && childResult.allOk
                  );
    }
  }

  lemma EvalChildrenSliceCore(
    cmd: Schema.ChmodCmd,
    plan: Base.CoreModePlan,
    visits: seq<RecursiveVisit>,
    i: nat,
    activeResolved: set<seq<string>>,
    fs: BenchWorld.FileSystem,
    now: int
  )
    requires i <= |visits|
    ensures EvalChildrenCore(
              cmd, plan, visits, i, activeResolved, fs, now
            ) == EvalChildrenCore(
                   cmd, plan, visits[i..], 0, activeResolved, fs, now
                 )
    decreases |visits| - i
  {
    if i < |visits| {
      var step := EvalVisitCore(
        cmd, plan, visits[i], activeResolved, fs, now
      );
      EvalChildrenSliceCore(
        cmd, plan, visits, i + 1, activeResolved, step.fs, now
      );
      EvalChildrenSliceCore(
        cmd, plan, visits[i..], 1, activeResolved, step.fs, now
      );
      assert visits[i..][0] == visits[i];
      assert visits[i..][1..] == visits[i + 1..];
    }
  }

  lemma ValidVisitsSliceCore(
    cmd: Schema.ChmodCmd,
    plan: Base.CoreModePlan,
    visits: seq<RecursiveVisit>,
    i: nat,
    activeResolved: set<seq<string>>,
    fs: BenchWorld.FileSystem,
    now: int
  )
    requires i <= |visits|
    ensures ValidVisitsCore(
              cmd, plan, visits, i, activeResolved, fs, now
            ) == ValidVisitsCore(
                   cmd, plan, visits[i..], 0, activeResolved, fs, now
                 )
    decreases |visits| - i
  {
    if i < |visits| {
      var step := EvalVisitCore(
        cmd, plan, visits[i], activeResolved, fs, now
      );
      ValidVisitsSliceCore(
        cmd, plan, visits, i + 1, activeResolved, step.fs, now
      );
      ValidVisitsSliceCore(
        cmd, plan, visits[i..], 1, activeResolved, step.fs, now
      );
      assert visits[i..][0] == visits[i];
      assert visits[i..][1..] == visits[i + 1..];
    }
  }

  lemma ValidVisitsSnocCore(
    cmd: Schema.ChmodCmd,
    plan: Base.CoreModePlan,
    visits: seq<RecursiveVisit>,
    child: RecursiveVisit,
    activeResolved: set<seq<string>>,
    fs: BenchWorld.FileSystem,
    now: int
  )
    requires ValidVisitsCore(
               cmd, plan, visits, 0, activeResolved, fs, now
             )
    requires ValidVisitCore(
               cmd,
               plan,
               child,
               activeResolved,
               EvalChildrenCore(
                 cmd, plan, visits, 0, activeResolved, fs, now
               ).fs,
               now
             )
    ensures ValidVisitsCore(
              cmd, plan, visits + [child], 0, activeResolved, fs, now
            )
    decreases |visits|
  {
    if |visits| > 0 {
      var first := EvalVisitCore(
        cmd, plan, visits[0], activeResolved, fs, now
      );
      assert ValidVisitCore(
          cmd, plan, visits[0], activeResolved, fs, now
        );
      ValidVisitsSliceCore(
        cmd, plan, visits, 1, activeResolved, first.fs, now
      );
      EvalChildrenSliceCore(
        cmd, plan, visits, 1, activeResolved, first.fs, now
      );
      ValidVisitsSnocCore(
        cmd,
        plan,
        visits[1..],
        child,
        activeResolved,
        first.fs,
        now
      );
      SnocConsDecomposition(visits, child);
      ValidVisitsSliceCore(
        cmd,
        plan,
        visits + [child],
        1,
        activeResolved,
        first.fs,
        now
      );
    }
  }

  lemma EvalChildrenConsCore(
    cmd: Schema.ChmodCmd,
    plan: Base.CoreModePlan,
    child: RecursiveVisit,
    children: seq<RecursiveVisit>,
    activeResolved: set<seq<string>>,
    fs: BenchWorld.FileSystem,
    now: int
  )
    ensures var first := EvalVisitCore(
                           cmd, plan, child, activeResolved, fs, now
                         );
            var suffix := EvalChildrenCore(
                            cmd, plan, children, 0, activeResolved, first.fs, now
                          );
            EvalChildrenCore(
              cmd, plan, [child] + children, 0, activeResolved, fs, now
            ) == RecursiveResult(
              suffix.fs,
              first.stdoutChunk + suffix.stdoutChunk,
              first.stderrChunk + suffix.stderrChunk,
              first.allOk && suffix.allOk
            )
  {
    var first := EvalVisitCore(
      cmd, plan, child, activeResolved, fs, now
    );
    EvalChildrenSliceCore(
      cmd,
      plan,
      [child] + children,
      1,
      activeResolved,
      first.fs,
      now
    );
    assert ([child] + children)[0] == child;
    assert ([child] + children)[1..] == children;
  }

  lemma ValidVisitsConsCore(
    cmd: Schema.ChmodCmd,
    plan: Base.CoreModePlan,
    child: RecursiveVisit,
    children: seq<RecursiveVisit>,
    activeResolved: set<seq<string>>,
    fs: BenchWorld.FileSystem,
    now: int
  )
    requires ValidVisitCore(cmd, plan, child, activeResolved, fs, now)
    requires ValidVisitsCore(
               cmd,
               plan,
               children,
               0,
               activeResolved,
               EvalVisitCore(cmd, plan, child, activeResolved, fs, now).fs,
               now
             )
    ensures ValidVisitsCore(
              cmd,
              plan,
              [child] + children,
              0,
              activeResolved,
              fs,
              now
            )
  {
    var first := EvalVisitCore(
      cmd, plan, child, activeResolved, fs, now
    );
    ValidVisitsSliceCore(
      cmd,
      plan,
      [child] + children,
      1,
      activeResolved,
      first.fs,
      now
    );
    assert ([child] + children)[0] == child;
    assert ([child] + children)[1..] == children;
  }

  ghost predicate RuntimeVisitOutcomeCore(
    cmd: Schema.ChmodCmd,
    plan: Base.CoreModePlan,
    displayPath: string,
    accessPath: BenchWorld.Path,
    isTopLevel: bool,
    activeSegments: set<seq<string>>,
    fs0: BenchWorld.FileSystem,
    stdout0: BenchWorld.Bytes,
    stderr0: BenchWorld.Bytes,
    fs2: BenchWorld.FileSystem,
    stdout2: BenchWorld.Bytes,
    stderr2: BenchWorld.Bytes,
    ok: bool,
    visit: RecursiveVisit,
    now: int
  )
  {
    VisitIdentityCore(visit).displayPath == displayPath &&
    VisitIdentityCore(visit).accessPath == accessPath &&
    VisitIdentityCore(visit).isTopLevel == isTopLevel &&
    ValidVisitCore(cmd, plan, visit, activeSegments, fs0, now) &&
    var result := EvalVisitCore(
                    cmd, plan, visit, activeSegments, fs0, now
                  );
    fs2 == result.fs &&
    stdout2 == stdout0 + result.stdoutChunk &&
    stderr2 == stderr0 + result.stderrChunk &&
    ok == result.allOk
  }

  lemma DirectoryVisitValidCore(
    cmd: Schema.ChmodCmd,
    plan: Base.CoreModePlan,
    identity: RecursiveIdentity,
    activeSegments: set<seq<string>>,
    fs0: BenchWorld.FileSystem,
    parentFs: BenchWorld.FileSystem,
    children: seq<RecursiveVisit>,
    terminal: RecursiveTerminal,
    now: int
  )
    requires IdentityResolvesCore(fs0, identity)
    requires identity.isDirectory
    requires !identity.isSymlink ||
             TraversalFollowCore(cmd, identity.isTopLevel)
    requires !(cmd.preserveRoot && identity.resolvedPath == "/")
    requires BenchWorld.PathSegments(identity.resolvedPath) !in
             activeSegments
    requires parentFs == ApplyResolvedCore(cmd, plan, identity, fs0, now).fs
    requires BenchWorld.FsContainsPath(parentFs, identity.resolvedPath)
    requires exists entries: seq<BenchWorld.DirEntry> ::
               |entries| == |children| &&
               ValidOpenSchedule(
                 IOContract.DirectoryEntriesForPathFields(
                   parentFs, identity.resolvedPath
                 ),
                 entries,
                 terminal
               ) &&
               (forall j :: 0 <= j < |children| ==>
                              VisitMatchesEntryCore(identity, entries[j], children[j])) &&
               ValidVisitsCore(
                 cmd,
                 plan,
                 children,
                 0,
                 activeSegments + {
                   BenchWorld.PathSegments(identity.resolvedPath)
                 },
                 parentFs,
                 now
               )
    ensures ValidVisitCore(
              cmd,
              plan,
              RecursiveNode(identity, children, terminal),
              activeSegments,
              fs0,
              now
            )
  {
    reveal ValidVisitCore;
    ApplyResolvedPreservesDirectory(cmd, plan, identity, fs0, now);
  }

  lemma EvalDirectoryVisitCore(
    cmd: Schema.ChmodCmd,
    plan: Base.CoreModePlan,
    identity: RecursiveIdentity,
    activeSegments: set<seq<string>>,
    fs0: BenchWorld.FileSystem,
    children: seq<RecursiveVisit>,
    terminal: RecursiveTerminal,
    now: int
  )
    requires BenchWorld.PathSegments(identity.resolvedPath) !in
             activeSegments
    ensures var parent := ApplyResolvedCore(cmd, plan, identity, fs0, now);
            var descendants := EvalChildrenCore(
                                 cmd,
                                 plan,
                                 children,
                                 0,
                                 activeSegments + {
                                   BenchWorld.PathSegments(identity.resolvedPath)
                                 },
                                 parent.fs,
                                 now
                               );
            EvalVisitCore(
              cmd,
              plan,
              RecursiveNode(identity, children, terminal),
              activeSegments,
              fs0,
              now
            ) == RecursiveResult(
              descendants.fs,
              parent.stdoutChunk + descendants.stdoutChunk +
              RecursiveReadStdoutCore(cmd, identity.displayPath, terminal),
              parent.stderrChunk + descendants.stderrChunk +
              RecursiveReadStderrCore(cmd, identity.displayPath, terminal),
              parent.ok && descendants.allOk && terminal.RecursiveEof?
            )
  {
  }

  lemma DirectoryStreamTraceCore(
    stream0: BenchWorld.Bytes,
    parentChunk: BenchWorld.Bytes,
    descendantsChunk: BenchWorld.Bytes,
    readChunk: BenchWorld.Bytes,
    parentStream: BenchWorld.Bytes,
    stream2: BenchWorld.Bytes
  )
    requires parentStream == stream0 + parentChunk
    requires stream2 == parentStream + descendantsChunk + readChunk
    ensures stream2 == stream0 +
                       (parentChunk + descendantsChunk + readChunk)
  {
  }

  lemma RuntimeVisitOutcomeFromPartsCore(
    cmd: Schema.ChmodCmd,
    plan: Base.CoreModePlan,
    displayPath: string,
    accessPath: BenchWorld.Path,
    isTopLevel: bool,
    activeSegments: set<seq<string>>,
    fs0: BenchWorld.FileSystem,
    stdout0: BenchWorld.Bytes,
    stderr0: BenchWorld.Bytes,
    fs2: BenchWorld.FileSystem,
    stdout2: BenchWorld.Bytes,
    stderr2: BenchWorld.Bytes,
    ok: bool,
    visit: RecursiveVisit,
    now: int
  )
    requires VisitIdentityCore(visit).displayPath == displayPath
    requires VisitIdentityCore(visit).accessPath == accessPath
    requires VisitIdentityCore(visit).isTopLevel == isTopLevel
    requires ValidVisitCore(cmd, plan, visit, activeSegments, fs0, now)
    requires var result := EvalVisitCore(
                             cmd, plan, visit, activeSegments, fs0, now
                           );
             fs2 == result.fs &&
             stdout2 == stdout0 + result.stdoutChunk &&
             stderr2 == stderr0 + result.stderrChunk &&
             ok == result.allOk
    ensures RuntimeVisitOutcomeCore(
              cmd,
              plan,
              displayPath,
              accessPath,
              isTopLevel,
              activeSegments,
              fs0,
              stdout0,
              stderr0,
              fs2,
              stdout2,
              stderr2,
              ok,
              visit,
              now
            )
  {
  }

  ghost predicate RuntimeFilesOutcomeCore(
    files: seq<string>,
    i: nat,
    cmd: Schema.ChmodCmd,
    plan: Base.CoreModePlan,
    cwd: BenchWorld.Path,
    fs0: BenchWorld.FileSystem,
    stdout0: BenchWorld.Bytes,
    stderr0: BenchWorld.Bytes,
    fs2: BenchWorld.FileSystem,
    stdout2: BenchWorld.Bytes,
    stderr2: BenchWorld.Bytes,
    allOk: bool,
    visits: seq<RecursiveVisit>,
    now: int
  )
    requires i <= |files|
  {
    |visits| == |files| - i &&
    (forall j :: 0 <= j < |visits| ==>
                   var identity := VisitIdentityCore(visits[j]);
                   identity.displayPath == files[i + j] &&
                   identity.accessPath == Base.MakeAbsoluteCore(cwd, files[i + j]) &&
                   identity.isTopLevel) &&
    ValidVisitsCore(cmd, plan, visits, 0, {}, fs0, now) &&
    var result := EvalChildrenCore(cmd, plan, visits, 0, {}, fs0, now);
    fs2 == result.fs &&
    stdout2 == stdout0 + result.stdoutChunk &&
    stderr2 == stderr0 + result.stderrChunk &&
    allOk == result.allOk
  }

  lemma EmptyNodeEvaluationCore(
    cmd: Schema.ChmodCmd,
    plan: Base.CoreModePlan,
    identity: RecursiveIdentity,
    activeSegments: set<seq<string>>,
    fs: BenchWorld.FileSystem,
    now: int
  )
    ensures var parent := ApplyResolvedCore(cmd, plan, identity, fs, now);
            EvalVisitCore(
              cmd,
              plan,
              RecursiveNode(identity, [], RecursiveEof),
              activeSegments,
              fs,
              now
            ) == RecursiveResult(
              parent.fs,
              parent.stdoutChunk,
              parent.stderrChunk,
              parent.ok
            )
  {
    if BenchWorld.PathSegments(identity.resolvedPath) !in activeSegments {
      assert EvalChildrenCore(
          cmd,
          plan,
          [],
          0,
          activeSegments + {BenchWorld.PathSegments(identity.resolvedPath)},
          ApplyResolvedCore(cmd, plan, identity, fs, now).fs,
          now
        ) == RecursiveResult(
                    ApplyResolvedCore(cmd, plan, identity, fs, now).fs,
                    [],
                    [],
                    true
                  );
    }
  }

  lemma NonDirectoryLeafValidCore(
    cmd: Schema.ChmodCmd,
    plan: Base.CoreModePlan,
    identity: RecursiveIdentity,
    activeSegments: set<seq<string>>,
    fs: BenchWorld.FileSystem,
    now: int
  )
    requires IdentityResolvesCore(fs, identity)
    requires !identity.isDirectory
    requires !identity.isSymlink ||
             TraversalFollowCore(cmd, identity.isTopLevel) ||
             ChmodFollowCore(cmd, identity.isTopLevel)
    ensures ValidVisitCore(
              cmd,
              plan,
              RecursiveNode(identity, [], RecursiveEof),
              activeSegments,
              fs,
              now
            )
  {
    reveal ValidVisitCore;
  }

  lemma NonTraversedSymlinkLeafValidCore(
    cmd: Schema.ChmodCmd,
    plan: Base.CoreModePlan,
    identity: RecursiveIdentity,
    activeSegments: set<seq<string>>,
    fs: BenchWorld.FileSystem,
    now: int
  )
    requires IdentityResolvesCore(fs, identity)
    requires identity.isSymlink
    requires !TraversalFollowCore(cmd, identity.isTopLevel)
    requires ChmodFollowCore(cmd, identity.isTopLevel)
    requires !(cmd.preserveRoot && identity.isDirectory &&
               identity.resolvedPath == "/")
    ensures ValidVisitCore(
              cmd,
              plan,
              RecursiveNode(identity, [], RecursiveEof),
              activeSegments,
              fs,
              now
            )
  {
    reveal ValidVisitCore;
  }

  lemma CycleLeafValidCore(
    cmd: Schema.ChmodCmd,
    plan: Base.CoreModePlan,
    identity: RecursiveIdentity,
    activeSegments: set<seq<string>>,
    fs: BenchWorld.FileSystem,
    now: int
  )
    requires IdentityResolvesCore(fs, identity)
    requires !identity.isSymlink ||
             TraversalFollowCore(cmd, identity.isTopLevel) ||
             ChmodFollowCore(cmd, identity.isTopLevel)
    requires !(cmd.preserveRoot && identity.isDirectory &&
               identity.resolvedPath == "/")
    requires BenchWorld.PathSegments(identity.resolvedPath) in activeSegments
    ensures ValidVisitCore(
              cmd,
              plan,
              RecursiveNode(identity, [], RecursiveEof),
              activeSegments,
              fs,
              now
            )
  {
    reveal ValidVisitCore;
  }

  lemma RuntimeIdentityResolvesCore(
    fs: BenchWorld.FileSystem,
    cwd: BenchWorld.Path,
    displayPath: string,
    accessPath: BenchWorld.Path,
    resolvedPath: BenchWorld.Path,
    isTopLevel: bool,
    isSymlink: bool,
    isDirectory: bool
  )
    requires IOContract.IsSymlinkContractFields(
               fs, accessPath, true, isSymlink, 0
             )
    requires IOContract.ResolvePathIdentityContractFields(
               fs, cwd, accessPath, true, resolvedPath, 0
             )
    requires BenchWorld.IsAbsolutePath(accessPath)
    requires IOContract.IsDirectoryContractFields(
               fs, accessPath, true, true, isDirectory, 0
             )
    ensures IdentityResolvesCore(
              fs,
              RecursiveIdentity(
                displayPath,
                accessPath,
                resolvedPath,
                isTopLevel,
                isSymlink,
                isDirectory
              )
            )
  {
  }

  lemma ExhaustedScheduleSetCore(
    snapshot: set<BenchWorld.DirEntry>,
    entries: seq<BenchWorld.DirEntry>,
    remaining: set<BenchWorld.DirEntry>
  )
    requires remaining == snapshot - EntriesSet(entries)
    requires remaining == {}
    requires forall j :: 0 <= j < |entries| ==>
                           entries[j] in snapshot
    ensures EntriesSet(entries) == snapshot
  {
    assert snapshot <= EntriesSet(entries) by {
      forall entry | entry in snapshot
        ensures entry in EntriesSet(entries)
      {
        if entry !in EntriesSet(entries) {
          assert entry in snapshot - EntriesSet(entries);
          assert entry in remaining;
          assert false;
        }
      }
    }
    assert EntriesSet(entries) <= snapshot by {
      forall entry | entry in EntriesSet(entries)
        ensures entry in snapshot
      {
        var j :| 0 <= j < |entries| && entry == entries[j];
      }
    }
  }

  function SegmentPaths(fs: BenchWorld.FileSystem): set<seq<string>>
  {
    BenchWorld.FsPathSegments(fs)
  }

  lemma LookupSegmentsInSegmentPaths(
    fs: BenchWorld.FileSystem,
    segments: seq<string>
  )
    requires BenchWorld.FsLookupSegments(fs, segments).Ok?
    ensures segments in SegmentPaths(fs)
  {
    WorldProof.FsLookupSegmentsInPathSet(fs, segments);
  }

  lemma CoreModeSetPreservesDirectory(
    fs: BenchWorld.FileSystem,
    path: BenchWorld.Path,
    mode: bv32,
    now: int
  )
    requires BenchWorld.FsContainsPath(fs, path)
    requires BenchWorld.FsNodeAt(fs, path).Directory?
    ensures BenchWorld.FsContainsPath(
              Base.CoreModeSetFs(fs, true, path, mode, now), path
            )
    ensures BenchWorld.FsNodeAt(
              Base.CoreModeSetFs(fs, true, path, mode, now), path
            ).Directory?
  {
    var next := BenchWorld.WithNodeChangeTime(
                  BenchWorld.WithNodeMode(
                    BenchWorld.FsNodeAt(fs, path), mode
                  ),
                  now,
                  0
                );
    assert BenchWorld.InodeSameNodeKind(
             BenchWorld.FsNodeAt(fs, path), next
           );
    WorldProof.FsSetPathIsInodeFsUpdateNode(fs, path, next);
    WorldProof.InodeUpdateAliasVisible(fs, path, path, next);
  }

  lemma ApplyResolvedPreservesDirectory(
    cmd: Schema.ChmodCmd,
    plan: Base.CoreModePlan,
    identity: RecursiveIdentity,
    fs: BenchWorld.FileSystem,
    now: int
  )
    requires IdentityResolvesCore(fs, identity)
    requires identity.isDirectory
    ensures var result := ApplyResolvedCore(cmd, plan, identity, fs, now);
            BenchWorld.FsContainsPath(result.fs, identity.resolvedPath) &&
            BenchWorld.FsNodeAt(result.fs, identity.resolvedPath).Directory?
  {
    if !(identity.isSymlink &&
         !ChmodFollowCore(cmd, identity.isTopLevel)) {
      var node := BenchWorld.FsNodeAt(fs, identity.resolvedPath);
      var desired := Base.CorePlannedMode(
        plan,
        BenchWorld.NodeMode(node),
        identity.isDirectory
      );
      CoreModeSetPreservesDirectory(
        fs, identity.resolvedPath, desired, now
      );
    }
  }

  lemma SetFileModePreservesSegmentPaths(
    fs: BenchWorld.FileSystem,
    path: BenchWorld.Path,
    follow: bool,
    mode: bv32,
    ok: bool,
    err: int,
    fs2: BenchWorld.FileSystem
  )
    requires IOContract.SetFileModeContractFields(
               fs, path, follow, mode, ok, err, fs2
             )
    ensures SegmentPaths(fs2) == SegmentPaths(fs)
  {
    if ok {
      match IOContract.ResolvePathForMetadataFields(fs, path, follow)
      case Err(_) =>
      case Ok(target) => WorldProof.SetNodeModePreservesPathSet(fs, target, mode);
    }
  }

  twostate predicate RecursiveCoreSummary(
    raw: Schema.ChmodCmdRaw,
    io: BenchIO.IO,
    exit: int
  )
    reads io.Footprint()
  {
    var cmd := Schema.Command(raw);
    cmd.recursive &&
    io.dirHandles() == old(io.dirHandles()) &&
    if cmd.mode == Schema.ModeHelp || cmd.mode == Schema.ModeVersion then
      Base.CoreSummary(raw, io, exit)
    else if cmd.dereferenceMode == 1 && cmd.traversalMode == 0 then
      io.fs() == old(io.fs()) &&
      io.stdout() == old(io.stdout()) &&
      io.stderr() == old(io.stderr()) +
      RecursiveDereferenceRequirementMessageCore() &&
      exit == 1
    else if (cmd.seenReference && cmd.diagnoseSurprises) ||
            |cmd.files| == 0 ||
            ((cmd.seenReference &&
              Base.CoreReferenceFailure(cmd, old(io.fs()), old(io.cwd()))) ||
             (!cmd.seenReference &&
              !Schema.IsValidModeExpr(cmd.modeExpr))) then
      Base.CoreSummary(raw, io, exit)
    else
      exists plan: Base.CoreModePlan, visits: seq<RecursiveVisit> ::
        RecursivePlanCore(
          cmd, old(io.fs()), old(io.cwd()), old(io.props()), plan
        ) &&
        TopLevelVisitsCore(
          cmd, plan, old(io.cwd()), visits, old(io.fs()), old(io.now())
        ) &&
        var result := EvalChildrenCore(
                        cmd,
                        plan,
                        visits,
                        0,
                        {},
                        old(io.fs()),
                        old(io.now())
                      );
        io.fs() == result.fs &&
        io.stdout() == old(io.stdout()) + result.stdoutChunk &&
        io.stderr() == old(io.stderr()) + result.stderrChunk &&
        exit == (if result.allOk then 0 else 1)
  }

}
