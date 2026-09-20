include "../../core/World.dfy"
include "../../core/Utf8.dfy"
include "../../core/IO.dfy"
include "ChmodSchema.dfy"
include "ChmodSpec.dfy"
include "ChmodQuoteSpec.dfy"

module ChmodRecursiveSpec {
  import BenchWorld
  import BenchIO
  import Utf8 = Utf8Semantics
  import Schema = ChmodSchema
  import Base = ChmodSpec
  import Quote = ChmodQuoteSpec
  import IOC = IOContract

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

  function VisitSizeSpec(visit: RecursiveVisit): nat
    decreases visit
  {
    match visit
    case RecursiveSkip(_) | RecursiveAccessFailure(_, _, _) |
      RecursivePreserveRoot(_, _) => 1
    case RecursiveNode(_, children, _) => 1 + VisitsSizeSpec(children)
  }

  function VisitsSizeSpec(visits: seq<RecursiveVisit>): nat
    decreases visits
  {
    if |visits| == 0 then 0
    else VisitSizeSpec(visits[0]) + VisitsSizeSpec(visits[1..])
  }

  function TraversalFollowSpec(cmd: Schema.ChmodCmd, isTopLevel: bool): bool
  {
    cmd.traversalMode == 2 || (cmd.traversalMode == 1 && isTopLevel)
  }

  function ChmodFollowSpec(cmd: Schema.ChmodCmd, isTopLevel: bool): bool
  {
    if cmd.dereferenceMode == 1 then true
    else if cmd.dereferenceMode == 0 then false
    else TraversalFollowSpec(cmd, isTopLevel)
  }

  function RootPreserveMessageSpec(displayPath: string, alias: bool): BenchWorld.Bytes
  {
    if alias then
      "chmod: it is dangerous to operate recursively on " +
      Quote.SpecQuoteAfBytes(Utf8.Encode(displayPath)) + " (same as '/')\n" +
      "chmod: use --no-preserve-root to override this failsafe\n"
    else
      "chmod: it is dangerous to operate recursively on '/'\n" +
      "chmod: use --no-preserve-root to override this failsafe\n"
  }

  function ReadDirectoryMessageSpec(path: string, err: int): BenchWorld.Bytes
  {
    "chmod: cannot read directory " +
    Quote.SpecQuoteAfBytes(Utf8.Encode(path)) + ": " +
    Base.ErrnoTextSpec(err) + "\n"
  }

  function DanglingSymlinkMessageSpec(path: string): BenchWorld.Bytes
  {
    Base.DanglingSymlinkMessageSpec(path)
  }

  function CannotDereferenceMessageSpec(path: string, err: int): BenchWorld.Bytes
  {
    "chmod: cannot dereference " +
    Quote.SpecQuoteAfBytes(Utf8.Encode(path)) + ": " +
    Base.ErrnoTextSpec(err) + "\n"
  }

  function NeitherChangedMessageSpec(path: string): BenchWorld.Bytes
  {
    Base.NeitherChangedMessageSpec(path)
  }

  function RecursiveDereferenceRequirementMessageSpec(): BenchWorld.Bytes
  {
    "chmod: -R --dereference requires either -H or -L\n"
  }

  function RecursiveAccessStdoutSpec(cmd: Schema.ChmodCmd, path: string): BenchWorld.Bytes
  {
    if cmd.verbose then Base.AccessFailureMessageSpec(path) else []
  }

  function RecursiveAccessStderrSpec(
    cmd: Schema.ChmodCmd,
    path: string,
    err: int,
    failureKind: RecursiveFailureKind
  ): BenchWorld.Bytes
  {
    if cmd.silent then []
    else if failureKind.RecursiveDangling? then DanglingSymlinkMessageSpec(path)
    else if failureKind.RecursiveDereference? then
      CannotDereferenceMessageSpec(path, err)
    else Base.AccessErrorMessageSpec(path, Base.ErrnoTextSpec(err))
  }

  function ResolutionFailureKindSpec(
    cmd: Schema.ChmodCmd,
    isTopLevel: bool,
    isSymlink: bool,
    err: int
  ): RecursiveFailureKind
  {
    if isSymlink && !TraversalFollowSpec(cmd, isTopLevel) &&
       ChmodFollowSpec(cmd, isTopLevel) then
      RecursiveDereference
    else if Base.SpecIsDanglingSymlinkFailure(isSymlink, err) then
      RecursiveDangling
    else
      RecursiveAccess
  }

  function RecursiveSkipStdoutSpec(cmd: Schema.ChmodCmd, path: string): BenchWorld.Bytes
  {
    if cmd.verbose then NeitherChangedMessageSpec(path) else []
  }

  function RecursiveReadStdoutSpec(
    cmd: Schema.ChmodCmd,
    path: string,
    terminal: RecursiveTerminal
  ): BenchWorld.Bytes
  {
    match terminal
    case RecursiveEof => []
    case RecursiveReadError(_) =>
      if cmd.verbose then Base.AccessFailureMessageSpec(path) else []
  }

  function RecursiveReadStderrSpec(
    cmd: Schema.ChmodCmd,
    path: string,
    terminal: RecursiveTerminal
  ): BenchWorld.Bytes
  {
    match terminal
    case RecursiveEof => []
    case RecursiveReadError(err) =>
      if cmd.silent then [] else ReadDirectoryMessageSpec(path, err)
  }

  ghost predicate ApplyResolvedSpecRelation(
    cmd: Schema.ChmodCmd,
    plan: Base.SpecModePlan,
    identity: RecursiveIdentity,
    fs: BenchWorld.FileSystem,
    result: Base.SpecPathResult,
    now: int
  )
  {
    if identity.isSymlink && !ChmodFollowSpec(cmd, identity.isTopLevel) then
      result == Base.SpecPathResult(
        fs,
        RecursiveSkipStdoutSpec(cmd, identity.displayPath),
        [],
        true,
        Base.SpecPathRetained(0 as bv32)
      )
    else if !BenchWorld.FsContainsPath(fs, identity.resolvedPath) then
      result == Base.SpecPathResult(
        fs,
        RecursiveAccessStdoutSpec(cmd, identity.displayPath),
        RecursiveAccessStderrSpec(
          cmd, identity.displayPath, 2, RecursiveAccess
        ),
        false,
        Base.SpecPathAccessFailed(2)
      )
    else
      var node := BenchWorld.FsNodeAt(fs, identity.resolvedPath);
      var before := BenchWorld.NodeMode(node);
      exists desired: bv32 ::
        Base.SpecPlannedModeRelation(
          plan, before, identity.isDirectory, desired
        ) &&
        var next := Base.SpecModeSetFs(
                      fs,
                      true,
                      identity.resolvedPath,
                      desired,
                      now
                    );
        var after := BenchWorld.NormalizeMode(desired);
        Base.SpecSuccessfulChangeResultRelation(
          cmd,
          plan,
          identity.displayPath,
          identity.accessPath,
          true,
          before,
          after,
          identity.isDirectory,
          next,
          result
        )
  }

  predicate DuplicateFreePrefix(entries: seq<BenchWorld.DirEntry>)
  {
    forall i, j :: 0 <= i < j < |entries| ==> entries[i] != entries[j]
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

  function VisitIdentitySpec(visit: RecursiveVisit): RecursiveIdentity
  {
    match visit
    case RecursiveSkip(identity) => identity
    case RecursiveAccessFailure(identity, _, _) => identity
    case RecursivePreserveRoot(identity, _) => identity
    case RecursiveNode(identity, _, _) => identity
  }

  ghost predicate IdentityResolvesSpec(
    fs: BenchWorld.FileSystem,
    identity: RecursiveIdentity
  )
  {
    match IOC.ResolvePathForMetadataFields(fs, identity.accessPath, false)
    case Err(_) => false
    case Ok(rawResolved) =>
      BenchWorld.FsContainsPath(fs, rawResolved) &&
      identity.isSymlink == BenchWorld.FsNodeAt(fs, rawResolved).Symlink? &&
      match IOC.ResolvePathForMetadataFields(fs, identity.accessPath, true)
      case Err(_) => false
      case Ok(resolved) =>
        identity.resolvedPath == resolved &&
        BenchWorld.FsContainsPath(fs, resolved) &&
        identity.isDirectory ==
        BenchWorld.FsNodeAt(fs, resolved).Directory?
  }

  ghost predicate VisitMatchesEntrySpec(
    parent: RecursiveIdentity,
    entry: BenchWorld.DirEntry,
    visit: RecursiveVisit
  )
  {
    var child := VisitIdentitySpec(visit);
    child.displayPath == BenchWorld.AppendPath(parent.displayPath, entry.name) &&
    child.accessPath == BenchWorld.AppendPath(parent.resolvedPath, entry.name) &&
    !child.isTopLevel
  }

  ghost predicate SkipVisitSpec(
    cmd: Schema.ChmodCmd,
    identity: RecursiveIdentity,
    fs: BenchWorld.FileSystem
  )
  {
    match IOC.ResolvePathForMetadataFields(fs, identity.accessPath, false)
    case Err(_) => false
    case Ok(rawResolved) =>
      BenchWorld.FsContainsPath(fs, rawResolved) &&
      BenchWorld.FsNodeAt(fs, rawResolved).Symlink? &&
      identity.isSymlink &&
      identity.resolvedPath == "" &&
      !identity.isDirectory &&
      !ChmodFollowSpec(cmd, identity.isTopLevel) &&
      (!TraversalFollowSpec(cmd, identity.isTopLevel) ||
       match IOC.ResolvePathForMetadataFields(
           fs, identity.accessPath, true
         )
       case Err(error) => Base.SpecIsDanglingSymlinkFailure(
         identity.isSymlink, IOC.IOErrorErrno(error)
       )
       case Ok(_) => false)
  }

  ghost predicate AccessFailureVisitSpec(
    cmd: Schema.ChmodCmd,
    identity: RecursiveIdentity,
    err: int,
    failureKind: RecursiveFailureKind,
    fs: BenchWorld.FileSystem
  )
  {
    match IOC.ResolvePathForMetadataFields(fs, identity.accessPath, false)
    case Err(error) =>
      err == IOC.IOErrorErrno(error) &&
      failureKind.RecursiveAccess? &&
      !identity.isSymlink &&
      identity.resolvedPath == "" &&
      !identity.isDirectory
    case Ok(rawResolved) =>
      if !BenchWorld.FsContainsPath(fs, rawResolved) then
        err == IOC.MetadataFailureErrFields(
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
        (!isLink || ChmodFollowSpec(cmd, identity.isTopLevel) ||
         (TraversalFollowSpec(cmd, identity.isTopLevel) &&
          !Base.SpecIsDanglingSymlinkFailure(isLink, err))) &&
        FollowAccessFailureVisitSpec(
          cmd,
          identity,
          isLink,
          err,
          failureKind,
          fs
        )
  }

  ghost predicate FollowAccessFailureVisitSpec(
    cmd: Schema.ChmodCmd,
    identity: RecursiveIdentity,
    isLink: bool,
    err: int,
    failureKind: RecursiveFailureKind,
    fs: BenchWorld.FileSystem
  )
  {
    match IOC.ResolvePathForMetadataFields(fs, identity.accessPath, true)
    case Err(error) =>
      err == IOC.IOErrorErrno(error) &&
      failureKind == ResolutionFailureKindSpec(
        cmd, identity.isTopLevel, isLink, err
      )
    case Ok(_) => false
  }

  ghost predicate VisitOutcomeBodySpec(
    cmd: Schema.ChmodCmd,
    plan: Base.SpecModePlan,
    visit: RecursiveVisit,
    activeResolved: set<seq<string>>,
    fs0: BenchWorld.FileSystem,
    fs2: BenchWorld.FileSystem,
    stdoutChunk: BenchWorld.Bytes,
    stderrChunk: BenchWorld.Bytes,
    allOk: bool,
    now: int
  )
    decreases VisitSizeSpec(visit), 0
  {
    var identity := VisitIdentitySpec(visit);
    match visit
    case RecursiveSkip(_) =>
      SkipVisitSpec(cmd, identity, fs0) &&
      fs2 == fs0 &&
      stdoutChunk == RecursiveSkipStdoutSpec(cmd, identity.displayPath) &&
      stderrChunk == [] &&
      allOk
    case RecursiveAccessFailure(_, err, failureKind) =>
      AccessFailureVisitSpec(cmd, identity, err, failureKind, fs0) &&
      fs2 == fs0 &&
      stdoutChunk == RecursiveAccessStdoutSpec(cmd, identity.displayPath) &&
      stderrChunk == RecursiveAccessStderrSpec(
        cmd, identity.displayPath, err, failureKind
      ) &&
      !allOk
    case RecursivePreserveRoot(_, alias) =>
      IdentityResolvesSpec(fs0, identity) &&
      (!identity.isSymlink ||
       TraversalFollowSpec(cmd, identity.isTopLevel) ||
       ChmodFollowSpec(cmd, identity.isTopLevel)) &&
      cmd.preserveRoot &&
      identity.isDirectory &&
      identity.resolvedPath == "/" &&
      alias == (identity.accessPath != "/") &&
      fs2 == fs0 &&
      stdoutChunk == [] &&
      stderrChunk == RootPreserveMessageSpec(identity.displayPath, alias) &&
      !allOk
    case RecursiveNode(_, children, terminal) =>
      IdentityResolvesSpec(fs0, identity) &&
      (!identity.isSymlink ||
       TraversalFollowSpec(cmd, identity.isTopLevel) ||
       ChmodFollowSpec(cmd, identity.isTopLevel)) &&
      !(cmd.preserveRoot && identity.isDirectory &&
        identity.resolvedPath == "/") &&
      exists parent: Base.SpecPathResult ::
        ApplyResolvedSpecRelation(cmd, plan, identity, fs0, parent, now) &&
        if BenchWorld.PathSegments(identity.resolvedPath) in activeResolved then
          |children| == 0 &&
          terminal.RecursiveEof? &&
          fs2 == parent.fs &&
          stdoutChunk == parent.stdoutChunk &&
          stderrChunk == parent.stderrChunk &&
          allOk == parent.ok
        else
          (if identity.isSymlink &&
              !TraversalFollowSpec(cmd, identity.isTopLevel) then
             |children| == 0 && terminal.RecursiveEof?
           else if !identity.isDirectory then
             |children| == 0 && terminal.RecursiveEof?
           else
             BenchWorld.FsContainsPath(parent.fs, identity.resolvedPath) &&
             exists entries: seq<BenchWorld.DirEntry> ::
               |entries| == |children| &&
               ValidOpenSchedule(
                 IOC.DirectoryEntriesForPathFields(
                   parent.fs,
                   identity.resolvedPath
                 ),
                 entries,
                 terminal
               ) &&
               (forall j :: 0 <= j < |children| ==>
                              VisitMatchesEntrySpec(
                                identity, entries[j], children[j]
                              ))) &&
          exists descendantsStdout: BenchWorld.Bytes,
            descendantsStderr: BenchWorld.Bytes,
            descendantsOk: bool ::
            VisitsOutcomeSpec(
              cmd,
              plan,
              children,
              activeResolved + {
                BenchWorld.PathSegments(identity.resolvedPath)
              },
              parent.fs,
              fs2,
              descendantsStdout,
              descendantsStderr,
              descendantsOk,
              now
            ) &&
            stdoutChunk ==
            parent.stdoutChunk + descendantsStdout +
            RecursiveReadStdoutSpec(
              cmd, identity.displayPath, terminal
            ) &&
            stderrChunk ==
            parent.stderrChunk + descendantsStderr +
            RecursiveReadStderrSpec(
              cmd, identity.displayPath, terminal
            ) &&
            allOk == (
              parent.ok && descendantsOk && terminal.RecursiveEof?
            )
  }

  opaque ghost predicate VisitOutcomeSpec(
    cmd: Schema.ChmodCmd,
    plan: Base.SpecModePlan,
    visit: RecursiveVisit,
    activeResolved: set<seq<string>>,
    fs0: BenchWorld.FileSystem,
    fs2: BenchWorld.FileSystem,
    stdoutChunk: BenchWorld.Bytes,
    stderrChunk: BenchWorld.Bytes,
    allOk: bool,
    now: int
  )
    decreases VisitSizeSpec(visit), 1
  {
    VisitOutcomeBodySpec(
      cmd,
      plan,
      visit,
      activeResolved,
      fs0,
      fs2,
      stdoutChunk,
      stderrChunk,
      allOk,
      now
    )
  }

  lemma IntroduceVisitOutcomeSpec(
    cmd: Schema.ChmodCmd,
    plan: Base.SpecModePlan,
    visit: RecursiveVisit,
    activeResolved: set<seq<string>>,
    fs0: BenchWorld.FileSystem,
    fs2: BenchWorld.FileSystem,
    stdoutChunk: BenchWorld.Bytes,
    stderrChunk: BenchWorld.Bytes,
    allOk: bool,
    now: int
  )
    requires VisitOutcomeBodySpec(
               cmd,
               plan,
               visit,
               activeResolved,
               fs0,
               fs2,
               stdoutChunk,
               stderrChunk,
               allOk,
               now
             )
    ensures VisitOutcomeSpec(
              cmd,
              plan,
              visit,
              activeResolved,
              fs0,
              fs2,
              stdoutChunk,
              stderrChunk,
              allOk,
              now
            )
  {
    reveal VisitOutcomeSpec;
  }

  opaque ghost predicate VisitsOutcomeSpec(
    cmd: Schema.ChmodCmd,
    plan: Base.SpecModePlan,
    visits: seq<RecursiveVisit>,
    activeResolved: set<seq<string>>,
    fs0: BenchWorld.FileSystem,
    fs2: BenchWorld.FileSystem,
    stdoutChunk: BenchWorld.Bytes,
    stderrChunk: BenchWorld.Bytes,
    allOk: bool,
    now: int
  )
    decreases VisitsSizeSpec(visits), 2
  {
    if |visits| == 0 then
      fs2 == fs0 &&
      stdoutChunk == [] &&
      stderrChunk == [] &&
      allOk
    else
      exists stepFs: BenchWorld.FileSystem,
        stepStdout: BenchWorld.Bytes,
        stepStderr: BenchWorld.Bytes,
        stepOk: bool,
        restStdout: BenchWorld.Bytes,
        restStderr: BenchWorld.Bytes,
        restOk: bool ::
        VisitOutcomeSpec(
          cmd,
          plan,
          visits[0],
          activeResolved,
          fs0,
          stepFs,
          stepStdout,
          stepStderr,
          stepOk,
          now
        ) &&
        VisitsOutcomeSpec(
          cmd,
          plan,
          visits[1..],
          activeResolved,
          stepFs,
          fs2,
          restStdout,
          restStderr,
          restOk,
          now
        ) &&
        stdoutChunk == stepStdout + restStdout &&
        stderrChunk == stepStderr + restStderr &&
        allOk == (stepOk && restOk)
  }

  ghost predicate TopLevelOutcomeSpec(
    cmd: Schema.ChmodCmd,
    plan: Base.SpecModePlan,
    cwd: BenchWorld.Path,
    visits: seq<RecursiveVisit>,
    fs0: BenchWorld.FileSystem,
    fs2: BenchWorld.FileSystem,
    stdoutChunk: BenchWorld.Bytes,
    stderrChunk: BenchWorld.Bytes,
    allOk: bool,
    now: int
  )
  {
    |visits| == |cmd.files| &&
    (forall i :: 0 <= i < |visits| ==>
                   var identity := VisitIdentitySpec(visits[i]);
                   identity.displayPath == cmd.files[i] &&
                   identity.accessPath == Base.MakeAbsolute(cwd, cmd.files[i]) &&
                   identity.isTopLevel) &&
    VisitsOutcomeSpec(
      cmd, plan, visits, {}, fs0, fs2,
      stdoutChunk, stderrChunk, allOk, now
    )
  }

  ghost predicate RecursivePlanSpec(
    cmd: Schema.ChmodCmd,
    fs: BenchWorld.FileSystem,
    cwd: BenchWorld.Path,
    props: map<string, string>,
    plan: Base.SpecModePlan
  )
  {
    if !cmd.seenReference then
      Base.SpecGeneralModePlanRelation(
        cmd.modeExpr,
        IOC.GetUmaskResultFields(props),
        plan
      )
    else
      exists referenceMode: bv32 ::
        IOC.GetFileModeContractFields(
          fs,
          Base.MakeAbsolute(cwd, cmd.referenceFile),
          true,
          true,
          referenceMode,
          0
        ) &&
        plan == Base.SpecReferenceModePlan(referenceMode)
  }

  twostate predicate RecursiveSpec(
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
      Base.Spec(raw, io, exit)
    else if cmd.dereferenceMode == 1 && cmd.traversalMode == 0 then
      io.fs() == old(io.fs()) &&
      io.stdout() == old(io.stdout()) &&
      io.stderr() == old(io.stderr()) +
      RecursiveDereferenceRequirementMessageSpec() &&
      exit == 1
    else if (cmd.seenReference && cmd.diagnoseSurprises) ||
            |cmd.files| == 0 ||
            ((cmd.seenReference &&
              Base.SpecReferenceFailure(cmd, old(io.fs()), old(io.cwd()))) ||
             (!cmd.seenReference &&
              !Schema.IsValidModeExpr(cmd.modeExpr))) then
      Base.Spec(raw, io, exit)
    else
      exists plan: Base.SpecModePlan ::
        RecursivePlanSpec(
          cmd, old(io.fs()), old(io.cwd()), old(io.props()), plan
        ) &&
        exists visits: seq<RecursiveVisit>,
          stdoutChunk: BenchWorld.Bytes,
          stderrChunk: BenchWorld.Bytes,
          allOk: bool ::
          TopLevelOutcomeSpec(
            cmd,
            plan,
            old(io.cwd()),
            visits,
            old(io.fs()),
            io.fs(),
            stdoutChunk,
            stderrChunk,
            allOk,
            old(io.now())
          ) &&
          io.stdout() == old(io.stdout()) + stdoutChunk &&
          io.stderr() == old(io.stderr()) + stderrChunk &&
          exit == (if allOk then 0 else 1)
  }

  // Public raw-command semantics cover both recursive and nonrecursive modes.
  twostate predicate Spec(
    raw: Schema.ChmodCmdRaw,
    io: BenchIO.IO,
    exit: int
  )
    reads io.Footprint()
  {
    !Base.SpecExternalDomain(raw) ||
    (if Schema.Command(raw).recursive then
       RecursiveSpec(raw, io, exit)
     else
       Base.Spec(raw, io, exit))
  }

  twostate lemma NonrecursiveBaseSpecImpliesSpec(
    raw: Schema.ChmodCmdRaw,
    io: BenchIO.IO,
    exit: int
  )
    requires !Schema.Command(raw).recursive
    requires Base.Spec(raw, io, exit)
    ensures Spec(raw, io, exit)
  {
    reveal Spec;
  }

}
