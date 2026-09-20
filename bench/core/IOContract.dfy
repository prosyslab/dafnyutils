include "World.dfy"
include "WorldLookupProof.dfy"
include "WorldRenameProof.dfy"

module IOContract {
  import opened BenchWorld
  import LookupProof = WorldLookupProof
  import RenameProof = WorldRenameProof

  function GetCwdResultFields(cwd: Path): Path { cwd }

  function GetUmaskResultFields(props: map<string, string>): bv32 { ParsedUmaskFromProps(props) }

  predicate GetEnvContractFields(env: map<string, string>, key: string, r: Result<string>)
  {
    if key in env then
      r == Ok(env[key])
    else
      match r
      case Err(_) => true
      case Ok(_) => false
  }

  ghost predicate EnvironmentKey(key: string)
  {
    |key| > 0 &&
    (forall i :: 0 <= i < |key| ==>
                   key[i] != '=' && key[i] != (0 as char))
  }

  ghost predicate ValidEnvironment(env: map<string, string>)
  {
    forall key :: key in env ==> EnvironmentKey(key)
  }

  type Environment = env: map<string, string> | ValidEnvironment(env)
    witness map[]

  ghost predicate EnvEntriesRepresentEnv(env: map<string, string>, entries: seq<string>)
  {
    (forall i, j :: 0 <= i < j < |entries| ==> entries[i] != entries[j]) &&
    (forall key :: key in env ==> EnvironmentKey(key)) &&
    (exists keys: seq<string> ::
       |keys| == |entries| &&
       (forall i :: 0 <= i < |entries| ==>
                      keys[i] in env &&
                      entries[i] == keys[i] + "=" + env[keys[i]])) &&
    (forall key :: key in env ==>
                     exists i :: 0 <= i < |entries| && entries[i] == key + "=" + env[key])
  }

  ghost predicate GetEnvironmentContractFields(
    env: map<string, string>,
    entries: seq<string>
  )
    requires ValidEnvironment(env)
  {
    EnvEntriesRepresentEnv(env, entries)
  }

  predicate GetLoginNameContractFields(props: map<string, string>, r: Result<string>)
  {
    if "loginName" in props then
      r == Ok(props["loginName"])
    else
      match r
      case Err(_) => true
      case Ok(_) => false
  }

  function TrustedTimeParseResultFields(
    parses: map<TimeParseRequest, ParsedTimeResult>,
    request: TimeParseRequest
  ): ParsedTimeResult
  {
    if request in parses then parses[request] else ParsedTimeResult(false, 0, 0)
  }

  ghost predicate ParseTimestampContractFields(
    parses: map<TimeParseRequest, ParsedTimeResult>,
    timestamp: string, nowSec: int, nowNsec: int,
    ok: bool, sec: int, nsec: int
  )
  {
    ParsedTimeResult(ok, sec, nsec) == TrustedTimeParseResultFields(
      parses, TimestampParseRequest(timestamp, nowSec, nowNsec)
    ) &&
    (ok ==> 0 <= nsec < 1000000000)
  }

  ghost predicate ParseDateContractFields(
    parses: map<TimeParseRequest, ParsedTimeResult>,
    date: string, refSec: int, refNsec: int,
    ok: bool, sec: int, nsec: int
  )
  {
    ParsedTimeResult(ok, sec, nsec) == TrustedTimeParseResultFields(
      parses, DateParseRequest(date, refSec, refNsec)
    ) &&
    (ok ==> 0 <= nsec < 1000000000)
  }

  // Resolves a path component-by-component so symlinked directories are
  // traversed before the terminal symlink decision.
  function ResolvePathThroughSymlinkComponentsFields(
    fs: FileSystem,
    path: Path,
    followTerminalSymlink: bool
  ): Result<Path>
  {
    ResolvePathThroughSymlinkComponentsWithVisitedFields(
      fs,
      path,
      {},
      SYMLINK_MAX_DEPTH,
      followTerminalSymlink
    )
  }

  function HasTrailingSlash(path: Path): bool
  {
    |path| > 0 && path[|path| - 1] == '/'
  }

  function ResolvePathThroughSymlinkComponentsWithVisitedFields(
    fs: FileSystem,
    path: Path,
    seen: set<Path>,
    fuel: nat,
    followTerminalSymlink: bool
  ): Result<Path>
    decreases fuel
  {
    if fuel == 0 then
      Err(InvalidPath)
    else
      ResolveRawSymlinkSegmentsFields(
        fs,
        RawPathSegmentsFields(path),
        0,
        if IsAbsolutePath(path) then "/" else "",
        seen,
        fuel,
        followTerminalSymlink,
        false,
        HasTrailingSlash(path)
      )
  }

  function RawPathSegmentsFields(path: Path): seq<string>
  {
    SplitSegments(StripLeadingSlash(path), 0, 0)
  }

  function HasRawTerminalSpecialFields(path: Path): bool
  {
    if HasTrailingSlash(path) then
      var segments := RawPathSegmentsFields(path);
      |segments| > 0 &&
      (segments[|segments| - 1] == "." ||
       segments[|segments| - 1] == "..")
    else
      var length := |path|;
      (length > 0 &&
       path[length - 1] == '.' &&
       (length == 1 || path[length - 2] == '/')) ||
      (length > 1 &&
       path[length - 2] == '.' &&
       path[length - 1] == '.' &&
       (length == 2 || path[length - 3] == '/'))
  }

  function IsNonRootRawEntryPathFields(path: Path): bool
  {
    |RawPathSegmentsFields(path)| > 0 &&
    !HasRawTerminalSpecialFields(path)
  }

  function ResolvePathThroughSymlinkExactWithVisitedFields(
    fs: FileSystem,
    path: Path,
    seen: set<Path>,
    fuel: nat,
    followTerminalSymlink: bool
  ): Result<Path>
    decreases fuel
  {
    if fuel == 0 then
      Err(InvalidPath)
    else if path in seen then
      Err(InvalidPath)
    else if !FsContainsPath(fs, path) then
      Err(NoSuchFile)
    else
      match FsNodeAt(fs, path)
      case Regular(_, _, _, _) => Ok(path)
      case Directory(_, _, _) => Ok(path)
      case Inaccessible(_) => Err(PermissionDenied)
      case Symlink(target, _, _, _) =>
        if followTerminalSymlink then
          var next := ResolveSymlinkTarget(path, target);
          ResolvePathThroughSymlinkExactWithVisitedFields(
            fs,
            next,
            seen + {path},
            fuel - 1,
            followTerminalSymlink
          )
        else
          Ok(path)
  }

  function DirectNoFollowResultFields(
    fs: FileSystem,
    path: Path
  ): Result<Path>
  {
    if path == "" then
      Err(NoSuchFile)
    else
      match FsLookupNode(fs, path)
      case Err(error) => Err(error)
      case Ok(node) =>
        match node
        case Inaccessible(_) => Err(PermissionDenied)
        case _ => Ok(path)
  }

  function TerminalNoFollowResultFields(
    fs: FileSystem,
    path: Path
  ): Result<Path>
  {
    if path != "" then
      DirectNoFollowResultFields(fs, path)
    else
      match FsLookupNode(fs, path)
      case Err(error) => Err(error)
      case Ok(node) =>
        match node
        case Inaccessible(_) => Err(PermissionDenied)
        case _ => Ok(path)
  }

  lemma InodeTopologyLookupTreeFields(
    before: FileSystem,
    after: FileSystem,
    tree: InodeTree,
    segs: seq<string>
  )
    requires FileSystemTopologyUnchangedExceptMode(before, after)
    ensures InodeFsLookupTreeSegments(
              before.inodes, tree, segs
            ) == InodeFsLookupTreeSegments(after.inodes, tree, segs)
    decreases |segs|
  {
    reveal FileSystemTopologyUnchangedExceptMode();
    if tree.id in before.inodes && |segs| > 0 {
      assert tree.id in after.inodes;
      assert NodeShapeUnchangedExceptMode(
          before.inodes[tree.id].node,
          after.inodes[tree.id].node
        );
      match (
          before.inodes[tree.id].node,
          after.inodes[tree.id].node
        )
      case (Directory(_, _, _), Directory(_, _, _)) =>
        if segs[0] in tree.children {
          InodeTopologyLookupTreeFields(
            before, after, tree.children[segs[0]], segs[1..]
          );
        }
      case (Regular(_, _, _, _), Regular(_, _, _, _)) =>
      case (Symlink(_, _, _, _), Symlink(_, _, _, _)) =>
      case (Inaccessible(_), Inaccessible(_)) =>
      case _ =>
        assert false by {
          reveal NodeShapeUnchangedExceptMode();
        }
    }
  }

  lemma FileSystemTopologyLookupSegmentsFields(
    before: FileSystem,
    after: FileSystem,
    segs: seq<string>
  )
    requires FileSystemTopologyUnchangedExceptMode(before, after)
    ensures FsLookupSegments(before, segs) ==
            FsLookupSegments(after, segs)
  {
    reveal FileSystemTopologyUnchangedExceptMode();
    assert before.namespace == after.namespace;
    InodeTopologyLookupTreeFields(
      before, after, before.namespace, segs
    );
  }

  lemma FileSystemTopologyPathFields(
    before: FileSystem,
    after: FileSystem,
    path: Path
  )
    requires FileSystemTopologyUnchangedExceptMode(before, after)
    ensures FsContainsPath(before, path) == FsContainsPath(after, path)
    ensures FsContainsPath(before, path) ==>
              NodeShapeUnchangedExceptMode(
                FsNodeAt(before, path), FsNodeAt(after, path)
              )
  {
    FileSystemTopologyLookupSegmentsFields(
      before, after, PathSegments(path)
    );
    reveal FsContainsPath(), FsLookupNode(), FsNodeAt();
    reveal InodeFsContainsPath(), InodeFsLookupNode(),
           InodeFsLookupId(), FsLookupSegments();
    if FsContainsPath(before, path) {
      var id := InodeFsLookupId(before, path).v;
      reveal FileSystemTopologyUnchangedExceptMode();
      assert id in before.inodes;
      assert id in after.inodes;
    }
  }

  lemma DirectNoFollowResultEqualExceptModeFields(
    before: FileSystem,
    after: FileSystem,
    path: Path
  )
    requires FileSystemTopologyUnchangedExceptMode(before, after)
    ensures DirectNoFollowResultFields(before, path) ==
            DirectNoFollowResultFields(after, path)
    ensures TerminalNoFollowResultFields(before, path) ==
            TerminalNoFollowResultFields(after, path)
  {
    FileSystemTopologyPathFields(before, after, path);
    FileSystemTopologyLookupSegmentsFields(
      before,
      after,
      PathSegments(path)
    );
    reveal DirectNoFollowResultFields(), TerminalNoFollowResultFields();
    reveal FsLookupNode(), InodeFsLookupNode(), InodeFsLookupId();
    if FsContainsPath(before, path) {
      reveal FileSystemTopologyUnchangedExceptMode();
      reveal NodeShapeUnchangedExceptMode();
    }
  }

  lemma DirectNoFollowSuccessContainsFields(fs: FileSystem, path: Path)
    requires DirectNoFollowResultFields(fs, path).Ok?
    ensures FsContainsPath(fs, path)
  {
    reveal DirectNoFollowResultFields();
    reveal FsLookupNode(), FsContainsPath();
    reveal InodeFsLookupNode(), InodeFsContainsPath();
  }

  lemma TerminalNoFollowSuccessContainsFields(fs: FileSystem, path: Path)
    requires TerminalNoFollowResultFields(fs, path).Ok?
    ensures FsContainsPath(fs, path)
  {
    reveal TerminalNoFollowResultFields();
    if path != "" {
      DirectNoFollowSuccessContainsFields(fs, path);
    } else {
      reveal FsLookupNode(), FsContainsPath();
      reveal InodeFsLookupNode(), InodeFsContainsPath();
    }
  }

  function ResolveRawSymlinkSegmentsFields(
    fs: FileSystem,
    segs: seq<string>,
    i: nat,
    current: Path,
    seen: set<Path>,
    fuel: nat,
    followTerminalSymlink: bool,
    allowMissingTerminal: bool,
    requireDirectory: bool
  ): (result: Result<Path>)
    requires i <= |segs|
    ensures !allowMissingTerminal && result.Ok? ==>
              FsContainsPath(fs, result.v) && !FsNodeAt(fs, result.v).Inaccessible?
    decreases fuel, |segs| - i
  {
    if i == |segs| then
      match TerminalNoFollowResultFields(fs, current)
      case Err(error) => Err(error)
      case Ok(_) =>
        match FsNodeAt(fs, current)
        case Regular(_, _, _, _) =>
          if requireDirectory then Err(NotDirectory) else Ok(current)
        case Directory(_, _, _) => Ok(current)
        case Inaccessible(_) => Err(PermissionDenied)
        case Symlink(target, _, _, _) =>
          if !followTerminalSymlink && !requireDirectory then
            Ok(current)
          else if target == "" then
            Err(NoSuchFile)
          else if fuel == 0 then
            Err(InvalidPath)
          else
            ResolveRawSymlinkSegmentsFields(
              fs,
              RawPathSegmentsFields(target),
              0,
              if IsAbsolutePath(target) then "/" else ParentPath(current),
              seen + {current},
              fuel - 1,
              followTerminalSymlink,
              allowMissingTerminal,
              requireDirectory || HasTrailingSlash(target)
            )
    else if FsContainsPath(fs, current) &&
            FsNodeAt(fs, current).Directory? &&
            !FixtureOwnerCanSearch(FsNodeAt(fs, current)) then
      Err(PermissionDenied)
    else if segs[i] == "." || segs[i] == ".." then
      match TerminalNoFollowResultFields(fs, current)
      case Err(error) => Err(error)
      case Ok(_) =>
        match FsNodeAt(fs, current)
        case Regular(_, _, _, _) => Err(NotDirectory)
        case Directory(_, _, _) =>
          ResolveRawSymlinkSegmentsFields(
            fs,
            segs,
            i + 1,
            if segs[i] == ".." then ParentPath(current) else current,
            seen,
            fuel,
            followTerminalSymlink,
            allowMissingTerminal,
            requireDirectory
          )
        case Inaccessible(_) => Err(PermissionDenied)
        case Symlink(target, _, _, _) =>
          if target == "" then
            Err(NoSuchFile)
          else if fuel == 0 then
            Err(InvalidPath)
          else
            ResolveRawSymlinkSegmentsFields(
              fs,
              RawPathSegmentsFields(target) + segs[i..],
              0,
              if IsAbsolutePath(target) then "/" else ParentPath(current),
              seen + {current},
              fuel - 1,
              followTerminalSymlink,
              allowMissingTerminal,
              requireDirectory
            )
    else
      var next := AppendPath(current, segs[i]);
      match DirectNoFollowResultFields(fs, next)
      case Err(NoSuchFile) =>
        if allowMissingTerminal &&
           i + 1 == |segs| &&
           !requireDirectory
        then
          Ok(next)
        else
          Err(NoSuchFile)
      case Err(error) => Err(error)
      case Ok(_) =>
        match FsNodeAt(fs, next)
        case Regular(_, _, _, _) =>
          if i + 1 == |segs| && !requireDirectory then
            Ok(next)
          else
            Err(NotDirectory)
        case Directory(_, _, _) =>
          ResolveRawSymlinkSegmentsFields(
            fs,
            segs,
            i + 1,
            next,
            seen,
            fuel,
            followTerminalSymlink,
            allowMissingTerminal,
            requireDirectory
          )
        case Inaccessible(_) => Err(PermissionDenied)
        case Symlink(target, _, _, _) =>
          if i + 1 == |segs| &&
             !followTerminalSymlink && !requireDirectory then
            Ok(next)
          else if target == "" then
            Err(NoSuchFile)
          else if fuel == 0 then
            Err(InvalidPath)
          else
            var remaining := segs[i + 1..];
            ResolveRawSymlinkSegmentsFields(
              fs,
              RawPathSegmentsFields(target) + remaining,
              0,
              if IsAbsolutePath(target) then "/" else ParentPath(next),
              seen + {next},
              fuel - 1,
              followTerminalSymlink,
              allowMissingTerminal,
              requireDirectory ||
              (|remaining| == 0 && HasTrailingSlash(target))
            )
  }

  lemma ResolveRawSuccessfulTargetsEqualExceptModeFieldsInternal(
    before: FileSystem,
    after: FileSystem,
    segs: seq<string>,
    i: nat,
    current: Path,
    seen: set<Path>,
    fuel: nat,
    followTerminalSymlink: bool,
    requireDirectory: bool,
    beforeTarget: Path,
    afterTarget: Path
  )
    requires FileSystemTopologyUnchangedExceptMode(before, after)
    requires i <= |segs|
    requires ResolveRawSymlinkSegmentsFields(
               before, segs, i, current, seen, fuel,
               followTerminalSymlink, false, requireDirectory
             ) == Ok(beforeTarget)
    requires ResolveRawSymlinkSegmentsFields(
               after, segs, i, current, seen, fuel,
               followTerminalSymlink, false, requireDirectory
             ) == Ok(afterTarget)
    ensures beforeTarget == afterTarget
    decreases fuel, |segs| - i
  {
    reveal ResolveRawSymlinkSegmentsFields();
    if i == |segs| {
      DirectNoFollowResultEqualExceptModeFields(before, after, current);
      assert TerminalNoFollowResultFields(before, current).Ok?;
      assert TerminalNoFollowResultFields(after, current).Ok?;
      TerminalNoFollowSuccessContainsFields(before, current);
      TerminalNoFollowSuccessContainsFields(after, current);
      FileSystemTopologyPathFields(before, after, current);
      match (FsNodeAt(before, current), FsNodeAt(after, current))
      case (Regular(_, _, _, _), Regular(_, _, _, _)) =>
      case (Directory(_, _, _), Directory(_, _, _)) =>
      case (Inaccessible(_), Inaccessible(_)) =>
      case (Symlink(beforeLink, _, _, _), Symlink(afterLink, _, _, _)) =>
        assert beforeLink == afterLink by {
          reveal NodeShapeUnchangedExceptMode();
        }
        if followTerminalSymlink || requireDirectory {
          assert beforeLink != "";
          assert fuel > 0;
          ResolveRawSuccessfulTargetsEqualExceptModeFieldsInternal(
            before,
            after,
            RawPathSegmentsFields(beforeLink),
            0,
            if IsAbsolutePath(beforeLink) then "/" else ParentPath(current),
            seen + {current},
            fuel - 1,
            followTerminalSymlink,
            requireDirectory || HasTrailingSlash(beforeLink),
            beforeTarget,
            afterTarget
          );
        }
      case _ =>
        assert false by {
          reveal NodeShapeUnchangedExceptMode();
        }
    } else if segs[i] == "." || segs[i] == ".." {
      DirectNoFollowResultEqualExceptModeFields(before, after, current);
      assert TerminalNoFollowResultFields(before, current).Ok?;
      assert TerminalNoFollowResultFields(after, current).Ok?;
      TerminalNoFollowSuccessContainsFields(before, current);
      TerminalNoFollowSuccessContainsFields(after, current);
      FileSystemTopologyPathFields(before, after, current);
      match (FsNodeAt(before, current), FsNodeAt(after, current))
      case (Regular(_, _, _, _), Regular(_, _, _, _)) =>
      case (Directory(_, _, _), Directory(_, _, _)) =>
        ResolveRawSuccessfulTargetsEqualExceptModeFieldsInternal(
          before,
          after,
          segs,
          i + 1,
          if segs[i] == ".." then ParentPath(current) else current,
          seen,
          fuel,
          followTerminalSymlink,
          requireDirectory,
          beforeTarget,
          afterTarget
        );
      case (Inaccessible(_), Inaccessible(_)) =>
      case (Symlink(beforeLink, _, _, _), Symlink(afterLink, _, _, _)) =>
        assert beforeLink == afterLink by {
          reveal NodeShapeUnchangedExceptMode();
        }
        assert beforeLink != "";
        assert fuel > 0;
        ResolveRawSuccessfulTargetsEqualExceptModeFieldsInternal(
          before,
          after,
          RawPathSegmentsFields(beforeLink) + segs[i..],
          0,
          if IsAbsolutePath(beforeLink) then "/" else ParentPath(current),
          seen + {current},
          fuel - 1,
          followTerminalSymlink,
          requireDirectory,
          beforeTarget,
          afterTarget
        );
      case _ =>
        assert false by {
          reveal NodeShapeUnchangedExceptMode();
        }
    } else {
      var next := AppendPath(current, segs[i]);
      DirectNoFollowResultEqualExceptModeFields(before, after, next);
      assert DirectNoFollowResultFields(before, next).Ok?;
      assert DirectNoFollowResultFields(after, next).Ok?;
      DirectNoFollowSuccessContainsFields(before, next);
      DirectNoFollowSuccessContainsFields(after, next);
      FileSystemTopologyPathFields(before, after, next);
      match (FsNodeAt(before, next), FsNodeAt(after, next))
      case (Regular(_, _, _, _), Regular(_, _, _, _)) =>
      case (Directory(_, _, _), Directory(_, _, _)) =>
        ResolveRawSuccessfulTargetsEqualExceptModeFieldsInternal(
          before,
          after,
          segs,
          i + 1,
          next,
          seen,
          fuel,
          followTerminalSymlink,
          requireDirectory,
          beforeTarget,
          afterTarget
        );
      case (Inaccessible(_), Inaccessible(_)) =>
      case (Symlink(beforeLink, _, _, _), Symlink(afterLink, _, _, _)) =>
        assert beforeLink == afterLink by {
          reveal NodeShapeUnchangedExceptMode();
        }
        if i + 1 < |segs| || followTerminalSymlink || requireDirectory {
          assert beforeLink != "";
          assert fuel > 0;
          var remaining := segs[i + 1..];
          ResolveRawSuccessfulTargetsEqualExceptModeFieldsInternal(
            before,
            after,
            RawPathSegmentsFields(beforeLink) + remaining,
            0,
            if IsAbsolutePath(beforeLink) then "/" else ParentPath(next),
            seen + {next},
            fuel - 1,
            followTerminalSymlink,
            requireDirectory ||
            (|remaining| == 0 && HasTrailingSlash(beforeLink)),
            beforeTarget,
            afterTarget
          );
        }
      case _ =>
        assert false by {
          reveal NodeShapeUnchangedExceptMode();
        }
    }
  }

  function ResolvePathThroughSymlinkSegmentsWithVisitedFields(
    fs: FileSystem,
    segs: seq<string>,
    i: nat,
    current: Path,
    seen: set<Path>,
    fuel: nat,
    followTerminalSymlink: bool
  ): Result<Path>
    requires 0 <= i <= |segs|
  {
    ResolvePathThroughSymlinkSegmentsWithTrailingFields(
      fs,
      segs,
      i,
      current,
      seen,
      fuel,
      followTerminalSymlink,
      false
    )
  }

  function ResolvePathThroughSymlinkSegmentsWithTrailingFields(
    fs: FileSystem,
    segs: seq<string>,
    i: nat,
    current: Path,
    seen: set<Path>,
    fuel: nat,
    followTerminalSymlink: bool,
    requireDirectory: bool
  ): Result<Path>
    requires 0 <= i <= |segs|
    decreases fuel, |segs| - i
  {
    if fuel == 0 then
      Err(InvalidPath)
    else if i >= |segs| then
      if current in seen then
        Err(InvalidPath)
      else if current == "" then
        Err(NoSuchFile)
      else
        match DirectNoFollowResultFields(fs, current)
        case Err(error) => Err(error)
        case Ok(_) =>
          match FsNodeAt(fs, current)
          case Regular(_, _, _, _) =>
            if requireDirectory then Err(NotDirectory) else Ok(current)
          case Directory(_, _, _) => Ok(current)
          case Inaccessible(_) => Err(PermissionDenied)
          case Symlink(target, _, _, _) =>
            if !followTerminalSymlink && !requireDirectory then
              Ok(current)
            else
              var resolvedTarget := ResolveSymlinkTarget(current, target);
              ResolvePathThroughSymlinkSegmentsWithTrailingFields(
                fs,
                PathSegments(resolvedTarget),
                0,
                if IsAbsolutePath(resolvedTarget) then "/" else "",
                seen + {current},
                fuel - 1,
                followTerminalSymlink,
                requireDirectory || HasTrailingSlash(target)
              )
    else
      var next := AppendPath(current, segs[i]);
      if next in seen then
        Err(InvalidPath)
      else
        match DirectNoFollowResultFields(fs, next)
        case Err(error) => Err(error)
        case Ok(_) =>
          match FsNodeAt(fs, next)
          case Regular(_, _, _, _) =>
            if i + 1 == |segs| && !requireDirectory then
              Ok(next)
            else
              Err(NotDirectory)
          case Directory(_, _, _) =>
            ResolvePathThroughSymlinkSegmentsWithTrailingFields(
              fs,
              segs,
              i + 1,
              next,
              seen,
              fuel,
              followTerminalSymlink,
              requireDirectory
            )
          case Inaccessible(_) => Err(PermissionDenied)
          case Symlink(target, _, _, _) =>
            if i + 1 == |segs| && !followTerminalSymlink && !requireDirectory then
              Ok(next)
            else
              var resolvedTarget := ResolveSymlinkTarget(next, target);
              var remaining := segs[i + 1..];
              var restarted := PathSegments(resolvedTarget) + remaining;
              ResolvePathThroughSymlinkSegmentsWithTrailingFields(
                fs,
                restarted,
                0,
                if IsAbsolutePath(resolvedTarget) then "/" else "",
                seen + {next},
                fuel - 1,
                followTerminalSymlink,
                requireDirectory || (|remaining| == 0 && HasTrailingSlash(target))
              )
  }

  function ResolvePathForMetadataFields(fs: FileSystem, path: Path, followSymlink: bool): (result: Result<Path>)
    ensures result.Ok? ==>
              FsContainsPath(fs, result.v) && !FsNodeAt(fs, result.v).Inaccessible?
  {
    if path == "" then
      Err(NoSuchFile)
    else
      var result := ResolvePathThroughSymlinkComponentsFields(fs, path, followSymlink);
      if path[|path| - 1] != '/' then
        result
      else
        match result
        case Err(e) => Err(e)
        case Ok(resolved) =>
          if !FsContainsPath(fs, resolved) then
            Err(NoSuchFile)
          else
            match FsNodeAt(fs, resolved)
            case Directory(_, _, _) => Ok(resolved)
            case Regular(_, _, _, _) | Symlink(_, _, _, _) => Err(NotDirectory)
            case Inaccessible(_) => Err(PermissionDenied)
  }

  lemma ResolvePathForMetadataSuccessfulTargetsEqualExceptModeFields(
    before: FileSystem,
    after: FileSystem,
    path: Path,
    follow: bool,
    beforeTarget: Path,
    afterTarget: Path
  )
    requires FileSystemTopologyUnchangedExceptMode(before, after)
    requires ResolvePathForMetadataFields(before, path, follow) ==
             Ok(beforeTarget)
    requires ResolvePathForMetadataFields(after, path, follow) ==
             Ok(afterTarget)
    ensures beforeTarget == afterTarget
  {
    assert path != "";
    assert ResolvePathThroughSymlinkComponentsFields(
        before, path, follow
      ) == Ok(beforeTarget) by {
      reveal ResolvePathForMetadataFields();
    }
    assert ResolvePathThroughSymlinkComponentsFields(
        after, path, follow
      ) == Ok(afterTarget) by {
      reveal ResolvePathForMetadataFields();
    }
    assert SYMLINK_MAX_DEPTH > 0 by {
      reveal SYMLINK_MAX_DEPTH;
    }
    assert ResolveRawSymlinkSegmentsFields(
        before,
        RawPathSegmentsFields(path),
        0,
        if IsAbsolutePath(path) then "/" else "",
        {},
        SYMLINK_MAX_DEPTH,
        follow,
        false,
        HasTrailingSlash(path)
      ) == Ok(beforeTarget) by {
      reveal ResolvePathThroughSymlinkComponentsFields();
      reveal ResolvePathThroughSymlinkComponentsWithVisitedFields();
    }
    assert ResolveRawSymlinkSegmentsFields(
        after,
        RawPathSegmentsFields(path),
        0,
        if IsAbsolutePath(path) then "/" else "",
        {},
        SYMLINK_MAX_DEPTH,
        follow,
        false,
        HasTrailingSlash(path)
      ) == Ok(afterTarget) by {
      reveal ResolvePathThroughSymlinkComponentsFields();
      reveal ResolvePathThroughSymlinkComponentsWithVisitedFields();
    }
    ResolveRawSuccessfulTargetsEqualExceptModeFieldsInternal(
      before,
      after,
      RawPathSegmentsFields(path),
      0,
      if IsAbsolutePath(path) then "/" else "",
      {},
      SYMLINK_MAX_DEPTH,
      follow,
      HasTrailingSlash(path),
      beforeTarget,
      afterTarget
    );
  }

  function ReadFileResultFields(fs: FileSystem, path: Path): Result<Bytes>
  {
    match ResolvePathThroughSymlinkComponentsFields(fs, path, true)
    case Ok(resolved) =>
      if FsContainsPath(fs, resolved) then
        match FsNodeAt(fs, resolved)
        case Regular(data, _, _, _) => Ok(data)
        case Directory(_, _, _) => Err(IsDirectory)
        case Symlink(_, _, _, _) => Err(InvalidPath)
        case Inaccessible(_) => Err(PermissionDenied)
      else
        Err(NoSuchFile)
    case Err(e) => Err(e)
  }

  predicate BytesPrefix(prefix: Bytes, whole: Bytes)
  {
    |prefix| <= |whole| && prefix == whole[..|prefix|]
  }

  ghost predicate TrustedReadFileWithOutcomeContractFields(
    observations: (TrustedStreamRequest) -> TrustedStreamResult,
    fs: FileSystem,
    path: Path,
    data: Bytes,
    err: int
  )
  {
    match observations(StreamReadFile(fs, path))
    case StreamReadFileResult(observedData, observedErr) =>
      data == observedData && err == observedErr && 0 <= err &&
      (match ReadFileResultFields(fs, path)
       case Ok(contents) =>
         BytesPrefix(data, contents) && (err == 0 ==> data == contents)
       case Err(_) => data == [] && err != 0)
    case StreamReadStdinResult(_, _, _) => false
    case StreamWriteResult(_, _, _) => false
  }

  ghost predicate TrustedReadStdinWithOutcomeContractFields(
    observations: (TrustedStreamRequest) -> TrustedStreamResult,
    beforeStdin: Bytes,
    afterStdin: Bytes,
    data: Bytes,
    err: int
  )
  {
    match observations(StreamReadStdin(beforeStdin))
    case StreamReadStdinResult(observedData, observedRemaining, observedErr) =>
      data == observedData && afterStdin == observedRemaining && err == observedErr &&
      0 <= err && data + afterStdin == beforeStdin &&
      (err == 0 ==> afterStdin == [])
    case StreamReadFileResult(_, _) => false
    case StreamWriteResult(_, _, _) => false
  }

  ghost predicate TrustedWriteWithOutcomeFields(
    observed: TrustedStreamResult,
    beforeOutput: Bytes,
    afterOutput: Bytes,
    requested: Bytes,
    committed: nat,
    err: int
  )
  {
    match observed
    case StreamWriteResult(observedCommitted, observedOutput, observedErr) =>
      committed == observedCommitted && afterOutput == observedOutput && err == observedErr &&
      committed <= |requested| && 0 <= err &&
      afterOutput == beforeOutput + requested[..committed] &&
      (err == 0 <==> committed == |requested|)
    case StreamReadFileResult(_, _) => false
    case StreamReadStdinResult(_, _, _) => false
  }

  ghost predicate TrustedWriteStdoutWithOutcomeContractFields(
    observations: (TrustedStreamRequest) -> TrustedStreamResult,
    beforeStdout: Bytes,
    afterStdout: Bytes,
    requested: Bytes,
    committed: nat,
    err: int
  )
  {
    TrustedWriteWithOutcomeFields(
      observations(StreamWriteStdout(beforeStdout, requested)),
      beforeStdout, afterStdout, requested, committed, err
    )
  }

  ghost predicate TrustedWriteStderrWithOutcomeContractFields(
    observations: (TrustedStreamRequest) -> TrustedStreamResult,
    beforeStderr: Bytes,
    afterStderr: Bytes,
    requested: Bytes,
    committed: nat,
    err: int
  )
  {
    TrustedWriteWithOutcomeFields(
      observations(StreamWriteStderr(beforeStderr, requested)),
      beforeStderr, afterStderr, requested, committed, err
    )
  }

  function ReadLinkResultFields(fs: FileSystem, path: Path): Result<Path>
  {
    match ResolvePathForMetadataFields(fs, path, false)
    case Ok(resolved) =>
      if FsContainsPath(fs, resolved) then
        match FsNodeAt(fs, resolved)
        case Symlink(target, _, _, _) => Ok(target)
        case _ => Err(InvalidPath)
      else
        Err(NoSuchFile)
    case Err(e) => Err(e)
  }

  function AfterReadStdinFields(beforeStdin: Bytes): Bytes { [] }

  predicate ReadStdinAllFields(beforeStdin: Bytes, afterStdin: Bytes, b: Bytes) { b == beforeStdin && afterStdin == AfterReadStdinFields(beforeStdin) }

  function AfterAppendStdoutFields(beforeStdout: Bytes, b: Bytes): Bytes { beforeStdout + b }

  predicate AppendStdoutFields(beforeStdout: Bytes, afterStdout: Bytes, b: Bytes) { afterStdout == AfterAppendStdoutFields(beforeStdout, b) }

  function AfterAppendStderrFields(beforeStderr: Bytes, b: Bytes): Bytes { beforeStderr + b }

  predicate AppendStderrFields(beforeStderr: Bytes, afterStderr: Bytes, b: Bytes) { afterStderr == AfterAppendStderrFields(beforeStderr, b) }

  function IOErrorErrno(err: IOError): int
  {
    match err
    case NoSuchFile => 2
    case PermissionDenied => 13
    case NotDirectory => 20
    case IsDirectory => 21
    case InvalidPath => 40
    case Other(_) => 5
  }

  function MetadataFailureErrFields(fs: FileSystem, path: Path, followSymlink: bool): int
  {
    match ResolvePathForMetadataFields(fs, path, followSymlink)
    case Err(e) => IOErrorErrno(e)
    case Ok(resolved) => if FsContainsPath(fs, resolved) then 0 else 2
  }

  function OpenDirFailureErrFields(fs: FileSystem, path: Path): int
  {
    match ResolvePathForMetadataFields(fs, path, true)
    case Err(e) => IOErrorErrno(e)
    case Ok(resolved) =>
      if !FsContainsPath(fs, resolved) then
        2
      else
        match FsNodeAt(fs, resolved)
        case Directory(_, _, _) => 0
        case _ => 20
  }

  predicate PathExistsContractFields(fs: FileSystem, path: Path, followSymlink: bool, found: bool, err: int)
  {
    found == (match ResolvePathForMetadataFields(fs, path, followSymlink)
              case Err(_) => false
              case Ok(resolved) => FsContainsPath(fs, resolved)) &&
    err == (if found then 0
            else MetadataFailureErrFields(fs, path, followSymlink))
  }

  ghost predicate TrustedFilesystemQueryContractFields(
    observations: (TrustedFilesystemRequest) -> TrustedFilesystemResult,
    fs: FileSystem,
    path: Path,
    followSymlink: bool,
    ok: bool,
    atimeSec: int,
    atimeNsec: int,
    mtimeSec: int,
    mtimeNsec: int,
    isDir: bool,
    isSymlink: bool,
    device: int,
    inode: int,
    linkCount: int,
    err: int
  )
  {
    var observed := observations(FilesystemQuery(fs, path, followSymlink));
    observed.postFs == fs &&
    ok == observed.ok &&
    err == observed.err &&
    atimeSec == observed.atimeSec &&
    atimeNsec == observed.atimeNsec &&
    mtimeSec == observed.mtimeSec &&
    mtimeNsec == observed.mtimeNsec &&
    isDir == observed.isDir &&
    isSymlink == observed.isSymlink &&
    device == observed.device &&
    inode == observed.inode &&
    linkCount == observed.linkCount
  }

  ghost predicate TrustedPathExistsContractFields(
    observations: (TrustedFilesystemRequest) -> TrustedFilesystemResult,
    fs: FileSystem,
    path: Path,
    followSymlink: bool,
    found: bool,
    err: int
  )
  {
    var observed := observations(FilesystemQuery(fs, path, followSymlink));
    observed.postFs == fs && found == observed.ok && err == observed.err
  }

  ghost predicate TrustedCreateFileContractFields(
    observations: (TrustedFilesystemRequest) -> TrustedFilesystemResult,
    fs: FileSystem,
    now: int,
    path: Path,
    ok: bool,
    err: int,
    fs2: FileSystem
  )
  {
    var observed := observations(FilesystemCreate(fs, path, now));
    ok == observed.ok && err == observed.err && fs2 == observed.postFs
  }

  ghost predicate TrustedFilesystemEffectContractFields(
    observations: (TrustedFilesystemRequest) -> TrustedFilesystemResult,
    request: TrustedFilesystemRequest,
    ok: bool,
    err: int,
    fs2: FileSystem
  )
  {
    var observed := observations(request);
    ok == observed.ok && err == observed.err && fs2 == observed.postFs &&
    0 <= err && (ok <==> err == 0)
  }

  ghost predicate TrustedFilesystemSyncContractFields(
    observations: (TrustedFilesystemRequest) -> TrustedFilesystemResult,
    fs: FileSystem,
    target: SyncTarget,
    mode: SyncMode,
    ok: bool,
    err: int
  )
  {
    var observed := observations(FilesystemSync(fs, target, mode));
    observed.postFs == fs && ok == observed.ok && err == observed.err &&
    0 <= err && (ok <==> err == 0)
  }

  predicate GetFileModeContractFields(fs: FileSystem, path: Path, followSymlink: bool, ok: bool, mode: bv32, err: int)
  {
    (!ok ==> err == MetadataFailureErrFields(fs, path, followSymlink)) &&
    (ok ==>
       err == 0 &&
       match ResolvePathForMetadataFields(fs, path, followSymlink)
       case Ok(resolved) =>
         FsContainsPath(fs, resolved) &&
         mode == NodeMode(FsNodeAt(fs, resolved))
       case Err(_) => false) &&
    (match ResolvePathForMetadataFields(fs, path, followSymlink)
     case Err(_) => !ok
     case Ok(resolved) => FsContainsPath(fs, resolved) ==> ok)
  }

  function GetFileStatusResultFields(
    fs: FileSystem,
    path: Path,
    followSymlink: bool
  ): Result<FileStatus>
  {
    match ResolvePathForMetadataFields(fs, path, followSymlink)
    case Err(error) => Err(error)
    case Ok(resolved) =>
      if !FsContainsPath(fs, resolved) then
        Err(NoSuchFile)
      else
        var record := fs.inodes[FsIdAt(fs, resolved)];
        match record.node
        case Inaccessible(_) => Err(PermissionDenied)
        case _ =>
          match record.links
          case LinkCountUnknown => Err(Other("unknown link count"))
          case LinkCountKnown(_) => Ok(FileStatusForRecord(record))
  }

  predicate FileStatusObservationFields(expected: FileStatus, observed: FileStatus)
  {
    observed == expected
  }

  predicate GetFileStatusContractFields(
    fs: FileSystem,
    path: Path,
    followSymlink: bool,
    ok: bool,
    status: FileStatus,
    err: int
  )
  {
    match GetFileStatusResultFields(fs, path, followSymlink)
    case Ok(expected) => ok && FileStatusObservationFields(expected, status) && err == 0
    case Err(error) => !ok && err == IOErrorErrno(error)
  }

  // A mode observation is a projection of the single stat observation.
  lemma FileStatusImpliesMode(
    fs: FileSystem, path: Path, followSymlink: bool,
    ok: bool, status: FileStatus, err: int
  )
    requires GetFileStatusContractFields(fs, path, followSymlink, ok, status, err)
    ensures GetFileModeContractFields(fs, path, followSymlink, ok, status.mode, err)
  {
    var resolved := ResolvePathForMetadataFields(fs, path, followSymlink);
    if resolved.Ok? {
      var id := FsIdAt(fs, resolved.v);
      assert fs.inodes[id].links.LinkCountKnown?;
      assert FsNodeAt(fs, resolved.v) == fs.inodes[id].node;
    }
  }

  // These are ghost consequences of stat fields, not executable convenience calls.
  lemma FileStatusImpliesMetadata(
    fs: FileSystem, path: Path, followSymlink: bool,
    ok: bool, status: FileStatus, err: int
  )
    requires GetFileStatusContractFields(fs, path, followSymlink, ok, status, err)
    ensures PathExistsContractFields(fs, path, followSymlink, ok, err)
    ensures IsDirectoryStrictContractFields(
              fs, path, followSymlink, ok, status.kind == DirectoryKind, err)
    ensures !followSymlink ==>
              IsSymlinkContractFields(fs, path, ok, status.kind == SymlinkKind, err)
    ensures GetFileTimesContractFields(
              fs, path, followSymlink, ok,
              status.times.atimeSec, status.times.atimeNsec,
              status.times.mtimeSec, status.times.mtimeNsec,
              status.kind == DirectoryKind, status.kind == SymlinkKind,
              status.hostKey.device, status.hostKey.inode, status.linkCount, err)
  {
    var resolved := ResolvePathForMetadataFields(fs, path, followSymlink);
    if resolved.Ok? {
      var id := FsIdAt(fs, resolved.v);
      assert fs.inodes[id].links.LinkCountKnown?;
      assert FsNodeAt(fs, resolved.v) == fs.inodes[id].node;
      assert InodeKindConsistent(fs.inodes[id]);
    }
  }

  predicate IsDirectoryContractFields(fs: FileSystem, path: Path, followSymlink: bool, ok: bool, isDir: bool, err: int)
  {
    (!ok ==> err == MetadataFailureErrFields(fs, path, followSymlink)) &&
    (ok ==>
       err == 0 &&
       match ResolvePathForMetadataFields(fs, path, followSymlink)
       case Ok(resolved) =>
         FsContainsPath(fs, resolved) &&
         isDir ==
         (match FsNodeAt(fs, resolved)
          case Directory(_, _, _) => true
          case _ => false)
       case Err(_) => false) &&
    (match ResolvePathForMetadataFields(fs, path, followSymlink)
     case Err(_) => !ok
     case Ok(resolved) => FsContainsPath(fs, resolved) ==> ok)
  }

  predicate IsDirectoryStrictContractFields(fs: FileSystem, path: Path, followSymlink: bool, ok: bool, isDir: bool, err: int)
  {
    IsDirectoryContractFields(fs, path, followSymlink, ok, isDir, err) &&
    (match ResolvePathForMetadataFields(fs, path, followSymlink)
     case Err(_) => !ok
     case Ok(_) => ok)
  }

  predicate IsSymlinkContractFields(fs: FileSystem, path: Path, ok: bool, isSymlink: bool, err: int)
  {
    (!ok ==> err == MetadataFailureErrFields(fs, path, false)) &&
    (ok ==>
       err == 0 &&
       match ResolvePathForMetadataFields(fs, path, false)
       case Ok(resolved) =>
         FsContainsPath(fs, resolved) &&
         isSymlink ==
         (match FsNodeAt(fs, resolved)
          case Symlink(_, _, _, _) => true
          case _ => false)
       case Err(_) => false) &&
    (match ResolvePathForMetadataFields(fs, path, false)
     case Err(_) => !ok
     case Ok(resolved) => FsContainsPath(fs, resolved) ==> ok)
  }

  function ResolvePathForCreateNoFollowTerminalFields(fs: FileSystem, path: Path): Result<Path>
  {
    if path == "" then
      Err(InvalidPath)
    else if HasTrailingSlash(path) ||
            HasRawTerminalSpecialFields(path)
    then
      ResolvePathThroughSymlinkComponentsFields(fs, path, false)
    else
      var segments := RawPathSegmentsFields(path);
      if |segments| == 0 then
        Err(InvalidPath)
      else
        var child := segments[|segments| - 1];
        var parentSegments := segments[..|segments| - 1];
        var root := if IsAbsolutePath(path) then "/" else "";
        if |parentSegments| == 0 then
          Ok(AppendPath(root, child))
        else
          match ResolveRawSymlinkSegmentsFields(
              fs,
              parentSegments,
              0,
              root,
              {},
              SYMLINK_MAX_DEPTH,
              true,
              false,
              true
            )
          case Ok(resolvedParent) =>
            if FsContainsPath(fs, resolvedParent) then
              match FsNodeAt(fs, resolvedParent)
              case Directory(_, _, _) => Ok(AppendPath(resolvedParent, child))
              case _ => Err(NotDirectory)
            else
              Err(NoSuchFile)
          case Err(e) => Err(e)
  }

  function ResolvePathForCreateFields(fs: FileSystem, path: Path): Result<Path>
  {
    if path == "" then
      Err(InvalidPath)
    else
      ResolveRawSymlinkSegmentsFields(
        fs,
        RawPathSegmentsFields(path),
        0,
        if IsAbsolutePath(path) then "/" else "",
        {},
        SYMLINK_MAX_DEPTH,
        true,
        true,
        HasTrailingSlash(path)
      )
  }

  function CreateFileFailureErrFields(fs: FileSystem, path: Path): int
  {
    if path == "" then
      22
    else
      match ResolvePathForCreateFields(fs, path)
      case Err(e) => IOErrorErrno(e)
      case Ok(target) =>
        if FsContainsPath(fs, target) then
          match FsNodeAt(fs, target)
          case Directory(_, _, _) => 21
          case _ => 0
        else
          0
  }

  ghost predicate FreshInsertionAtTimestampFields(
    fs: FileSystem,
    path: Path,
    id: InodeId,
    key: HostInodeKey,
    node: FsNode,
    timestampSec: int,
    timestampNsec: int,
    fs2: FileSystem
  )
  {
    id !in fs.inodes &&
    (forall oldId :: oldId in fs.inodes ==>
                       fs.inodes[oldId].hostKey != key) &&
    InodeCanCreateFresh(fs, path, id, key, node) &&
    exists ownership: Ownership,
      allocatedBlocks: nat,
      ioBlockBytes: nat,
      parentStorage: StorageInfo ::
      0 < ioBlockBytes &&
      DirectoryStorageObservationFields(parentStorage) &&
      fs2 == RefreshParentDirectoryStorageFields(
        InodeFsTouchParentModificationAndChangeTimestamp(
          InodeFsInsertFreshData(
            fs,
            path,
            id,
            key,
            node,
            ownership,
            StorageInfo(
              NodeStorageSize(node),
              allocatedBlocks,
              ioBlockBytes
            )
          ),
          path,
          timestampSec,
          timestampNsec
        ),
        path,
        parentStorage
      )
  }

  ghost predicate FreshInsertionFields(
    fs: FileSystem,
    now: int,
    path: Path,
    id: InodeId,
    key: HostInodeKey,
    node: FsNode,
    fs2: FileSystem
  )
  {
    FreshInsertionAtTimestampFields(
      fs, path, id, key, node, now, 0, fs2
    )
  }

  predicate DirectoryStorageObservationFields(storage: StorageInfo)
  {
    0 < storage.preferredIoBlockBytes
  }

  function RefreshParentDirectoryStorageFields(
    fs: InodeFileSystemData,
    path: Path,
    storage: StorageInfo
  ): InodeFileSystemData
  {
    var parent := ParentPath(path);
    if !InodeFsContainsPath(fs, parent) then
      fs
    else
      InodeFsRefreshDirectoryStorage(
        fs, InodeFsLookupId(fs, parent).v, storage
      )
  }

  function CreationOwnershipFields(
    fs: FileSystem,
    path: Path,
    credentials: ProcessCredentials
  ): Ownership
  {
    var parent := ParentPath(path);
    if FsContainsPath(fs, parent) &&
       FsNodeAt(fs, parent).Directory? &&
       (NodeMode(FsNodeAt(fs, parent)) & SET_GROUP_ID_MODE_BIT) !=
       0 as bv32
    then
      Ownership(
        credentials.effectiveUid,
        fs.inodes[FsIdAt(fs, parent)].ownership.gid
      )
    else
      Ownership(credentials.effectiveUid, credentials.effectiveGid)
  }

  ghost predicate CreatedPathOwnershipFields(
    fs: FileSystem,
    credentials: ProcessCredentials,
    path: Path,
    ok: bool,
    fs2: FileSystem
  )
  {
    ok ==>
      match ResolvePathForCreateNoFollowTerminalFields(fs, path)
      case Err(_) => true
      case Ok(target) =>
        if FsContainsPath(fs, target) then
          true
        else
          FsContainsPath(fs2, target) &&
          fs2.inodes[FsIdAt(fs2, target)].ownership ==
          CreationOwnershipFields(fs, target, credentials)
  }

  ghost predicate CreatedRegularModeFields(
    fs: FileSystem,
    props: map<string, string>,
    path: Path,
    ok: bool,
    fs2: FileSystem
  )
  {
    ok ==>
      match ResolvePathForCreateFields(fs, path)
      case Err(_) => true
      case Ok(target) =>
        if FsContainsPath(fs, target) then
          true
        else
          FsContainsPath(fs2, target) &&
          NodeMode(FsNodeAt(fs2, target)) == NormalizeMode(
            CREATE_FILE_MODE &
            (ParsedUmaskFromProps(props) ^ ALL_MODE_BITS)
          )
  }

  ghost predicate CreatedRegularOwnershipFields(
    fs: FileSystem,
    credentials: ProcessCredentials,
    path: Path,
    ok: bool,
    fs2: FileSystem
  )
  {
    ok ==>
      match ResolvePathForCreateFields(fs, path)
      case Err(_) => true
      case Ok(target) =>
        if FsContainsPath(fs, target) then
          true
        else
          FsContainsPath(fs2, target) &&
          fs2.inodes[FsIdAt(fs2, target)].ownership ==
          CreationOwnershipFields(fs, target, credentials)
  }

  ghost predicate CreateFileContractFields(fs: FileSystem, now: int, path: Path, ok: bool, err: int, fs2: FileSystem)
  {
    (!ok ==> fs2 == fs && err == CreateFileFailureErrFields(fs, path)) &&
    (ok ==>
       !HasTrailingSlash(path) &&
       !HasRawTerminalSpecialFields(path) &&
       err == 0 &&
       match ResolvePathForCreateFields(fs, path)
       case Ok(target) =>
         if FsContainsPath(fs, target) then
           match FsNodeAt(fs, target)
           case Directory(_, _, _) => false
           case _ => fs2 == fs
         else
           exists id: InodeId, key: HostInodeKey, createMode: bv32,
             timestampNsec: int ::
             ValidTimestampNanoseconds(timestampNsec) &&
             FreshInsertionAtTimestampFields(
               fs,
               target,
               id,
               key,
               Regular(
                 [],
                 createMode,
                 FileTimes(
                   now, timestampNsec,
                   now, timestampNsec,
                   now, timestampNsec
                 ),
                 map[]
               ),
               now,
               timestampNsec,
               fs2
             )
       case Err(_) => false) &&
    (match ResolvePathForCreateFields(fs, path)
     case Err(_) => !ok
     case Ok(target) =>
       if FsContainsPath(fs, target) then
         match FsNodeAt(fs, target)
         case Directory(_, _, _) => !ok
         case _ => ok
       else
         ok)
  }

  ghost predicate CreateFileWithCredentialsContractFields(
    fs: FileSystem,
    now: int,
    props: map<string, string>,
    credentials: ProcessCredentials,
    path: Path,
    ok: bool,
    err: int,
    fs2: FileSystem
  )
  {
    CreateFileContractFields(fs, now, path, ok, err, fs2) &&
    CreatedRegularOwnershipFields(
      fs, credentials, path, ok, fs2
    ) &&
    CreatedRegularModeFields(fs, props, path, ok, fs2)
  }

  lemma CreateFileWithCredentialsImpliesLegacy(
    fs: FileSystem,
    now: int,
    props: map<string, string>,
    credentials: ProcessCredentials,
    path: Path,
    ok: bool,
    err: int,
    fs2: FileSystem
  )
    requires CreateFileWithCredentialsContractFields(
               fs, now, props, credentials, path, ok, err, fs2
             )
    ensures CreateFileContractFields(fs, now, path, ok, err, fs2)
  {
  }

  function FsWithoutPath(fs: FileSystem, path: Path): FileSystem
  {
    FsRemovePath(fs, path)
  }

  function DeleteFsWithMetadataFields(
    fs: FileSystem,
    path: Path,
    now: int,
    parentStorage: StorageInfo
  ): InodeFileSystemData
    requires FsContainsPath(fs, path)
  {
    var id := FsIdAt(fs, path);
    var removed := FsWithoutPath(fs, path);
    var withLinkChange :=
      InodeFsTouchRecordChangeTime(removed, id, now);
    RefreshParentDirectoryStorageFields(
      InodeFsTouchParentModificationAndChangeTime(
        withLinkChange, path, now
      ),
      path,
      parentStorage
    )
  }

  function WriteFileFailureErrFields(fs: FileSystem, path: Path): int
  {
    if path == "" then
      22
    else
      match ResolvePathForCreateFields(fs, path)
      case Err(e) => IOErrorErrno(e)
      case Ok(target) =>
        if FsContainsPath(fs, target) then
          match FsNodeAt(fs, target)
          case Regular(_, _, _, _) => 0
          case Directory(_, _, _) => 21
          case Inaccessible(_) => 13
          case Symlink(_, _, _, _) => 40
        else
          0
  }

  ghost predicate WriteFileContractFields(
    fs: FileSystem,
    now: int,
    path: Path,
    data: Bytes,
    ok: bool,
    err: int,
    fs2: FileSystem
  )
  {
    // Host/device write failures after a modeled path has been accepted are
    // outside the modeled state; invalid modeled paths and node kinds are the failure cases.
    (!ok ==> fs2 == fs && err == WriteFileFailureErrFields(fs, path)) &&
    (ok ==>
       !HasTrailingSlash(path) &&
       !HasRawTerminalSpecialFields(path) &&
       err == 0 &&
       match ResolvePathForCreateFields(fs, path)
       case Ok(target) =>
         if FsContainsPath(fs, target) then
           match FsNodeAt(fs, target)
           case Regular(_, _, _, _) =>
             exists allocatedBlocks: nat, ioBlockBytes: nat ::
               0 < ioBlockBytes &&
               fs2 == InodeFsUpdateNodeAndStorage(
                 fs,
                 target,
                 WithNodeModificationAndChangeTime(
                   ToRegularNode(FsNodeAt(fs, target), data),
                   now,
                   0
                 ),
                 StorageInfo(
                   |data|, allocatedBlocks, ioBlockBytes
                 )
               )
           case _ => false
         else
           exists id: InodeId, key: HostInodeKey, createMode: bv32 ::
             FreshInsertionFields(
               fs,
               now,
               target,
               id,
               key,
               Regular(
                 data,
                 createMode,
                 FileTimes(now, 0, now, 0, now, 0),
                 map[]
               ),
               fs2
             )
       case Err(_) => false) &&
    (match ResolvePathForCreateFields(fs, path)
     case Err(_) => !ok
     case Ok(target) =>
       if FsContainsPath(fs, target) then
         match FsNodeAt(fs, target)
         case Regular(_, _, _, _) => ok
         case _ => !ok
       else
         ok)
  }

  ghost predicate WriteFileWithCredentialsContractFields(
    fs: FileSystem,
    now: int,
    props: map<string, string>,
    credentials: ProcessCredentials,
    path: Path,
    data: Bytes,
    ok: bool,
    err: int,
    fs2: FileSystem
  )
  {
    WriteFileContractFields(fs, now, path, data, ok, err, fs2) &&
    CreatedRegularOwnershipFields(
      fs, credentials, path, ok, fs2
    ) &&
    CreatedRegularModeFields(fs, props, path, ok, fs2)
  }

  lemma WriteFileWithCredentialsImpliesLegacy(
    fs: FileSystem,
    now: int,
    props: map<string, string>,
    credentials: ProcessCredentials,
    path: Path,
    data: Bytes,
    ok: bool,
    err: int,
    fs2: FileSystem
  )
    requires WriteFileWithCredentialsContractFields(
               fs, now, props, credentials, path, data, ok, err, fs2
             )
    ensures WriteFileContractFields(fs, now, path, data, ok, err, fs2)
  {
  }

  function CreateSymlinkFailureErrFields(
    fs: FileSystem,
    path: Path,
    target: Path
  ): int
  {
    if path == "" then
      22
    else if target == "" then
      2
    else
      match ResolvePathForCreateNoFollowTerminalFields(fs, path)
      case Err(e) => IOErrorErrno(e)
      case Ok(linkPath) => if FsContainsPath(fs, linkPath) then 17 else 0
  }

  ghost predicate CreateSymlinkContractFields(
    fs: FileSystem,
    now: int,
    path: Path,
    target: Path,
    ok: bool,
    err: int,
    fs2: FileSystem
  )
  {
    // Host-specific symlink creation failures beyond path resolution and
    // existing-destination checks are outside the modeled state.
    (!ok ==> (
         fs2 == fs &&
         err == CreateSymlinkFailureErrFields(fs, path, target)
       )) &&
    (ok ==>
       target != "" &&
       !HasTrailingSlash(path) &&
       !HasRawTerminalSpecialFields(path) &&
       err == 0 &&
       match ResolvePathForCreateNoFollowTerminalFields(fs, path)
       case Ok(linkPath) =>
         !FsContainsPath(fs, linkPath) &&
         exists id: InodeId, key: HostInodeKey ::
           FreshInsertionFields(
             fs,
             now,
             linkPath,
             id,
             key,
             Symlink(
               target,
               DEFAULT_SYMLINK_MODE,
               FileTimes(now, 0, now, 0, now, 0),
               map[]
             ),
             fs2
           )
       case Err(_) => false) &&
    (if target == "" then
       !ok
     else
       match ResolvePathForCreateNoFollowTerminalFields(fs, path)
       case Err(_) => !ok
       case Ok(linkPath) =>
         if FsContainsPath(fs, linkPath) then
           !ok
         else
           ok)
  }

  ghost predicate CreateSymlinkWithCredentialsContractFields(
    fs: FileSystem,
    now: int,
    credentials: ProcessCredentials,
    path: Path,
    target: Path,
    ok: bool,
    err: int,
    fs2: FileSystem
  )
  {
    CreateSymlinkContractFields(
      fs, now, path, target, ok, err, fs2
    ) &&
    CreatedPathOwnershipFields(fs, credentials, path, ok, fs2)
  }

  lemma CreateSymlinkWithCredentialsImpliesLegacy(
    fs: FileSystem,
    now: int,
    credentials: ProcessCredentials,
    path: Path,
    target: Path,
    ok: bool,
    err: int,
    fs2: FileSystem
  )
    requires CreateSymlinkWithCredentialsContractFields(
               fs, now, credentials, path, target, ok, err, fs2
             )
    ensures CreateSymlinkContractFields(
              fs, now, path, target, ok, err, fs2
            )
  {
  }

  function DeletePathFailureErrFields(fs: FileSystem, path: Path): int
  {
    match ResolvePathForMetadataFields(fs, path, false)
    case Err(e) => IOErrorErrno(e)
    case Ok(target) =>
      if FsContainsPath(fs, target) then
        match FsNodeAt(fs, target)
        case Directory(_, _, _) => 21
        case _ => 0
      else
        2
  }

  ghost predicate DeletePathContractFields(fs: FileSystem, path: Path, ok: bool, err: int, fs2: FileSystem)
  {
    (!ok ==> fs2 == fs && err == DeletePathFailureErrFields(fs, path)) &&
    (ok ==>
       err == 0 &&
       match ResolvePathForMetadataFields(fs, path, false)
       case Ok(target) =>
         FsContainsPath(fs, target) &&
         (match FsNodeAt(fs, target)
          case Directory(_, _, _) => false
          case _ =>
            exists transitionNow: int, parentStorage: StorageInfo ::
              DirectoryStorageObservationFields(parentStorage) &&
              fs2 == DeleteFsWithMetadataFields(
                fs, target, transitionNow, parentStorage
              ))
       case Err(_) => false) &&
    (match ResolvePathForMetadataFields(fs, path, false)
     case Err(_) => !ok
     case Ok(target) =>
       FsContainsPath(fs, target) &&
       match FsNodeAt(fs, target)
       case Directory(_, _, _) => !ok
       case _ => ok)
  }

  ghost predicate DeletePathWithChangeTimeContractFields(
    fs: FileSystem,
    now: int,
    path: Path,
    ok: bool,
    err: int,
    fs2: FileSystem
  )
  {
    DeletePathContractFields(fs, path, ok, err, fs2) &&
    (ok ==>
       match ResolvePathForMetadataFields(fs, path, false)
       case Err(_) => false
       case Ok(target) =>
         exists parentStorage: StorageInfo ::
           DirectoryStorageObservationFields(parentStorage) &&
           fs2 == DeleteFsWithMetadataFields(
             fs, target, now, parentStorage
           ))
  }

  lemma DeletePathWithChangeTimeImpliesLegacy(
    fs: FileSystem,
    now: int,
    path: Path,
    ok: bool,
    err: int,
    fs2: FileSystem
  )
    requires DeletePathWithChangeTimeContractFields(
               fs, now, path, ok, err, fs2
             )
    ensures DeletePathContractFields(fs, path, ok, err, fs2)
  {
  }

  predicate SetModeTargetOk(before: FsNode, after: FsNode, desired: bv32, allowSuccessNoChange: bool)
  {
    if after == before then
      allowSuccessNoChange || NodeMode(before) == NormalizeMode(desired)
    else
      !allowSuccessNoChange &&
      NodeShapeUnchangedExceptMode(before, after) &&
      NodeMode(after) == NormalizeMode(desired)
  }

  ghost predicate SetFileModeContractFields(
    fs: FileSystem,
    path: Path,
    followSymlink: bool,
    mode: bv32,
    ok: bool,
    err: int,
    fs2: FileSystem
  )
  {
    FileSystemTopologyUnchangedExceptMode(fs, fs2) &&
    (!ok ==> fs2 == fs) &&
    (!ok ==> err == MetadataFailureErrFields(fs, path, followSymlink)) &&
    (ok ==>
       err == 0 &&
       match ResolvePathForMetadataFields(fs, path, followSymlink)
       case Ok(target) =>
         FsContainsPath(fs, target) &&
         (if !followSymlink &&
             match FsNodeAt(fs, target)
             case Symlink(_, _, _, _) => true
             case _ => false
          then fs2 == fs else true) &&
         FsContainsPath(fs2, target) &&
         SetModeTargetOk(
           FsNodeAt(fs, target),
           FsNodeAt(fs2, target),
           mode,
           !followSymlink &&
           match FsNodeAt(fs, target)
           case Symlink(_, _, _, _) => true
           case _ => false
         )
       case Err(_) => false) &&
    (match ResolvePathForMetadataFields(fs, path, followSymlink)
     case Err(_) => !ok
     case Ok(resolved) => FsContainsPath(fs, resolved) ==> ok)
  }

  ghost predicate SetFileModeWithChangeTimeContractFields(
    fs: FileSystem,
    now: int,
    path: Path,
    followSymlink: bool,
    mode: bv32,
    ok: bool,
    err: int,
    fs2: FileSystem
  )
  {
    SetFileModeContractFields(
      fs, path, followSymlink, mode, ok, err, fs2
    ) &&
    (ok ==>
       match ResolvePathForMetadataFields(fs, path, followSymlink)
       case Err(_) => false
       case Ok(target) =>
         if !followSymlink && FsNodeAt(fs, target).Symlink? then
           fs2 == fs
         else
           fs2 == FsSetPath(
             fs,
             target,
             WithNodeChangeTime(
               WithNodeMode(FsNodeAt(fs, target), mode), now, 0
             )
           ))
  }

  lemma SetFileModeWithChangeTimeImpliesLegacy(
    fs: FileSystem,
    now: int,
    path: Path,
    followSymlink: bool,
    mode: bv32,
    ok: bool,
    err: int,
    fs2: FileSystem
  )
    requires SetFileModeWithChangeTimeContractFields(
               fs, now, path, followSymlink, mode, ok, err, fs2
             )
    ensures SetFileModeContractFields(
              fs, path, followSymlink, mode, ok, err, fs2
            )
  {
  }

  predicate SetTimesTargetOk(before: FsNode, after: FsNode, times: FileTimes)
  {
    if after == before then
      NodeTimes(before) == times
    else
      NodeShapeUnchangedExceptTimes(before, after) &&
      NodeTimes(after) == times
  }

  predicate ValidTimestampNanoseconds(nsec: int)
  {
    0 <= nsec < 1000000000
  }

  predicate TimestampUpdateMatchesFields(
    beforeSec: int,
    beforeNsec: int,
    request: TimestampUpdate,
    now: int,
    afterSec: int,
    afterNsec: int
  )
  {
    match request
    case Current =>
      afterSec == now && ValidTimestampNanoseconds(afterNsec)
    case Keep =>
      afterSec == beforeSec && afterNsec == beforeNsec
    case Exact(sec, nsec) =>
      ValidTimestampNanoseconds(nsec) &&
      afterSec == sec && afterNsec == nsec
  }

  predicate GetFileTimesContractFields(
    fs: FileSystem,
    path: Path,
    followSymlink: bool,
    ok: bool,
    atimeSec: int,
    atimeNsec: int,
    mtimeSec: int,
    mtimeNsec: int,
    isDir: bool,
    isSymlink: bool,
    device: int,
    inode: int,
    linkCount: int,
    err: int
  )
  {
    (!ok ==> err == MetadataFailureErrFields(fs, path, followSymlink)) &&
    (ok ==>
       err == 0 &&
       match ResolvePathForMetadataFields(fs, path, followSymlink)
       case Ok(resolved) =>
         FsContainsPath(fs, resolved) &&
         var id := FsIdAt(fs, resolved);
         var record := fs.inodes[id];
         var node := FsNodeAt(fs, resolved);
         var times := NodeTimes(FsNodeAt(fs, resolved));
         atimeSec == times.atimeSec &&
         atimeNsec == times.atimeNsec &&
         mtimeSec == times.mtimeSec &&
         mtimeNsec == times.mtimeNsec &&
         isDir == node.Directory? &&
         isSymlink == node.Symlink? &&
         HostInodeKey(device, inode) == record.hostKey &&
         0 <= linkCount &&
         record.links == LinkCountKnown(linkCount as nat)
       case Err(_) => false) &&
    (match ResolvePathForMetadataFields(fs, path, followSymlink)
     case Err(_) => !ok
     case Ok(resolved) => ok == FsContainsPath(fs, resolved))
  }

  ghost predicate SetFileTimesContractFields(
    fs: FileSystem,
    now: int,
    path: Path,
    followSymlink: bool,
    atime: TimestampUpdate,
    mtime: TimestampUpdate,
    ok: bool,
    err: int,
    fs2: FileSystem
  )
  {
    FileSystemTopologyUnchangedExceptTimes(fs, fs2) &&
    (!ok ==> fs2 == fs && err == MetadataFailureErrFields(fs, path, followSymlink)) &&
    (ok ==>
       err == 0 &&
       match ResolvePathForMetadataFields(fs, path, followSymlink)
       case Ok(target) =>
         FsContainsPath(fs, target) &&
         FsContainsPath(fs2, target) &&
         NodeShapeUnchangedExceptTimes(
           FsNodeAt(fs, target), FsNodeAt(fs2, target)
         ) &&
         var before := NodeTimes(FsNodeAt(fs, target));
         var after := NodeTimes(FsNodeAt(fs2, target));
         TimestampUpdateMatchesFields(
           before.atimeSec, before.atimeNsec,
           atime,
           now,
           after.atimeSec, after.atimeNsec
         ) &&
         TimestampUpdateMatchesFields(
           before.mtimeSec, before.mtimeNsec,
           mtime,
           now,
           after.mtimeSec, after.mtimeNsec
         ) &&
         (if atime == Keep && mtime == Keep then
            after.ctimeSec == before.ctimeSec &&
            after.ctimeNsec == before.ctimeNsec
          else
            after.ctimeSec == now && ValidTimestampNanoseconds(after.ctimeNsec))
       case Err(_) => false) &&
    (match ResolvePathForMetadataFields(fs, path, followSymlink)
     case Err(_) => !ok
     case Ok(target) =>
       ok == (FsContainsPath(fs, target) &&
              TimestampUpdateValidFields(atime) && TimestampUpdateValidFields(mtime)))
  }

  ghost predicate TrustedSetFileTimesContractFields(
    observations: (TrustedFilesystemRequest) -> TrustedFilesystemResult,
    fs: FileSystem,
    now: int,
    path: Path,
    followSymlink: bool,
    atime: TimestampUpdate,
    mtime: TimestampUpdate,
    ok: bool,
    err: int,
    fs2: FileSystem
  )
  {
    var observed := observations(
      FilesystemSetTimes(fs, path, followSymlink, now, atime, mtime)
    );
    ok == observed.ok && err == observed.err && fs2 == observed.postFs
  }

  predicate TimestampUpdateValidFields(request: TimestampUpdate)
  {
    match request
    case Current => true
    case Keep => true
    case Exact(_, nsec) => ValidTimestampNanoseconds(nsec)
  }

  predicate StdoutTimestampUpdateFields(
    before: AccessModificationTimes,
    after: AccessModificationTimes,
    atime: TimestampUpdate,
    mtime: TimestampUpdate,
    now: int
  )
  {
    TimestampUpdateMatchesFields(
      before.atimeSec, before.atimeNsec, atime, now,
      after.atimeSec, after.atimeNsec
    ) &&
    TimestampUpdateMatchesFields(
      before.mtimeSec, before.mtimeNsec, mtime, now,
      after.mtimeSec, after.mtimeNsec
    )
  }

  // High-level observation of the object associated with standard output.
  // Stream bytes and target timestamps are intentionally separate observables.
  ghost predicate SetStdoutTimesContractFields(
    before: StdoutTimestampState,
    after: StdoutTimestampState,
    now: int,
    atime: TimestampUpdate,
    mtime: TimestampUpdate,
    ok: bool,
    err: int
  )
  {
    match before
    case StdoutTimestampUnavailable(unavailableErr) =>
      !ok && err == unavailableErr && after == before
    case StdoutTimestampAvailable(beforeTimes) =>
      ok && err == 0 &&
      exists afterTimes: AccessModificationTimes ::
        after == StdoutTimestampAvailable(afterTimes) &&
        StdoutTimestampUpdateFields(beforeTimes, afterTimes, atime, mtime, now)
  }

  predicate ValidLeafName(name: string)
  {
    name != "" && !IsAbsolutePath(name) && PathSegments(name) == [name]
  }

  ghost function EntryForNode(path: Path, node: FsNode): DirEntry
  {
    match node
    case Directory(_, _, _) => DirEntry(LeafName(path), true, false)
    case Symlink(_, _, _, _) => DirEntry(LeafName(path), false, true)
    case _ => DirEntry(LeafName(path), false, false)
  }

  ghost function InodeTreeChildNodeFields(
    fs: FileSystem,
    tree: InodeTree,
    name: string
  ): FsNode
    requires InodeTreeWellFormed(tree, fs.inodes)
    requires name in tree.children
  {
    assert InodeTreeWellFormed(tree.children[name], fs.inodes);
    fs.inodes[tree.children[name].id].node
  }

  ghost function DirectoryEntriesForTreeFields(
    fs: FileSystem,
    tree: InodeTree
  ): set<DirEntry>
    requires InodeTreeWellFormed(tree, fs.inodes)
  {
    set name: string |
      name in tree.children && ValidLeafName(name) ::
      EntryForNode(name, InodeTreeChildNodeFields(fs, tree, name))
  }

  ghost function DirectoryEntriesForPathFields(
    fs: FileSystem,
    path: Path
  ): set<DirEntry>
    requires FsContainsPath(fs, path)
  {
    var tree := InodeFsLookupTreeSegments(
                  fs.inodes, fs.namespace, PathSegments(path)
                ).v;
    LookupProof.InodeLookupTreeWellFormed(
      fs.inodes, fs.namespace, PathSegments(path), tree
    );
    DirectoryEntriesForTreeFields(fs, tree)
  }

  ghost predicate OpenDirContractFields(
    fs: FileSystem,
    dirHandles: map<int, DirHandleState>,
    path: Path,
    ok: bool,
    handle: int,
    err: int,
    dirHandles2: map<int, DirHandleState>
  )
  {
    (!ok ==> dirHandles2 == dirHandles) &&
    (!ok ==> err == OpenDirFailureErrFields(fs, path)) &&
    (ok ==>
       err == 0 &&
       !(handle in dirHandles) &&
       match ResolvePathForMetadataFields(fs, path, true)
       case Ok(resolved) =>
         FsContainsPath(fs, resolved) &&
         (match FsNodeAt(fs, resolved)
          case Directory(_, _, _) =>
            dirHandles2 == dirHandles[handle := DirHandleState(resolved, DirectoryEntriesForPathFields(fs, resolved))]
          case _ => false)
       case Err(_) => false) &&
    (match ResolvePathForMetadataFields(fs, path, true)
     case Err(_) => !ok
     case Ok(resolved) =>
       FsContainsPath(fs, resolved) &&
       (match FsNodeAt(fs, resolved)
        case Directory(_, _, _) => ok
        case _ => !ok))
  }

  predicate ResolvePathIdentityContractFields(
    fs: FileSystem,
    cwd: Path,
    path: Path,
    ok: bool,
    resolvedPath: Path,
    err: int
  )
  {
    var absolutePath :=
      if IsAbsolutePath(path) then path
      else AppendPath(BuildPath(true, PathSegments(cwd)), path);
    match ResolvePathForMetadataFields(fs, absolutePath, true)
    case Err(error) =>
      !ok && resolvedPath == "" && err == IOErrorErrno(error)
    case Ok(resolved) =>
      ok &&
      resolvedPath == resolved &&
      err == 0 &&
      FsContainsPath(fs, resolved) &&
      NormalizePath(resolved) == resolved &&
      IsAbsolutePath(resolved)
  }

  ghost predicate ReadDirContractFields(
    dirHandles: map<int, DirHandleState>,
    handle: int,
    hasMore: bool,
    name: string,
    isDir: bool,
    isSymlink: bool,
    err: int,
    dirHandles2: map<int, DirHandleState>
  )
  {
    if !(handle in dirHandles) then
      !hasMore &&
      err != 0 &&
      dirHandles2 == dirHandles
    else
      var state := dirHandles[handle];
      if err != 0 then
        !hasMore &&
        name == "" &&
        !isDir &&
        !isSymlink &&
        dirHandles2 == dirHandles
      else if |state.remaining| == 0 then
        !hasMore &&
        err == 0 &&
        name == "" &&
        !isDir &&
        !isSymlink &&
        dirHandles2 == dirHandles
      else
        exists entry :: entry in state.remaining &&
                        hasMore &&
                        err == 0 &&
                        name != "" &&
                        !IsAbsolutePath(name) &&
                        ValidLeafName(name) &&
                        name == entry.name &&
                        isDir == entry.isDir &&
                        isSymlink == entry.isSymlink &&
                        dirHandles2 == dirHandles[handle := DirHandleState(state.path, state.remaining - {entry})]
  }

  ghost predicate CloseDirContractFields(dirHandles: map<int, DirHandleState>, handle: int, dirHandles2: map<int, DirHandleState>) { if handle in dirHandles then dirHandles2 == dirHandles - {handle} else dirHandles2 == dirHandles }

  function HasPathPrefix(root: Path, path: Path): bool { path == root || (root != "" && root != "/" && |root| < |path| && path[..|root|] == root && path[|root|] == '/') }

  function ResolvePathForRenameNoFollowTerminalFields(
    fs: FileSystem,
    path: Path
  ): Result<Path>
  {
    var entryPath := BuildPath(
                       IsAbsolutePath(path),
                       RawPathSegmentsFields(path)
                     );
    match ResolvePathThroughSymlinkComponentsFields(fs, entryPath, false)
    case Err(error) => Err(error)
    case Ok(resolved) =>
      if !HasTrailingSlash(path) then
        Ok(resolved)
      else if !FsContainsPath(fs, resolved) then
        Err(NoSuchFile)
      else
        match FsNodeAt(fs, resolved)
        case Directory(_, _, _) => Ok(resolved)
        case Regular(_, _, _, _) | Symlink(_, _, _, _) =>
          Err(NotDirectory)
        case Inaccessible(_) => Err(PermissionDenied)
  }

  function ResolvePathForRenameDestinationFields(fs: FileSystem, path: Path): Result<Path>
  {
    match ResolvePathForRenameNoFollowTerminalFields(fs, path)
    case Err(NoSuchFile) =>
      if HasTrailingSlash(path) ||
         HasRawTerminalSpecialFields(path)
      then
        Err(NoSuchFile)
      else
        ResolvePathForCreateFields(fs, path)
    case result => result
  }

  ghost predicate HasNoDescendants(fs: FileSystem, path: Path)
  {
    FsContainsPath(fs, path) &&
    |InodeFsLookupTreeSegments(
      fs.inodes, fs.namespace, PathSegments(path)
    ).v.children| == 0
  }

  ghost predicate RenameKindCompatible(fs: FileSystem, source: Path, target: Path)
    requires FsContainsPath(fs, source)
  {
    match FsNodeAt(fs, source)
    case Inaccessible(_) => false
    case Directory(_, _, _) =>
      !FsContainsPath(fs, target) ||
      (match FsNodeAt(fs, target)
       case Directory(_, _, _) => HasNoDescendants(fs, target)
       case _ => false)
    case _ =>
      !FsContainsPath(fs, target) ||
      (match FsNodeAt(fs, target)
       case Directory(_, _, _) => false
       case _ => true)
  }

  function RenameFs(
    fs: FileSystem,
    source: Path,
    target: Path
  ): FileSystem
    requires FsContainsPath(fs, source)
  {
    var candidate := InodeFsRename(fs, source, target);
    if ValidInodeFileSystemData(candidate) then candidate else fs
  }

  function RenameDirectoryParentLinksFields(
    fs: FileSystem,
    renamed: InodeFileSystemData,
    source: Path,
    target: Path
  ): InodeFileSystemData
    requires FsContainsPath(fs, source)
  {
    var sourceParent := ParentPath(source);
    var targetParent := ParentPath(target);
    if InodeSameObject(fs, source, target) ||
       !FsNodeAt(fs, source).Directory? ||
       !FsContainsPath(fs, sourceParent) ||
       !FsContainsPath(fs, targetParent)
    then
      renamed
    else
      var sourceParentId := FsIdAt(fs, sourceParent);
      var targetParentId := FsIdAt(fs, targetParent);
      var targetDirectoryExists := FsContainsPath(fs, target) &&
                                   FsNodeAt(fs, target).Directory?;
      if sourceParentId == targetParentId then
        if targetDirectoryExists then
          InodeFsDecrementRecordLinks(renamed, sourceParentId)
        else
          renamed
      else
        var withoutSourceDirectoryLink :=
          InodeFsDecrementRecordLinks(renamed, sourceParentId);
        if targetDirectoryExists then
          withoutSourceDirectoryLink
        else
          InodeFsIncrementRecordLinks(
            withoutSourceDirectoryLink, targetParentId
          )
  }

  function RefreshRenameParentStorageFields(
    fs: FileSystem,
    renamed: InodeFileSystemData,
    source: Path,
    target: Path,
    sourceParentStorage: StorageInfo,
    targetParentStorage: StorageInfo
  ): InodeFileSystemData
  {
    var sourceParent := ParentPath(source);
    var targetParent := ParentPath(target);
    if !FsContainsPath(fs, sourceParent) ||
       !FsContainsPath(fs, targetParent)
    then
      renamed
    else if FsIdAt(fs, sourceParent) == FsIdAt(fs, targetParent) then
        RefreshParentDirectoryStorageFields(
          renamed, source, sourceParentStorage
        )
      else
        RefreshParentDirectoryStorageFields(
          RefreshParentDirectoryStorageFields(
            renamed, source, sourceParentStorage
          ),
          target,
          targetParentStorage
        )
  }

  function RenameFsWithMetadataFields(
    fs: FileSystem,
    source: Path,
    target: Path,
    now: int,
    sourceParentStorage: StorageInfo,
    targetParentStorage: StorageInfo
  ): InodeFileSystemData
    requires FsContainsPath(fs, source)
  {
    var sourceId := FsIdAt(fs, source);
    var targetExists := FsContainsPath(fs, target);
    var targetId := if targetExists then FsIdAt(fs, target) else sourceId;
    var renamed := RenameFs(fs, source, target);
    var withParentLinks := RenameDirectoryParentLinksFields(
                             fs, renamed, source, target
                           );
    var withMovedChange :=
      InodeFsTouchRecordChangeTime(withParentLinks, sourceId, now);
    var withOverwrittenChange :=
      if targetExists && targetId != sourceId then
        InodeFsTouchRecordChangeTime(
          withMovedChange, targetId, now
        )
      else
        withMovedChange;
    var withSourceParent :=
      InodeFsTouchParentModificationAndChangeTime(
        withOverwrittenChange, source, now
      );
    RefreshRenameParentStorageFields(
      fs,
      InodeFsTouchParentModificationAndChangeTime(
        withSourceParent, target, now
      ),
      source,
      target,
      sourceParentStorage,
      targetParentStorage
    )
  }

  lemma RenameFsIsInodeFsRename(
    fs: FileSystem,
    source: Path,
    target: Path
  )
    requires FsContainsPath(fs, source)
    ensures RenameFs(fs, source, target) ==
            InodeFsRename(fs, source, target)
    ensures InodeSameObject(fs, source, target) ==>
              RenameFs(fs, source, target) == fs
  {
    RenameProof.InodeFsRenameValid(fs, source, target);
    if InodeSameObject(fs, source, target) {
      RenameProof.InodeRenameSameObjectNoop(fs, source, target);
    }
  }

  ghost predicate RenamePathContractFields(fs: FileSystem, source: Path, target: Path, ok: bool, err: int, fs2: FileSystem)
  {
    if !IsNonRootRawEntryPathFields(source) ||
       !IsNonRootRawEntryPathFields(target)
    then
      !ok && err != 0 && fs2 == fs
    else
      var sourceResult :=
        ResolvePathForRenameNoFollowTerminalFields(fs, source);
      var targetNotDirectory :=
        match sourceResult
        case Ok(_) =>
          ResolvePathForRenameDestinationFields(fs, target) ==
          Err(NotDirectory)
        case Err(_) => false;
      if sourceResult == Err(NotDirectory) || targetNotDirectory then
        !ok && err == 20 && fs2 == fs
      else
        (!ok ==> err != 0 && fs2 == fs) &&
        (ok ==>
           err == 0 &&
           match sourceResult
           case Ok(resolvedSource) =>
             (match ResolvePathForRenameDestinationFields(fs, target)
              case Ok(resolvedTarget) =>
                FsContainsPath(fs, resolvedSource) &&
                if InodeSameObject(fs, resolvedSource, resolvedTarget) then
                  fs2 == fs
                else
                  resolvedSource != resolvedTarget &&
                  !HasPathPrefix(resolvedSource, resolvedTarget) &&
                  RenameKindCompatible(fs, resolvedSource, resolvedTarget) &&
                  exists transitionNow: int,
                    sourceParentStorage: StorageInfo,
                    targetParentStorage: StorageInfo ::
                    DirectoryStorageObservationFields(sourceParentStorage) &&
                    DirectoryStorageObservationFields(targetParentStorage) &&
                    fs2 == RenameFsWithMetadataFields(
                      fs,
                      resolvedSource,
                      resolvedTarget,
                      transitionNow,
                      sourceParentStorage,
                      targetParentStorage
                    )
              case Err(_) => false)
           case Err(_) => false) &&
        (match sourceResult
         case Ok(resolvedSource) =>
           (match ResolvePathForRenameDestinationFields(fs, target)
            case Ok(resolvedTarget) =>
              if FsContainsPath(fs, resolvedSource) &&
                 InodeSameObject(fs, resolvedSource, resolvedTarget)
              then
                ok && err == 0 && fs2 == fs
              else if FsContainsPath(fs, resolvedSource) &&
                      FsNodeAt(fs, resolvedSource).Directory? &&
                      resolvedSource != resolvedTarget &&
                      HasPathPrefix(resolvedSource, resolvedTarget)
                then
                  !ok && err == 22
                else
                  true
            case Err(_) => true)
         case Err(_) => true)
  }

  ghost predicate RenamePathWithChangeTimeContractFields(
    fs: FileSystem,
    now: int,
    source: Path,
    target: Path,
    ok: bool,
    err: int,
    fs2: FileSystem
  )
  {
    RenamePathContractFields(fs, source, target, ok, err, fs2) &&
    (ok ==>
       match ResolvePathForRenameNoFollowTerminalFields(fs, source)
       case Err(_) => false
       case Ok(resolvedSource) =>
         match ResolvePathForRenameDestinationFields(fs, target)
         case Err(_) => false
         case Ok(resolvedTarget) =>
           if InodeSameObject(fs, resolvedSource, resolvedTarget) then
             fs2 == fs
           else
             exists sourceParentStorage: StorageInfo,
               targetParentStorage: StorageInfo ::
               DirectoryStorageObservationFields(sourceParentStorage) &&
               DirectoryStorageObservationFields(targetParentStorage) &&
               fs2 == RenameFsWithMetadataFields(
                 fs,
                 resolvedSource,
                 resolvedTarget,
                 now,
                 sourceParentStorage,
                 targetParentStorage
               ))
  }

  lemma RenamePathWithChangeTimeImpliesLegacy(
    fs: FileSystem,
    now: int,
    source: Path,
    target: Path,
    ok: bool,
    err: int,
    fs2: FileSystem
  )
    requires RenamePathWithChangeTimeContractFields(
               fs, now, source, target, ok, err, fs2
             )
    ensures RenamePathContractFields(
              fs, source, target, ok, err, fs2
            )
  {
  }

  // Abstract diagnostic results are shared by the named IO postconditions.
  ghost function CLocaleErrnoTextResult(err: int): string

  ghost function QuoteafPathResult(path: Path): Bytes

  ghost function QuoteArgumentResult(value: Bytes): Bytes

  // API-specific IO postconditions delegate to the shared contract relations.
  ghost predicate ReadFileSpec(beforeFs: FileSystem, path: Path, r: Result<Bytes>)
  {
    r == ReadFileResultFields(beforeFs, path)
  }

  ghost predicate ReadFileWithOutcomeSpec(
    beforeFs: FileSystem,
    beforeTrustedStreams: (TrustedStreamRequest) -> TrustedStreamResult,
    path: Path,
    data: Bytes,
    err: int
  )
  {
    TrustedReadFileWithOutcomeContractFields(
      beforeTrustedStreams, beforeFs, path, data, err
    )
  }

  ghost predicate ReadLinkSpec(beforeFs: FileSystem, path: Path, r: Result<Path>)
  {
    r == ReadLinkResultFields(beforeFs, path)
  }

  ghost predicate ReadStdinAllSpec(beforeStdin: Bytes, afterStdin: Bytes, b: Bytes)
  {
    ReadStdinAllFields(beforeStdin, afterStdin, b)
  }

  ghost predicate ReadStdinWithOutcomeSpec(
    beforeStdin: Bytes,
    beforeTrustedStreams: (TrustedStreamRequest) -> TrustedStreamResult,
    afterStdin: Bytes,
    data: Bytes,
    err: int
  )
  {
    TrustedReadStdinWithOutcomeContractFields(
      beforeTrustedStreams, beforeStdin, afterStdin, data, err
    )
  }

  ghost predicate AppendStdoutSpec(beforeStdout: Bytes, afterStdout: Bytes, b: Bytes)
  {
    AppendStdoutFields(beforeStdout, afterStdout, b)
  }

  ghost predicate AppendStderrSpec(beforeStderr: Bytes, afterStderr: Bytes, b: Bytes)
  {
    AppendStderrFields(beforeStderr, afterStderr, b)
  }

  ghost predicate WriteStdoutWithOutcomeSpec(
    beforeStdout: Bytes,
    beforeTrustedStreams: (TrustedStreamRequest) -> TrustedStreamResult,
    afterStdout: Bytes,
    b: Bytes,
    committed: nat,
    err: int
  )
  {
    TrustedWriteStdoutWithOutcomeContractFields(
      beforeTrustedStreams, beforeStdout, afterStdout, b, committed, err
    )
  }

  ghost predicate WriteStderrWithOutcomeSpec(
    beforeStderr: Bytes,
    beforeTrustedStreams: (TrustedStreamRequest) -> TrustedStreamResult,
    afterStderr: Bytes,
    b: Bytes,
    committed: nat,
    err: int
  )
  {
    TrustedWriteStderrWithOutcomeContractFields(
      beforeTrustedStreams, beforeStderr, afterStderr, b, committed, err
    )
  }

  ghost predicate GetCLocaleErrnoTextSpec(err: int, text: string)
  {
    text == CLocaleErrnoTextResult(err)
  }

  ghost predicate QuoteafPathSpec(path: Path, quoted: Bytes)
  {
    quoted == QuoteafPathResult(path)
  }

  ghost predicate QuoteArgumentSpec(value: Bytes, quoted: Bytes)
  {
    quoted == QuoteArgumentResult(value)
  }

  ghost predicate GetCwdSpec(beforeCwd: Path, cwd: Path)
  {
    cwd == GetCwdResultFields(beforeCwd)
  }

  ghost predicate GetEnvSpec(beforeEnv: Environment, key: string, r: Result<string>)
  {
    GetEnvContractFields(beforeEnv, key, r)
  }

  ghost predicate GetEnvironmentSpec(beforeEnv: Environment, entries: seq<string>)
    requires ValidEnvironment(beforeEnv)
  {
    GetEnvironmentContractFields(beforeEnv, entries)
  }

  ghost predicate GetLoginNameSpec(beforeProps: map<string, string>, r: Result<string>)
  {
    GetLoginNameContractFields(beforeProps, r)
  }

  ghost predicate NowSpec(beforeNow: int, t: int)
  {
    t == beforeNow
  }

  ghost predicate ParseTimestampSpec(
    beforeTrustedTimeParses: map<TimeParseRequest, ParsedTimeResult>,
    timestamp: string,
    nowSec: int,
    nowNsec: int,
    ok: bool,
    sec: int,
    nsec: int
  )
  {
    ParseTimestampContractFields(beforeTrustedTimeParses, timestamp, nowSec, nowNsec, ok, sec, nsec)
  }

  ghost predicate ParseDateSpec(
    beforeTrustedTimeParses: map<TimeParseRequest, ParsedTimeResult>,
    date: string,
    refSec: int,
    refNsec: int,
    ok: bool,
    sec: int,
    nsec: int
  )
  {
    ParseDateContractFields(beforeTrustedTimeParses, date, refSec, refNsec, ok, sec, nsec)
  }

  ghost predicate PathExistsSpec(
    beforeFs: FileSystem,
    beforeTrustedFilesystem: (TrustedFilesystemRequest) -> TrustedFilesystemResult,
    path: Path,
    followSymlink: bool,
    found: bool,
    err: int
  )
  {
    TrustedPathExistsContractFields(
      beforeTrustedFilesystem, beforeFs, path, followSymlink, found, err
    )
  }

  ghost predicate CreateFileSpec(
    beforeFs: FileSystem,
    beforeNow: int,
    beforeTrustedFilesystem: (TrustedFilesystemRequest) -> TrustedFilesystemResult,
    afterFs: FileSystem,
    path: Path,
    ok: bool,
    err: int
  )
  {
    TrustedCreateFileContractFields(
      beforeTrustedFilesystem, beforeFs, beforeNow, path, ok, err, afterFs
    )
  }

  ghost predicate WriteFileSpec(
    beforeFs: FileSystem,
    beforeProps: map<string, string>,
    beforeNow: int,
    beforeCredentials: ProcessCredentials,
    afterFs: FileSystem,
    path: Path,
    data: Bytes,
    ok: bool,
    err: int
  )
  {
    WriteFileWithCredentialsContractFields(
      beforeFs, beforeNow, beforeProps, beforeCredentials,
      path, data, ok, err, afterFs
    ) &&
    WriteFileContractFields(beforeFs, beforeNow, path, data, ok, err, afterFs)
  }

  ghost predicate CreateSymlinkSpec(
    beforeFs: FileSystem,
    beforeNow: int,
    beforeCredentials: ProcessCredentials,
    afterFs: FileSystem,
    path: Path,
    target: Path,
    ok: bool,
    err: int
  )
  {
    CreateSymlinkWithCredentialsContractFields(
      beforeFs, beforeNow, beforeCredentials, path, target, ok, err, afterFs
    ) &&
    CreateSymlinkContractFields(beforeFs, beforeNow, path, target, ok, err, afterFs)
  }

  ghost predicate DeletePathSpec(
    beforeFs: FileSystem,
    beforeNow: int,
    afterFs: FileSystem,
    path: Path,
    ok: bool,
    err: int
  )
  {
    DeletePathWithChangeTimeContractFields(
      beforeFs, beforeNow, path, ok, err, afterFs
    ) &&
    DeletePathContractFields(beforeFs, path, ok, err, afterFs)
  }

  // mkdir accepts trailing slashes, but does not follow a terminal symlink.
  // Preserve raw dot components until the existing resolver processes them.
  function ResolveDirectoryCreationPathFields(fs: FileSystem, path: Path): Result<Path>
  {
    if path == "" || (0 as char) in path then
      Err(InvalidPath)
    else
      ResolvePathForCreateNoFollowTerminalFields(
        fs, BuildPath(IsAbsolutePath(path), RawPathSegmentsFields(path)))
  }

  // Namespace and preservation guarantees only. Native mode, ownership, storage,
  // timestamps and link counts remain observations, not a simulated POSIX policy.
  ghost predicate DirectoryCreationEffectFields(
    before: FileSystem, path: Path, after: FileSystem
  )
  {
    match ResolveDirectoryCreationPathFields(before, path)
    case Err(_) => false
    case Ok(target) =>
      !FsContainsPath(before, target) &&
      FsContainsPath(before, ParentPath(target)) &&
      FsNodeAt(before, ParentPath(target)).Directory? &&
      FsContainsPath(after, target) &&
      FsNodeAt(after, target).Directory? &&
      var id := FsIdAt(after, target);
      var parentId := FsIdAt(before, ParentPath(target));
      id !in before.inodes &&
      InodeTreeCanInsert(before.inodes, before.namespace, PathSegments(target)) &&
      after.namespace == InodeTreeSetSubtreeSegments(
        before.namespace, PathSegments(target), InodeTreeNode(id, map[])) &&
      after.inodes.Keys == before.inodes.Keys + {id} &&
      (forall oldId | oldId in before.inodes ::
        if oldId != parentId then
          // Path traversal can refresh symlink atime. No traversal trace is modeled.
          if before.inodes[oldId].node.Symlink? then
            var times := NodeTimes(before.inodes[oldId].node);
            var observedTimes := NodeTimes(after.inodes[oldId].node);
            after.inodes[oldId] == before.inodes[oldId].(
              node := WithNodeTimes(before.inodes[oldId].node,
                times.(atimeSec := observedTimes.atimeSec, atimeNsec := observedTimes.atimeNsec)))
          else
            after.inodes[oldId] == before.inodes[oldId]
        else
          after.inodes[oldId].hostKey == before.inodes[oldId].hostKey &&
          after.inodes[oldId].ownership == before.inodes[oldId].ownership &&
          after.inodes[oldId].kind == before.inodes[oldId].kind &&
          after.inodes[oldId].node.Directory? &&
          after.inodes[oldId].node.mode == before.inodes[oldId].node.mode &&
          after.inodes[oldId].node.ext == before.inodes[oldId].node.ext)
  }

  ghost predicate ValidDirectoryObservation(
    request: TrustedFilesystemRequest, result: TrustedFilesystemResult
  )
  {
    request.FilesystemCreateDirectory? ==>
      0 <= result.err && (result.ok <==> result.err == 0) &&
      (result.ok ==> DirectoryCreationEffectFields(request.preFs, request.path, result.postFs))
  }

  // A subset, rather than an extra extern postcondition on arbitrary observations,
  // keeps every admitted mkdir request/result binding consistent with its effects.
  type DirectoryValidFilesystemObservations =
    observations: ((TrustedFilesystemRequest) -> TrustedFilesystemResult) |
      (forall request :: ValidDirectoryObservation(request, observations(request)))
    ghost witness (request: TrustedFilesystemRequest) =>
      TrustedFilesystemResult(false, 5, request.preFs, 0, 0, 0, 0, false, false, 0, 0, 0)

  ghost predicate CreateDirectorySpec(
    beforeFs: FileSystem,
    beforeNow: int,
    beforeTrustedFilesystem: DirectoryValidFilesystemObservations,
    beforeUmask: bv32,
    afterFs: FileSystem,
    path: Path,
    mode: bv32,
    ok: bool,
    err: int
  )
  {
    TrustedFilesystemEffectContractFields(
      beforeTrustedFilesystem,
      FilesystemCreateDirectory(beforeFs, path, mode, beforeUmask, beforeNow),
      ok, err, afterFs
    ) &&
    (ok ==> DirectoryCreationEffectFields(beforeFs, path, afterFs))
  }

  ghost predicate RemoveDirectorySpec(
    beforeFs: FileSystem,
    beforeNow: int,
    beforeTrustedFilesystem: (TrustedFilesystemRequest) -> TrustedFilesystemResult,
    afterFs: FileSystem,
    path: Path,
    ok: bool,
    err: int
  )
  {
    TrustedFilesystemEffectContractFields(
      beforeTrustedFilesystem,
      FilesystemRemoveDirectory(beforeFs, path, beforeNow),
      ok, err, afterFs
    )
  }

  ghost predicate CreateHardLinkSpec(
    beforeFs: FileSystem,
    beforeNow: int,
    beforeTrustedFilesystem: (TrustedFilesystemRequest) -> TrustedFilesystemResult,
    afterFs: FileSystem,
    source: Path,
    target: Path,
    ok: bool,
    err: int
  )
  {
    TrustedFilesystemEffectContractFields(
      beforeTrustedFilesystem,
      FilesystemCreateHardLink(beforeFs, source, target, beforeNow),
      ok, err, afterFs
    )
  }

  ghost predicate UnlinkPathSpec(
    beforeFs: FileSystem,
    beforeNow: int,
    beforeTrustedFilesystem: (TrustedFilesystemRequest) -> TrustedFilesystemResult,
    afterFs: FileSystem,
    path: Path,
    ok: bool,
    err: int
  )
  {
    TrustedFilesystemEffectContractFields(
      beforeTrustedFilesystem,
      FilesystemUnlink(beforeFs, path, beforeNow),
      ok, err, afterFs
    )
  }

  ghost predicate TruncateFileSpec(
    beforeFs: FileSystem,
    beforeNow: int,
    beforeTrustedFilesystem: (TrustedFilesystemRequest) -> TrustedFilesystemResult,
    afterFs: FileSystem,
    path: Path,
    size: nat,
    ok: bool,
    err: int
  )
  {
    TrustedFilesystemEffectContractFields(
      beforeTrustedFilesystem,
      FilesystemTruncate(beforeFs, path, size, beforeNow),
      ok, err, afterFs
    )
  }

  ghost predicate CreateSpecialNodeSpec(
    beforeFs: FileSystem,
    beforeNow: int,
    beforeTrustedFilesystem: (TrustedFilesystemRequest) -> TrustedFilesystemResult,
    beforeUmask: bv32,
    afterFs: FileSystem,
    path: Path,
    kind: SpecialNodeKind,
    mode: bv32,
    major: nat,
    minor: nat,
    ok: bool,
    err: int
  )
  {
    TrustedFilesystemEffectContractFields(
      beforeTrustedFilesystem,
      FilesystemCreateSpecialNode(
        beforeFs, path, kind, mode, major, minor, beforeUmask, beforeNow
      ),
      ok, err, afterFs
    )
  }

  ghost predicate SyncSpec(
    beforeFs: FileSystem,
    beforeTrustedFilesystem: (TrustedFilesystemRequest) -> TrustedFilesystemResult,
    target: SyncTarget,
    mode: SyncMode,
    ok: bool,
    err: int
  )
  {
    TrustedFilesystemSyncContractFields(
      beforeTrustedFilesystem, beforeFs, target, mode, ok, err
    )
  }

  ghost predicate SetFileTimesNowSpec(
    beforeFs: FileSystem,
    beforeNow: int,
    beforeTrustedFilesystem: (TrustedFilesystemRequest) -> TrustedFilesystemResult,
    afterFs: FileSystem,
    path: Path,
    followSymlink: bool,
    ok: bool,
    err: int
  )
  {
    TrustedSetFileTimesContractFields(
      beforeTrustedFilesystem, beforeFs, beforeNow,
      path, followSymlink, Current, Current,
      ok, err, afterFs
    )
  }

  ghost predicate SetFileAccessTimeNowSpec(
    beforeFs: FileSystem,
    beforeNow: int,
    beforeTrustedFilesystem: (TrustedFilesystemRequest) -> TrustedFilesystemResult,
    afterFs: FileSystem,
    path: Path,
    followSymlink: bool,
    ok: bool,
    err: int
  )
  {
    TrustedSetFileTimesContractFields(
      beforeTrustedFilesystem, beforeFs, beforeNow,
      path, followSymlink, Current, Keep,
      ok, err, afterFs
    )
  }

  ghost predicate SetFileModificationTimeNowSpec(
    beforeFs: FileSystem,
    beforeNow: int,
    beforeTrustedFilesystem: (TrustedFilesystemRequest) -> TrustedFilesystemResult,
    afterFs: FileSystem,
    path: Path,
    followSymlink: bool,
    ok: bool,
    err: int
  )
  {
    TrustedSetFileTimesContractFields(
      beforeTrustedFilesystem, beforeFs, beforeNow,
      path, followSymlink, Keep, Current,
      ok, err, afterFs
    )
  }

  ghost predicate GetFileTimesSpec(
    beforeFs: FileSystem,
    beforeTrustedFilesystem: (TrustedFilesystemRequest) -> TrustedFilesystemResult,
    path: Path,
    followSymlink: bool,
    ok: bool,
    atimeSec: int,
    atimeNsec: int,
    mtimeSec: int,
    mtimeNsec: int,
    isDir: bool,
    isSymlink: bool,
    device: int,
    inode: int,
    linkCount: int,
    err: int
  )
  {
    TrustedFilesystemQueryContractFields(
      beforeTrustedFilesystem, beforeFs, path, followSymlink, ok,
      atimeSec, atimeNsec, mtimeSec, mtimeNsec,
      isDir, isSymlink, device, inode, linkCount, err
    )
  }

  ghost predicate SetFileTimesSpec(
    beforeFs: FileSystem,
    beforeNow: int,
    beforeTrustedFilesystem: (TrustedFilesystemRequest) -> TrustedFilesystemResult,
    afterFs: FileSystem,
    path: Path,
    followSymlink: bool,
    atimeSec: int,
    atimeNsec: int,
    mtimeSec: int,
    mtimeNsec: int,
    ok: bool,
    err: int
  )
  {
    TrustedSetFileTimesContractFields(
      beforeTrustedFilesystem, beforeFs, beforeNow, path, followSymlink,
      Exact(atimeSec, atimeNsec), Exact(mtimeSec, mtimeNsec),
      ok, err, afterFs
    )
  }

  ghost predicate SetStdoutTimesNowSpec(
    beforeNow: int,
    beforeStdoutTimestamp: StdoutTimestampState,
    afterStdoutTimestamp: StdoutTimestampState,
    ok: bool,
    err: int
  )
  {
    SetStdoutTimesContractFields(
      beforeStdoutTimestamp, afterStdoutTimestamp, beforeNow, Current, Current,
      ok, err
    )
  }

  ghost predicate SetStdoutAccessTimeNowSpec(
    beforeNow: int,
    beforeStdoutTimestamp: StdoutTimestampState,
    afterStdoutTimestamp: StdoutTimestampState,
    ok: bool,
    err: int
  )
  {
    SetStdoutTimesContractFields(
      beforeStdoutTimestamp, afterStdoutTimestamp, beforeNow, Current, Keep,
      ok, err
    )
  }

  ghost predicate SetStdoutModificationTimeNowSpec(
    beforeNow: int,
    beforeStdoutTimestamp: StdoutTimestampState,
    afterStdoutTimestamp: StdoutTimestampState,
    ok: bool,
    err: int
  )
  {
    SetStdoutTimesContractFields(
      beforeStdoutTimestamp, afterStdoutTimestamp, beforeNow, Keep, Current,
      ok, err
    )
  }

  ghost predicate SetStdoutTimesSpec(
    beforeNow: int,
    beforeStdoutTimestamp: StdoutTimestampState,
    afterStdoutTimestamp: StdoutTimestampState,
    atime: TimestampUpdate,
    mtime: TimestampUpdate,
    ok: bool,
    err: int
  )
  {
    SetStdoutTimesContractFields(
      beforeStdoutTimestamp, afterStdoutTimestamp, beforeNow,
      atime, mtime, ok, err
    )
  }

  ghost predicate GetFileModeSpec(
    beforeFs: FileSystem,
    path: Path,
    followSymlink: bool,
    ok: bool,
    mode: bv32,
    err: int
  )
  {
    GetFileModeContractFields(beforeFs, path, followSymlink, ok, mode, err)
  }

  ghost predicate GetFileStatusSpec(
    beforeFs: FileSystem,
    path: Path,
    followSymlink: bool,
    ok: bool,
    status: FileStatus,
    err: int
  )
  {
    GetFileStatusContractFields(
      beforeFs, path, followSymlink, ok, status, err
    )
  }

  ghost predicate SetFileModeSpec(
    beforeFs: FileSystem,
    beforeNow: int,
    afterFs: FileSystem,
    path: Path,
    followSymlink: bool,
    mode: bv32,
    ok: bool,
    err: int
  )
  {
    SetFileModeWithChangeTimeContractFields(
      beforeFs, beforeNow, path, followSymlink, mode, ok, err, afterFs
    ) &&
    SetFileModeContractFields(beforeFs, path, followSymlink, mode, ok, err, afterFs) &&
    FileSystemTopologyUnchangedExceptMode(beforeFs, afterFs)
  }

  ghost predicate GetUmaskSpec(beforeProps: map<string, string>, mask: bv32)
  {
    mask == GetUmaskResultFields(beforeProps)
  }

  ghost predicate OpenDirSpec(
    beforeFs: FileSystem,
    beforeDirHandles: map<int, DirHandleState>,
    afterDirHandles: map<int, DirHandleState>,
    path: Path,
    ok: bool,
    handle: int,
    err: int
  )
  {
    OpenDirContractFields(
      beforeFs, beforeDirHandles, path,
      ok, handle, err, afterDirHandles
    )
  }

  ghost predicate ResolvePathIdentitySpec(
    beforeFs: FileSystem,
    beforeCwd: Path,
    path: Path,
    ok: bool,
    resolvedPath: Path,
    err: int
  )
  {
    ResolvePathIdentityContractFields(
      beforeFs, beforeCwd, path, ok, resolvedPath, err
    )
  }

  ghost predicate ReadDirSpec(
    beforeDirHandles: map<int, DirHandleState>,
    afterDirHandles: map<int, DirHandleState>,
    handle: int,
    hasMore: bool,
    name: string,
    isDir: bool,
    isSymlink: bool,
    err: int
  )
  {
    ReadDirContractFields(beforeDirHandles, handle, hasMore, name, isDir, isSymlink, err, afterDirHandles)
  }

  ghost predicate CloseDirSpec(
    beforeDirHandles: map<int, DirHandleState>,
    afterDirHandles: map<int, DirHandleState>,
    handle: int
  )
  {
    CloseDirContractFields(beforeDirHandles, handle, afterDirHandles)
  }

  ghost predicate IsDirectorySpec(
    beforeFs: FileSystem,
    path: Path,
    followSymlink: bool,
    ok: bool,
    isDir: bool,
    err: int
  )
  {
    IsDirectoryContractFields(beforeFs, path, followSymlink, ok, isDir, err)
  }

  ghost predicate IsDirectoryStrictSpec(
    beforeFs: FileSystem,
    path: Path,
    followSymlink: bool,
    ok: bool,
    isDir: bool,
    err: int
  )
  {
    IsDirectoryStrictContractFields(beforeFs, path, followSymlink, ok, isDir, err)
  }

  ghost predicate IsSymlinkSpec(
    beforeFs: FileSystem,
    path: Path,
    ok: bool,
    isSymlink: bool,
    err: int
  )
  {
    IsSymlinkContractFields(beforeFs, path, ok, isSymlink, err)
  }

  ghost predicate RenamePathSpec(
    beforeFs: FileSystem,
    beforeNow: int,
    afterFs: FileSystem,
    source: Path,
    target: Path,
    ok: bool,
    err: int
  )
  {
    RenamePathWithChangeTimeContractFields(
      beforeFs, beforeNow, source, target, ok, err, afterFs
    ) &&
    RenamePathContractFields(beforeFs, source, target, ok, err, afterFs)
  }

}
