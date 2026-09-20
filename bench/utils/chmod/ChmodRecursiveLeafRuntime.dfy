include "ChmodRecursiveCore.dfy"

module ChmodRecursiveLeafRuntime {
  import BenchWorld
  import BenchIO
  import Schema = ChmodSchema
  import Base = ChmodCore
  import opened ChmodRecursiveCore

  method AppendRuntimeAccessFailure(
    cmd: Schema.ChmodCmd,
    displayPath: string,
    err: int,
    failureKind: RecursiveFailureKind,
    io: BenchIO.IO
  )
    modifies io.stdoutRegion, io.stderrRegion
    ensures io.stdout() == old(io.stdout()) +
                         RecursiveAccessStdoutCore(cmd, displayPath)
    ensures io.stderr() == old(io.stderr()) +
                         RecursiveAccessStderrCore(cmd, displayPath, err, failureKind)
  {
    if !cmd.silent {
      io.AppendStderr(
        RecursiveAccessStderrCore(cmd, displayPath, err, failureKind)
      );
    }
    if cmd.verbose {
      io.AppendStdout(Base.AccessFailureMessageCore(displayPath));
    }
  }

  method {:isolate_assertions} {:vcs_split_on_every_assert} ApplyPathRuntime(
    cmd: Schema.ChmodCmd,
    plan: Base.CoreModePlan,
    identity: RecursiveIdentity,
    ghost universe: set<seq<string>>,
    io: BenchIO.IO
  ) returns (ok: bool)
    requires SegmentPaths(io.fs()) == universe
    requires IdentityResolvesCore(io.fs(), identity)
    modifies io.fsRegion, io.stdoutRegion, io.stderrRegion
    ensures SegmentPaths(io.fs()) == universe
    ensures io.fs() == old(io.fs()) ||
            BenchWorld.FileSystemTopologyUnchangedExceptMode(old(io.fs()), io.fs())
    ensures var result := ApplyResolvedCore(
                            cmd, plan, identity, old(io.fs()), old(io.now())
                          );
            io.fs() == result.fs &&
            io.stdout() == old(io.stdout()) + result.stdoutChunk &&
            io.stderr() == old(io.stderr()) + result.stderrChunk &&
            ok == result.ok
  {
    var displayPath := identity.displayPath;
    var accessPath := identity.accessPath;
    var isDirectory := identity.isDirectory;
    var isSymlink := identity.isSymlink;
    var isTopLevel := identity.isTopLevel;
    if isSymlink && !ChmodFollowCore(cmd, isTopLevel) {
      if cmd.verbose {
        io.AppendStdout(NeitherChangedMessageCore(displayPath));
      }
      ok := true;
      return;
    }

    ghost var beforeFs := io.fs();
    var gotMode, rawModeStatus1, modeErr := io.GetFileStatus(accessPath, true);
    IOContract.FileStatusImpliesMode(io.fs(), accessPath, true, gotMode, rawModeStatus1, modeErr);
    var before := rawModeStatus1.mode;
    if !gotMode {
      AppendRuntimeAccessFailure(
        cmd,
        displayPath,
        modeErr,
        ResolutionFailureKindCore(
          cmd, isTopLevel, isSymlink, modeErr
        ),
        io
      );
      ok := false;
      return;
    }

    var desired := Base.CorePlannedMode(plan, before, isDirectory);
    var setOk, setErr := io.SetFileMode(accessPath, true, desired);
    SetFileModePreservesSegmentPaths(
      beforeFs,
      accessPath,
      true,
      desired,
      setOk,
      setErr,
      io.fs()
    );
    if !setOk {
      if !cmd.silent {
        io.AppendStderr(
          Base.ChangeErrorMessageCore(displayPath, Base.ErrnoTextCore(setErr))
        );
      }
      ok := false;
      return;
    }

    ok := Base.FinishSuccessfulChangeCore(
      cmd,
      plan,
      displayPath,
      accessPath,
      true,
      before,
      BenchWorld.NormalizeMode(desired),
      isDirectory,
      io
    );
  }

  method ApplyLeafRuntime(
    cmd: Schema.ChmodCmd,
    plan: Base.CoreModePlan,
    identity: RecursiveIdentity,
    ghost universe: set<seq<string>>,
    activeSegments: set<seq<string>>,
    io: BenchIO.IO
  ) returns (ok: bool, ghost visit: RecursiveVisit)
    requires SegmentPaths(io.fs()) == universe
    requires IdentityResolvesCore(io.fs(), identity)
    requires ValidVisitCore(
               cmd,
               plan,
               RecursiveNode(identity, [], RecursiveEof),
               activeSegments,
               io.fs(),
               io.now()
             )
    modifies io.fsRegion, io.stdoutRegion, io.stderrRegion
    ensures SegmentPaths(io.fs()) == universe
    ensures RuntimeVisitOutcomeCore(
              cmd,
              plan,
              identity.displayPath,
              identity.accessPath,
              identity.isTopLevel,
              activeSegments,
              old(io.fs()),
              old(io.stdout()),
              old(io.stderr()),
              io.fs(),
              io.stdout(),
              io.stderr(),
              ok,
              visit,
              old(io.now())
            )
  {
    ghost var fs0 := io.fs();
    ghost var now0 := io.now();
    ok := ApplyPathRuntime(cmd, plan, identity, universe, io);
    visit := RecursiveNode(identity, [], RecursiveEof);
    EmptyNodeEvaluationCore(
      cmd, plan, identity, activeSegments, fs0, now0
    );
  }

  method ApplyDirectoryParentRuntime(
    cmd: Schema.ChmodCmd,
    plan: Base.CoreModePlan,
    identity: RecursiveIdentity,
    ghost universe: set<seq<string>>,
    activeSegments: set<seq<string>>,
    io: BenchIO.IO
  ) returns (parentOk: bool)
    requires activeSegments <= universe
    requires SegmentPaths(io.fs()) == universe
    requires IdentityResolvesCore(io.fs(), identity)
    requires identity.isDirectory
    requires BenchWorld.PathSegments(identity.resolvedPath) !in
             activeSegments
    modifies io.fsRegion, io.stdoutRegion, io.stderrRegion
    ensures SegmentPaths(io.fs()) == universe
    ensures BenchWorld.PathSegments(identity.resolvedPath) in
              universe - activeSegments
    ensures io.fs() == old(io.fs()) ||
            BenchWorld.FileSystemTopologyUnchangedExceptMode(old(io.fs()), io.fs())
    ensures BenchWorld.FsContainsPath(io.fs(), identity.resolvedPath)
    ensures BenchWorld.FsNodeAt(
              io.fs(), identity.resolvedPath
            ).Directory?
    ensures var result := ApplyResolvedCore(
                            cmd, plan, identity, old(io.fs()), old(io.now())
                          );
            io.fs() == result.fs &&
            io.stdout() == old(io.stdout()) + result.stdoutChunk &&
            io.stderr() == old(io.stderr()) + result.stderrChunk &&
            parentOk == result.ok
  {
    ghost var fs0 := io.fs();
    ghost var now0 := io.now();
    var resolvedSegments := BenchWorld.PathSegments(identity.resolvedPath);
    LookupSegmentsInSegmentPaths(fs0, resolvedSegments);
    assert resolvedSegments in universe - activeSegments;
    ApplyResolvedPreservesDirectory(cmd, plan, identity, fs0, now0);
    parentOk := ApplyPathRuntime(cmd, plan, identity, universe, io);
    assert BenchWorld.FsContainsPath(io.fs(), identity.resolvedPath);
    assert BenchWorld.FsNodeAt(io.fs(), identity.resolvedPath).Directory?;
  }

}
