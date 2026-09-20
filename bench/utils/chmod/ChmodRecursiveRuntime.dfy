include "ChmodRecursiveCore.dfy"
include "ChmodRecursiveLeafRuntime.dfy"

module ChmodRecursiveRuntime {
  import BenchWorld
  import BenchIO
  import IOContract
  import Schema = ChmodSchema
  import Base = ChmodCore
  import opened ChmodRecursiveCore
  import Leaf = ChmodRecursiveLeafRuntime

  method AppendRuntimeReadFailure(
    cmd: Schema.ChmodCmd,
    displayPath: string,
    err: int,
    io: BenchIO.IO
  )
    requires err != 0
    modifies io.stdoutRegion, io.stderrRegion
    ensures io.stdout() == old(io.stdout()) +
                         RecursiveReadStdoutCore(
                           cmd, displayPath, RecursiveReadError(err)
                         )
    ensures io.stderr() == old(io.stderr()) +
                         RecursiveReadStderrCore(
                           cmd, displayPath, RecursiveReadError(err)
                         )
  {
    if !cmd.silent {
      io.AppendStderr(ReadDirectoryMessageCore(displayPath, err));
    }
    if cmd.verbose {
      io.AppendStdout(Base.AccessFailureMessageCore(displayPath));
    }
  }

  method ProcessDirectoryEntryChildRuntime(
    cmd: Schema.ChmodCmd,
    plan: Base.CoreModePlan,
    parent: RecursiveIdentity,
    name: string,
    ghost entry: BenchWorld.DirEntry,
    ghost universe: set<seq<string>>,
    activeSegments: set<seq<string>>,
    io: BenchIO.IO
  ) returns (childOk: bool, ghost child: RecursiveVisit)
    requires activeSegments <= universe
    requires parent.isDirectory
    requires BenchWorld.IsAbsolutePath(parent.resolvedPath)
    requires BenchWorld.PathSegments(parent.resolvedPath) in
               universe - activeSegments
    requires entry.name == name
    requires SegmentPaths(io.fs()) == universe
    modifies io.fsRegion, io.stdoutRegion, io.stderrRegion, io.dirHandlesRegion
    ensures io.dirHandles() == old(io.dirHandles())
    ensures SegmentPaths(io.fs()) == universe
    ensures VisitMatchesEntryCore(parent, entry, child)
    ensures RuntimeVisitOutcomeCore(
              cmd,
              plan,
              BenchWorld.AppendPath(parent.displayPath, name),
              BenchWorld.AppendPath(parent.resolvedPath, name),
              false,
              activeSegments + {
                BenchWorld.PathSegments(parent.resolvedPath)
              },
              old(io.fs()),
              old(io.stdout()),
              old(io.stderr()),
              io.fs(),
              io.stdout(),
              io.stderr(),
              childOk,
              child,
              old(io.now())
            )
    decreases |universe - activeSegments|, 0, 0, 0
  {
    var childDisplay := BenchWorld.AppendPath(
      parent.displayPath, name
    );
    var childAccess := BenchWorld.AppendPath(
      parent.resolvedPath, name
    );
    RemainingUniverseDecreases(
      universe,
      activeSegments,
      BenchWorld.PathSegments(parent.resolvedPath)
    );
    childOk, child := ProcessRecursivePathRuntime(
      cmd,
      plan,
      childDisplay,
      childAccess,
      false,
      universe,
      activeSegments + {
        BenchWorld.PathSegments(parent.resolvedPath)
      },
      io
    );
    assert VisitMatchesEntryCore(parent, entry, child);
  }

  method {:isolate_assertions} ProcessDirectorySuffixAccumulatorRuntime(
    cmd: Schema.ChmodCmd,
    plan: Base.CoreModePlan,
    parent: RecursiveIdentity,
    handle: int,
    ghost entry: BenchWorld.DirEntry,
    childOk: bool,
    ghost child: RecursiveVisit,
    ghost universe: set<seq<string>>,
    activeSegments: set<seq<string>>,
    ghost childFs0: BenchWorld.FileSystem,
    ghost childStdout0: BenchWorld.Bytes,
    ghost childStderr0: BenchWorld.Bytes,
    ghost beforeReadHandles: map<int, BenchWorld.DirHandleState>,
    io: BenchIO.IO
  ) returns (
      descendantsOk: bool,
      ghost entries: seq<BenchWorld.DirEntry>,
      ghost children: seq<RecursiveVisit>,
      ghost terminal: RecursiveTerminal
    )
    requires activeSegments <= universe
    requires parent.isDirectory
    requires BenchWorld.IsAbsolutePath(parent.resolvedPath)
    requires BenchWorld.PathSegments(parent.resolvedPath) in
               universe - activeSegments
    requires handle in beforeReadHandles
    requires beforeReadHandles[handle].path == parent.resolvedPath
    requires entry in beforeReadHandles[handle].remaining
    requires io.dirHandles() == beforeReadHandles[handle :=
                              BenchWorld.DirHandleState(
                                beforeReadHandles[handle].path,
                                beforeReadHandles[handle].remaining - {entry}
                              )
                              ]
    requires SegmentPaths(childFs0) == universe
    requires SegmentPaths(io.fs()) == universe
    requires VisitMatchesEntryCore(parent, entry, child)
    requires RuntimeVisitOutcomeCore(
               cmd,
               plan,
               BenchWorld.AppendPath(parent.displayPath, entry.name),
               BenchWorld.AppendPath(parent.resolvedPath, entry.name),
               false,
               activeSegments + {
                 BenchWorld.PathSegments(parent.resolvedPath)
               },
               childFs0,
               childStdout0,
               childStderr0,
               io.fs(),
               io.stdout(),
               io.stderr(),
               childOk,
               child,
               io.now()
             )
    modifies io.fsRegion, io.stdoutRegion, io.stderrRegion, io.dirHandlesRegion
    ensures handle in io.dirHandles()
    ensures io.dirHandles().Keys == beforeReadHandles.Keys
    ensures forall h :: h in beforeReadHandles && h != handle ==>
                          io.dirHandles()[h] == beforeReadHandles[h]
    ensures io.dirHandles()[handle].path == parent.resolvedPath
    ensures io.dirHandles()[handle].remaining ==
            beforeReadHandles[handle].remaining - EntriesSet(entries)
    ensures SegmentPaths(io.fs()) == universe
    ensures terminal.RecursiveReadError? ==> terminal.err != 0
    ensures |entries| == |children|
    ensures ValidOpenSchedule(
              beforeReadHandles[handle].remaining, entries, terminal
            )
    ensures forall j :: 0 <= j < |children| ==>
                          VisitMatchesEntryCore(parent, entries[j], children[j])
    ensures ValidVisitsCore(
              cmd,
              plan,
              children,
              0,
              activeSegments + {
                BenchWorld.PathSegments(parent.resolvedPath)
              },
              childFs0,
              old(io.now())
            )
    ensures var descendants := EvalChildrenCore(
                                 cmd,
                                 plan,
                                 children,
                                 0,
                                 activeSegments + {
                                   BenchWorld.PathSegments(parent.resolvedPath)
                                 },
                                 childFs0,
                                 old(io.now())
                               );
            io.fs() == descendants.fs &&
            io.stdout() == childStdout0 + descendants.stdoutChunk +
            RecursiveReadStdoutCore(cmd, parent.displayPath, terminal) &&
            io.stderr() == childStderr0 + descendants.stderrChunk +
            RecursiveReadStderrCore(cmd, parent.displayPath, terminal) &&
            descendantsOk == (descendants.allOk && terminal.RecursiveEof?)
    decreases |universe - activeSegments|, 0,
              |io.dirHandles()[handle].remaining|, 1
  {
    ghost var now0 := io.now();
    ghost var childActive := activeSegments + {
      BenchWorld.PathSegments(parent.resolvedPath)
    };
    ghost var childResult := EvalVisitCore(
      cmd, plan, child, childActive, childFs0, now0
    );
    assert ValidVisitCore(cmd, plan, child, childActive, childFs0, now0);
    assert io.fs() == childResult.fs;
    assert io.stdout() == childStdout0 + childResult.stdoutChunk;
    assert io.stderr() == childStderr0 + childResult.stderrChunk;
    assert childOk == childResult.allOk;
    ghost var suffixFs0 := io.fs();
    ghost var suffixStdout0 := io.stdout();
    ghost var suffixStderr0 := io.stderr();
    ghost var afterReadHandles := io.dirHandles();
    var suffixOk, suffixEntries, suffixChildren, suffixTerminal :=
      ReadDirectoryChildrenRuntime(
        cmd,
        plan,
        parent,
        handle,
        universe,
        activeSegments,
        io
      );
    ghost var suffixResult := EvalChildrenCore(
      cmd, plan, suffixChildren, 0, childActive, suffixFs0, now0
    );
    assert ValidVisitsCore(
        cmd, plan, suffixChildren, 0, childActive, suffixFs0, now0
      );
    assert io.fs() == suffixResult.fs;
    assert io.stdout() == suffixStdout0 + suffixResult.stdoutChunk +
                        RecursiveReadStdoutCore(cmd, parent.displayPath, suffixTerminal);
    assert io.stderr() == suffixStderr0 + suffixResult.stderrChunk +
                        RecursiveReadStderrCore(cmd, parent.displayPath, suffixTerminal);
    assert suffixOk ==
           (suffixResult.allOk && suffixTerminal.RecursiveEof?);
    assert io.dirHandles().Keys == afterReadHandles.Keys;
    assert forall h :: h in afterReadHandles && h != handle ==>
                         io.dirHandles()[h] == afterReadHandles[h];
    assert io.dirHandles()[handle].path == parent.resolvedPath;
    assert io.dirHandles()[handle].remaining ==
           afterReadHandles[handle].remaining - EntriesSet(suffixEntries);
    descendantsOk := childOk && suffixOk;
    entries := [entry] + suffixEntries;
    children := [child] + suffixChildren;
    terminal := suffixTerminal;

    RemainingAfterCons(
      beforeReadHandles[handle].remaining, entry, suffixEntries
    );
    assert ValidOpenSchedule(
        beforeReadHandles[handle].remaining, entries, terminal
      ) by {
      ValidOpenScheduleCons(
        beforeReadHandles[handle].remaining,
        entry,
        suffixEntries,
        suffixTerminal
      );
    }
    assert {:split_here} true;
    assert forall j :: 0 <= j < |children| ==>
                         VisitMatchesEntryCore(parent, entries[j], children[j]) by {
      forall j | 0 <= j < |children|
        ensures VisitMatchesEntryCore(parent, entries[j], children[j])
      {
        if j == 0 {
          assert VisitMatchesEntryCore(parent, entry, child);
        } else {
          ConsTailIndex(entry, suffixEntries, j);
          ConsTailIndex(child, suffixChildren, j);
        }
      }
    }
    assert ValidVisitsCore(
        cmd,
        plan,
        children,
        0,
        childActive,
        childFs0,
        now0
      ) by {
      ValidVisitsConsCore(
        cmd,
        plan,
        child,
        suffixChildren,
        childActive,
        childFs0,
        now0
      );
    }
    ghost var descendants := EvalChildrenCore(
      cmd,
      plan,
      children,
      0,
      childActive,
      childFs0,
      now0
    );
    EvalChildrenConsCore(
      cmd,
      plan,
      child,
      suffixChildren,
      childActive,
      childFs0,
      now0
    );
    assert descendants.stdoutChunk ==
           childResult.stdoutChunk + suffixResult.stdoutChunk;
    assert descendants.stderrChunk ==
           childResult.stderrChunk + suffixResult.stderrChunk;
    assert io.stdout() == childStdout0 + descendants.stdoutChunk +
                        RecursiveReadStdoutCore(
                          cmd, parent.displayPath, terminal
                        ) by {
      calc {
        io.stdout();
      ==
        suffixStdout0 + suffixResult.stdoutChunk +
        RecursiveReadStdoutCore(
          cmd, parent.displayPath, suffixTerminal
        );
      ==
        (childStdout0 + childResult.stdoutChunk) +
        suffixResult.stdoutChunk +
        RecursiveReadStdoutCore(
          cmd, parent.displayPath, suffixTerminal
        );
      == {
          Base.AppendAssociative(
            childStdout0,
            childResult.stdoutChunk,
            suffixResult.stdoutChunk
          );
        }
        childStdout0 +
        (childResult.stdoutChunk + suffixResult.stdoutChunk) +
        RecursiveReadStdoutCore(
          cmd, parent.displayPath, terminal
        );
      ==
        childStdout0 + descendants.stdoutChunk +
        RecursiveReadStdoutCore(
          cmd, parent.displayPath, terminal
        );
      }
    }
    assert io.stderr() == childStderr0 + descendants.stderrChunk +
                        RecursiveReadStderrCore(
                          cmd, parent.displayPath, terminal
                        ) by {
      calc {
        io.stderr();
      ==
        suffixStderr0 + suffixResult.stderrChunk +
        RecursiveReadStderrCore(
          cmd, parent.displayPath, suffixTerminal
        );
      ==
        (childStderr0 + childResult.stderrChunk) +
        suffixResult.stderrChunk +
        RecursiveReadStderrCore(
          cmd, parent.displayPath, suffixTerminal
        );
      == {
          Base.AppendAssociative(
            childStderr0,
            childResult.stderrChunk,
            suffixResult.stderrChunk
          );
        }
        childStderr0 +
        (childResult.stderrChunk + suffixResult.stderrChunk) +
        RecursiveReadStderrCore(
          cmd, parent.displayPath, terminal
        );
      ==
        childStderr0 + descendants.stderrChunk +
        RecursiveReadStderrCore(
          cmd, parent.displayPath, terminal
        );
      }
    }
    assert io.fs() == descendants.fs &&
           io.stdout() == childStdout0 + descendants.stdoutChunk +
           RecursiveReadStdoutCore(cmd, parent.displayPath, terminal) &&
           io.stderr() == childStderr0 + descendants.stderrChunk +
           RecursiveReadStderrCore(cmd, parent.displayPath, terminal) &&
           descendantsOk == (descendants.allOk && terminal.RecursiveEof?) by {
      EvalChildrenConsCore(
        cmd,
        plan,
        child,
        suffixChildren,
        childActive,
        childFs0,
        now0
      );
    }
  }

  method ProcessDirectoryEntryAndSuffixRuntime(
    cmd: Schema.ChmodCmd,
    plan: Base.CoreModePlan,
    parent: RecursiveIdentity,
    handle: int,
    name: string,
    ghost entry: BenchWorld.DirEntry,
    ghost universe: set<seq<string>>,
    activeSegments: set<seq<string>>,
    ghost initialFs: BenchWorld.FileSystem,
    ghost initialStdout: string,
    ghost initialStderr: string,
    ghost initialHandles: map<int, BenchWorld.DirHandleState>,
    io: BenchIO.IO
  ) returns (
      descendantsOk: bool,
      ghost entries: seq<BenchWorld.DirEntry>,
      ghost children: seq<RecursiveVisit>,
      ghost terminal: RecursiveTerminal
    )
    requires activeSegments <= universe
    requires parent.isDirectory
    requires BenchWorld.IsAbsolutePath(parent.resolvedPath)
    requires BenchWorld.PathSegments(parent.resolvedPath) in
               universe - activeSegments
    requires io.fs() == initialFs
    requires io.stdout() == initialStdout
    requires io.stderr() == initialStderr
    requires handle in initialHandles
    requires initialHandles[handle].path == parent.resolvedPath
    requires entry.name == name
    requires entry in initialHandles[handle].remaining
    requires io.dirHandles() == initialHandles[handle :=
                              BenchWorld.DirHandleState(
                                initialHandles[handle].path,
                                initialHandles[handle].remaining - {entry}
                              )
                              ]
    requires SegmentPaths(io.fs()) == universe
    modifies io.fsRegion, io.stdoutRegion, io.stderrRegion, io.dirHandlesRegion
    ensures handle in io.dirHandles()
    ensures io.dirHandles().Keys == initialHandles.Keys
    ensures forall h :: h in initialHandles && h != handle ==>
                          io.dirHandles()[h] == initialHandles[h]
    ensures io.dirHandles()[handle].path == parent.resolvedPath
    ensures io.dirHandles()[handle].remaining ==
            initialHandles[handle].remaining - EntriesSet(entries)
    ensures SegmentPaths(io.fs()) == universe
    ensures terminal.RecursiveReadError? ==> terminal.err != 0
    ensures |entries| == |children|
    ensures ValidOpenSchedule(
              initialHandles[handle].remaining, entries, terminal
            )
    ensures forall j :: 0 <= j < |children| ==>
                          VisitMatchesEntryCore(parent, entries[j], children[j])
    ensures ValidVisitsCore(
              cmd,
              plan,
              children,
              0,
              activeSegments + {
                BenchWorld.PathSegments(parent.resolvedPath)
              },
              initialFs,
              old(io.now())
            )
    ensures var descendants := EvalChildrenCore(
                                 cmd,
                                 plan,
                                 children,
                                 0,
                                 activeSegments + {
                                   BenchWorld.PathSegments(parent.resolvedPath)
                                 },
                                 initialFs,
                                 old(io.now())
                               );
            io.fs() == descendants.fs &&
            io.stdout() == initialStdout + descendants.stdoutChunk +
            RecursiveReadStdoutCore(cmd, parent.displayPath, terminal) &&
            io.stderr() == initialStderr + descendants.stderrChunk +
            RecursiveReadStderrCore(cmd, parent.displayPath, terminal) &&
            descendantsOk == (descendants.allOk && terminal.RecursiveEof?)
    decreases |universe - activeSegments|, 0,
              |io.dirHandles()[handle].remaining|, 2
  {
    ghost var childFs0 := io.fs();
    ghost var childStdout0 := io.stdout();
    ghost var childStderr0 := io.stderr();
    var childOk, child := ProcessDirectoryEntryChildRuntime(
      cmd,
      plan,
      parent,
      name,
      entry,
      universe,
      activeSegments,
      io
    );
    descendantsOk, entries, children, terminal :=
      ProcessDirectorySuffixAccumulatorRuntime(
        cmd,
        plan,
        parent,
        handle,
        entry,
        childOk,
        child,
        universe,
        activeSegments,
        childFs0,
        childStdout0,
        childStderr0,
        initialHandles,
        io
      );
  }

  method ReadDirectoryChildrenRuntime(
    cmd: Schema.ChmodCmd,
    plan: Base.CoreModePlan,
    parent: RecursiveIdentity,
    handle: int,
    ghost universe: set<seq<string>>,
    activeSegments: set<seq<string>>,
    io: BenchIO.IO
  ) returns (
      descendantsOk: bool,
      ghost entries: seq<BenchWorld.DirEntry>,
      ghost children: seq<RecursiveVisit>,
      ghost terminal: RecursiveTerminal
    )
    requires activeSegments <= universe
    requires parent.isDirectory
    requires BenchWorld.IsAbsolutePath(parent.resolvedPath)
    requires BenchWorld.PathSegments(parent.resolvedPath) in
               universe - activeSegments
    requires SegmentPaths(io.fs()) == universe
    requires handle in io.dirHandles()
    requires io.dirHandles()[handle].path == parent.resolvedPath
    modifies io.fsRegion, io.stdoutRegion, io.stderrRegion, io.dirHandlesRegion
    ensures handle in io.dirHandles()
    ensures io.dirHandles().Keys == old(io.dirHandles()).Keys
    ensures forall h :: h in old(io.dirHandles()) && h != handle ==>
                          io.dirHandles()[h] == old(io.dirHandles())[h]
    ensures io.dirHandles()[handle].path == parent.resolvedPath
    ensures io.dirHandles()[handle].remaining ==
            old(io.dirHandles()[handle].remaining) - EntriesSet(entries)
    ensures SegmentPaths(io.fs()) == universe
    ensures terminal.RecursiveReadError? ==> terminal.err != 0
    ensures |entries| == |children|
    ensures ValidOpenSchedule(
              old(io.dirHandles()[handle].remaining), entries, terminal
            )
    ensures forall j :: 0 <= j < |children| ==>
                          VisitMatchesEntryCore(parent, entries[j], children[j])
    ensures ValidVisitsCore(
              cmd,
              plan,
              children,
              0,
              activeSegments + {
                BenchWorld.PathSegments(parent.resolvedPath)
              },
              old(io.fs()),
              old(io.now())
            )
    ensures var descendants := EvalChildrenCore(
                                 cmd,
                                 plan,
                                 children,
                                 0,
                                 activeSegments + {
                                   BenchWorld.PathSegments(parent.resolvedPath)
                                 },
                                 old(io.fs()),
                                 old(io.now())
                               );
            io.fs() == descendants.fs &&
            io.stdout() == old(io.stdout()) + descendants.stdoutChunk +
            RecursiveReadStdoutCore(cmd, parent.displayPath, terminal) &&
            io.stderr() == old(io.stderr()) + descendants.stderrChunk +
            RecursiveReadStderrCore(cmd, parent.displayPath, terminal) &&
            descendantsOk == (descendants.allOk && terminal.RecursiveEof?)
    decreases |universe - activeSegments|, 0,
              |io.dirHandles()[handle].remaining|, 0
  {
    ghost var initialFs := io.fs();
    ghost var initialStdout := io.stdout();
    ghost var initialStderr := io.stderr();
    ghost var initialHandles := io.dirHandles();
    ghost var initialRemaining := io.dirHandles()[handle].remaining;
    var hasMore, name, entryIsDir, entryIsSymlink, readErr :=
      io.ReadDir(handle);
    if readErr != 0 {
      terminal := RecursiveReadError(readErr);
      AppendRuntimeReadFailure(cmd, parent.displayPath, readErr, io);
      descendantsOk := false;
      entries := [];
      children := [];
      return;
    }
    if !hasMore {
      descendantsOk := true;
      entries := [];
      children := [];
      terminal := RecursiveEof;
      assert initialRemaining == {};
      return;
    }

    ghost var entry := BenchWorld.DirEntry(
      name, entryIsDir, entryIsSymlink
    );
    assert entry in initialRemaining;
    assert io.dirHandles() == initialHandles[handle :=
                            BenchWorld.DirHandleState(
                              initialHandles[handle].path,
                              initialRemaining - {entry}
                            )
                            ];
    assert |initialRemaining - {entry}| < |initialRemaining|;
    descendantsOk, entries, children, terminal :=
      ProcessDirectoryEntryAndSuffixRuntime(
        cmd,
        plan,
        parent,
        handle,
        name,
        entry,
        universe,
        activeSegments,
        initialFs,
        initialStdout,
        initialStderr,
        initialHandles,
        io
      );
  }

  method {:isolate_assertions} {:vcs_split_on_every_assert} TraverseDirectoryRuntime(
    cmd: Schema.ChmodCmd,
    plan: Base.CoreModePlan,
    identity: RecursiveIdentity,
    parentOk: bool,
    ghost beforeFs: BenchWorld.FileSystem,
    ghost universe: set<seq<string>>,
    activeSegments: set<seq<string>>,
    io: BenchIO.IO
  ) returns (
      allOk: bool,
      ghost children: seq<RecursiveVisit>,
      ghost terminal: RecursiveTerminal
    )
    requires activeSegments <= universe
    requires SegmentPaths(io.fs()) == universe
    requires identity.isDirectory
    requires BenchWorld.IsAbsolutePath(identity.resolvedPath)
    requires BenchWorld.PathSegments(identity.resolvedPath) in
               universe - activeSegments
    requires IdentityResolvesCore(beforeFs, identity)
    requires io.fs() == beforeFs ||
             BenchWorld.FileSystemTopologyUnchangedExceptMode(beforeFs, io.fs())
    requires BenchWorld.FsContainsPath(io.fs(), identity.resolvedPath)
    requires BenchWorld.FsNodeAt(
               io.fs(), identity.resolvedPath
             ).Directory?
    modifies io.fsRegion, io.stdoutRegion, io.stderrRegion, io.dirHandlesRegion
    ensures io.dirHandles() == old(io.dirHandles())
    ensures SegmentPaths(io.fs()) == universe
    ensures terminal.RecursiveReadError? ==> terminal.err != 0
    ensures exists entries: seq<BenchWorld.DirEntry> ::
              |entries| == |children| &&
              ValidOpenSchedule(
                IOContract.DirectoryEntriesForPathFields(
                  old(io.fs()), identity.resolvedPath
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
                old(io.fs()),
                old(io.now())
              )
    ensures var descendants := EvalChildrenCore(
                                 cmd,
                                 plan,
                                 children,
                                 0,
                                 activeSegments + {
                                   BenchWorld.PathSegments(identity.resolvedPath)
                                 },
                                 old(io.fs()),
                                 old(io.now())
                               );
            io.fs() == descendants.fs &&
            io.stdout() == old(io.stdout()) + descendants.stdoutChunk +
            RecursiveReadStdoutCore(cmd, identity.displayPath, terminal) &&
            io.stderr() == old(io.stderr()) + descendants.stderrChunk +
            RecursiveReadStderrCore(cmd, identity.displayPath, terminal) &&
            allOk == (parentOk && descendants.allOk && terminal.RecursiveEof?)
    decreases |universe - activeSegments|, 1, 0, 0
  {
    ghost var baseHandles := io.dirHandles();
    ghost var startFs := io.fs();
    ghost var now0 := io.now();
    ghost var startStdout := io.stdout();
    ghost var startStderr := io.stderr();
    var openOk, handle, openErr := io.OpenDir(identity.accessPath);
    if !openOk {
      assert openErr ==
             IOContract.OpenDirFailureErrFields(
               startFs, identity.accessPath
             );
      assert IOContract.OpenDirFailureErrFields(
          startFs, identity.accessPath
        ) != 0 by {
        reveal IOContract.OpenDirContractFields;
        reveal IOContract.OpenDirFailureErrFields;
        reveal IOContract.IOErrorErrno;
      }
      assert openErr != 0;
      AppendRuntimeReadFailure(cmd, identity.displayPath, openErr, io);
      allOk := false;
      children := [];
      terminal := RecursiveReadError(openErr);
      assert terminal.err != 0;
      ghost var descendants := EvalChildrenCore(
        cmd,
        plan,
        children,
        0,
        activeSegments + {
          BenchWorld.PathSegments(identity.resolvedPath)
        },
        startFs,
        now0
      );
      assert descendants.fs == startFs;
      assert io.fs() == descendants.fs;
      assert descendants.stdoutChunk == [];
      assert descendants.stderrChunk == [];
      assert descendants.allOk;
      assert io.stdout() == startStdout +
                          RecursiveReadStdoutCore(
                            cmd, identity.displayPath, terminal
                          );
      assert io.stderr() == startStderr +
                          RecursiveReadStderrCore(
                            cmd, identity.displayPath, terminal
                          );
      assert !allOk;
      return;
    }

    assert handle !in baseHandles;
    assert io.dirHandles().Keys == baseHandles.Keys + {handle};
    if io.fs() != beforeFs {
      IOContract.ResolvePathForMetadataSuccessfulTargetsEqualExceptModeFields(
        beforeFs,
        io.fs(),
        identity.accessPath,
        true,
        identity.resolvedPath,
        io.dirHandles()[handle].path
      );
    }
    assert identity.resolvedPath == io.dirHandles()[handle].path;
    ghost var snapshot := io.dirHandles()[handle].remaining;
    var descendantsOk, schedule, visits, readTerminal :=
      ReadDirectoryChildrenRuntime(
        cmd,
        plan,
        identity,
        handle,
        universe,
        activeSegments,
        io
      );
    EmptyOwnedRestores(baseHandles, io.dirHandles() - {handle});
    children := visits;
    terminal := readTerminal;
    allOk := parentOk && descendantsOk;
    assert terminal.RecursiveReadError? ==> terminal.err != 0 by {
      assert terminal == readTerminal;
    }
    ghost var descendants := EvalChildrenCore(
      cmd,
      plan,
      children,
      0,
      activeSegments + {
        BenchWorld.PathSegments(identity.resolvedPath)
      },
      startFs,
      now0
    );
    assert descendantsOk ==
           (descendants.allOk && terminal.RecursiveEof?) by {
      assert children == visits;
      assert terminal == readTerminal;
    }
    assert io.fs() == descendants.fs;
    assert io.stdout() == startStdout + descendants.stdoutChunk +
                        RecursiveReadStdoutCore(
                          cmd, identity.displayPath, terminal
                        ) by {
      assert children == visits;
      assert terminal == readTerminal;
    }
    assert io.stderr() == startStderr + descendants.stderrChunk +
                        RecursiveReadStderrCore(
                          cmd, identity.displayPath, terminal
                        ) by {
      assert children == visits;
      assert terminal == readTerminal;
    }
    assert exists entries: seq<BenchWorld.DirEntry> ::
        |entries| == |children| &&
        ValidOpenSchedule(
          IOContract.DirectoryEntriesForPathFields(
            startFs, identity.resolvedPath
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
          startFs,
          now0
        ) by {
      assert snapshot == IOContract.DirectoryEntriesForPathFields(
                           startFs, identity.resolvedPath
                         );
      assert |schedule| == |children|;
      assert ValidOpenSchedule(
               IOContract.DirectoryEntriesForPathFields(
                 startFs, identity.resolvedPath
               ),
               schedule,
               terminal
             );
      assert forall j :: 0 <= j < |children| ==>
                             VisitMatchesEntryCore(
                               identity, schedule[j], children[j]
                             );
      assert ValidVisitsCore(
               cmd,
               plan,
               children,
               0,
               activeSegments + {
                 BenchWorld.PathSegments(identity.resolvedPath)
               },
               startFs,
               now0
             );
    }
    io.CloseDir(handle);
    assert io.dirHandles() == baseHandles;
    assert io.stdout() == old(io.stdout()) + descendants.stdoutChunk +
                          RecursiveReadStdoutCore(
                            cmd, identity.displayPath, terminal
                          ) by {
      assert startStdout == old(io.stdout());
    }
    assert io.stderr() == old(io.stderr()) + descendants.stderrChunk +
                          RecursiveReadStderrCore(
                            cmd, identity.displayPath, terminal
                          ) by {
      assert startStderr == old(io.stderr());
    }
    assert allOk ==
           (parentOk && descendants.allOk && terminal.RecursiveEof?) by {
      assert allOk == (parentOk && descendantsOk);
    }
  }

  method ProcessDirectoryNodeRuntime(
    cmd: Schema.ChmodCmd,
    plan: Base.CoreModePlan,
    identity: RecursiveIdentity,
    ghost universe: set<seq<string>>,
    activeSegments: set<seq<string>>,
    io: BenchIO.IO
  ) returns (ok: bool, ghost visit: RecursiveVisit)
    requires activeSegments <= universe
    requires SegmentPaths(io.fs()) == universe
    requires IdentityResolvesCore(io.fs(), identity)
    requires identity.isDirectory
    requires BenchWorld.IsAbsolutePath(identity.resolvedPath)
    requires !identity.isSymlink ||
             TraversalFollowCore(cmd, identity.isTopLevel)
    requires !(cmd.preserveRoot && identity.resolvedPath == "/")
    requires BenchWorld.PathSegments(identity.resolvedPath) !in activeSegments
    modifies io.fsRegion, io.stdoutRegion, io.stderrRegion, io.dirHandlesRegion
    ensures io.dirHandles() == old(io.dirHandles())
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
    decreases |universe - activeSegments|, 2, 0, 0
  {
    ghost var fs0 := io.fs();
    ghost var now0 := io.now();
    ghost var stdout0 := io.stdout();
    ghost var stderr0 := io.stderr();
    var parentOk := Leaf.ApplyDirectoryParentRuntime(
      cmd,
      plan,
      identity,
      universe,
      activeSegments,
      io
    );
    ghost var parentFs := io.fs();
    ghost var parentStdout := io.stdout();
    ghost var parentStderr := io.stderr();
    var directoryOk, children, terminal := TraverseDirectoryRuntime(
      cmd,
      plan,
      identity,
      parentOk,
      fs0,
      universe,
      activeSegments,
      io
    );
    visit := RecursiveNode(identity, children, terminal);
    ok := directoryOk;
    DirectoryVisitValidCore(
      cmd,
      plan,
      identity,
      activeSegments,
      fs0,
      parentFs,
      children,
      terminal,
      now0
    );
    EvalDirectoryVisitCore(
      cmd, plan, identity, activeSegments, fs0, children, terminal, now0
    );
    ghost var parent := ApplyResolvedCore(cmd, plan, identity, fs0, now0);
    ghost var descendants := EvalChildrenCore(
      cmd,
      plan,
      children,
      0,
      activeSegments + {
        BenchWorld.PathSegments(identity.resolvedPath)
      },
      parent.fs,
      now0
    );
    ghost var result := EvalVisitCore(
      cmd, plan, visit, activeSegments, fs0, now0
    );
    DirectoryStreamTraceCore(
      stdout0,
      parent.stdoutChunk,
      descendants.stdoutChunk,
      RecursiveReadStdoutCore(cmd, identity.displayPath, terminal),
      parentStdout,
      io.stdout()
    );
    DirectoryStreamTraceCore(
      stderr0,
      parent.stderrChunk,
      descendants.stderrChunk,
      RecursiveReadStderrCore(cmd, identity.displayPath, terminal),
      parentStderr,
      io.stderr()
    );
    assert io.fs() == result.fs;
    assert io.stdout() == stdout0 + result.stdoutChunk;
    assert io.stderr() == stderr0 + result.stderrChunk;
    assert ok == result.allOk;
    assert VisitIdentityCore(visit).displayPath == identity.displayPath;
    assert VisitIdentityCore(visit).accessPath == identity.accessPath;
    assert VisitIdentityCore(visit).isTopLevel == identity.isTopLevel;
    RuntimeVisitOutcomeFromPartsCore(
      cmd,
      plan,
      identity.displayPath,
      identity.accessPath,
      identity.isTopLevel,
      activeSegments,
      fs0,
      stdout0,
      stderr0,
      io.fs(),
      io.stdout(),
      io.stderr(),
      ok,
      visit,
      now0
    );
  }

  method ProcessRecursivePathRuntime(
    cmd: Schema.ChmodCmd,
    plan: Base.CoreModePlan,
    displayPath: string,
    accessPath: BenchWorld.Path,
    isTopLevel: bool,
    ghost universe: set<seq<string>>,
    activeSegments: set<seq<string>>,
    io: BenchIO.IO
  ) returns (ok: bool, ghost visit: RecursiveVisit)
    requires activeSegments <= universe
    requires SegmentPaths(io.fs()) == universe
    requires accessPath == "" || BenchWorld.IsAbsolutePath(accessPath)
    modifies io.fsRegion, io.stdoutRegion, io.stderrRegion, io.dirHandlesRegion
    ensures io.dirHandles() == old(io.dirHandles())
    ensures SegmentPaths(io.fs()) == universe
    ensures RuntimeVisitOutcomeCore(
              cmd,
              plan,
              displayPath,
              accessPath,
              isTopLevel,
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
    decreases |universe - activeSegments|, 3, 0, 0
  {
    ghost var baseHandles := io.dirHandles();
    ghost var fs0 := io.fs();
    ghost var now0 := io.now();
    ghost var stdout0 := io.stdout();
    ghost var stderr0 := io.stderr();
    var rawMetadataOk2, rawMetadataStatus2, rawMetadataErr2 := io.GetFileStatus(accessPath, false);
    IOContract.FileStatusImpliesMetadata(io.fs(), accessPath, false, rawMetadataOk2, rawMetadataStatus2, rawMetadataErr2);
    var linkOk := rawMetadataOk2;
    var isSymlink := rawMetadataStatus2.kind == BenchWorld.SymlinkKind;
    var linkErr := rawMetadataErr2;
    if !linkOk {
      Leaf.AppendRuntimeAccessFailure(
        cmd, displayPath, linkErr, RecursiveAccess, io
      );
      ok := false;
      visit := RecursiveAccessFailure(
        RecursiveIdentity(
          displayPath, accessPath, "", isTopLevel, false, false
        ),
        linkErr,
        RecursiveAccess
      );
      reveal ValidVisitCore;
      assert RuntimeVisitOutcomeCore(
          cmd, plan, displayPath, accessPath, isTopLevel,
          activeSegments, fs0, stdout0, stderr0,
          io.fs(), io.stdout(), io.stderr(), ok, visit, now0
        );
      return;
    }
    assert accessPath != "";
    assert BenchWorld.IsAbsolutePath(accessPath);

    var followTraversal := TraversalFollowCore(cmd, isTopLevel);
    var followChmod := ChmodFollowCore(cmd, isTopLevel);
    if isSymlink && !followTraversal && !followChmod {
      if cmd.verbose {
        io.AppendStdout(NeitherChangedMessageCore(displayPath));
      }
      ok := true;
      visit := RecursiveSkip(
        RecursiveIdentity(
          displayPath, accessPath, "", isTopLevel, true, false
        )
      );
      reveal ValidVisitCore;
      assert RuntimeVisitOutcomeCore(
          cmd, plan, displayPath, accessPath, isTopLevel,
          activeSegments, fs0, stdout0, stderr0,
          io.fs(), io.stdout(), io.stderr(), ok, visit, now0
        );
      return;
    }

    var identityOk, resolvedPath, identityErr :=
      io.ResolvePathIdentity(accessPath);
    if !identityOk {
      if isSymlink && !followChmod &&
         (!followTraversal ||
          Base.CoreIsDanglingSymlinkFailure(isSymlink, identityErr)) {
        if cmd.verbose {
          io.AppendStdout(NeitherChangedMessageCore(displayPath));
        }
        ok := true;
        visit := RecursiveSkip(
          RecursiveIdentity(
            displayPath, accessPath, "", isTopLevel, true, false
          )
        );
      } else {
        Leaf.AppendRuntimeAccessFailure(
          cmd,
          displayPath,
          identityErr,
          ResolutionFailureKindCore(
            cmd, isTopLevel, isSymlink, identityErr
          ),
          io
        );
        ok := false;
        visit := RecursiveAccessFailure(
          RecursiveIdentity(
            displayPath, accessPath, "", isTopLevel, isSymlink, false
          ),
          identityErr,
          ResolutionFailureKindCore(
            cmd, isTopLevel, isSymlink, identityErr
          )
        );
      }
      reveal ValidVisitCore;
      assert RuntimeVisitOutcomeCore(
          cmd, plan, displayPath, accessPath, isTopLevel,
          activeSegments, fs0, stdout0, stderr0,
          io.fs(), io.stdout(), io.stderr(), ok, visit, now0
        );
      return;
    }
    assert BenchWorld.FsContainsPath(io.fs(), resolvedPath);
    var resolvedSegments := BenchWorld.PathSegments(resolvedPath);
    LookupSegmentsInSegmentPaths(io.fs(), resolvedSegments);
    assert resolvedSegments in universe;

    var rawMetadataOk1, rawMetadataStatus1, rawMetadataErr1 := io.GetFileStatus(accessPath, true);
    IOContract.FileStatusImpliesMetadata(io.fs(), accessPath, true, rawMetadataOk1, rawMetadataStatus1, rawMetadataErr1);
    var dirOk := rawMetadataOk1;
    var isDirectory := rawMetadataStatus1.kind == BenchWorld.DirectoryKind;
    var dirErr := rawMetadataErr1;
    if !dirOk {
      Leaf.AppendRuntimeAccessFailure(
        cmd,
        displayPath,
        dirErr,
        ResolutionFailureKindCore(
          cmd, isTopLevel, isSymlink, dirErr
        ),
        io
      );
      ok := false;
      visit := RecursiveAccessFailure(
        RecursiveIdentity(
          displayPath, accessPath, "", isTopLevel, isSymlink, false
        ),
        dirErr,
        ResolutionFailureKindCore(cmd, isTopLevel, isSymlink, dirErr)
      );
      reveal ValidVisitCore;
      assert RuntimeVisitOutcomeCore(
          cmd, plan, displayPath, accessPath, isTopLevel,
          activeSegments, fs0, stdout0, stderr0,
          io.fs(), io.stdout(), io.stderr(), ok, visit, now0
        );
      return;
    }

    var identity := RecursiveIdentity(
      displayPath,
      accessPath,
      resolvedPath,
      isTopLevel,
      isSymlink,
      isDirectory
    );
    RuntimeIdentityResolvesCore(
      fs0,
      io.cwd(),
      displayPath,
      accessPath,
      resolvedPath,
      isTopLevel,
      isSymlink,
      isDirectory
    );

    if !isDirectory {
      NonDirectoryLeafValidCore(
        cmd,
        plan,
        identity,
        activeSegments,
        fs0,
        now0
      );
      ok, visit := Leaf.ApplyLeafRuntime(
        cmd,
        plan,
        identity,
        universe,
        activeSegments,
        io
      );
      assert RuntimeVisitOutcomeCore(
          cmd, plan, displayPath, accessPath, isTopLevel,
          activeSegments, fs0, stdout0, stderr0,
          io.fs(), io.stdout(), io.stderr(), ok, visit, now0
        );
      return;
    }

    if cmd.preserveRoot && resolvedPath == "/" {
      io.AppendStderr(
        RootPreserveMessageCore(displayPath, accessPath != "/")
      );
      ok := false;
      visit := RecursivePreserveRoot(identity, accessPath != "/");
      reveal ValidVisitCore;
      assert RuntimeVisitOutcomeCore(
          cmd, plan, displayPath, accessPath, isTopLevel,
          activeSegments, fs0, stdout0, stderr0,
          io.fs(), io.stdout(), io.stderr(), ok, visit, now0
        );
      return;
    }

    if isSymlink && !followTraversal {
      assert followChmod;
      NonTraversedSymlinkLeafValidCore(
        cmd,
        plan,
        identity,
        activeSegments,
        fs0,
        now0
      );
      ok, visit := Leaf.ApplyLeafRuntime(
        cmd,
        plan,
        identity,
        universe,
        activeSegments,
        io
      );
      assert RuntimeVisitOutcomeCore(
          cmd, plan, displayPath, accessPath, isTopLevel,
          activeSegments, fs0, stdout0, stderr0,
          io.fs(), io.stdout(), io.stderr(), ok, visit, now0
        );
      return;
    }

    if resolvedSegments in activeSegments {
      CycleLeafValidCore(
        cmd,
        plan,
        identity,
        activeSegments,
        fs0,
        now0
      );
      ok, visit := Leaf.ApplyLeafRuntime(
        cmd,
        plan,
        identity,
        universe,
        activeSegments,
        io
      );
      assert RuntimeVisitOutcomeCore(
          cmd, plan, displayPath, accessPath, isTopLevel,
          activeSegments, fs0, stdout0, stderr0,
          io.fs(), io.stdout(), io.stderr(), ok, visit, now0
        );
      return;
    }
    RemainingUniverseDecreases(
      universe,
      activeSegments,
      resolvedSegments
    );
    ok, visit := ProcessDirectoryNodeRuntime(
      cmd,
      plan,
      identity,
      universe,
      activeSegments,
      io
    );
    assert RuntimeVisitOutcomeCore(
        cmd, plan, displayPath, accessPath, isTopLevel,
        activeSegments, fs0, stdout0, stderr0,
        io.fs(), io.stdout(), io.stderr(), ok, visit, now0
      );
  }

  method ProcessRecursiveFilesRuntime(
    files: seq<string>,
    i: nat,
    cmd: Schema.ChmodCmd,
    plan: Base.CoreModePlan,
    cwd: BenchWorld.Path,
    ghost universe: set<seq<string>>,
    io: BenchIO.IO
  ) returns (allOk: bool, ghost visits: seq<RecursiveVisit>)
    requires i <= |files|
    requires SegmentPaths(io.fs()) == universe
    modifies io.fsRegion, io.stdoutRegion, io.stderrRegion, io.dirHandlesRegion
    ensures io.dirHandles() == old(io.dirHandles())
    ensures SegmentPaths(io.fs()) == universe
    ensures RuntimeFilesOutcomeCore(
              files,
              i,
              cmd,
              plan,
              cwd,
              old(io.fs()),
              old(io.stdout()),
              old(io.stderr()),
              io.fs(),
              io.stdout(),
              io.stderr(),
              allOk,
              visits,
              old(io.now())
            )
    decreases |files| - i
  {
    ghost var fs0 := io.fs();
    ghost var now0 := io.now();
    ghost var stdout0 := io.stdout();
    ghost var stderr0 := io.stderr();
    if i == |files| {
      allOk := true;
      visits := [];
      return;
    }
    var actual := Base.MakeAbsoluteCore(cwd, files[i]);
    assert actual == "" || BenchWorld.IsAbsolutePath(actual);
    var stepOk, stepVisit := ProcessRecursivePathRuntime(
      cmd,
      plan,
      files[i],
      actual,
      true,
      universe,
      {},
      io
    );
    ghost var stepFs := io.fs();
    ghost var stepStdout := io.stdout();
    ghost var stepStderr := io.stderr();
    var restOk, restVisits := ProcessRecursiveFilesRuntime(
      files,
      i + 1,
      cmd,
      plan,
      cwd,
      universe,
      io
    );
    allOk := stepOk && restOk;
    visits := [stepVisit] + restVisits;
    assert visits[0] == stepVisit;
    assert visits[1..] == restVisits;
    ValidVisitsSliceCore(cmd, plan, visits, 1, {}, stepFs, now0);
    assert ValidVisitsCore(cmd, plan, visits, 0, {}, fs0, now0) by {
      assert EvalVisitCore(cmd, plan, stepVisit, {}, fs0, now0).fs == stepFs;
    }
    assert forall j :: 0 <= j < |visits| ==>
                         var identity := VisitIdentityCore(visits[j]);
                         identity.displayPath == files[i + j] &&
                         identity.accessPath == Base.MakeAbsoluteCore(cwd, files[i + j]) &&
                         identity.isTopLevel by {
      forall j | 0 <= j < |visits|
        ensures var identity := VisitIdentityCore(visits[j]);
                identity.displayPath == files[i + j] &&
                identity.accessPath == Base.MakeAbsoluteCore(cwd, files[i + j]) &&
                identity.isTopLevel
      {
        if j > 0 {
          assert visits[j] == restVisits[j - 1];
          assert i + j == (i + 1) + (j - 1);
        }
      }
    }
    var stepResult := EvalVisitCore(cmd, plan, stepVisit, {}, fs0, now0);
    var restResult := EvalChildrenCore(
      cmd, plan, restVisits, 0, {}, stepResult.fs, now0
    );
    EvalChildrenSliceCore(cmd, plan, visits, 1, {}, stepResult.fs, now0);
    assert EvalChildrenCore(cmd, plan, visits, 0, {}, fs0, now0) ==
           RecursiveResult(
             restResult.fs,
             stepResult.stdoutChunk + restResult.stdoutChunk,
             stepResult.stderrChunk + restResult.stderrChunk,
             stepResult.allOk && restResult.allOk
           );
    assert io.stdout() == stdout0 +
                        (stepResult.stdoutChunk + restResult.stdoutChunk) by {
      assert stepStdout == stdout0 + stepResult.stdoutChunk;
      assert io.stdout() == stepStdout + restResult.stdoutChunk;
      Base.AppendAssociative(stdout0, stepResult.stdoutChunk, restResult.stdoutChunk);
    }
    assert io.stderr() == stderr0 +
                        (stepResult.stderrChunk + restResult.stderrChunk) by {
      assert stepStderr == stderr0 + stepResult.stderrChunk;
      assert io.stderr() == stepStderr + restResult.stderrChunk;
      Base.AppendAssociative(stderr0, stepResult.stderrChunk, restResult.stderrChunk);
    }
  }

  method RunRecursiveCore(
    raw: Schema.ChmodCmdRaw,
    io: BenchIO.IO
  ) returns (exit: int)
    requires Schema.Command(raw).recursive
    modifies io.fsRegion, io.stdoutRegion, io.stderrRegion, io.dirHandlesRegion
    ensures RecursiveCoreSummary(raw, io, exit)
  {
    var cmd := Schema.Command(raw);
    if cmd.mode == Schema.ModeHelp || cmd.mode == Schema.ModeVersion {
      exit := Base.RunCore(raw, io);
      return;
    }
    if cmd.dereferenceMode == 1 && cmd.traversalMode == 0 {
      io.AppendStderr(RecursiveDereferenceRequirementMessageCore());
      exit := 1;
      return;
    }
    if (cmd.seenReference && cmd.diagnoseSurprises) ||
       |cmd.files| == 0 ||
       (!cmd.seenReference && !Schema.IsValidModeExpr(cmd.modeExpr)) {
      exit := Base.RunCore(raw, io);
      return;
    }
    var cwd := io.GetCwd();
    var plan := Base.CoreGeneralModePlan(cmd.modeExpr, 0 as bv32);
    if cmd.seenReference {
      var referencePath := Base.MakeAbsoluteCore(cwd, cmd.referenceFile);
      var refOk, rawReferenceStatus, refErr := io.GetFileStatus(referencePath, true);
      IOContract.FileStatusImpliesMode(io.fs(), referencePath, true, refOk, rawReferenceStatus, refErr);
      var refMode := rawReferenceStatus.mode;
      if !refOk {
        io.AppendStderr(
          Base.ReferenceErrorMessageCore(
            cmd.referenceFile,
            Base.ErrnoTextCore(refErr)
          )
        );
        exit := 1;
        return;
      }
      plan := Base.CoreReferenceModePlan(refMode);
    } else {
      var umask := io.GetUmask();
      plan := Base.CoreGeneralModePlan(cmd.modeExpr, umask);
    }
    ghost var universe := SegmentPaths(io.fs());
    var allOk, visits := ProcessRecursiveFilesRuntime(
      cmd.files,
      0,
      cmd,
      plan,
      cwd,
      universe,
      io
    );
    exit := if allOk then 0 else 1;
  }
}
