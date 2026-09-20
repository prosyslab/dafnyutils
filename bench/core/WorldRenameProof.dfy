include "World.dfy"
include "WorldLookupProof.dfy"
include "WorldRemoveProof.dfy"

// Subtree relocation and rename validity.
module WorldRenameProof {
  import opened BenchWorld
  import Lookup = WorldLookupProof
  import Remove = WorldRemoveProof

  lemma {:isolate_assertions} InodeTreeDetachSubtreeProperties(
    tree: InodeTree,
    inodes: map<InodeId, InodeRecord>,
    segs: seq<string>,
    subtree: InodeTree
  )
    requires InodeTreeWellFormed(tree, inodes)
    requires |segs| > 0
    requires InodeFsLookupTreeSegments(inodes, tree, segs) ==
             Ok(subtree)
    ensures InodeTreeWellFormed(
              InodeTreeRemoveSegments(tree, segs), inodes
            )
    ensures InodeFsLookupTreeSegments(
              inodes, InodeTreeRemoveSegments(tree, segs), segs
            ) == Err(NoSuchFile)
    ensures forall id ::
              InodeNamespaceIdPaths(
                InodeTreeRemoveSegments(tree, segs), id
              ) == InodeNamespaceIdPaths(tree, id) -
              InodePrefixPaths(
                segs, InodeNamespaceIdPaths(subtree, id)
              )
    decreases |segs|
  {
    if |segs| == 1 {
      assert segs == [segs[0]];
      assert tree.children[segs[0]] == subtree;
      assert InodeTreeChildren(
          InodeTreeRemoveSegments(tree, segs)
        ) == tree.children - {segs[0]};
      forall id
        ensures InodeNamespaceIdPaths(
                  InodeTreeRemoveSegments(tree, segs), id
                ) == InodeNamespaceIdPaths(tree, id) -
                     InodePrefixPaths(
                       segs, InodeNamespaceIdPaths(subtree, id)
                     )
      {
        forall path |
          path in InodeNamespaceIdPaths(
                    InodeTreeRemoveSegments(tree, segs), id
                  )
          ensures path in InodeNamespaceIdPaths(tree, id) &&
                  path !in InodePrefixPaths(
                    segs, InodeNamespaceIdPaths(subtree, id)
                  )
        {
          if path != [] {
            var name, suffix :|
              name in InodeTreeChildren(
                        InodeTreeRemoveSegments(tree, segs)
                      ) &&
              suffix in InodeNamespaceIdPaths(
                          InodeTreeChildren(
                            InodeTreeRemoveSegments(tree, segs)
                          )[name],
                          id
                        ) &&
              path == [name] + suffix;
            assert name != segs[0];
            if path in InodePrefixPaths(
                         segs, InodeNamespaceIdPaths(subtree, id)
                       ) {
              var removedSuffix :|
                removedSuffix in InodeNamespaceIdPaths(subtree, id) &&
                path == segs + removedSuffix;
              assert path[0] == name;
              assert path[0] == segs[0];
              assert name == segs[0];
            }
          }
        }
        forall path |
          path in InodeNamespaceIdPaths(tree, id) &&
          path !in InodePrefixPaths(
            segs, InodeNamespaceIdPaths(subtree, id)
          )
          ensures path in InodeNamespaceIdPaths(
                            InodeTreeRemoveSegments(tree, segs), id
                          )
        {
          if path != [] {
            var name, suffix :|
              name in tree.children &&
              suffix in InodeNamespaceIdPaths(
                          tree.children[name], id
                        ) &&
              path == [name] + suffix;
            if name == segs[0] {
              assert suffix in InodeNamespaceIdPaths(subtree, id);
              assert path in InodePrefixPaths(
                               segs, InodeNamespaceIdPaths(subtree, id)
                             );
            }
          }
        }
      }
    } else {
      InodeTreeDetachSubtreeProperties(
        tree.children[segs[0]],
        inodes,
        segs[1..],
        subtree
      );
      assert [segs[0]] + segs[1..] == segs;
      assert InodeTreeChildren(
          InodeTreeRemoveSegments(tree, segs)
        )[segs[0]] ==
             InodeTreeRemoveSegments(
               tree.children[segs[0]], segs[1..]
             );
      forall id
        ensures InodeNamespaceIdPaths(
                  InodeTreeRemoveSegments(tree, segs), id
                ) == InodeNamespaceIdPaths(tree, id) -
                     InodePrefixPaths(
                       segs, InodeNamespaceIdPaths(subtree, id)
                     )
      {
        Lookup.InodePrefixPathsCompose(
          [segs[0]],
          segs[1..],
          InodeNamespaceIdPaths(subtree, id)
        );
        assert InodeNamespaceIdPaths(
            InodeTreeRemoveSegments(
              tree.children[segs[0]], segs[1..]
            ),
            id
          ) == InodeNamespaceIdPaths(
                      tree.children[segs[0]], id
                    ) - InodePrefixPaths(
                      segs[1..], InodeNamespaceIdPaths(subtree, id)
                    );
        forall path |
          path in InodeNamespaceIdPaths(
                    InodeTreeRemoveSegments(tree, segs), id
                  )
          ensures path in InodeNamespaceIdPaths(tree, id) &&
                  path !in InodePrefixPaths(
                    segs, InodeNamespaceIdPaths(subtree, id)
                  )
        {
          if path != [] {
            var name, suffix :|
              name in InodeTreeChildren(
                        InodeTreeRemoveSegments(tree, segs)
                      ) &&
              suffix in InodeNamespaceIdPaths(
                          InodeTreeChildren(
                            InodeTreeRemoveSegments(tree, segs)
                          )[name],
                          id
                        ) &&
              path == [name] + suffix;
            if name == segs[0] {
              assert suffix in InodeNamespaceIdPaths(
                                 tree.children[name], id
                               );
              assert suffix !in InodePrefixPaths(
                  segs[1..],
                  InodeNamespaceIdPaths(subtree, id)
                );
              if path in InodePrefixPaths(
                           segs, InodeNamespaceIdPaths(subtree, id)
                         ) {
                var removedSuffix :|
                  removedSuffix in InodeNamespaceIdPaths(subtree, id) &&
                  path == segs + removedSuffix;
                assert path[1..] == suffix;
                assert (segs + removedSuffix)[1..] ==
                       segs[1..] + removedSuffix;
                assert suffix == segs[1..] + removedSuffix;
                assert suffix in InodePrefixPaths(
                                   segs[1..],
                                   InodeNamespaceIdPaths(subtree, id)
                                 );
              }
            } else if path in InodePrefixPaths(
                                segs, InodeNamespaceIdPaths(subtree, id)
                              ) {
              var removedSuffix :|
                removedSuffix in InodeNamespaceIdPaths(subtree, id) &&
                path == segs + removedSuffix;
              assert path[0] == name;
              assert path[0] == segs[0];
            }
          }
        }
        forall path |
          path in InodeNamespaceIdPaths(tree, id) &&
          path !in InodePrefixPaths(
            segs, InodeNamespaceIdPaths(subtree, id)
          )
          ensures path in InodeNamespaceIdPaths(
                            InodeTreeRemoveSegments(tree, segs), id
                          )
        {
          if path != [] {
            var name, suffix :|
              name in tree.children &&
              suffix in InodeNamespaceIdPaths(
                          tree.children[name], id
                        ) &&
              path == [name] + suffix;
            if name == segs[0] {
              if suffix in InodePrefixPaths(
                             segs[1..],
                             InodeNamespaceIdPaths(subtree, id)
                           ) {
                var removedSuffix :|
                  removedSuffix in InodeNamespaceIdPaths(subtree, id) &&
                  suffix == segs[1..] + removedSuffix;
                assert path == segs + removedSuffix;
                assert path in InodePrefixPaths(
                                 segs, InodeNamespaceIdPaths(subtree, id)
                               );
              }
              assert suffix !in InodePrefixPaths(
                  segs[1..],
                  InodeNamespaceIdPaths(subtree, id)
                );
            }
          }
        }
      }
    }
  }

  lemma {:isolate_assertions} InodeTreeAttachSubtreeProperties(
    tree: InodeTree,
    inodes: map<InodeId, InodeRecord>,
    segs: seq<string>,
    subtree: InodeTree
  )
    requires InodeTreeWellFormed(tree, inodes)
    requires InodeTreeWellFormed(subtree, inodes)
    requires InodeTreeCanInsert(inodes, tree, segs)
    ensures InodeTreeWellFormed(
              InodeTreeSetSubtreeSegments(tree, segs, subtree), inodes
            )
    ensures InodeFsLookupTreeSegments(
              inodes,
              InodeTreeSetSubtreeSegments(tree, segs, subtree),
              segs
            ) == Ok(subtree)
    ensures forall id ::
              InodeNamespaceIdPaths(
                InodeTreeSetSubtreeSegments(tree, segs, subtree), id
              ) == InodeNamespaceIdPaths(tree, id) +
              InodePrefixPaths(
                segs, InodeNamespaceIdPaths(subtree, id)
              )
    decreases |segs|
  {
    if |segs| == 1 {
      assert segs == [segs[0]];
    } else {
      InodeTreeAttachSubtreeProperties(
        tree.children[segs[0]],
        inodes,
        segs[1..],
        subtree
      );
      assert [segs[0]] + segs[1..] == segs;
      forall id
        ensures InodeNamespaceIdPaths(
                  InodeTreeSetSubtreeSegments(tree, segs, subtree), id
                ) == InodeNamespaceIdPaths(tree, id) +
                     InodePrefixPaths(
                       segs, InodeNamespaceIdPaths(subtree, id)
                     )
      {
        Lookup.InodePrefixPathsCompose(
          [segs[0]],
          segs[1..],
          InodeNamespaceIdPaths(subtree, id)
        );
      }
    }
  }

  lemma {:isolate_assertions} InodeTreeRelocateSubtreeProperties(
    tree: InodeTree,
    inodes: map<InodeId, InodeRecord>,
    source: seq<string>,
    target: seq<string>,
    subtree: InodeTree
  )
    requires InodeTreeWellFormed(tree, inodes)
    requires InodeFsLookupTreeSegments(inodes, tree, source) ==
             Ok(subtree)
    requires InodeTreeCanInsert(inodes, tree, target)
    requires InodeSegmentsDisjoint(source, target)
    requires InodeFsLookupTreeSegments(
               inodes,
               InodeTreeSetSubtreeSegments(tree, target, subtree),
               source
             ) == Ok(subtree)
    ensures InodeTreeWellFormed(
              InodeTreeRemoveSegments(
                InodeTreeSetSubtreeSegments(tree, target, subtree),
                source
              ),
              inodes
            )
    ensures forall id ::
              InodeNamespaceRefCount(
                InodeTreeRemoveSegments(
                  InodeTreeSetSubtreeSegments(tree, target, subtree),
                  source
                ),
                id
              ) == InodeNamespaceRefCount(tree, id)
    ensures InodeNamespaceIds(
              InodeTreeRemoveSegments(
                InodeTreeSetSubtreeSegments(tree, target, subtree),
                source
              )
            ) == InodeNamespaceIds(tree)
  {
    Lookup.InodeLookupTreeWellFormed(inodes, tree, source, subtree);
    InodeTreeAttachSubtreeProperties(
      tree, inodes, target, subtree
    );
    var attached :=
      InodeTreeSetSubtreeSegments(tree, target, subtree);
    InodeTreeDetachSubtreeProperties(
      attached, inodes, source, subtree
    );
    var result := InodeTreeRemoveSegments(attached, source);
    forall id
      ensures InodeNamespaceRefCount(result, id) ==
              InodeNamespaceRefCount(tree, id)
    {
      var before := InodeNamespaceIdPaths(tree, id);
      var subtreePaths := InodeNamespaceIdPaths(subtree, id);
      var sourcePaths := InodePrefixPaths(source, subtreePaths);
      var targetPaths := InodePrefixPaths(target, subtreePaths);
      var attachedPaths := InodeNamespaceIdPaths(attached, id);
      var resultPaths := InodeNamespaceIdPaths(result, id);

      Lookup.InodeLookupPrefixPathsSubset(
        inodes, tree, source, subtree, id
      );
      Lookup.InodeInsertPrefixPathsDisjoint(
        inodes, tree, target, subtreePaths, id
      );
      Lookup.InodeDisjointPrefixPaths(
        source, target, subtreePaths, subtreePaths
      );
      Lookup.InodePrefixPathsCardinality(source, subtreePaths);
      Lookup.InodePrefixPathsCardinality(target, subtreePaths);

      assert sourcePaths <= before;
      assert before * targetPaths == {};
      assert sourcePaths * targetPaths == {};
      assert attachedPaths == before + targetPaths;
      assert resultPaths == attachedPaths - sourcePaths;
      assert sourcePaths <= attachedPaths;
      assert |attachedPaths| == |before| + |targetPaths|;
      assert |resultPaths| == |attachedPaths| - |sourcePaths|;
      assert |sourcePaths| == |targetPaths|;
      assert |resultPaths| == |before|;
    }
    assert forall id ::
        id in InodeNamespaceIds(result) <==>
              id in InodeNamespaceIds(tree) by {
      forall id
        ensures id in InodeNamespaceIds(result) <==>
                id in InodeNamespaceIds(tree)
      {
        Lookup.InodeNamespaceIdRefCount(result, id);
        Lookup.InodeNamespaceIdRefCount(tree, id);
      }
    }
  }

  lemma {:isolate_assertions} InodeFsRenameValid(
    fs: InodeFileSystem,
    source: Path,
    target: Path
  )
    ensures ValidInodeFileSystemData(
              InodeFsRename(fs, source, target)
            )
  {
    var result := InodeFsRename(fs, source, target);
    if result != fs {
      var sourceSegs := PathSegments(source);
      var targetSegs := PathSegments(target);
      assert |sourceSegs| > 0 && |targetSegs| > 0;
      assert InodeFsContainsPath(fs, source);
      var sourceTree := InodeFsLookupTreeSegments(
        fs.inodes, fs.namespace, sourceSegs
      ).v;
      var withoutTarget :=
        if InodeFsContainsPath(fs, target) then
          InodeFsRemovePath(fs, target)
        else
          fs;
      if InodeFsContainsPath(fs, target) {
        Remove.InodeFsRemovePathValid(fs, target);
      }
      assert ValidInodeFileSystemData(withoutTarget);
      var safeWithoutTarget: InodeFileSystem := withoutTarget;
      assert InodeTreeCanInsert(
          withoutTarget.inodes,
          withoutTarget.namespace,
          targetSegs
        );
      assert InodeFsLookupTreeSegments(
          withoutTarget.inodes,
          withoutTarget.namespace,
          sourceSegs
        ) == Ok(sourceTree);
      var attached := InodeTreeSetSubtreeSegments(
        withoutTarget.namespace, targetSegs, sourceTree
      );
      assert InodeFsLookupTreeSegments(
          withoutTarget.inodes, attached, sourceSegs
        ) == Ok(sourceTree);
      if sourceSegs == targetSegs {
        assert InodeFsContainsPath(fs, target);
        assert InodeFsLookupId(fs, source) ==
               InodeFsLookupId(fs, target);
        assert InodeSameObject(fs, source, target);
      }
      assert sourceSegs != targetSegs;
      if |sourceSegs| <= |targetSegs| {
        if |sourceSegs| == |targetSegs| {
          assert targetSegs[..|sourceSegs|] == targetSegs;
        }
        assert targetSegs[..|sourceSegs|] != sourceSegs;
      } else {
        if |targetSegs| == |sourceSegs| {
          assert sourceSegs[..|targetSegs|] == sourceSegs;
        }
        assert sourceSegs[..|targetSegs|] != targetSegs;
      }
      assert InodeSegmentsDisjoint(sourceSegs, targetSegs);

      InodeTreeRelocateSubtreeProperties(
        withoutTarget.namespace,
        withoutTarget.inodes,
        sourceSegs,
        targetSegs,
        sourceTree
      );
      assert result.namespace ==
             InodeTreeRemoveSegments(attached, sourceSegs);
      assert result.inodes == withoutTarget.inodes;
      assert InodeTreeWellFormed(result.namespace, result.inodes);
      assert InodeNamespaceIds(result.namespace) ==
             InodeNamespaceIds(withoutTarget.namespace);
      assert result.inodes.Keys ==
             InodeNamespaceIds(result.namespace);
      assert forall id :: (InodeNamespaceRefCount(
                             result.namespace, id
                           ) == InodeNamespaceRefCount(
                                  withoutTarget.namespace, id
                                ));
      assert forall liveId :: (
                                liveId in result.inodes &&
                                FsNodeCanHaveChildren(result.inodes[liveId].node)) ==>
                                InodeNamespaceRefCount(result.namespace, liveId) == 1 by {
        forall liveId | liveId in result.inodes &&
                        FsNodeCanHaveChildren(result.inodes[liveId].node)
          ensures InodeNamespaceRefCount(
                    result.namespace, liveId
                  ) == 1
        {
          assert InodeNamespaceRefCount(
              result.namespace, liveId
            ) == InodeNamespaceRefCount(
                        withoutTarget.namespace, liveId
                      );
        }
      }
      assert InodeNamespaceWellFormed(result);
      assert InodeUniqueHostKeys(result);
      assert forall liveId :: liveId in result.inodes ==>
                                InodeStorageConsistent(result.inodes[liveId]) &&
                                InodeKindConsistent(result.inodes[liveId]) by {
        forall liveId | liveId in result.inodes
          ensures InodeStorageConsistent(result.inodes[liveId]) &&
                  InodeKindConsistent(result.inodes[liveId])
        {
          assert result.inodes[liveId] ==
                 withoutTarget.inodes[liveId];
        }
      }
      assert InodeValidLinkObservations(result);
      assert result.namespace.id == withoutTarget.namespace.id;
      assert result.namespace.id in result.inodes;
      assert result.inodes[result.namespace.id].node.Directory?;
    }
  }

  ghost method InodeFsRenameVerified(
    fs: InodeFileSystem,
    source: Path,
    target: Path
  ) returns (result: InodeFileSystem)
    ensures result == InodeFsRename(fs, source, target)
  {
    InodeFsRenameValid(fs, source, target);
    result := InodeFsRename(fs, source, target);
  }

  lemma InodeRenameSameObjectNoop(
    fs: InodeFileSystem,
    source: Path,
    target: Path
  )
    requires InodeSameObject(fs, source, target)
    ensures InodeFsRename(fs, source, target) == fs
  {
    assert InodeFsRename(fs, source, target) == fs;
  }
}
