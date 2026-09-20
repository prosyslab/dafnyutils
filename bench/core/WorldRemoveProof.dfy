include "World.dfy"
include "WorldLookupProof.dfy"

// Leaf removal and the remaining inode namespace.
module WorldRemoveProof {
  import opened BenchWorld
  import Lookup = WorldLookupProof

  lemma InodeTreeCanRemoveFindsLeaf(
    inodes: map<InodeId, InodeRecord>,
    tree: InodeTree,
    segs: seq<string>
  )
    requires InodeTreeCanRemove(inodes, tree, segs)
    ensures exists id ::
              InodeFsLookupTreeSegments(inodes, tree, segs) ==
              Ok(InodeTreeNode(id, map[]))
    decreases |segs|
  {
    reveal InodeTreeCanRemove();
    if |segs| == 1 {
      var child := tree.children[segs[0]];
      assert child.children == map[];
      assert InodeFsLookupTreeSegments(inodes, tree, segs).Ok?;
      assert InodeFsLookupTreeSegments(inodes, tree, segs) ==
             Ok(child);
      assert child == InodeTreeNode(child.id, map[]);
    } else {
      InodeTreeCanRemoveFindsLeaf(
        inodes, tree.children[segs[0]], segs[1..]
      );
      var id :|
        InodeFsLookupTreeSegments(
          inodes, tree.children[segs[0]], segs[1..]
        ) == Ok(InodeTreeNode(id, map[]));
      assert InodeFsLookupTreeSegments(inodes, tree, segs) ==
             Ok(InodeTreeNode(id, map[]));
    }
  }

  lemma InodeTreeRemoveLeafWellFormed(
    tree: InodeTree,
    inodes: map<InodeId, InodeRecord>,
    segs: seq<string>
  )
    requires InodeTreeWellFormed(tree, inodes)
    requires InodeTreeCanRemove(inodes, tree, segs)
    ensures InodeTreeWellFormed(
              InodeTreeRemoveSegments(tree, segs), inodes
            )
    decreases |segs|
  {
    if |segs| > 1 {
      InodeTreeRemoveLeafWellFormed(
        tree.children[segs[0]], inodes, segs[1..]
      );
    }
  }

  lemma InodeTreeWellFormedWithoutUnusedRecord(
    tree: InodeTree,
    inodes: map<InodeId, InodeRecord>,
    id: InodeId
  )
    requires InodeTreeWellFormed(tree, inodes)
    requires id !in InodeNamespaceIds(tree)
    ensures InodeTreeWellFormed(tree, inodes - {id})
    decreases tree
  {
    forall name | name in tree.children
      ensures InodeTreeWellFormed(
                tree.children[name], inodes - {id}
              )
    {
      assert id !in InodeNamespaceIds(tree.children[name]);
      InodeTreeWellFormedWithoutUnusedRecord(
        tree.children[name], inodes, id
      );
    }
  }

  lemma {:isolate_assertions} InodeTreeRemoveLeafProperties(
    tree: InodeTree,
    inodes: map<InodeId, InodeRecord>,
    segs: seq<string>,
    removedId: InodeId
  )
    requires InodeTreeWellFormed(tree, inodes)
    requires InodeTreeCanRemove(inodes, tree, segs)
    requires InodeFsLookupTreeSegments(inodes, tree, segs) ==
             Ok(InodeTreeNode(removedId, map[]))
    ensures InodeNamespaceIdPaths(
              InodeTreeRemoveSegments(tree, segs), removedId
            ) == InodeNamespaceIdPaths(tree, removedId) - {segs}
    ensures forall id :: id != removedId ==>
                           InodeNamespaceIdPaths(
                             InodeTreeRemoveSegments(tree, segs), id
                           ) == InodeNamespaceIdPaths(tree, id)
    decreases |segs|
  {
    Lookup.InodeLookupTreePathWitness(
      inodes, tree, segs, InodeTreeNode(removedId, map[])
    );
    assert segs in InodeNamespaceIdPaths(tree, removedId);
    if |segs| == 1 {
      assert segs == [segs[0]];
      assert InodeTreeChildren(
          InodeTreeRemoveSegments(tree, segs)
        ) == tree.children - {segs[0]};
      forall path |
        path in InodeNamespaceIdPaths(
                  InodeTreeRemoveSegments(tree, segs), removedId
                )
        ensures path in InodeNamespaceIdPaths(tree, removedId) &&
                path != segs
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
                        removedId
                      ) &&
            path == [name] + suffix;
          assert name != segs[0];
        }
      }
      forall path |
        path in InodeNamespaceIdPaths(tree, removedId) &&
        path != segs
        ensures path in InodeNamespaceIdPaths(
                          InodeTreeRemoveSegments(tree, segs), removedId
                        )
      {
        if path != [] {
          var name, suffix :|
            name in tree.children &&
            suffix in InodeNamespaceIdPaths(
                        tree.children[name], removedId
                      ) &&
            path == [name] + suffix;
          if name == segs[0] {
            assert tree.children[name] ==
                   InodeTreeNode(removedId, map[]);
            assert suffix == [];
            assert path == segs;
          }
        }
      }
    } else {
      InodeTreeRemoveLeafProperties(
        tree.children[segs[0]],
        inodes,
        segs[1..],
        removedId
      );
      assert InodeTreeChildren(
          InodeTreeRemoveSegments(tree, segs)
        )[segs[0]] ==
             InodeTreeRemoveSegments(
               tree.children[segs[0]], segs[1..]
             );
      assert InodeNamespaceIdPaths(
          InodeTreeRemoveSegments(
            tree.children[segs[0]], segs[1..]
          ),
          removedId
        ) == InodeNamespaceIdPaths(
                    tree.children[segs[0]], removedId
                  ) - {segs[1..]};
      forall path |
        path in InodeNamespaceIdPaths(
                  InodeTreeRemoveSegments(tree, segs), removedId
                )
        ensures path in InodeNamespaceIdPaths(tree, removedId) &&
                path != segs
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
                        removedId
                      ) &&
            path == [name] + suffix;
          if name == segs[0] {
            assert suffix != segs[1..];
          }
        }
      }
      forall path |
        path in InodeNamespaceIdPaths(tree, removedId) &&
        path != segs
        ensures path in InodeNamespaceIdPaths(
                          InodeTreeRemoveSegments(tree, segs), removedId
                        )
      {
        if path != [] {
          var name, suffix :|
            name in tree.children &&
            suffix in InodeNamespaceIdPaths(
                        tree.children[name], removedId
                      ) &&
            path == [name] + suffix;
          if name == segs[0] {
            assert suffix != segs[1..];
          }
        }
      }
    }
  }

  lemma {:isolate_assertions} InodeTreeRemoveLeafIdsSubset(
    tree: InodeTree,
    inodes: map<InodeId, InodeRecord>,
    segs: seq<string>,
    removedId: InodeId
  )
    requires InodeTreeWellFormed(tree, inodes)
    requires InodeTreeCanRemove(inodes, tree, segs)
    requires InodeFsLookupTreeSegments(inodes, tree, segs) ==
             Ok(InodeTreeNode(removedId, map[]))
    ensures InodeNamespaceIds(
              InodeTreeRemoveSegments(tree, segs)
            ) <= (
                   if InodeNamespaceRefCount(tree, removedId) == 1 then
                     InodeNamespaceIds(tree) - {removedId}
                   else
                     InodeNamespaceIds(tree)
                 )
  {
    InodeTreeRemoveLeafProperties(
      tree, inodes, segs, removedId
    );
    Lookup.InodeLookupTreePathWitness(
      inodes, tree, segs, InodeTreeNode(removedId, map[])
    );
    var nextTree := InodeTreeRemoveSegments(tree, segs);
    forall liveId | liveId in InodeNamespaceIds(nextTree)
      ensures liveId in (
                          if InodeNamespaceRefCount(tree, removedId) == 1 then
                            InodeNamespaceIds(tree) - {removedId}
                          else
                            InodeNamespaceIds(tree)
                        )
    {
      Lookup.InodeNamespaceIdHasPath(nextTree, liveId);
      var livePath :|
        livePath in InodeNamespaceIdPaths(nextTree, liveId);
      if liveId == removedId {
        assert livePath in
                 InodeNamespaceIdPaths(tree, removedId) - {segs};
        if InodeNamespaceRefCount(tree, removedId) == 1 {
          Lookup.FiniteSetSingleton(
            InodeNamespaceIdPaths(tree, removedId), segs
          );
          assert false;
        }
      } else {
        assert livePath in InodeNamespaceIdPaths(tree, liveId);
      }
      Lookup.InodeNamespaceIdPathHasId(tree, liveId, livePath);
    }
  }

  lemma {:isolate_assertions} InodeTreeRemoveLeafIdsSuperset(
    tree: InodeTree,
    inodes: map<InodeId, InodeRecord>,
    segs: seq<string>,
    removedId: InodeId
  )
    requires InodeTreeWellFormed(tree, inodes)
    requires InodeTreeCanRemove(inodes, tree, segs)
    requires InodeFsLookupTreeSegments(inodes, tree, segs) ==
             Ok(InodeTreeNode(removedId, map[]))
    ensures (
              if InodeNamespaceRefCount(tree, removedId) == 1 then
                InodeNamespaceIds(tree) - {removedId}
              else
                InodeNamespaceIds(tree)
            ) <= InodeNamespaceIds(
                   InodeTreeRemoveSegments(tree, segs)
                 )
  {
    InodeTreeRemoveLeafProperties(
      tree, inodes, segs, removedId
    );
    Lookup.InodeLookupTreePathWitness(
      inodes, tree, segs, InodeTreeNode(removedId, map[])
    );
    var nextTree := InodeTreeRemoveSegments(tree, segs);
    forall liveId | liveId in (
                                if InodeNamespaceRefCount(tree, removedId) == 1 then
                                  InodeNamespaceIds(tree) - {removedId}
                                else
                                  InodeNamespaceIds(tree)
                              )
      ensures liveId in InodeNamespaceIds(nextTree)
    {
      if liveId == removedId {
        assert InodeNamespaceRefCount(tree, removedId) != 1;
        assert |InodeNamespaceIdPaths(tree, removedId)| > 0;
        assert |InodeNamespaceIdPaths(tree, removedId)| > 1;
        assert InodeNamespaceIdPaths(tree, removedId) - {segs} != {};
        var livePath :|
          livePath in InodeNamespaceIdPaths(tree, removedId) - {segs};
        assert livePath in
                 InodeNamespaceIdPaths(nextTree, removedId);
        Lookup.InodeNamespaceIdPathHasId(nextTree, removedId, livePath);
      } else {
        Lookup.InodeNamespaceIdHasPath(tree, liveId);
        var livePath :|
          livePath in InodeNamespaceIdPaths(tree, liveId);
        assert livePath in InodeNamespaceIdPaths(nextTree, liveId);
        Lookup.InodeNamespaceIdPathHasId(nextTree, liveId, livePath);
      }
    }
  }

  lemma InodeTreeRemoveLeafIds(
    tree: InodeTree,
    inodes: map<InodeId, InodeRecord>,
    segs: seq<string>,
    removedId: InodeId
  )
    requires InodeTreeWellFormed(tree, inodes)
    requires InodeTreeCanRemove(inodes, tree, segs)
    requires InodeFsLookupTreeSegments(inodes, tree, segs) ==
             Ok(InodeTreeNode(removedId, map[]))
    ensures InodeNamespaceIds(
              InodeTreeRemoveSegments(tree, segs)
            ) == (
                   if InodeNamespaceRefCount(tree, removedId) == 1 then
                     InodeNamespaceIds(tree) - {removedId}
                   else
                     InodeNamespaceIds(tree)
                 )
  {
    InodeTreeRemoveLeafIdsSubset(
      tree, inodes, segs, removedId
    );
    InodeTreeRemoveLeafIdsSuperset(
      tree, inodes, segs, removedId
    );
  }

  lemma {:isolate_assertions} InodeFsRemovePathValid(
    fs: InodeFileSystem,
    path: Path
  )
    ensures ValidInodeFileSystemData(InodeFsRemovePath(fs, path))
  {
    var segs := PathSegments(path);
    if InodeTreeCanRemove(fs.inodes, fs.namespace, segs) {
      InodeTreeCanRemoveFindsLeaf(
        fs.inodes, fs.namespace, segs
      );
      var id :|
        InodeFsLookupTreeSegments(
          fs.inodes, fs.namespace, segs
        ) == Ok(InodeTreeNode(id, map[]));
      var result := InodeFsRemovePath(fs, path);
      var oldRefs :=
        InodeNamespaceRefCount(fs.namespace, id);

      InodeTreeRemoveLeafWellFormed(
        fs.namespace, fs.inodes, segs
      );
      InodeTreeRemoveLeafProperties(
        fs.namespace, fs.inodes, segs, id
      );
      Lookup.InodeLookupTreePathWitness(
        fs.inodes,
        fs.namespace,
        segs,
        InodeTreeNode(id, map[])
      );
      InodeTreeRemoveLeafIds(
        fs.namespace, fs.inodes, segs, id
      );

      assert oldRefs > 0;
      assert InodeNamespaceRefCount(result.namespace, id) ==
             oldRefs - 1;
      assert result.namespace.id == fs.namespace.id;

      if oldRefs == 1 {
        assert id !in InodeNamespaceIds(result.namespace);
        InodeTreeWellFormedWithoutUnusedRecord(
          result.namespace, fs.inodes, id
        );
        assert result.inodes == fs.inodes - {id};
      } else {
        var nextRecord := InodeRecordAfterUnlink(fs.inodes[id]);
        assert InodeSameNodeKind(
            fs.inodes[id].node, nextRecord.node
          );
        Lookup.InodeTreeWellFormedAfterNodeUpdate(
          result.namespace, fs.inodes, id, nextRecord
        );
        assert result.inodes == fs.inodes[id := nextRecord];
      }
      assert InodeTreeWellFormed(result.namespace, result.inodes);

      assert result.inodes.Keys ==
             InodeNamespaceIds(result.namespace);
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
          if liveId == id {
            assert oldRefs != 1;
            assert FsNodeCanHaveChildren(fs.inodes[id].node);
            assert oldRefs == 1;
          } else {
            assert InodeNamespaceIdPaths(
                result.namespace, liveId
              ) == InodeNamespaceIdPaths(fs.namespace, liveId);
          }
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
          if liveId == id && oldRefs != 1 {
            assert result.inodes[id] ==
                   InodeRecordAfterUnlink(fs.inodes[id]);
          } else {
            assert result.inodes[liveId] == fs.inodes[liveId];
          }
        }
      }
      assert forall liveId :: liveId in result.inodes ==>
                                var refs :=
                                  InodeNamespaceRefCount(result.namespace, liveId);
                                result.inodes[liveId].links.LinkCountKnown? &&
                                0 < result.inodes[liveId].links.count &&
                                refs <= result.inodes[liveId].links.count by {
        forall liveId | liveId in result.inodes
          ensures
            var refs :=
              InodeNamespaceRefCount(result.namespace, liveId);
            result.inodes[liveId].links.LinkCountKnown? &&
            0 < result.inodes[liveId].links.count &&
            refs <= result.inodes[liveId].links.count
        {
          if liveId == id {
            assert oldRefs > 1;
            assert fs.inodes[id].links.LinkCountKnown?;
            assert fs.inodes[id].links.count >= oldRefs;
            assert result.inodes[id].links.count ==
                   fs.inodes[id].links.count - 1;
          } else {
            assert InodeNamespaceIdPaths(
                result.namespace, liveId
              ) == InodeNamespaceIdPaths(fs.namespace, liveId);
          }
        }
      }
      assert InodeValidLinkObservations(result);

      if id == fs.namespace.id {
        assert [] in InodeNamespaceIdPaths(fs.namespace, id);
        assert segs != [];
        assert oldRefs > 1;
        assert fs.inodes[id].node.Directory?;
        assert oldRefs == 1;
      }
      assert result.namespace.id in result.inodes;
      assert result.inodes[result.namespace.id].node.Directory?;
    }
  }

  ghost method InodeFsRemovePathVerified(
    fs: InodeFileSystem,
    path: Path
  ) returns (result: InodeFileSystem)
    ensures result == InodeFsRemovePath(fs, path)
  {
    InodeFsRemovePathValid(fs, path);
    result := InodeFsRemovePath(fs, path);
  }
}
