include "World.dfy"
include "WorldLookupProof.dfy"

// Fresh inode insertion preserves filesystem validity.
module WorldInsertProof {
  import opened BenchWorld
  import Lookup = WorldLookupProof

  lemma InodeTreeWellFormedAfterFreshRecord(
    tree: InodeTree,
    inodes: map<InodeId, InodeRecord>,
    id: InodeId,
    record: InodeRecord
  )
    requires InodeTreeWellFormed(tree, inodes)
    requires id !in inodes
    ensures InodeTreeWellFormed(tree, inodes[id := record])
    decreases tree
  {
    forall name | name in tree.children
      ensures InodeTreeWellFormed(
                tree.children[name], inodes[id := record]
              )
    {
      InodeTreeWellFormedAfterFreshRecord(
        tree.children[name], inodes, id, record
      );
    }
  }

  lemma InodeTreeInsertFreshProperties(
    tree: InodeTree,
    inodes: map<InodeId, InodeRecord>,
    segs: seq<string>,
    id: InodeId,
    record: InodeRecord
  )
    requires InodeTreeWellFormed(tree, inodes)
    requires InodeTreeCanInsert(inodes, tree, segs)
    requires id !in inodes
    ensures InodeTreeWellFormed(
              InodeTreeSetSubtreeSegments(
                tree, segs, InodeTreeNode(id, map[])
              ),
              inodes[id := record]
            )
    ensures InodeNamespaceIds(
              InodeTreeSetSubtreeSegments(
                tree, segs, InodeTreeNode(id, map[])
              )
            ) == InodeNamespaceIds(tree) + {id}
    ensures InodeNamespaceIdPaths(
              InodeTreeSetSubtreeSegments(
                tree, segs, InodeTreeNode(id, map[])
              ),
              id
            ) == {segs}
    ensures forall oldId :: oldId in inodes ==>
                              InodeNamespaceIdPaths(
                                InodeTreeSetSubtreeSegments(
                                  tree, segs, InodeTreeNode(id, map[])
                                ),
                                oldId
                              ) == InodeNamespaceIdPaths(tree, oldId)
    decreases |segs|
  {
    InodeTreeWellFormedAfterFreshRecord(tree, inodes, id, record);
    Lookup.InodeTreeIdsInInodes(tree, inodes);
    assert id !in InodeNamespaceIds(tree);
    if |segs| == 1 {
      assert segs == [segs[0]];
      assert FsNodeCanHaveChildren(
          inodes[id := record][tree.id].node
        );
      assert InodeTreeWellFormed(
          InodeTreeNode(id, map[]), inodes[id := record]
        );
      forall name | name in
                      InodeTreeChildren(
                        InodeTreeSetSubtreeSegments(
                          tree, segs, InodeTreeNode(id, map[])
                        )
                      )
        ensures InodeTreeWellFormed(
                  InodeTreeChildren(
                    InodeTreeSetSubtreeSegments(
                      tree, segs, InodeTreeNode(id, map[])
                    )
                  )[name],
                  inodes[id := record]
                )
      {
        if name == segs[0] {
        } else {
          InodeTreeWellFormedAfterFreshRecord(
            tree.children[name], inodes, id, record
          );
        }
      }
      forall liveId |
        liveId in InodeNamespaceIds(
                    InodeTreeSetSubtreeSegments(
                      tree, segs, InodeTreeNode(id, map[])
                    )
                  )
        ensures liveId in InodeNamespaceIds(tree) + {id}
      {
        if liveId != tree.id {
          var name :| name in
                        InodeTreeChildren(
                          InodeTreeSetSubtreeSegments(
                            tree, segs, InodeTreeNode(id, map[])
                          )
                        ) &&
                      liveId in InodeNamespaceIds(
                                  InodeTreeChildren(
                                    InodeTreeSetSubtreeSegments(
                                      tree, segs, InodeTreeNode(id, map[])
                                    )
                                  )[name]
                                );
          if name != segs[0] {
            assert name in tree.children;
          }
        }
      }
      forall liveId | liveId in InodeNamespaceIds(tree) + {id}
        ensures liveId in InodeNamespaceIds(
                            InodeTreeSetSubtreeSegments(
                              tree, segs, InodeTreeNode(id, map[])
                            )
                          )
      {
        if liveId == id {
          assert id in InodeNamespaceIds(InodeTreeNode(id, map[]));
          assert segs[0] in InodeTreeChildren(
                              InodeTreeSetSubtreeSegments(
                                tree, segs, InodeTreeNode(id, map[])
                              )
                            );
        } else if liveId != tree.id {
          var name :| name in tree.children &&
                      liveId in InodeNamespaceIds(tree.children[name]);
          assert name != segs[0];
          assert InodeTreeChildren(
              InodeTreeSetSubtreeSegments(
                tree, segs, InodeTreeNode(id, map[])
              )
            )[name] == tree.children[name];
        }
      }
      forall path |
        path in InodeNamespaceIdPaths(
                  InodeTreeSetSubtreeSegments(
                    tree, segs, InodeTreeNode(id, map[])
                  ),
                  id
                )
        ensures path == segs
      {
        var name, suffix :|
          name in InodeTreeChildren(
                    InodeTreeSetSubtreeSegments(
                      tree, segs, InodeTreeNode(id, map[])
                    )
                  ) &&
          suffix in InodeNamespaceIdPaths(
                      InodeTreeChildren(
                        InodeTreeSetSubtreeSegments(
                          tree, segs, InodeTreeNode(id, map[])
                        )
                      )[name],
                      id
                    ) &&
          path == [name] + suffix;
        if name != segs[0] {
          assert name in tree.children;
          Lookup.InodeTreeIdsInInodes(tree.children[name], inodes);
          Lookup.InodeNamespaceIdPathHasId(
            tree.children[name], id, suffix
          );
          assert id !in InodeNamespaceIds(tree.children[name]);
          assert false;
        }
      }
      assert [] in InodeNamespaceIdPaths(
                     InodeTreeNode(id, map[]), id
                   );
      assert [segs[0]] + [] in InodeNamespaceIdPaths(
                                 InodeTreeSetSubtreeSegments(
                                   tree, segs, InodeTreeNode(id, map[])
                                 ),
                                 id
                               );
      assert segs in InodeNamespaceIdPaths(
                       InodeTreeSetSubtreeSegments(
                         tree, segs, InodeTreeNode(id, map[])
                       ),
                       id
                     );
    } else {
      var name := segs[0];
      InodeTreeInsertFreshProperties(
        tree.children[name],
        inodes,
        segs[1..],
        id,
        record
      );
      assert [name] + segs[1..] == segs;
      forall childName | childName in tree.children
        ensures InodeTreeWellFormed(
                  InodeTreeChildren(
                    InodeTreeSetSubtreeSegments(
                      tree, segs, InodeTreeNode(id, map[])
                    )
                  )[childName],
                  inodes[id := record]
                )
      {
        if childName != name {
          InodeTreeWellFormedAfterFreshRecord(
            tree.children[childName], inodes, id, record
          );
        }
      }
      forall path |
        path in InodeNamespaceIdPaths(
                  InodeTreeSetSubtreeSegments(
                    tree, segs, InodeTreeNode(id, map[])
                  ),
                  id
                )
        ensures path == segs
      {
        var childName, suffix :|
          childName in InodeTreeChildren(
                         InodeTreeSetSubtreeSegments(
                           tree, segs, InodeTreeNode(id, map[])
                         )
                       ) &&
          suffix in InodeNamespaceIdPaths(
                      InodeTreeChildren(
                        InodeTreeSetSubtreeSegments(
                          tree, segs, InodeTreeNode(id, map[])
                        )
                      )[childName],
                      id
                    ) &&
          path == [childName] + suffix;
        if childName != name {
          assert childName in tree.children;
          Lookup.InodeTreeIdsInInodes(tree.children[childName], inodes);
          Lookup.InodeNamespaceIdPathHasId(
            tree.children[childName], id, suffix
          );
          assert id !in InodeNamespaceIds(tree.children[childName]);
          assert false;
        }
      }
      assert segs in InodeNamespaceIdPaths(
                       InodeTreeSetSubtreeSegments(
                         tree, segs, InodeTreeNode(id, map[])
                       ),
                       id
                     );
    }
  }

  lemma InodeInsertFreshValid(
    fs: InodeFileSystem,
    path: Path,
    id: InodeId,
    key: HostInodeKey,
    node: FsNode,
    ownership: Ownership,
    storage: StorageInfo
  )
    requires InodeCanCreateFresh(fs, path, id, key, node)
    requires id !in fs.inodes
    requires forall oldId :: oldId in fs.inodes ==>
                               fs.inodes[oldId].hostKey != key
    requires InodeStorageConsistent(
               FreshInodeRecord(key, node, ownership, storage)
             )
    ensures ValidInodeFileSystemData(
              InodeFsInsertFreshData(
                fs, path, id, key, node, ownership, storage
              )
            )
  {
    var record := FreshInodeRecord(
      key, node, ownership, storage
    );
    var result := InodeFsInsertFreshData(
      fs, path, id, key, node, ownership, storage
    );
    InodeTreeInsertFreshProperties(
      fs.namespace,
      fs.inodes,
      PathSegments(path),
      id,
      record
    );
    assert result.namespace.id == fs.namespace.id;
    assert result.inodes.Keys == fs.inodes.Keys + {id};
    assert InodeNamespaceIds(result.namespace) ==
           InodeNamespaceIds(fs.namespace) + {id};
    assert result.inodes.Keys == InodeNamespaceIds(result.namespace);
    assert InodeNamespaceRefCount(result.namespace, id) == 1;

    assert forall oldId :: oldId in fs.inodes ==>
                             InodeNamespaceRefCount(result.namespace, oldId) ==
                             InodeNamespaceRefCount(fs.namespace, oldId);

    assert forall liveId :: (liveId in result.inodes &&
                             FsNodeCanHaveChildren(result.inodes[liveId].node)) ==>
                              InodeNamespaceRefCount(result.namespace, liveId) == 1 by {
      forall liveId | liveId in result.inodes &&
                      FsNodeCanHaveChildren(result.inodes[liveId].node)
        ensures InodeNamespaceRefCount(result.namespace, liveId) == 1
      {
        if liveId != id {
          assert liveId in fs.inodes;
        }
      }
    }
    assert InodeNamespaceWellFormed(result);

    assert forall left, right ::
        left in result.inodes && right in result.inodes &&
        result.inodes[left].hostKey == result.inodes[right].hostKey ==>
          left == right by {
      forall left, right | left in result.inodes &&
                           right in result.inodes &&
                           result.inodes[left].hostKey == result.inodes[right].hostKey
        ensures left == right
      {
        if left == id && right != id {
          assert right in fs.inodes;
          assert fs.inodes[right].hostKey != key;
        } else if right == id && left != id {
          assert left in fs.inodes;
          assert fs.inodes[left].hostKey != key;
        } else if left != id && right != id {
          assert left in fs.inodes && right in fs.inodes;
        }
      }
    }
    assert InodeUniqueHostKeys(result);

    assert forall liveId :: liveId in result.inodes ==>
                              var refs := InodeNamespaceRefCount(result.namespace, liveId);
                              result.inodes[liveId].links.LinkCountKnown? &&
                              0 < result.inodes[liveId].links.count &&
                              refs <= result.inodes[liveId].links.count by {
      forall liveId | liveId in result.inodes
        ensures
          var refs := InodeNamespaceRefCount(result.namespace, liveId);
          result.inodes[liveId].links.LinkCountKnown? &&
          0 < result.inodes[liveId].links.count &&
          refs <= result.inodes[liveId].links.count
      {
        if liveId != id {
          assert liveId in fs.inodes;
        }
      }
    }
    assert InodeValidLinkObservations(result);
  }

  ghost method InodeFsInsertFreshVerified(
    fs: InodeFileSystem,
    path: Path,
    id: InodeId,
    key: HostInodeKey,
    node: FsNode,
    ownership: Ownership,
    storage: StorageInfo
  ) returns (result: InodeFileSystem)
    requires InodeCanCreateFresh(fs, path, id, key, node)
    requires id !in fs.inodes
    requires forall oldId :: oldId in fs.inodes ==>
                               fs.inodes[oldId].hostKey != key
    requires InodeStorageConsistent(
               FreshInodeRecord(key, node, ownership, storage)
             )
    ensures result == InodeFsInsertFreshData(
                        fs, path, id, key, node, ownership, storage
                      )
  {
    InodeInsertFreshValid(
      fs, path, id, key, node, ownership, storage
    );
    result := InodeFsInsertFreshData(
      fs, path, id, key, node, ownership, storage
    );
  }
}
