include "World.dfy"
include "WorldLookupProof.dfy"

// Node updates, alias visibility and path-level API facts.
module WorldFileSystemProof {
  import opened BenchWorld
  import Lookup = WorldLookupProof

  lemma FsSetPathIsInodeFsUpdateNode(
    fs: FileSystem,
    path: Path,
    node: FsNode
  )
    ensures FsSetPath(fs, path, node) ==
            InodeFsUpdateNode(fs, path, node)
  {
    InodeFsUpdateNodeValid(fs, path, node);
  }

  lemma FsLookupSegmentsInPathSet(fs: FileSystem, segments: seq<string>)
    requires FsLookupSegments(fs, segments).Ok?
    ensures segments in FsPathSegments(fs)
    ensures FsCanSetSegments(fs, segments)
  {
    var tree := FsLookupSegments(fs, segments).v;
    Lookup.InodeLookupTreePathWitness(
      fs.inodes, fs.namespace, segments, tree
    );
    assert tree.id in fs.inodes;
  }

  lemma SetNodeModePreservesPathSet(fs: FileSystem, path: Path, mode: bv32)
    ensures FsPathSegments(SetNodeMode(fs, path, mode)) == FsPathSegments(fs)
    ensures FsContainsPath(fs, path) ==>
              FsContainsPath(SetNodeMode(fs, path, mode), path) &&
              FsNodeAt(SetNodeMode(fs, path, mode), path) ==
              WithNodeMode(FsNodeAt(fs, path), mode)
  {
    FsSetPathIsInodeFsUpdateNode(
      fs,
      path,
      if FsContainsPath(fs, path)
      then WithNodeMode(FsNodeAt(fs, path), mode)
      else Inaccessible(map[])
    );
    if FsContainsPath(fs, path) {
      var node := FsNodeAt(fs, path);
      assert InodeSameNodeKind(node, WithNodeMode(node, mode));
      assert InodeFsUpdateNode(
          fs, path, WithNodeMode(node, mode)
        ).namespace == fs.namespace;
      InodeUpdateAliasVisible(
        fs, path, path, WithNodeMode(node, mode)
      );
    }
  }

  lemma InodeUpdateAliasVisible(
    fs: InodeFileSystem,
    p: Path,
    q: Path,
    node: FsNode
  )
    requires InodeFsContainsPath(fs, p)
    requires InodeFsContainsPath(fs, q)
    requires InodeFsLookupId(fs, p) == InodeFsLookupId(fs, q)
    requires InodeSameNodeKind(InodeFsNodeAt(fs, p), node)
    ensures InodeFsContainsPath(InodeFsUpdateNode(fs, p, node), q)
    ensures InodeFsNodeAt(InodeFsUpdateNode(fs, p, node), q) == node
  {
    var id := InodeFsLookupId(fs, p).v;
    var priorRecord := fs.inodes[id];
    Lookup.InodeLookupUnchangedByRecordUpdate(
      fs.inodes,
      fs.namespace,
      PathSegments(q),
      id,
      InodeRecordWithNode(priorRecord, node)
    );
    assert InodeFsLookupId(InodeFsUpdateNode(fs, p, node), q) ==
           InodeFsLookupId(fs, q);
    assert InodeFsContainsPath(InodeFsUpdateNode(fs, p, node), q);
    assert InodeFsLookupId(InodeFsUpdateNode(fs, p, node), q).v == id;
  }

  lemma InodeFsUpdateNodeValid(
    fs: InodeFileSystem,
    path: Path,
    node: FsNode
  )
    ensures ValidInodeFileSystemData(
              InodeFsUpdateNode(fs, path, node)
            )
  {
    if InodeFsContainsPath(fs, path) &&
       InodeSameNodeKind(InodeFsNodeAt(fs, path), node)
    {
      var id := InodeFsLookupId(fs, path).v;
      var priorRecord := fs.inodes[id];
      var record :=
        InodeRecordWithNode(priorRecord, node);
      var result := InodeFsUpdateNode(fs, path, node);
      Lookup.InodeTreeWellFormedAfterNodeUpdate(
        fs.namespace, fs.inodes, id, record
      );
      assert result.namespace == fs.namespace;
      assert result.inodes.Keys == fs.inodes.Keys;
      assert InodeNamespaceIds(result.namespace) ==
             InodeNamespaceIds(fs.namespace);
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
            assert FsNodeCanHaveChildren(fs.inodes[id].node);
          }
        }
      }
      assert InodeNamespaceWellFormed(result);
      assert InodeUniqueHostKeys(result);
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
            assert InodeSameNodeKind(
                fs.inodes[id].node, result.inodes[id].node
              );
          }
        }
      }
      assert InodeValidLinkObservations(result);
      if id == fs.namespace.id {
        assert result.inodes[result.namespace.id].node.Directory?;
      }
    }
  }

  ghost method InodeFsUpdateNodeVerified(
    fs: InodeFileSystem,
    path: Path,
    node: FsNode
  ) returns (result: InodeFileSystem)
    ensures result == InodeFsUpdateNode(fs, path, node)
  {
    InodeFsUpdateNodeValid(fs, path, node);
    result := InodeFsUpdateNode(fs, path, node);
  }
}
