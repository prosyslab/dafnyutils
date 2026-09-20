include "World.dfy"

// Structural lookup, path-set and inode-record facts.
module WorldLookupProof {
  import opened BenchWorld

  lemma InodeLookupTreePathWitness(
    inodes: map<InodeId, InodeRecord>,
    tree: InodeTree,
    segs: seq<string>,
    found: InodeTree
  )
    requires InodeFsLookupTreeSegments(inodes, tree, segs) == Ok(found)
    ensures segs in InodeNamespaceIdPaths(tree, found.id)
    decreases |segs|
  {
    if |segs| > 0 {
      InodeLookupTreePathWitness(
        inodes, tree.children[segs[0]], segs[1..], found
      );
      assert [segs[0]] + segs[1..] == segs;
      assert segs in InodeNamespaceIdPaths(tree, found.id);
    }
  }

  lemma {:isolate_assertions} InodePrefixPathsCardinality(
    prefix: seq<string>,
    paths: set<seq<string>>
  )
    ensures |InodePrefixPaths(prefix, paths)| == |paths|
    decreases |paths|
  {
    if paths != {} {
      var path :| path in paths;
      InodePrefixPathsCardinality(prefix, paths - {path});
      assert InodePrefixPaths(prefix, paths) ==
             InodePrefixPaths(prefix, paths - {path}) + {prefix + path};
      if prefix + path in InodePrefixPaths(prefix, paths - {path}) {
        var other :| other in paths - {path} &&
                     prefix + other == prefix + path;
        assert (prefix + other)[|prefix|..] == other;
        assert (prefix + path)[|prefix|..] == path;
        assert false;
      }
    }
  }

  lemma InodePrefixPathsCompose(
    first: seq<string>,
    second: seq<string>,
    paths: set<seq<string>>
  )
    ensures InodePrefixPaths(first + second, paths) ==
            InodePrefixPaths(first, InodePrefixPaths(second, paths))
  {
    forall path | path in InodePrefixPaths(first + second, paths)
      ensures path in InodePrefixPaths(
                        first, InodePrefixPaths(second, paths)
                      )
    {
      var suffix :| suffix in paths &&
                    path == (first + second) + suffix;
      assert second + suffix in InodePrefixPaths(second, paths);
      assert path == first + (second + suffix);
    }
    forall path | path in InodePrefixPaths(
                            first, InodePrefixPaths(second, paths)
                          )
      ensures path in InodePrefixPaths(first + second, paths)
    {
      var middle :|
        middle in InodePrefixPaths(second, paths) &&
        path == first + middle;
      var suffix :| suffix in paths &&
                    middle == second + suffix;
      assert path == (first + second) + suffix;
    }
  }

  lemma InodeTreeIdsInInodes(
    tree: InodeTree,
    inodes: map<InodeId, InodeRecord>
  )
    requires InodeTreeWellFormed(tree, inodes)
    ensures InodeNamespaceIds(tree) <= inodes.Keys
    decreases tree
  {
    forall name | name in tree.children
      ensures InodeNamespaceIds(tree.children[name]) <= inodes.Keys
    {
      InodeTreeIdsInInodes(tree.children[name], inodes);
    }
  }

  lemma InodeNamespaceIdPathHasId(
    tree: InodeTree,
    id: InodeId,
    path: seq<string>
  )
    requires path in InodeNamespaceIdPaths(tree, id)
    ensures id in InodeNamespaceIds(tree)
    decreases tree
  {
    if tree.id != id {
      var name, suffix :|
        name in tree.children &&
        suffix in InodeNamespaceIdPaths(tree.children[name], id) &&
        path == [name] + suffix;
      InodeNamespaceIdPathHasId(tree.children[name], id, suffix);
    }
  }

  lemma InodeNamespaceIdHasPath(tree: InodeTree, id: InodeId)
    requires id in InodeNamespaceIds(tree)
    ensures exists path :: path in InodeNamespaceIdPaths(tree, id)
    decreases tree
  {
    if tree.id == id {
      assert [] in InodeNamespaceIdPaths(tree, id);
    } else {
      var name :| name in tree.children &&
                  id in InodeNamespaceIds(tree.children[name]);
      InodeNamespaceIdHasPath(tree.children[name], id);
      var suffix :|
        suffix in InodeNamespaceIdPaths(tree.children[name], id);
      assert [name] + suffix in InodeNamespaceIdPaths(tree, id);
    }
  }

  lemma FiniteSetSingleton<T>(values: set<T>, value: T)
    requires value in values
    requires |values| == 1
    ensures values == {value}
  {
    assert values == {value} + (values - {value});
    assert |values| == |{value}| + |values - {value}|;
    assert |values - {value}| == 0;
    assert values - {value} == {};
  }

  lemma InodeLookupTreeWellFormed(
    inodes: map<InodeId, InodeRecord>,
    tree: InodeTree,
    segs: seq<string>,
    subtree: InodeTree
  )
    requires InodeTreeWellFormed(tree, inodes)
    requires InodeFsLookupTreeSegments(inodes, tree, segs) ==
             Ok(subtree)
    ensures InodeTreeWellFormed(subtree, inodes)
    decreases |segs|
  {
    if |segs| > 0 {
      InodeLookupTreeWellFormed(
        inodes, tree.children[segs[0]], segs[1..], subtree
      );
    }
  }

  lemma {:isolate_assertions} InodeLookupPrefixPathsSubset(
    inodes: map<InodeId, InodeRecord>,
    tree: InodeTree,
    segs: seq<string>,
    subtree: InodeTree,
    id: InodeId
  )
    requires InodeFsLookupTreeSegments(inodes, tree, segs) ==
             Ok(subtree)
    ensures InodePrefixPaths(
              segs, InodeNamespaceIdPaths(subtree, id)
            ) <= InodeNamespaceIdPaths(tree, id)
    decreases |segs|
  {
    if |segs| == 0 {
      assert tree.id in inodes;
      assert InodeFsLookupTreeSegments(inodes, tree, []) ==
             Ok(tree);
      assert tree == subtree;
      assert InodeNamespaceIdPaths(tree, id) ==
             InodeNamespaceIdPaths(subtree, id);
      forall path | path in InodePrefixPaths(
                              [], InodeNamespaceIdPaths(subtree, id)
                            )
        ensures path in InodeNamespaceIdPaths(tree, id)
      {
        var suffix :|
          suffix in InodeNamespaceIdPaths(subtree, id) &&
          path == [] + suffix;
        assert path == suffix;
        assert suffix in InodeNamespaceIdPaths(tree, id);
        assert path in InodeNamespaceIdPaths(tree, id);
      }
      forall path | path in InodeNamespaceIdPaths(tree, id)
        ensures path in InodePrefixPaths(
                          [], InodeNamespaceIdPaths(subtree, id)
                        )
      {
        assert path == [] + path;
      }
    } else {
      InodeLookupPrefixPathsSubset(
        inodes,
        tree.children[segs[0]],
        segs[1..],
        subtree,
        id
      );
      InodePrefixPathsCompose(
        [segs[0]],
        segs[1..],
        InodeNamespaceIdPaths(subtree, id)
      );
      forall path | path in InodePrefixPaths(
                              segs, InodeNamespaceIdPaths(subtree, id)
                            )
        ensures path in InodeNamespaceIdPaths(tree, id)
      {
        var suffix :|
          suffix in InodeNamespaceIdPaths(subtree, id) &&
          path == segs + suffix;
        assert segs[1..] + suffix in InodePrefixPaths(
                                       segs[1..], InodeNamespaceIdPaths(subtree, id)
                                     );
        assert segs[1..] + suffix in InodeNamespaceIdPaths(
                                       tree.children[segs[0]], id
                                     );
        assert path == [segs[0]] + (segs[1..] + suffix);
      }
    }
  }

  lemma {:isolate_assertions} InodeInsertPrefixPathsDisjoint(
    inodes: map<InodeId, InodeRecord>,
    tree: InodeTree,
    segs: seq<string>,
    paths: set<seq<string>>,
    id: InodeId
  )
    requires InodeTreeCanInsert(inodes, tree, segs)
    ensures InodeNamespaceIdPaths(tree, id) *
            InodePrefixPaths(segs, paths) == {}
    decreases |segs|
  {
    if |segs| == 1 {
      assert segs[0] !in tree.children;
      if InodeNamespaceIdPaths(tree, id) *
        InodePrefixPaths(segs, paths) != {}
      {
        var path :| path in InodeNamespaceIdPaths(tree, id) *
                            InodePrefixPaths(segs, paths);
        assert path != [];
        var name, suffix :|
          name in tree.children &&
          suffix in InodeNamespaceIdPaths(tree.children[name], id) &&
          path == [name] + suffix;
        var insertedSuffix :| insertedSuffix in paths &&
                              path == segs + insertedSuffix;
        assert path[0] == name;
        assert path[0] == segs[0];
        assert false;
      }
    } else {
      InodeInsertPrefixPathsDisjoint(
        inodes,
        tree.children[segs[0]],
        segs[1..],
        paths,
        id
      );
      InodePrefixPathsCompose([segs[0]], segs[1..], paths);
      if InodeNamespaceIdPaths(tree, id) *
        InodePrefixPaths(segs, paths) != {}
      {
        var path :| path in InodeNamespaceIdPaths(tree, id) *
                            InodePrefixPaths(segs, paths);
        assert path != [];
        var name, suffix :|
          name in tree.children &&
          suffix in InodeNamespaceIdPaths(tree.children[name], id) &&
          path == [name] + suffix;
        var insertedSuffix :| insertedSuffix in paths &&
                              path == segs + insertedSuffix;
        assert path[0] == name;
        assert path[0] == segs[0];
        assert name == segs[0];
        assert path[1..] == suffix;
        assert (segs + insertedSuffix)[1..] ==
               segs[1..] + insertedSuffix;
        assert suffix in InodePrefixPaths(segs[1..], paths);
        assert false;
      }
    }
  }

  lemma InodeDisjointPrefixPaths(
    left: seq<string>,
    right: seq<string>,
    leftPaths: set<seq<string>>,
    rightPaths: set<seq<string>>
  )
    requires InodeSegmentsDisjoint(left, right)
    ensures InodePrefixPaths(left, leftPaths) *
            InodePrefixPaths(right, rightPaths) == {}
  {
    if InodePrefixPaths(left, leftPaths) *
      InodePrefixPaths(right, rightPaths) != {}
    {
      var path :| path in InodePrefixPaths(left, leftPaths) *
                          InodePrefixPaths(right, rightPaths);
      var leftSuffix :| leftSuffix in leftPaths &&
                        path == left + leftSuffix;
      var rightSuffix :| rightSuffix in rightPaths &&
                         path == right + rightSuffix;
      if |left| <= |right| {
        assert path[..|left|] == left;
        assert path[..|left|] == right[..|left|];
      } else {
        assert path[..|right|] == right;
        assert path[..|right|] == left[..|right|];
      }
      assert false;
    }
  }

  lemma InodeSegmentsDisjointTails(
    left: seq<string>,
    right: seq<string>
  )
    requires InodeSegmentsDisjoint(left, right)
    requires left[0] == right[0]
    ensures InodeSegmentsDisjoint(left[1..], right[1..])
  {
    assert left == [left[0]] + left[1..];
    assert right == [right[0]] + right[1..];
    if |left| == 1 {
      assert right[..|left|] == left;
    }
    if |right| == 1 {
      assert left[..|right|] == right;
    }
    if |left[1..]| <= |right[1..]| &&
       right[1..][..|left[1..]|] == left[1..]
    {
      assert right[..|left|] == left;
    }
    if |right[1..]| <= |left[1..]| &&
       left[1..][..|right[1..]|] == right[1..]
    {
      assert left[..|right|] == right;
    }
  }

  lemma InodeTreeSetSubtreeLookupDisjoint(
    tree: InodeTree,
    inodes: map<InodeId, InodeRecord>,
    source: seq<string>,
    target: seq<string>,
    found: InodeTree,
    subtree: InodeTree
  )
    requires InodeFsLookupTreeSegments(
               inodes, tree, source
             ) == Ok(found)
    requires InodeTreeCanInsert(inodes, tree, target)
    requires InodeSegmentsDisjoint(source, target)
    ensures InodeFsLookupTreeSegments(
              inodes,
              InodeTreeSetSubtreeSegments(tree, target, subtree),
              source
            ) == Ok(found)
    decreases |source| + |target|
  {
    if source[0] == target[0] {
      InodeSegmentsDisjointTails(source, target);
      InodeTreeSetSubtreeLookupDisjoint(
        tree.children[source[0]],
        inodes,
        source[1..],
        target[1..],
        found,
        subtree
      );
    }
  }

  lemma InodeTreeRemoveLookupDisjoint(
    tree: InodeTree,
    inodes: map<InodeId, InodeRecord>,
    removed: seq<string>,
    retained: seq<string>,
    removedTree: InodeTree,
    retainedTree: InodeTree
  )
    requires InodeFsLookupTreeSegments(
               inodes, tree, removed
             ) == Ok(removedTree)
    requires InodeFsLookupTreeSegments(
               inodes, tree, retained
             ) == Ok(retainedTree)
    requires InodeSegmentsDisjoint(removed, retained)
    ensures InodeFsLookupTreeSegments(
              inodes,
              InodeTreeRemoveSegments(tree, removed),
              retained
            ) == Ok(retainedTree)
    decreases |removed| + |retained|
  {
    if removed[0] == retained[0] {
      InodeSegmentsDisjointTails(removed, retained);
      InodeTreeRemoveLookupDisjoint(
        tree.children[removed[0]],
        inodes,
        removed[1..],
        retained[1..],
        removedTree,
        retainedTree
      );
    }
  }

  lemma InodeNamespaceIdRefCount(
    tree: InodeTree,
    id: InodeId
  )
    ensures (id in InodeNamespaceIds(tree)) ==
            (InodeNamespaceRefCount(tree, id) > 0)
  {
    if id in InodeNamespaceIds(tree) {
      InodeNamespaceIdHasPath(tree, id);
      var path :| path in InodeNamespaceIdPaths(tree, id);
      assert InodeNamespaceRefCount(tree, id) > 0;
    } else if InodeNamespaceRefCount(tree, id) > 0 {
      assert InodeNamespaceIdPaths(tree, id) != {};
      var path :| path in InodeNamespaceIdPaths(tree, id);
      InodeNamespaceIdPathHasId(tree, id, path);
    }
  }

  lemma InodeLookupUnchangedByRecordUpdate(
    inodes: map<InodeId, InodeRecord>,
    tree: InodeTree,
    segs: seq<string>,
    id: InodeId,
    record: InodeRecord
  )
    requires id in inodes
    requires InodeSameNodeKind(inodes[id].node, record.node)
    ensures InodeFsLookupTreeSegments(
              inodes[id := record], tree, segs
            ) == InodeFsLookupTreeSegments(inodes, tree, segs)
    decreases |segs|
  {
    if tree.id in inodes && |segs| > 0 {
      if inodes[tree.id].node.Directory? &&
         segs[0] in tree.children
      {
        InodeLookupUnchangedByRecordUpdate(
          inodes, tree.children[segs[0]], segs[1..], id, record
        );
      }
    }
  }

  lemma InodeTreeWellFormedAfterNodeUpdate(
    tree: InodeTree,
    inodes: map<InodeId, InodeRecord>,
    id: InodeId,
    record: InodeRecord
  )
    requires InodeTreeWellFormed(tree, inodes)
    requires id in inodes
    requires InodeSameNodeKind(inodes[id].node, record.node)
    ensures InodeTreeWellFormed(tree, inodes[id := record])
    decreases tree
  {
    assert FsNodeCanHaveChildren(inodes[id].node) ==
           FsNodeCanHaveChildren(record.node);
    forall name | name in tree.children
      ensures InodeTreeWellFormed(
                tree.children[name], inodes[id := record]
              )
    {
      InodeTreeWellFormedAfterNodeUpdate(
        tree.children[name], inodes, id, record
      );
    }
  }
}
