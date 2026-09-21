include "World.dfy"

module SecurityModel {
  import opened BenchWorld

  // IDs used by filesystem checks can differ from effective process IDs.
  datatype FilesystemIdentity = FilesystemIdentity(fsuid: nat, fsgid: nat)

  // Permission checks use filesystem IDs, supplementary groups, and capabilities.
  // Access/default ACLs, additional LSM restrictions, and grpid mounts need separate models.
  datatype FilesystemSecurityContext = FilesystemSecurityContext(
    fsuid: nat,
    fsgid: nat,
    supplementaryGroups: set<nat>,
    dacOverride: bool,
    dacReadSearch: bool,
    fowner: bool,
    fsetid: bool
  )

  ghost predicate DirectoryAccessAllowed(
    record: InodeRecord, security: FilesystemSecurityContext, requested: bv32
  )
  {
    record.node.Directory? && requested <= (7 as bv32) &&
    (security.dacOverride ||
     (security.dacReadSearch && (requested & (2 as bv32)) == (0 as bv32)) ||
     (var mode := NodeMode(record.node);
      var permission :=
        if security.fsuid == record.ownership.uid then mode >> 6
        else if security.fsgid == record.ownership.gid ||
                record.ownership.gid in security.supplementaryGroups then mode >> 3
        else mode;
      (permission & requested) == requested))
  }

  ghost predicate StickyRemovalAllowed(
    parent: InodeRecord, target: InodeRecord, security: FilesystemSecurityContext
  )
  {
    (NodeMode(parent.node) & (512 as bv32)) == (0 as bv32) ||
    security.fsuid == parent.ownership.uid ||
    security.fsuid == target.ownership.uid || security.fowner
  }

  // Linux generic_permission for non-directories, without ACL/idmapped-mount
  // adjustments. Capabilities do not bypass an absent executable bit on files.
  ghost predicate FileAccessAllowed(
    record: InodeRecord, security: FilesystemSecurityContext, requested: bv32
  )
  {
    !record.node.Directory? && requested <= (7 as bv32) &&
    ((security.dacReadSearch && requested == (4 as bv32)) ||
     (security.dacOverride &&
      ((requested & (1 as bv32)) == (0 as bv32) ||
       (NodeMode(record.node) & (73 as bv32)) != (0 as bv32))) ||
     (var mode := NodeMode(record.node);
      var permission :=
        if security.fsuid == record.ownership.uid then mode >> 6
        else if security.fsgid == record.ownership.gid ||
                record.ownership.gid in security.supplementaryGroups then mode >> 3
        else mode;
      (permission & requested) == requested))
  }

  lemma FileReadSearchCapabilityDoesNotGrantWrite(record: InodeRecord)
    requires !record.node.Directory?
    requires NodeMode(record.node) == (0 as bv32)
    ensures FileAccessAllowed(record,
                              FilesystemSecurityContext(0, 0, {}, false, true, false, false), 4 as bv32)
    ensures !FileAccessAllowed(record,
                               FilesystemSecurityContext(0, 0, {}, false, true, false, false), 2 as bv32)
  {
  }

  lemma DacOverrideNeedsExecutableBit(record: InodeRecord)
    requires !record.node.Directory?
    requires (NodeMode(record.node) & (73 as bv32)) == (0 as bv32)
    ensures !FileAccessAllowed(record,
                               FilesystemSecurityContext(0, 0, {}, true, false, false, false), 1 as bv32)
  {
  }

  // Reuse the established path resolver's owner-search bit as a ghost view of
  // the actual process's search decision. This never changes the observed fs.
  ghost function DirectorySearchRecord(
    record: InodeRecord, security: FilesystemSecurityContext
  ): InodeRecord
  {
    if !record.node.Directory? then record else
    var mode := NodeMode(record.node);
    var viewedMode := if DirectoryAccessAllowed(record, security, 1 as bv32)
                      then mode | OWNER_EXECUTE_MODE_BIT
                      else mode & (ALL_MODE_BITS ^ OWNER_EXECUTE_MODE_BIT);
    InodeRecordWithNode(record, WithNodeMode(record.node, viewedMode))
  }

  ghost function DirectorySearchInodes(
    inodes: map<InodeId, InodeRecord>, security: FilesystemSecurityContext
  ): map<InodeId, InodeRecord>
  {
    map id | id in inodes :: DirectorySearchRecord(inodes[id], security)
  }

  lemma SearchRecordReflectsPermission(
    record: InodeRecord, security: FilesystemSecurityContext
  )
    requires record.node.Directory?
    ensures FixtureOwnerCanSearch(DirectorySearchRecord(record, security).node) ==
            DirectoryAccessAllowed(record, security, 1 as bv32)
  {
  }

  lemma SearchTreeWellFormed(
    tree: InodeTree, inodes: map<InodeId, InodeRecord>,
    security: FilesystemSecurityContext
  )
    requires InodeTreeWellFormed(tree, inodes)
    ensures InodeTreeWellFormed(tree, DirectorySearchInodes(inodes, security))
    decreases tree
  {
    forall name | name in tree.children
      ensures InodeTreeWellFormed(tree.children[name],
                                  DirectorySearchInodes(inodes, security))
    {
      SearchTreeWellFormed(tree.children[name], inodes, security);
    }
  }

  ghost function DirectorySearchData(
    fs: FileSystem, security: FilesystemSecurityContext
  ): InodeFileSystemData
  {
    InodeFileSystemData(fs.namespace, DirectorySearchInodes(fs.inodes, security))
  }

  lemma DirectorySearchDataValid(fs: FileSystem, security: FilesystemSecurityContext)
    ensures ValidInodeFileSystemData(DirectorySearchData(fs, security))
  {
    var viewed := DirectorySearchData(fs, security);
    SearchTreeWellFormed(fs.namespace, fs.inodes, security);
    assert viewed.inodes.Keys == fs.inodes.Keys;
    assert forall id | id in fs.inodes ::
        viewed.inodes[id].hostKey == fs.inodes[id].hostKey &&
        viewed.inodes[id].links == fs.inodes[id].links &&
        InodeSameNodeKind(viewed.inodes[id].node, fs.inodes[id].node);
  }

  ghost function DirectorySearchView(
    fs: FileSystem, security: FilesystemSecurityContext
  ): FileSystem
  {
    DirectorySearchDataValid(fs, security);
    DirectorySearchData(fs, security)
  }

  lemma SearchViewPreservesTopology(fs: FileSystem, security: FilesystemSecurityContext)
    ensures FileSystemTopologyUnchangedExceptMode(fs, DirectorySearchView(fs, security))
  {
  }

  lemma OwnerPermissionsTakePrecedence()
  {
    var record := InodeRecord(HostInodeKey(0, 1),
                              Directory(7 as bv32, DEFAULT_FILE_TIMES, map[]), LinkCountKnown(2),
                              Ownership(1000, 100), StorageInfo(4096, 8, 4096), DirectoryKind);
    var owner := FilesystemSecurityContext(1000, 100, {}, false, false, false, false);
    var other := FilesystemSecurityContext(2000, 200, {}, false, false, false, false);
    assert !DirectoryAccessAllowed(record, owner, 3 as bv32);
    assert DirectoryAccessAllowed(record, other, 3 as bv32);
  }

  lemma SupplementaryGroupGrantsDirectoryAccess()
  {
    var record := InodeRecord(HostInodeKey(0, 1),
                              Directory(56 as bv32, DEFAULT_FILE_TIMES, map[]), LinkCountKnown(2),
                              Ownership(1000, 100), StorageInfo(4096, 8, 4096), DirectoryKind);
    var member := FilesystemSecurityContext(2000, 200, {100}, false, false, false, false);
    var nonmember := FilesystemSecurityContext(2000, 200, {}, false, false, false, false);
    assert DirectoryAccessAllowed(record, member, 3 as bv32);
    assert !DirectoryAccessAllowed(record, nonmember, 3 as bv32);
  }

  lemma ReadSearchCapabilityDoesNotGrantWrite()
  {
    var record := InodeRecord(HostInodeKey(0, 1),
                              Directory(0 as bv32, DEFAULT_FILE_TIMES, map[]), LinkCountKnown(2),
                              Ownership(1000, 100), StorageInfo(4096, 8, 4096), DirectoryKind);
    var security := FilesystemSecurityContext(2000, 200, {}, false, true, false, false);
    assert DirectoryAccessAllowed(record, security, 1 as bv32);
    assert !DirectoryAccessAllowed(record, security, 3 as bv32);
  }

  lemma StickyDirectoryProtectsOtherOwners()
  {
    var parent := InodeRecord(HostInodeKey(0, 1),
                              Directory(1023 as bv32, DEFAULT_FILE_TIMES, map[]), LinkCountKnown(3),
                              Ownership(1000, 100), StorageInfo(4096, 8, 4096), DirectoryKind);
    var target := InodeRecord(HostInodeKey(0, 2),
                              Directory(511 as bv32, DEFAULT_FILE_TIMES, map[]), LinkCountKnown(2),
                              Ownership(2000, 200), StorageInfo(4096, 8, 4096), DirectoryKind);
    var other := FilesystemSecurityContext(3000, 300, {}, false, false, false, false);
    var owner := FilesystemSecurityContext(2000, 300, {}, false, false, false, false);
    var capable := FilesystemSecurityContext(3000, 300, {}, false, false, true, false);
    assert DirectoryAccessAllowed(parent, other, 3 as bv32);
    assert !StickyRemovalAllowed(parent, target, other);
    assert StickyRemovalAllowed(parent, target, owner);
    assert StickyRemovalAllowed(parent, target, capable);
  }

}
