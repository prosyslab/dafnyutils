module BenchWorld {
  type Path = string
  type Bytes = RawBytes

  // Utility-visible file contents, stdin and stdout are binary. Paths and arguments retain text.
  type RawByte = value: char | (value as int) < 256 witness '\0'
  type RawBytes = seq<RawByte>

  // Request-bound logical stream results. Library adapters may perform several
  // native reads or writes, but successful prefixes and the terminal errno stay
  // observable to utility code.
  datatype TrustedStreamRequest =
    | StreamReadFile(preFs: FileSystem, path: Path)
    | StreamReadStdin(preStdin: Bytes)
    | StreamWriteStdout(preStdout: Bytes, requested: Bytes)
    | StreamWriteStderr(preStderr: Bytes, requested: Bytes)

  datatype TrustedStreamResult =
    | StreamReadFileResult(data: Bytes, err: int)
    | StreamReadStdinResult(data: Bytes, remaining: Bytes, err: int)
    | StreamWriteResult(committed: nat, postOutput: Bytes, err: int)
  datatype FileTimes = FileTimes(
    atimeSec: int,
    atimeNsec: int,
    mtimeSec: int,
    mtimeNsec: int,
    ctimeSec: int,
    ctimeNsec: int
  )

  datatype TimestampUpdate =
    | Current
    | Keep
    | Exact(sec: int, nsec: int)

  datatype TimeParseRequest =
    | TimestampParseRequest(text: string, referenceSec: int, referenceNsec: int)
    | DateParseRequest(text: string, referenceSec: int, referenceNsec: int)

  datatype ParsedTimeResult = ParsedTimeResult(ok: bool, sec: int, nsec: int)

  datatype AccessModificationTimes = AccessModificationTimes(
    atimeSec: int,
    atimeNsec: int,
    mtimeSec: int,
    mtimeNsec: int
  )

  datatype StdoutTimestampState =
    | StdoutTimestampAvailable(times: AccessModificationTimes)
    | StdoutTimestampUnavailable(err: int)

  datatype Ownership = Ownership(uid: nat, gid: nat)

  // High-level storage projection used by utilities such as du and stat.
  datatype StorageInfo = StorageInfo(
    size: nat,
    allocatedBlocks: nat,
    preferredIoBlockBytes: nat
  )

  datatype ProcessCredentials = ProcessCredentials(
    effectiveUid: nat,
    effectiveGid: nat
  )

  datatype SpecialNodeKind =
    | FifoNode
    | BlockDeviceNode
    | CharacterDeviceNode

  datatype SyncMode =
    | SyncDataOnly
    | SyncDataAndMetadata
    | SyncContainingFilesystem
    | SyncAllFilesystems

  datatype SyncTarget =
    | AllSyncTargets
    | PathSyncTarget(path: Path)

  datatype FsNode =
    | Regular(data: Bytes, mode: bv32, times: FileTimes, ext: map<string, string>)
    | Directory(mode: bv32, times: FileTimes, ext: map<string, string>)
    | Symlink(target: Path, mode: bv32, times: FileTimes, ext: map<string, string>)
    | Inaccessible(ext: map<string, string>)

  type FileSystem = InodeFileSystem

  // Request-bound observations supplied by the trusted filesystem boundary.
  // Every request contains its complete prestate and every result contains the
  // complete poststate, including read-only queries whose poststate is unchanged.
  datatype TrustedFilesystemRequest =
    | FilesystemQuery(preFs: FileSystem, path: Path, followSymlink: bool)
    | FilesystemCreate(preFs: FileSystem, path: Path, now: int)
    | FilesystemSetTimes(
        preFs: FileSystem,
        path: Path,
        followSymlink: bool,
        now: int,
        atime: TimestampUpdate,
        mtime: TimestampUpdate
      )
    | FilesystemCreateDirectory(
        preFs: FileSystem,
        path: Path,
        requestedMode: bv32,
        umask: bv32,
        now: int
      )
    | FilesystemRemoveDirectory(preFs: FileSystem, path: Path, now: int)
    | FilesystemCreateHardLink(
        preFs: FileSystem,
        source: Path,
        hardLinkTarget: Path,
        now: int
      )
    | FilesystemUnlink(preFs: FileSystem, path: Path, now: int)
    | FilesystemTruncate(preFs: FileSystem, path: Path, size: nat, now: int)
    | FilesystemCreateSpecialNode(
        preFs: FileSystem,
        path: Path,
        kind: SpecialNodeKind,
        requestedMode: bv32,
        major: nat,
        minor: nat,
        umask: bv32,
        now: int
      )
    | FilesystemSync(preFs: FileSystem, syncTarget: SyncTarget, mode: SyncMode)

  datatype TrustedFilesystemResult = TrustedFilesystemResult(
    ok: bool,
    err: int,
    postFs: FileSystem,
    atimeSec: int,
    atimeNsec: int,
    mtimeSec: int,
    mtimeNsec: int,
    isDir: bool,
    isSymlink: bool,
    device: int,
    inode: int,
    linkCount: int
  )

  datatype DirEntry =
    | DirEntry(name: string, isDir: bool, isSymlink: bool)

  datatype DirHandleState =
    | DirHandleState(path: Path, remaining: set<DirEntry>)

  const ALL_MODE_BITS: bv32 := 4095 as bv32
  const DEFAULT_FILE_MODE: bv32 := 420 as bv32
  const CREATE_FILE_MODE: bv32 := 438 as bv32
  const DEFAULT_SYMLINK_MODE: bv32 := 511 as bv32
  const DEFAULT_UMASK: bv32 := 18 as bv32
  const OWNER_EXECUTE_MODE_BIT: bv32 := 64 as bv32
  const SET_GROUP_ID_MODE_BIT: bv32 := 1024 as bv32
  const SYMLINK_MAX_DEPTH: nat := 40
  const BV32_MOD: int := 4294967296
  const DEFAULT_FILE_TIMES: FileTimes := FileTimes(0, 0, 0, 0, 0, 0)
  const DEFAULT_OWNERSHIP: Ownership := Ownership(0, 0)
  const DEFAULT_IO_BLOCK_BYTES: nat := 4096
  const STAT_BLOCK_BYTES: nat := 512
  function NodeMode(node: FsNode): bv32
  {
    match node
    case Regular(_, mode, _, _) => NormalizeMode(mode)
    case Directory(mode, _, _) => NormalizeMode(mode)
    case Symlink(_, mode, _, _) => NormalizeMode(mode)
    case Inaccessible(_) => 0 as bv32
  }

  function FixtureOwnerCanSearch(node: FsNode): bool
  {
    match node
    case Directory(mode, _, _) =>
      (NormalizeMode(mode) & OWNER_EXECUTE_MODE_BIT) != 0 as bv32
    case _ => false
  }

  function NodeTimes(node: FsNode): FileTimes
  {
    match node
    case Regular(_, _, times, _) => times
    case Directory(_, times, _) => times
    case Symlink(_, _, times, _) => times
    case Inaccessible(_) => DEFAULT_FILE_TIMES
  }

  function NormalizeMode(mode: bv32): bv32
  {
    mode & ALL_MODE_BITS
  }

  function WithNodeMode(node: FsNode, mode: bv32): FsNode
  {
    var next := NormalizeMode(mode);
    match node
    case Regular(data, _, times, ext) => Regular(data, next, times, ext)
    case Directory(_, times, ext) => Directory(next, times, ext)
    case Symlink(target, _, times, ext) => Symlink(target, next, times, ext)
    case Inaccessible(ext) => Inaccessible(ext)
  }

  function WithNodeTimes(node: FsNode, times: FileTimes): FsNode
  {
    match node
    case Regular(data, mode, _, ext) => Regular(data, mode, times, ext)
    case Directory(mode, _, ext) => Directory(mode, times, ext)
    case Symlink(target, mode, _, ext) => Symlink(target, mode, times, ext)
    case Inaccessible(ext) => Inaccessible(ext)
  }

  function WithNodeChangeTime(node: FsNode, sec: int, nsec: int): FsNode
  {
    var before := NodeTimes(node);
    WithNodeTimes(node, FileTimes(
                    before.atimeSec, before.atimeNsec,
                    before.mtimeSec, before.mtimeNsec,
                    sec, nsec
                  ))
  }

  function WithNodeModificationAndChangeTime(
    node: FsNode,
    sec: int,
    nsec: int
  ): FsNode
  {
    var before := NodeTimes(node);
    WithNodeTimes(node, FileTimes(
                    before.atimeSec, before.atimeNsec,
                    sec, nsec,
                    sec, nsec
                  ))
  }

  function ToRegularNode(node: FsNode, data: Bytes): FsNode
  {
    match node
    case Regular(_, mode, times, ext) => Regular(data, mode, times, ext)
    case Directory(mode, times, ext) => Regular(data, mode, times, ext)
    case Symlink(_, mode, times, ext) => Regular(data, mode, times, ext)
    case Inaccessible(ext) => Regular(data, 0 as bv32, DEFAULT_FILE_TIMES, ext)
  }

  function IsOctalDigit(c: char): bool
  {
    '0' <= c <= '7'
  }

  function CharToDigit(c: char): int
    requires '0' <= c <= '7'
  {
    (c as int) - ('0' as int)
  }

  function AllOctalDigits(text: string, i: nat): bool
    decreases |text| - i
  {
    if i >= |text| then
      true
    else if !IsOctalDigit(text[i]) then
      false
    else
      AllOctalDigits(text, i + 1)
  }

  function OctalValue(text: string, i: nat, acc: int): int
    requires i <= |text|
    requires AllOctalDigits(text, i)
    decreases |text| - i
  {
    if i >= |text| then
      acc
    else
      OctalValue(text, i + 1, acc * 8 + CharToDigit(text[i]))
  }

  function ToBv32(x: int): bv32
  {
    ((x % BV32_MOD + BV32_MOD) % BV32_MOD) as bv32
  }

  function ParsedUmaskFromProps(props: map<string, string>): bv32
  {
    if !("umask" in props) then
      DEFAULT_UMASK
    else
      var raw := props["umask"];
      var text :=
        if |raw| > 2 && raw[0] == '0' && (raw[1] == 'o' || raw[1] == 'O') then
          raw[2..]
        else
          raw;
      if |text| == 0 || !AllOctalDigits(text, 0) then
        DEFAULT_UMASK
      else
        NormalizeMode(ToBv32(OctalValue(text, 0, 0)))
  }

  predicate NodeShapeUnchangedExceptMode(before: FsNode, after: FsNode)
  {
    match (before, after)
    case (Regular(data, _, times, ext), Regular(data2, _, times2, ext2)) =>
      data == data2 &&
      times.atimeSec == times2.atimeSec &&
      times.atimeNsec == times2.atimeNsec &&
      times.mtimeSec == times2.mtimeSec &&
      times.mtimeNsec == times2.mtimeNsec &&
      ext == ext2
    case (Directory(_, times, ext), Directory(_, times2, ext2)) =>
      times.atimeSec == times2.atimeSec &&
      times.atimeNsec == times2.atimeNsec &&
      times.mtimeSec == times2.mtimeSec &&
      times.mtimeNsec == times2.mtimeNsec &&
      ext == ext2
    case (Symlink(target, _, times, ext), Symlink(target2, _, times2, ext2)) =>
      target == target2 &&
      times.atimeSec == times2.atimeSec &&
      times.atimeNsec == times2.atimeNsec &&
      times.mtimeSec == times2.mtimeSec &&
      times.mtimeNsec == times2.mtimeNsec &&
      ext == ext2
    case (Inaccessible(ext), Inaccessible(ext2)) =>
      ext == ext2
    case _ => false
  }

  ghost predicate FileSystemTopologyUnchangedExceptMode(
    before: FileSystem,
    after: FileSystem
  )
  {
    before.namespace == after.namespace &&
    before.inodes.Keys == after.inodes.Keys &&
    forall id | id in before.inodes.Keys ::
      before.inodes[id].hostKey == after.inodes[id].hostKey &&
      before.inodes[id].links == after.inodes[id].links &&
      before.inodes[id].ownership == after.inodes[id].ownership &&
      before.inodes[id].storage == after.inodes[id].storage &&
      NodeShapeUnchangedExceptMode(
        before.inodes[id].node,
        after.inodes[id].node
      )
  }

  predicate NodeShapeUnchangedExceptTimes(before: FsNode, after: FsNode)
  {
    match (before, after)
    case (Regular(data, mode, _, ext), Regular(data2, mode2, _, ext2)) =>
      data == data2 && mode == mode2 && ext == ext2
    case (Directory(mode, _, ext), Directory(mode2, _, ext2)) =>
      mode == mode2 && ext == ext2
    case (Symlink(target, mode, _, ext), Symlink(target2, mode2, _, ext2)) =>
      target == target2 && mode == mode2 && ext == ext2
    case (Inaccessible(ext), Inaccessible(ext2)) =>
      ext == ext2
    case _ => false
  }

  ghost predicate FileSystemTopologyUnchangedExceptTimes(
    before: FileSystem,
    after: FileSystem
  )
  {
    before.namespace == after.namespace &&
    before.inodes.Keys == after.inodes.Keys &&
    forall id | id in before.inodes.Keys ::
      before.inodes[id].hostKey == after.inodes[id].hostKey &&
      before.inodes[id].links == after.inodes[id].links &&
      before.inodes[id].ownership == after.inodes[id].ownership &&
      before.inodes[id].storage == after.inodes[id].storage &&
      NodeShapeUnchangedExceptTimes(
        before.inodes[id].node,
        after.inodes[id].node
      )
  }

  function IsAbsolutePath(path: string): bool
  {
    |path| > 0 && path[0] == '/'
  }

  function StripLeadingSlash(path: string): string
  {
    if IsAbsolutePath(path) then
      path[1..]
    else
      path
  }

  function SplitSegments(path: string, i: int, start: int): seq<string>
    requires 0 <= start <= i <= |path|
    decreases |path| - i
  {
    if i >= |path| then
      if start >= |path| then
        []
      else
        [path[start..i]]
    else if path[i] == '/' then
      var head := if i == start then [] else [path[start..i]];
      head + SplitSegments(path, i + 1, i + 1)
    else
      SplitSegments(path, i + 1, start)
  }

  function NormalizeSegments(segs: seq<string>, i: int, acc: seq<string>): seq<string>
    requires 0 <= i <= |segs|
    decreases |segs| - i
  {
    if i >= |segs| then
      acc
    else if segs[i] == "" || segs[i] == "." then
      NormalizeSegments(segs, i + 1, acc)
    else if segs[i] == ".." then
      if |acc| == 0 then
        NormalizeSegments(segs, i + 1, acc)
      else
        NormalizeSegments(segs, i + 1, acc[..|acc| - 1])
    else
      NormalizeSegments(segs, i + 1, acc + [segs[i]])
  }

  function JoinSegments(segs: seq<string>): string
  {
    if |segs| == 0 then
      ""
    else if |segs| == 1 then
      segs[0]
    else
      segs[0] + "/" + JoinSegments(segs[1..])
  }

  function NormalizePath(path: string): string
  {
    var abs := IsAbsolutePath(path);
    var segs := NormalizeSegments(SplitSegments(StripLeadingSlash(path), 0, 0), 0, []);
    var joined := JoinSegments(segs);
    if abs && joined != "" then
      "/" + joined
    else if abs then
      "/"
    else
      joined
  }

  function ParentSegments(path: string): seq<string>
  {
    var segs := NormalizeSegments(SplitSegments(StripLeadingSlash(path), 0, 0), 0, []);
    if |segs| == 0 then [] else segs[..|segs| - 1]
  }

  function PathSegments(path: string): seq<string>
  {
    NormalizeSegments(SplitSegments(StripLeadingSlash(path), 0, 0), 0, [])
  }

  function BuildPath(abs: bool, segs: seq<string>): string
  {
    var joined := JoinSegments(segs);
    if abs && joined != "" then
      "/" + joined
    else if abs then
      "/"
    else
      joined
  }

  function ParentPath(path: string): string
  {
    BuildPath(IsAbsolutePath(path), ParentSegments(path))
  }

  function LeafName(path: string): string
  {
    var segs := PathSegments(path);
    if |segs| == 0 then "" else segs[|segs| - 1]
  }

  function AppendPath(parent: string, child: string): string
  {
    if parent == "" then
      child
    else if parent == "/" then
      "/" + child
    else
      parent + "/" + child
  }

  function ResolveSymlinkTarget(basePath: string, target: string): string
  {
    if IsAbsolutePath(target) then
      NormalizePath(target)
    else
      var combined := ParentSegments(basePath) + SplitSegments(StripLeadingSlash(target), 0, 0);
      var joined := JoinSegments(NormalizeSegments(combined, 0, []));
      if IsAbsolutePath(basePath) && joined != "" then
        "/" + joined
      else if IsAbsolutePath(basePath) then
        "/"
      else
        joined
  }

  datatype IOError =
    | NoSuchFile
    | IsDirectory
    | NotDirectory
    | PermissionDenied
    | InvalidPath
    | Other(msg: string)

  datatype Result<T> = Ok(v: T) | Err(e: IOError)

  function FsNodeCanHaveChildren(node: FsNode): bool
  {
    match node
    case Directory(_, _, _) => true
    case _ => false
  }

  function FsLookupSegments(
    fs: FileSystem,
    segs: seq<string>
  ): Result<InodeTree>
  {
    InodeFsLookupTreeSegments(fs.inodes, fs.namespace, segs)
  }

  function FsLookupNode(fs: FileSystem, path: Path): Result<FsNode>
  {
    InodeFsLookupNode(fs, path)
  }

  predicate FsContainsPath(fs: FileSystem, path: Path)
  {
    InodeFsContainsPath(fs, path)
  }

  function FsNodeAt(fs: FileSystem, path: Path): FsNode
    requires FsContainsPath(fs, path)
  {
    InodeFsNodeAt(fs, path)
  }

  function FsIdAt(fs: FileSystem, path: Path): InodeId
    requires FsContainsPath(fs, path)
  {
    InodeFsLookupId(fs, path).v
  }

  function InodeLinkCountAt(
    fs: FileSystem,
    path: Path
  ): LinkCountObservation
    requires FsContainsPath(fs, path)
  {
    fs.inodes[FsIdAt(fs, path)].links
  }

  function FsCanSetSegments(fs: FileSystem, segs: seq<string>): bool
  {
    FsLookupSegments(fs, segs).Ok?
  }

  function FsSetPath(
    fs: FileSystem,
    path: Path,
    node: FsNode
  ): FileSystem
  {
    var candidate := InodeFsUpdateNode(fs, path, node);
    if ValidInodeFileSystemData(candidate) then candidate else fs
  }

  function FsRemovePath(fs: FileSystem, path: Path): FileSystem
  {
    var candidate := InodeFsRemovePath(fs, path);
    if ValidInodeFileSystemData(candidate) then candidate else fs
  }

  function SetNodeMode(fs: FileSystem, path: Path, mode: bv32): FileSystem
  {
    if FsContainsPath(fs, path) then
      FsSetPath(fs, path, WithNodeMode(FsNodeAt(fs, path), mode))
    else
      fs
  }

  function FsPathSegments(fs: FileSystem): set<seq<string>>
  {
    set id: InodeId, path: seq<string> |
      id in fs.inodes.Keys &&
      path in InodeNamespaceIdPaths(fs.namespace, id) ::
      path
  }

  datatype HostInodeKey = HostInodeKey(device: int, inode: int)

  datatype FileKind =
    RegularKind |
    DirectoryKind |
    SymlinkKind |
    BlockDeviceKind |
    CharacterDeviceKind |
    FifoKind |
    SocketKind

  datatype FileStatus = FileStatus(
    kind: FileKind,
    mode: bv32,
    ownership: Ownership,
    storage: StorageInfo,
    times: FileTimes,
    hostKey: HostInodeKey,
    linkCount: nat
  )

  const DEFAULT_FILE_STATUS: FileStatus := FileStatus(
                                             RegularKind,
                                             0 as bv32,
                                             DEFAULT_OWNERSHIP,
                                             StorageInfo(0, 0, DEFAULT_IO_BLOCK_BYTES),
                                             DEFAULT_FILE_TIMES,
                                             HostInodeKey(0, 0),
                                             0
                                           )

  function FileKindForNode(node: FsNode): FileKind
  {
    match node
    case Directory(_, _, _) => DirectoryKind
    case Symlink(_, _, _, _) => SymlinkKind
    case _ => RegularKind
  }

  function FileStatusForRecord(record: InodeRecord): FileStatus
  {
    FileStatus(
      record.kind,
      NodeMode(record.node),
      record.ownership,
      record.storage,
      NodeTimes(record.node),
      record.hostKey,
      match record.links
      case LinkCountKnown(count) => count
      case LinkCountUnknown => 0
    )
  }

  datatype InodeId = InodeId(token: nat)

  datatype LinkCountObservation =
    | LinkCountUnknown
    | LinkCountKnown(count: nat)

  datatype InodeRecord = InodeRecord(
    hostKey: HostInodeKey,
    node: FsNode,
    links: LinkCountObservation,
    ownership: Ownership,
    storage: StorageInfo,
    kind: FileKind
  )

  function Utf8ByteWidth(c: char): nat
  {
    var value := c as int;
    if value <= 127 then 1
    else if value <= 2047 then 2
    else if value <= 65535 then 3
    else 4
  }

  function Utf8ByteLength(text: string): nat
    decreases |text|
  {
    if |text| == 0 then 0
    else Utf8ByteWidth(text[0]) + Utf8ByteLength(text[1..])
  }

  function NodeStorageSize(node: FsNode): nat
  {
    match node
    case Regular(data, _, _, _) => |data|
    case Symlink(target, _, _, _) => Utf8ByteLength(target)
    case _ => 0
  }

  function DefaultStorageInfo(node: FsNode): StorageInfo
  {
    StorageInfo(NodeStorageSize(node), 0, DEFAULT_IO_BLOCK_BYTES)
  }

  predicate InodeStorageConsistent(record: InodeRecord)
  {
    0 < record.storage.preferredIoBlockBytes &&
    (record.node.Regular? || record.node.Symlink? ==>
       record.storage.size == NodeStorageSize(record.node))
  }

  predicate InodeKindConsistent(record: InodeRecord)
  {
    match record.node
    case Directory(_, _, _) => record.kind == DirectoryKind
    case Symlink(_, _, _, _) => record.kind == SymlinkKind
    case Regular(_, _, _, _) =>
      record.kind != DirectoryKind && record.kind != SymlinkKind
    case Inaccessible(_) =>
      record.kind != DirectoryKind && record.kind != SymlinkKind
  }

  function InodeRecordWithNode(
    record: InodeRecord,
    node: FsNode
  ): InodeRecord
  {
    InodeRecord(
      record.hostKey,
      node,
      record.links,
      record.ownership,
      if node.Regular? || node.Symlink? then
        StorageInfo(
          NodeStorageSize(node),
          record.storage.allocatedBlocks,
          record.storage.preferredIoBlockBytes
        )
      else
        record.storage,
      record.kind
    )
  }

  function InodeRecordWithNodeAndStorage(
    record: InodeRecord,
    node: FsNode,
    storage: StorageInfo
  ): InodeRecord
  {
    InodeRecord(
      record.hostKey,
      node,
      record.links,
      record.ownership,
      storage,
      record.kind
    )
  }

  function FreshInodeRecord(
    key: HostInodeKey,
    node: FsNode,
    ownership: Ownership,
    storage: StorageInfo
  ): InodeRecord
  {
    InodeRecord(
      key,
      node,
      InodeInitialLinks(node),
      ownership,
      storage,
      FileKindForNode(node)
    )
  }

  function InodeRecordWithStorage(
    record: InodeRecord,
    storage: StorageInfo
  ): InodeRecord
  {
    InodeRecord(
      record.hostKey,
      record.node,
      record.links,
      record.ownership,
      storage,
      record.kind
    )
  }

  function InodeRecordWithIncrementedLinks(
    record: InodeRecord
  ): InodeRecord
  {
    match record.links
    case LinkCountKnown(count) => InodeRecord(
      record.hostKey,
      record.node,
      LinkCountKnown(count + 1),
      record.ownership,
      record.storage,
      record.kind
    )
    case LinkCountUnknown => record
  }

  function InodeRecordWithDecrementedLinks(
    record: InodeRecord
  ): InodeRecord
  {
    match record.links
    case LinkCountKnown(count) =>
      if count <= 2 then record else InodeRecord(
        record.hostKey,
        record.node,
        LinkCountKnown(count - 1),
        record.ownership,
        record.storage,
        record.kind
      )
    case LinkCountUnknown => record
  }

  datatype InodeTree = InodeTreeNode(
    id: InodeId,
    children: map<string, InodeTree>
  )

  datatype InodeFileSystemData = InodeFileSystemData(
    namespace: InodeTree,
    inodes: map<InodeId, InodeRecord>
  )

  function InodeTreeId(tree: InodeTree): InodeId
  {
    tree.id
  }

  function InodeTreeChildren(tree: InodeTree): map<string, InodeTree>
  {
    tree.children
  }

  function InodeNamespaceIds(tree: InodeTree): set<InodeId>
    decreases tree
  {
    {tree.id} +
    set name: string, childId: InodeId |
      name in tree.children &&
      childId in InodeNamespaceIds(tree.children[name]) ::
      childId
  }

  function InodeNamespaceIdPaths(
    tree: InodeTree,
    id: InodeId
  ): set<seq<string>>
    decreases tree
  {
    (if tree.id == id then {[]} else {}) +
    set name: string, suffix: seq<string> |
      name in tree.children &&
      suffix in InodeNamespaceIdPaths(tree.children[name], id) ::
      [name] + suffix
  }

  function InodeNamespaceRefCount(tree: InodeTree, id: InodeId): nat
  {
    |InodeNamespaceIdPaths(tree, id)|
  }

  function InodeNamespacePaths(tree: InodeTree): set<Path>
    decreases tree
  {
    {""} +
    set name: string, suffix: Path |
      name in tree.children &&
      suffix in InodeNamespacePaths(tree.children[name]) ::
      (if suffix == "" then name else AppendPath(name, suffix))
  }

  predicate InodeChildNameValid(name: string)
  {
    name != "" && name != "." && name != ".." && '/' !in name
  }

  predicate InodeTreeWellFormed(
    tree: InodeTree,
    inodes: map<InodeId, InodeRecord>
  )
    decreases tree
  {
    tree.id in inodes &&
    (FsNodeCanHaveChildren(inodes[tree.id].node) || |tree.children| == 0) &&
    (forall name :: name in tree.children ==>
                      InodeChildNameValid(name) &&
                      InodeTreeWellFormed(tree.children[name], inodes))
  }

  predicate InodeNamespaceWellFormed(data: InodeFileSystemData)
  {
    InodeTreeWellFormed(data.namespace, data.inodes) &&
    data.inodes.Keys == InodeNamespaceIds(data.namespace) &&
    (forall id :: (id in data.inodes &&
                   FsNodeCanHaveChildren(data.inodes[id].node)) ==>
                    InodeNamespaceRefCount(data.namespace, id) == 1)
  }

  predicate InodeUniqueHostKeys(data: InodeFileSystemData)
  {
    forall left, right ::
      left in data.inodes && right in data.inodes &&
      data.inodes[left].hostKey == data.inodes[right].hostKey ==>
        left == right
  }

  predicate InodeValidLinkObservations(data: InodeFileSystemData)
  {
    forall id :: id in data.inodes ==>
                   var refs := InodeNamespaceRefCount(data.namespace, id);
                   data.inodes[id].links.LinkCountKnown? &&
                   0 < data.inodes[id].links.count &&
                   refs <= data.inodes[id].links.count
  }

  predicate ValidInodeFileSystemData(data: InodeFileSystemData)
  {
    data.namespace.id in data.inodes &&
    data.inodes[data.namespace.id].node.Directory? &&
    InodeNamespaceWellFormed(data) &&
    InodeUniqueHostKeys(data) &&
    (forall id :: id in data.inodes ==>
                    InodeStorageConsistent(data.inodes[id]) &&
                    InodeKindConsistent(data.inodes[id])) &&
    InodeValidLinkObservations(data)
  }

  function DefaultInodeFileSystemData(): InodeFileSystemData
  {
    var id := InodeId(0);
    InodeFileSystemData(
      InodeTreeNode(id, map[]),
      map[id := InodeRecord(
            HostInodeKey(0, 0),
            Directory(493 as bv32, DEFAULT_FILE_TIMES, map[]),
            LinkCountKnown(2),
            DEFAULT_OWNERSHIP,
            DefaultStorageInfo(
              Directory(493 as bv32, DEFAULT_FILE_TIMES, map[])
            ),
            DirectoryKind
          )]
    )
  }

  type InodeFileSystem =
    fs: InodeFileSystemData | ValidInodeFileSystemData(fs)
    witness DefaultInodeFileSystemData()

  function InodeFsLookupTreeSegments(
    inodes: map<InodeId, InodeRecord>,
    tree: InodeTree,
    segs: seq<string>
  ): Result<InodeTree>
    ensures InodeFsLookupTreeSegments(inodes, tree, segs).Ok? ==>
              InodeFsLookupTreeSegments(inodes, tree, segs).v.id in inodes
    decreases |segs|
  {
    if tree.id !in inodes then
      Err(NoSuchFile)
    else if |segs| == 0 then
      Ok(tree)
    else
      match inodes[tree.id].node
      case Directory(_, _, _) =>
        if segs[0] in tree.children then
          InodeFsLookupTreeSegments(
            inodes, tree.children[segs[0]], segs[1..]
          )
        else
          Err(NoSuchFile)
      case Inaccessible(_) => Err(PermissionDenied)
      case _ => Err(NotDirectory)
  }

  function InodeFsLookupId(
    fs: InodeFileSystemData,
    path: Path
  ): Result<InodeId>
    ensures InodeFsLookupId(fs, path).Ok? ==>
              InodeFsLookupId(fs, path).v in fs.inodes
  {
    match InodeFsLookupTreeSegments(fs.inodes, fs.namespace, PathSegments(path))
    case Ok(tree) => Ok(tree.id)
    case Err(e) => Err(e)
  }

  function InodeFsLookupNode(
    fs: InodeFileSystemData,
    path: Path
  ): Result<FsNode>
  {
    match InodeFsLookupId(fs, path)
    case Ok(id) => Ok(fs.inodes[id].node)
    case Err(e) => Err(e)
  }

  predicate InodeFsContainsPath(fs: InodeFileSystemData, path: Path)
  {
    InodeFsLookupId(fs, path).Ok?
  }

  function InodeFsNodeAt(fs: InodeFileSystemData, path: Path): FsNode
    requires InodeFsContainsPath(fs, path)
  {
    match InodeFsLookupNode(fs, path)
    case Ok(node) => node
    case Err(_) => Inaccessible(map[])
  }

  function InodeTreeSetSubtreeSegments(
    tree: InodeTree,
    segs: seq<string>,
    subtree: InodeTree
  ): InodeTree
    decreases |segs|
  {
    if |segs| == 0 then
      subtree
    else if segs[0] in tree.children then
      InodeTreeNode(
        tree.id,
        tree.children[segs[0] :=
        InodeTreeSetSubtreeSegments(
          tree.children[segs[0]], segs[1..], subtree
        )]
      )
    else if |segs| == 1 then
      InodeTreeNode(tree.id, tree.children[segs[0] := subtree])
    else
      tree
  }

  function InodeTreeRemoveSegments(
    tree: InodeTree,
    segs: seq<string>
  ): InodeTree
    decreases |segs|
  {
    if |segs| == 0 || segs[0] !in tree.children then
      tree
    else if |segs| == 1 then
      InodeTreeNode(tree.id, tree.children - {segs[0]})
    else
      InodeTreeNode(
        tree.id,
        tree.children[segs[0] :=
        InodeTreeRemoveSegments(tree.children[segs[0]], segs[1..])]
      )
  }

  function InodePrefixPaths(
    prefix: seq<string>,
    paths: set<seq<string>>
  ): set<seq<string>>
  {
    set suffix | suffix in paths :: prefix + suffix
  }

  function InodeInitialLinks(node: FsNode): LinkCountObservation
  {
    LinkCountKnown(1)
  }

  predicate InodeTreeCanInsert(
    inodes: map<InodeId, InodeRecord>,
    tree: InodeTree,
    segs: seq<string>
  )
    decreases |segs|
  {
    |segs| > 0 &&
    tree.id in inodes &&
    inodes[tree.id].node.Directory? &&
    if |segs| == 1 then
      InodeChildNameValid(segs[0]) && segs[0] !in tree.children
    else
      segs[0] in tree.children &&
      InodeTreeCanInsert(
        inodes, tree.children[segs[0]], segs[1..]
      )
  }

  predicate InodeSegmentsDisjoint(
    left: seq<string>,
    right: seq<string>
  )
  {
    |left| > 0 &&
    |right| > 0 &&
    !(|left| <= |right| && right[..|left|] == left) &&
    !(|right| <= |left| && left[..|right|] == right)
  }

  predicate InodeSameNodeKind(left: FsNode, right: FsNode)
  {
    (left.Regular? && right.Regular?) ||
    (left.Directory? && right.Directory?) ||
    (left.Symlink? && right.Symlink?) ||
    (left.Inaccessible? && right.Inaccessible?)
  }

  function InodeFsUpdateNode(
    fs: InodeFileSystemData,
    path: Path,
    node: FsNode
  ): InodeFileSystemData
  {
    if !InodeFsContainsPath(fs, path) then
      fs
    else if !InodeSameNodeKind(InodeFsNodeAt(fs, path), node) then
      fs
    else
      var id := InodeFsLookupId(fs, path).v;
      var priorRecord := fs.inodes[id];
      InodeFileSystemData(
        fs.namespace,
        fs.inodes[id := InodeRecordWithNode(priorRecord, node)]
      )
  }

  function InodeFsUpdateNodeAndStorage(
    fs: InodeFileSystemData,
    path: Path,
    node: FsNode,
    storage: StorageInfo
  ): InodeFileSystemData
  {
    if !InodeFsContainsPath(fs, path) then
      fs
    else if !InodeSameNodeKind(InodeFsNodeAt(fs, path), node) then
      fs
    else
      var id := InodeFsLookupId(fs, path).v;
      InodeFileSystemData(
        fs.namespace,
        fs.inodes[id := InodeRecordWithNodeAndStorage(
          fs.inodes[id], node, storage
        )]
      )
  }

  function InodeFsRefreshDirectoryStorage(
    fs: InodeFileSystemData,
    id: InodeId,
    storage: StorageInfo
  ): InodeFileSystemData
  {
    if id !in fs.inodes || !fs.inodes[id].node.Directory? then
      fs
    else
      InodeFileSystemData(
        fs.namespace,
        fs.inodes[id := InodeRecordWithStorage(
          fs.inodes[id], storage
        )]
      )
  }

  function InodeFsIncrementRecordLinks(
    fs: InodeFileSystemData,
    id: InodeId
  ): InodeFileSystemData
  {
    if id !in fs.inodes then
      fs
    else
      InodeFileSystemData(
        fs.namespace,
        fs.inodes[id := InodeRecordWithIncrementedLinks(fs.inodes[id])]
      )
  }

  function InodeFsDecrementRecordLinks(
    fs: InodeFileSystemData,
    id: InodeId
  ): InodeFileSystemData
  {
    if id !in fs.inodes then
      fs
    else
      InodeFileSystemData(
        fs.namespace,
        fs.inodes[id := InodeRecordWithDecrementedLinks(fs.inodes[id])]
      )
  }

  function InodeFsTouchPathModificationAndChangeTimestamp(
    fs: InodeFileSystemData,
    path: Path,
    sec: int,
    nsec: int
  ): InodeFileSystemData
  {
    if !InodeFsContainsPath(fs, path) then
      fs
    else
      InodeFsUpdateNode(
        fs,
        path,
        WithNodeModificationAndChangeTime(
          InodeFsNodeAt(fs, path), sec, nsec
        )
      )
  }

  function InodeFsTouchPathModificationAndChangeTime(
    fs: InodeFileSystemData,
    path: Path,
    now: int
  ): InodeFileSystemData
  {
    InodeFsTouchPathModificationAndChangeTimestamp(fs, path, now, 0)
  }

  function InodeFsTouchRecordChangeTime(
    fs: InodeFileSystemData,
    id: InodeId,
    now: int
  ): InodeFileSystemData
  {
    if id !in fs.inodes then
      fs
    else
      InodeFileSystemData(
        fs.namespace,
        fs.inodes[id := InodeRecordWithNode(
          fs.inodes[id],
          WithNodeChangeTime(fs.inodes[id].node, now, 0)
        )]
      )
  }

  function InodeFsTouchParentModificationAndChangeTimestamp(
    fs: InodeFileSystemData,
    path: Path,
    sec: int,
    nsec: int
  ): InodeFileSystemData
  {
    InodeFsTouchPathModificationAndChangeTimestamp(
      fs, ParentPath(path), sec, nsec
    )
  }

  function InodeFsTouchParentModificationAndChangeTime(
    fs: InodeFileSystemData,
    path: Path,
    now: int
  ): InodeFileSystemData
  {
    InodeFsTouchParentModificationAndChangeTimestamp(
      fs, path, now, 0
    )
  }

  predicate InodeCanCreateFresh(
    fs: InodeFileSystem,
    path: Path,
    id: InodeId,
    key: HostInodeKey,
    node: FsNode
  )
  {
    InodeTreeCanInsert(fs.inodes, fs.namespace, PathSegments(path))
  }

  function InodeFsInsertFreshData(
    fs: InodeFileSystem,
    path: Path,
    id: InodeId,
    key: HostInodeKey,
    node: FsNode,
    ownership: Ownership,
    storage: StorageInfo
  ): InodeFileSystemData
  {
    InodeFileSystemData(
      InodeTreeSetSubtreeSegments(
        fs.namespace,
        PathSegments(path),
        InodeTreeNode(id, map[])
      ),
      fs.inodes[id := FreshInodeRecord(
        key, node, ownership, storage
      )]
    )
  }

  function InodeRecordAfterUnlink(
    record: InodeRecord
  ): InodeRecord
  {
    match record.links
    case LinkCountKnown(count) =>
      if count == 0 then record
      else InodeRecord(
             record.hostKey,
             record.node,
             LinkCountKnown(count - 1),
             record.ownership,
             record.storage,
             record.kind
           )
    case LinkCountUnknown => record
  }

  predicate InodeTreeCanRemove(
    inodes: map<InodeId, InodeRecord>,
    tree: InodeTree,
    segs: seq<string>
  )
    decreases |segs|
  {
    |segs| > 0 &&
    InodeFsLookupTreeSegments(inodes, tree, segs).Ok? &&
    tree.id in inodes &&
    inodes[tree.id].node.Directory? &&
    segs[0] in tree.children &&
    if |segs| == 1 then
      |tree.children[segs[0]].children| == 0
    else
      InodeTreeCanRemove(
        inodes, tree.children[segs[0]], segs[1..]
      )
  }

  function InodeFsRemovePath(
    fs: InodeFileSystem,
    path: Path
  ): InodeFileSystemData
  {
    if !InodeTreeCanRemove(
         fs.inodes, fs.namespace, PathSegments(path)
       ) then
      fs
    else
      var lookup := InodeFsLookupTreeSegments(
                      fs.inodes, fs.namespace, PathSegments(path)
                    );
      var removedTree :=
        match lookup
        case Ok(tree) => tree
        case Err(_) => fs.namespace;
      var id := removedTree.id;
      var namespace :=
        InodeTreeRemoveSegments(fs.namespace, PathSegments(path));
      var inodes :=
        if InodeNamespaceRefCount(fs.namespace, id) == 1 then
          fs.inodes - {id}
        else
          fs.inodes[id := InodeRecordAfterUnlink(fs.inodes[id])];
      InodeFileSystemData(namespace, inodes)
  }

  predicate InodeSameObject(
    fs: InodeFileSystemData,
    left: Path,
    right: Path
  )
  {
    InodeFsContainsPath(fs, left) &&
    InodeFsContainsPath(fs, right) &&
    InodeFsLookupId(fs, left) == InodeFsLookupId(fs, right)
  }

  function InodeFsRename(
    fs: InodeFileSystem,
    source: Path,
    target: Path
  ): InodeFileSystemData
  {
    if InodeSameObject(fs, source, target) then
      fs
    else if |PathSegments(source)| == 0 ||
            |PathSegments(target)| == 0 ||
            !InodeFsContainsPath(fs, source) ||
            !InodeFsContainsPath(fs, ParentPath(target)) ||
            !InodeFsNodeAt(fs, ParentPath(target)).Directory?
    then
      fs
    else if |PathSegments(source)| < |PathSegments(target)| &&
            PathSegments(target)[..|PathSegments(source)|] ==
            PathSegments(source)
      then
        fs
      else if |PathSegments(target)| < |PathSegments(source)| &&
              PathSegments(source)[..|PathSegments(target)|] ==
              PathSegments(target)
        then
          fs
        else if InodeFsContainsPath(fs, target) &&
                |InodeFsLookupTreeSegments(
                  fs.inodes, fs.namespace, PathSegments(target)
                ).v.children| > 0
          then
            fs
          else if InodeFsContainsPath(fs, target) &&
                  (InodeFsNodeAt(fs, source).Directory? !=
                   InodeFsNodeAt(fs, target).Directory?)
            then
              fs
            else
              var sourceTree :=
                InodeFsLookupTreeSegments(
                  fs.inodes, fs.namespace, PathSegments(source)
                ).v;
              var withoutTarget :=
                if InodeFsContainsPath(fs, target) then
                  InodeFsRemovePath(fs, target)
                else
                  fs;
              if !InodeTreeCanInsert(
                   withoutTarget.inodes,
                   withoutTarget.namespace,
                   PathSegments(target)
                 ) then
                fs
              else if InodeFsLookupTreeSegments(
                        withoutTarget.inodes,
                        withoutTarget.namespace,
                        PathSegments(source)
                      ) != Ok(sourceTree) then
                fs
              else
                var movedNamespace :=
                  InodeTreeSetSubtreeSegments(
                    withoutTarget.namespace,
                    PathSegments(target),
                    sourceTree
                  );
                if InodeFsLookupTreeSegments(
                     withoutTarget.inodes,
                     movedNamespace,
                     PathSegments(source)
                   ) != Ok(sourceTree) then
                  fs
                else
                  var resultNamespace :=
                    InodeTreeRemoveSegments(
                      movedNamespace, PathSegments(source)
                    );
                  InodeFileSystemData(resultNamespace, withoutTarget.inodes)
  }
}
