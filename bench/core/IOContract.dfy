include "Errno.dfy"
include "World.dfy"

module IOContract {
  // Public primitive relations and model types retain their exact definitions.
  // Provided lemmas establish model validity and primitive contract feasibility;
  // utility compatibility proofs are candidate-owned.
  export
    provides Result, Errno, BenchWorld
    reveals ValidStreamObservation, StreamObservationsValid, StreamFailureWitness, ValidStreamObservations
    reveals TimeParseObservationsValid, ValidTimeParseObservations
    provides StreamObservationAdmitsRequest, TimeParseObservationAdmitsRequest
    reveals AtCwdPathFields, AtDirPathFields, AtDirHandleAppliesFields, DirectoryParentAnchorCurrentFields, DirectoryParentAnchorForRequestFields
    reveals ResolvePathAtDirForMetadataFields, GetFileStatusAtDirResultFields, GetFileStatusAtDirStructureContractFields, OpenDirAtDirFailureErrFields, SetModeAtDirCanSucceedFields
    reveals LookupAtDirFailureErrnosFields, SetFileModeAtDirTargetContractFields, OpenDirAtDirTargetContractFields, SetModeCanSucceedFields, MetadataFailureErrnosFields
    reveals NativeStatusFailureErrnosFields, NativeRequestHasInvalidAbiPath, NativeFailureErrnosFields, NativeRequestCanSucceedFields, ValidNativeFailureObservation
    reveals NativeFailureWitness, ValidNativeFailureObservations, ObservedNativeStatusResultFields, ObservedNativeStatusAtCwdResultFields, ObservedNativeFileStatusAtCwdContractFields
    reveals ObservedNativeStatusAtDirResultFields, ObservedNativeFileStatusAtDirContractFields, NativeFailureContractFields, GetCwdResultFields, GetUmaskResultFields
    reveals GetEnvContractFields, EnvironmentKey, ValidEnvironment, Environment, EnvEntriesRepresentEnv
    reveals GetEnvironmentContractFields, GetLoginNameContractFields, TrustedTimeParseResultFields, ParseTimestampContractFields, ParseDateContractFields
    reveals ResolvePathThroughSymlinkComponentsFields, HasTrailingSlash, ResolvePathThroughSymlinkComponentsWithVisitedFields, RawPathSegmentsFields, HasRawTerminalSpecialFields
    reveals IsNonRootRawEntryPathFields, ResolvePathThroughSymlinkExactWithVisitedFields, DirectNoFollowResultFields, TerminalNoFollowResultFields, ResolveRawSymlinkSegmentsFields
    reveals ResolvePathThroughSymlinkSegmentsWithVisitedFields, ResolvePathThroughSymlinkSegmentsWithTrailingFields, ResolvePathForMetadataFields, ModeledReadFileResultFields, BytesPrefix
    reveals FileReadResultFromOutcome, ResultErrno, ResultValue, ReadResultData, ReadResultStage
    reveals WriteResultCommitted, WriteResultStage, ParsedResultValue, IOErrorIsDirectory, IOErrorIsReadFailure
    reveals ReadFailureData, StreamReadResultFromOutcome, StreamWriteResultFromOutcome, ObservedReadStdinResultFields, ObservedReadStdinRemainingFields
    reveals ReadStdinChunkSpec, ObservedReadStdinChunkResultFields, ObservedReadStdinChunkRemainingFields
    reveals StdinReadChunkSize, ReadStdinPositiveChunkFields, ReadStdinPrefixFields, ReadStdinTerminalErrFields
    reveals ReadStdinPartitionFields, ReadStdinOutcomeFields
    provides ReadStdinPartitionPropertiesFields, ReadStdinPrefixAgreementFields, ReadStdinPartitionDeterministicFields, ReadStdinPrefixAppendFields, ReadStdinDerivedOutcomeFields
    reveals ObservedReadFileResultFields, TrustedReadFileContractFields, ObservedOpenReadFileResultFields, TrustedOpenReadFileContractFields, TrustedReadStdinWithOutcomeContractFields
    reveals TrustedWriteWithOutcomeFields, TrustedWriteStdoutWithOutcomeContractFields, TrustedWriteStderrWithOutcomeContractFields, ReadLinkResultFields, AfterReadStdinFields
    reveals ReadStdinAllFields, AfterAppendStdoutFields, AppendStdoutFields, AfterAppendStderrFields, AppendStderrFields
    reveals IOErrorErrno, MetadataFailureErrFields, OpenDirFailureErrFields, PathExistsContractFields, TrustedFilesystemQueryContractFields
    reveals TrustedPathExistsContractFields, TrustedCreateFileContractFields, TrustedFilesystemEffectContractFields, TrustedFilesystemSyncContractFields, GetFileModeContractFields
    reveals GetFileStatusResultFields, FileStatusObservationFields, ObservedFileStatusResultFields, ObservedFileStatusContractFields, ObservedNativeFileStatusContractFields
    reveals FileStatusStructureContractFields, GetFileStatusContractFields, IsDirectoryContractFields, IsDirectoryStrictContractFields, IsSymlinkContractFields
    reveals ResolvePathForCreateNoFollowTerminalFields, ResolvePathForCreateFields, CreateFileFailureErrFields, FreshInsertionAtTimestampFields, FreshInsertionFields
    reveals DirectoryStorageObservationFields, RefreshParentDirectoryStorageFields, CreationOwnershipFields, CreatedPathOwnershipFields, CreatedRegularModeFields
    reveals CreatedRegularRequestedModeFields, CreatedRegularOwnershipFields, CreateFileContractFields, CreateFileWithCredentialsContractFields, FsWithoutPath
    reveals DeleteFsWithMetadataFields, WriteFileFailureErrFields, CompletedWriteFileEffectFields, WriteOpenFailureErrnosFields, WriteFileOutcomeFields
    reveals WriteFileContractFields, WriteFileWithCredentialsContractFields, ExistingAppendEffectFields, CompletedAppendEffectFields, AppendFileContractFields
    reveals CreateSymlinkFailureErrFields, CreateSymlinkContractFields, CreateSymlinkWithCredentialsContractFields, DeletePathFailureErrFields, DeletePathContractFields
    reveals DeletePathWithChangeTimeContractFields, SetModeTargetOk, SetFileModeContractFields, SetFileModeWithChangeTimeContractFields, SetTimesTargetOk
    reveals ValidTimestampNanoseconds, TimestampUpdateMatchesFields, GetFileTimesContractFields, SetFileTimesContractFields, TrustedSetFileTimesContractFields
    reveals TimestampUpdateValidFields, StdoutTimestampUpdateFields, SetStdoutTimesContractFields, ValidLeafName, EntryForNode
    reveals InodeTreeChildNodeFields, DirectoryEntriesForTreeFields, DirectoryEntriesForPathFields, DirectoryEntriesIncludingDotsForPathFields, OpenDirOutcomeFields
    reveals OpenDirContractFields, ResolvePathIdentityContractFields, DirectoryEntryKindForFileKind, DirectoryEntryKindMatchesEntry, DirectoryEntryKindMatchesFilesystemFields
    reveals DirectoryDotEntryMatchesFilesystemFields, ReadDirContractFields, ReadDirInodeFields, GetOpenDirectoryStatusContractFields, CloseDirContractFields
    reveals HasPathPrefix, ResolvePathForRenameNoFollowTerminalFields, ResolvePathForRenameDestinationFields, HasNoDescendants, RenameKindCompatible
    reveals RenameFs, RenameDirectoryParentLinksFields, RefreshRenameParentStorageFields, RenameFsWithMetadataFields, RenameFailureErrnosFields
    reveals RenamePathContractFields, RenamePathWithChangeTimeContractFields, CLocaleErrnoTextResult, QuoteafPathResult, QuoteArgumentResult
    reveals ReadFileSpec, OpenReadFileSpec, ObservedReadLinkResultFields, ObservedReadLinkAtCwdResultFields, ReadLinkAtCwdSpec
    reveals ReadLinkSpec, ReadStdinAllSpec, ReadStdinSpec, AppendStdoutSpec, AppendStderrSpec
    reveals WriteStdoutSpec, WriteStderrSpec, GetCLocaleErrnoTextSpec, QuoteafPathSpec, QuoteArgumentSpec
    reveals GetEnvSpec, GetEnvironmentSpec, GetLoginNameSpec, NowSpec, ParseTimestampSpec
    reveals ParseDateSpec, PathExistsSpec, CreateFileSpec, WriteFileSpec, AppendFileSpec
    reveals CreateSymlinkSpec, DeletePathSpec, ResolveDirectoryCreationPathFields, DirectoryCreationEffectFields, TraversalRecordEffectFields
    reveals ParentDirectoryEffectFields, EntryRemovalEffectFields, HardLinkEffectFields, TruncatedContentsFields, TruncationEffectFields
    reveals NativeLookupFaultErrnos, NativeMutationFaultErrnos, LookupFailureErrnosFields, HardLinkFailureErrnosFields, EntryRemovalFailureErrnosFields
    reveals FilesystemRequestHasInvalidAbiPath, FilesystemFailureErrnosFields, FailedFilesystemEffectFields, FilesystemRequestCanSucceedFields, FilesystemQueryShapeFields
    reveals ValidFilesystemObservation, FilesystemFailureWitness, ValidFilesystemObservations, CreateDirectorySpec, RemoveDirectorySpec
    reveals CreateHardLinkSpec, UnlinkPathSpec, TruncateFileSpec, CreateSpecialNodeSpec, SyncSpec
    reveals SetFileTimesNowSpec, SetFileAccessTimeNowSpec, SetFileModificationTimeNowSpec, GetFileTimesSpec, SetFileTimesSpec
    reveals SetStdoutTimesNowSpec, SetStdoutAccessTimeNowSpec, SetStdoutModificationTimeNowSpec, SetStdoutTimesSpec, GetFileModeSpec
    reveals GetFileStatusAtDirSpec, SetFileModeAtDirSpec, OpenDirAtDirSpec, GetFileStatusAtCwdSpec, SetFileModeAtCwdSpec
    reveals OpenDirAtCwdSpec, CapabilityStatusObservationPathFields, ObservedOpenDirectoryCapabilityResultFields, GetOpenDirectoryCapabilityStatusSpec, GetFileStatusSpec
    reveals SetFileModeSpec, GetUmaskSpec, OpenDirSpec, ResolvePathIdentitySpec, ReadDirSpec
    reveals GetOpenDirectoryStatusSpec, CloseDirSpec, IsDirectorySpec, IsSymlinkSpec, RenamePathSpec
    reveals FilesystemObjectRecordsFields, LiveObjectRecordsFields, LiveRecordStatusFields, LiveDirectoryTopologyFields, DirectoryCapabilityNamesFields
    reveals DirectoryCapabilityAnchorCurrentFields, DirectoryCapabilityReadCurrentFields, DirectoryOperationCapabilitiesCurrentFields, LiveDirectoryCapabilitiesFields, DirectoryOperationErrnos
    reveals DirectoryRequestFields, DirectoryStatusSameStructure, DirectoryResponseFields, DirectoryOperationSpec, DirectoryPathResultFields
    reveals DirectoryStatusResultFields, DirectoryHandleResultFields, DirectoryDescriptorResultFields, DirectoryReadResultFields, DirectoryUnitResultFields
    reveals DirectoryModelFields, DirectoryStateFields, DefaultLiveDirectoryTopology, DefaultDirectoryResponse, DefaultDirectoryState
    reveals ValidDirectoryState, DirectoryResources, DirectoryResourcesFields, DirectoryResourcesFromLegacy, ValidDirectoryResources
    reveals DirectoryResourcesReplaceLegacy, DirectoryResourcesReplaceLive, DirectoryStateRequestFields, DirectoryNextPositionFields, DirectoryNextCapabilitiesFields
    reveals DirectoryNextStateFields, DirectoryResourcesNextStateFields, DirectoryStateAtSnapshotFields, SimpleSegments, NamedDirectoryEntriesFields
    reveals FreshPosition, Extends, AddNamedDirectoryFields, ExtendNamedDirectoryTopologyFields, ExtendTopologyDomainFields
    reveals ExtendDirectoryModelFields, DirectoryStateAtExpandedSnapshotFields, CanonicalExistingPathFields, ModeChangedRecordFields, ModeChangedRecordsFields
    reveals ModeChangedStatusFields, ModeChangedEntryFields, ModeChangedDirectoryFields, ModeChangedTopologyFields, ModeChangedFilesystemFields
    reveals CwdContextReadStepFields, DirectoryParentAnchorForContextRequestFields, UnknownDirectoryParentErrnoFields, ResolvePathAtDirContextForMetadataFields, GetFileStatusAtDirContextResultFields
    reveals CwdStatusObservationPathFields, AtDirContextStatusObservationPathFields, CwdLookupFailureErrnosFields, AtDirContextLookupFailureErrnosFields, CwdResolvedModeCanSucceedFields
    reveals CwdResolvedOpenFailureErrFields, GetFileStatusAtCwdStructureContractFields, GetFileStatusAtDirContextStructureContractFields, SetFileModeFromCwdTargetContractFields, CwdOpenedTopologyFields
    reveals CwdOpenedPositionFields, OpenDirFromCwdTargetContractFields, GetOpenDirectoryCapabilityResultFields, DirectoryRequestForContextFields, ContextOperationSpec
    reveals DirectoryResourcesContextViewFields, DirectoryResourcesAdvanceFields, DirectoryResourcesOpenedFields, DirectoryResourcesModeFields, CwdContextFields
    reveals CwdTargetFields, CwdTargetRecordFields, CwdTargetNamedPathFields, CwdNamedResultFields, ResolveLiveDirectorySegmentsFields
    reveals ResolvePathAtCwdForMetadataFields, GetFileStatusFromCwdContextResultFields, ReadLinkFromCwdContextResultFields
    provides BuiltSegmentsFields, CanonicalPathFields, CwdModeContextValidityFields, DirectoryStateAdmitsRequest
    provides DirectoryTransitionOwnershipFields, DirectoryTransitionStateFields, KernelLookupTreeWellFormed, LeafNameFields
    provides LookupPrefix, LookupSegmentsSimple, ModeChangedFilesystemValid, NamedDirectoryChildFields
    provides NamedDirectorySnapshotFields, NativeFailureDomainContainsError, RootDirectoryNamedEntryFields, RootDirectorySnapshotFields

  import Errno = Errnos
  import Result = Results
  import opened BenchWorld
  import LookupProof = KernelLookup
  import RenameProof = KernelRename

  function AtCwdPathFields(cwd: Path, path: Path): Path
  {
    if path == "" || IsAbsolutePath(path) then path else AppendPath(BuildPath(true, PathSegments(cwd)), path)
  }

  function AtDirPathFields(handles: map<int, DirHandleState>, handle: int, path: Path): Path
  {
    if path == "" || IsAbsolutePath(path) then path
    else if handle in handles then AppendPath(handles[handle].path, path)
    else ""
  }

  predicate AtDirHandleAppliesFields(handles: map<int, DirHandleState>, handle: int, path: Path)
  {
    IsAbsolutePath(path) || handle in handles
  }

  // An opening snapshot authenticates the logical directory represented by a
  // live handle. Metadata changes may preserve this anchor; namespace movement
  // is not inferred from a historical pathname.
  ghost predicate DirectoryParentAnchorCurrentFields(
    fs: FileSystem, handles: map<int, DirHandleState>, origins: map<int, FileSystem>, parent: int)
  {
    parent in handles && parent in origins &&
    var path := handles[parent].path;
    var opening := origins[parent];
    FsContainsPath(opening, path) && FsNodeAt(opening, path).Directory? &&
    FsContainsPath(fs, path) && FsNodeAt(fs, path).Directory? &&
    opening.inodes[FsIdAt(opening, path)].hostKey == fs.inodes[FsIdAt(fs, path)].hostKey
  }

  ghost predicate DirectoryParentAnchorForRequestFields(
    fs: FileSystem, handles: map<int, DirHandleState>, origins: map<int, FileSystem>,
    parent: int, path: Path)
  {
    path == "" || (0 as char) in path || IsAbsolutePath(path) || parent !in handles ||
    DirectoryParentAnchorCurrentFields(fs, handles, origins, parent)
  }

  ghost function ResolvePathAtDirForMetadataFields(
    fs: FileSystem, handles: map<int, DirHandleState>, parent: int, path: Path, follow: bool
  ): (result: IOResult<Path>)
    ensures result.Ok? ==> FsContainsPath(fs, result.v) && !FsNodeAt(fs, result.v).Inaccessible?
  {
    if (0 as char) in path then
      Result.Err(NativeFailure(Errno.EINVAL, CLocaleErrnoTextResult(Errno.EINVAL)))
    else if path == "" then Result.Err(NoSuchFile)
    else if IsAbsolutePath(path) then ResolvePathForMetadataFields(fs, path, follow)
    else if parent !in handles then
      Result.Err(NativeFailure(Errno.EINVAL, CLocaleErrnoTextResult(Errno.EINVAL)))
    else ResolveRawSymlinkSegmentsFields(
           fs, RawPathSegmentsFields(path), 0, handles[parent].path,
           {}, SYMLINK_MAX_DEPTH, follow, false, HasTrailingSlash(path))
  }

  ghost function GetFileStatusAtDirResultFields(
    fs: FileSystem, handles: map<int, DirHandleState>, parent: int, path: Path, follow: bool
  ): IOResult<FileStatus>
  {
    match ResolvePathAtDirForMetadataFields(fs, handles, parent, path, follow)
    case Err(error) => Result.Err(error)
    case Ok(target) =>
      var record := fs.inodes[FsIdAt(fs, target)];
      match record.node
      case Inaccessible(_) => Result.Err(PermissionDenied)
      case _ =>
        match record.links
        case LinkCountUnknown => Result.Err(Other("unknown link count"))
        case LinkCountKnown(_) => Result.Ok(FileStatusForRecord(record))
  }

  ghost predicate GetFileStatusAtDirStructureContractFields(
    fs: FileSystem, handles: map<int, DirHandleState>, parent: int, path: Path, follow: bool,
    ok: bool, status: FileStatus, err: int)
  {
    0 <= err && (ok <==> err == 0) &&
    (ok ==>
       match GetFileStatusAtDirResultFields(fs, handles, parent, path, follow)
       case Err(_) => false
       case Ok(expected) => status.(times := expected.times) == expected)
  }

  ghost function OpenDirAtDirFailureErrFields(
    fs: FileSystem, handles: map<int, DirHandleState>, parent: int, path: Path): int
  {
    match ResolvePathAtDirForMetadataFields(fs, handles, parent, path, true)
    case Err(error) => IOErrorErrno(error)
    case Ok(target) => if FsNodeAt(fs, target).Directory? then 0 else Errno.ENOTDIR
  }

  ghost predicate SetModeAtDirCanSucceedFields(
    fs: FileSystem, handles: map<int, DirHandleState>, parent: int, path: Path, follow: bool)
  {
    match ResolvePathAtDirForMetadataFields(fs, handles, parent, path, follow)
    case Err(_) => false
    case Ok(target) => follow || !FsNodeAt(fs, target).Symlink?
  }

  ghost function LookupAtDirFailureErrnosFields(
    fs: FileSystem, handles: map<int, DirHandleState>, parent: int, path: Path, follow: bool): set<int>
  {
    NativeLookupFaultErrnos +
    (match ResolvePathAtDirForMetadataFields(fs, handles, parent, path, follow)
     case Err(error) => {IOErrorErrno(error)}
     case Ok(_) => {})
  }

  ghost predicate SetFileModeAtDirTargetContractFields(
    fs: FileSystem, handles: map<int, DirHandleState>, now: int, after: FileSystem,
    parent: int, path: Path, follow: bool, mode: bv32, ok: bool, err: int)
  {
    FileSystemTopologyUnchangedExceptMode(fs, after) &&
    0 <= err && (ok <==> err == 0) &&
    (if !ok then after == fs else
     match ResolvePathAtDirForMetadataFields(fs, handles, parent, path, follow)
     case Err(_) => false
     case Ok(target) =>
       FsContainsPath(after, target) &&
       SetModeTargetOk(FsNodeAt(fs, target), FsNodeAt(after, target), mode,
                       !follow && FsNodeAt(fs, target).Symlink?) &&
       (if !follow && FsNodeAt(fs, target).Symlink? then after == fs
        else after == FsSetPath(fs, target,
                                WithNodeChangeTime(WithNodeMode(FsNodeAt(fs, target), mode), now, 0))))
  }

  ghost predicate OpenDirAtDirTargetContractFields(
    fs: FileSystem, handles: map<int, DirHandleState>, after: map<int, DirHandleState>,
    parent: int, path: Path, dots: bool, ok: bool, handle: int, err: int)
  {
    0 <= err && (ok <==> err == 0) &&
    (if !ok then after == handles else
     handle !in handles &&
     match ResolvePathAtDirForMetadataFields(fs, handles, parent, path, true)
     case Err(_) => false
     case Ok(target) =>
       FsNodeAt(fs, target).Directory? &&
       after == handles[handle :=
       if dots then DotDirHandleState(target, DirectoryEntriesIncludingDotsForPathFields(fs, target))
       else DirHandleState(target, DirectoryEntriesForPathFields(fs, target))])
  }

  ghost predicate SetModeCanSucceedFields(fs: FileSystem, path: Path, follow: bool)
  {
    match ResolvePathForMetadataFields(fs, path, follow)
    case Err(_) => false
    case Ok(target) => FsContainsPath(fs, target) && (follow || !FsNodeAt(fs, target).Symlink?)
  }

  ghost function MetadataFailureErrnosFields(fs: FileSystem, path: Path, follow: bool): set<int>
  {
    if (0 as char) in path then {Errno.EINVAL}
    else LookupFailureErrnosFields(fs, path, follow) + {Errno.EOVERFLOW}
  }

  ghost function NativeStatusFailureErrnosFields(fs: FileSystem, path: Path, follow: bool): set<int>
  {
    MetadataFailureErrnosFields(fs, path, follow) +
    (match GetFileStatusResultFields(fs, path, follow)
     case Ok(_) => {}
     case Err(error) => {IOErrorErrno(error)})
  }

  function NativeRequestHasInvalidAbiPath(request: NativeFailureRequest): bool
  {
    if request.CapabilityStatusRequest? || request.StdoutTimesRequest? || request.OpenDirectoryStatusRequest? || request.ReadDirectoryRequest? || request.CloseDirectoryRequest? then false
    else if request.RenameRequest? then (0 as char) in request.source || (0 as char) in request.target
    else if request.CreateSymlinkRequest? then (0 as char) in request.path || (0 as char) in request.target
    else (0 as char) in request.path
  }

  ghost function NativeFailureErrnosFields(request: NativeFailureRequest): set<int>
  {
    if NativeRequestHasInvalidAbiPath(request) then {Errno.EINVAL} else
    match request
    case StatusAtDirRequest(_, fs, context, handle, path, follow) =>
      AtDirContextLookupFailureErrnosFields(fs,context,handle,path,follow)
    case SetModeAtDirRequest(fs, _, context, handle, path, follow, _) =>
      if path == "" then {Errno.ENOENT}
      else if !IsAbsolutePath(path) && handle !in context.capabilities && handle !in context.legacyHandles then
        {UnknownDirectoryParentErrnoFields(handle)}
      else AtDirContextLookupFailureErrnosFields(fs,context,handle,path,follow) +
           NativeMutationFaultErrnos + {Errno.EOPNOTSUPP}
    case OpenDirectoryAtDirRequest(fs, context, handle, path, _) =>
      if path == "" then {Errno.ENOENT}
      else if !IsAbsolutePath(path) && handle !in context.capabilities && handle !in context.legacyHandles then
        {UnknownDirectoryParentErrnoFields(handle)}
      else AtDirContextLookupFailureErrnosFields(fs,context,handle,path,true) +
           {Errno.ENFILE,Errno.EMFILE} +
           (if CwdResolvedOpenFailureErrFields(fs,context,
                                               ResolvePathAtDirContextForMetadataFields(fs,context,handle,path,true)) == 0 then {}
            else {CwdResolvedOpenFailureErrFields(fs,context,
                                                  ResolvePathAtDirContextForMetadataFields(fs,context,handle,path,true))})
    case StatusAtCwdRequest(_, fs, context, path, follow) =>
      CwdLookupFailureErrnosFields(fs,context,path,follow)
    case ReadLinkAtCwdRequest(fs, context, path) =>
      if path == "" then {Errno.ENOENT}
      else CwdLookupFailureErrnosFields(fs,context,path,false) +
           (if ReadLinkFromCwdContextResultFields(fs,context,path).Ok? then {} else {Errno.EINVAL})
    case SetModeAtCwdRequest(fs, context, _, path, follow, _) =>
      if path == "" then {Errno.ENOENT}
      else CwdLookupFailureErrnosFields(fs,context,path,follow) + NativeMutationFaultErrnos + {Errno.EOPNOTSUPP}
    case OpenDirectoryAtCwdRequest(fs, context, path, _) =>
      if path == "" then {Errno.ENOENT}
      else CwdLookupFailureErrnosFields(fs,context,path,true) + {Errno.ENFILE,Errno.EMFILE} +
           (if CwdResolvedOpenFailureErrFields(fs,context,
                                               ResolvePathAtCwdForMetadataFields(fs,context,path,true)) == 0 then {}
            else {CwdResolvedOpenFailureErrFields(fs,context,
                                                  ResolvePathAtCwdForMetadataFields(fs,context,path,true))})
    case CapabilityStatusRequest(_, fs, context, handle) =>
      if handle !in context.capabilities then {Errno.EBADF}
      else NativeLookupFaultErrnos + {Errno.EBADF,Errno.EINTR,Errno.EOVERFLOW,Errno.ENOSYS} +
           (match GetOpenDirectoryCapabilityResultFields(fs,context,handle)
            case Err(error) => {IOErrorErrno(error)}
            case Ok(_) => {})
    case StatusRequest(_, fs, path, follow) => NativeStatusFailureErrnosFields(fs, path, follow)
    case MetadataQueryRequest(fs, path, follow, _) => MetadataFailureErrnosFields(fs, path, follow)
    case ReadLinkRequest(fs, path) =>
      MetadataFailureErrnosFields(fs, path, false) +
      (if ReadLinkResultFields(fs, path).Ok? then {} else {Errno.EINVAL})
    case ResolveIdentityRequest(fs, cwd, path) =>
      MetadataFailureErrnosFields(fs, if IsAbsolutePath(path) then path else AppendPath(BuildPath(true, PathSegments(cwd)), path), true)
    case CreateSymlinkRequest(fs, _, path, target) =>
      NativeLookupFaultErrnos + NativeMutationFaultErrnos +
      (if CreateSymlinkFailureErrFields(fs, path, target) == 0 then {}
       else {CreateSymlinkFailureErrFields(fs, path, target)})
    case DeletePathRequest(fs, path) => EntryRemovalFailureErrnosFields(fs, path, false)
    case SetModeRequest(fs, _, path, follow, _) =>
      MetadataFailureErrnosFields(fs, path, follow) + NativeMutationFaultErrnos + {Errno.EOPNOTSUPP}
    case RenameRequest(fs, _, source, target) => RenameFailureErrnosFields(fs, source, target)
    case StdoutTimesRequest(before, _, _, _) =>
      {Errno.EBADF, Errno.EINVAL, Errno.EPERM, Errno.EACCES, Errno.EIO, Errno.EROFS, Errno.ENOMEM, Errno.EOVERFLOW} +
      (if before.StdoutTimestampUnavailable? && before.err > 0 then {before.err} else {})
    case OpenDirectoryStatusRequest(_, fs, handles, handle) =>
      if handle in handles then NativeStatusFailureErrnosFields(fs, handles[handle].path, true) + {Errno.EBADF, Errno.EINTR, Errno.ENOSYS}
      else {Errno.EINVAL}
    case OpenDirectoryRequest(fs, _, path, _) =>
      NativeLookupFaultErrnos + {Errno.ENFILE, Errno.EMFILE} +
      (if OpenDirFailureErrFields(fs, path) == 0 then {} else {OpenDirFailureErrFields(fs, path)})
    case ReadDirectoryRequest(_, handles, handle) =>
      if handle in handles then {Errno.EIO, Errno.EBADF, Errno.EINTR, Errno.EOVERFLOW} else {Errno.EINVAL}
    case CloseDirectoryRequest(handles, handle) =>
      if handle in handles then {Errno.EBADF, Errno.EINTR, Errno.EIO} else {Errno.EINVAL}
  }

  ghost predicate NativeRequestCanSucceedFields(request: NativeFailureRequest)
  {
    !NativeRequestHasInvalidAbiPath(request) &&
    match request
    case StatusAtDirRequest(_, fs, context, handle, path, follow) =>
      GetFileStatusAtDirContextResultFields(fs,context,handle,path,follow).Ok?
    case SetModeAtDirRequest(fs, _, context, handle, path, follow, _) =>
      CwdResolvedModeCanSucceedFields(fs,context,
                                      ResolvePathAtDirContextForMetadataFields(fs,context,handle,path,follow))
    case OpenDirectoryAtDirRequest(fs, context, handle, path, _) =>
      CwdResolvedOpenFailureErrFields(fs,context,
                                      ResolvePathAtDirContextForMetadataFields(fs,context,handle,path,true)) == 0
    case StatusAtCwdRequest(_, fs, context, path, follow) =>
      GetFileStatusFromCwdContextResultFields(fs,context,path,follow).Ok?
    case ReadLinkAtCwdRequest(fs, context, path) => ReadLinkFromCwdContextResultFields(fs,context,path).Ok?
    case SetModeAtCwdRequest(fs, context, _, path, follow, _) =>
      CwdResolvedModeCanSucceedFields(fs,context,
                                      ResolvePathAtCwdForMetadataFields(fs,context,path,follow))
    case OpenDirectoryAtCwdRequest(fs, context, path, _) =>
      CwdResolvedOpenFailureErrFields(fs,context,
                                      ResolvePathAtCwdForMetadataFields(fs,context,path,true)) == 0
    case CapabilityStatusRequest(_, fs, context, handle) =>
      GetOpenDirectoryCapabilityResultFields(fs,context,handle).Ok?
    case StatusRequest(_, fs, path, follow) => GetFileStatusResultFields(fs, path, follow).Ok?
    case MetadataQueryRequest(fs, path, follow, _) => ResolvePathForMetadataFields(fs, path, follow).Ok?
    case ReadLinkRequest(fs, path) => ReadLinkResultFields(fs, path).Ok?
    case ResolveIdentityRequest(fs, cwd, path) =>
      path != "" && ResolvePathForMetadataFields(fs,
                                                 if IsAbsolutePath(path) then path else AppendPath(BuildPath(true, PathSegments(cwd)), path), true).Ok?
    case CreateSymlinkRequest(fs, _, path, target) =>
      !HasTrailingSlash(path) && !HasRawTerminalSpecialFields(path) && CreateSymlinkFailureErrFields(fs, path, target) == 0
    case DeletePathRequest(fs, path) => !HasTrailingSlash(path) && DeletePathFailureErrFields(fs, path) == 0
    case SetModeRequest(fs, _, path, follow, _) => SetModeCanSucceedFields(fs, path, follow)
    case RenameRequest(fs, _, source, target) =>
      source != "" && target != "" && IsNonRootRawEntryPathFields(source) && IsNonRootRawEntryPathFields(target) &&
      (match ResolvePathForRenameNoFollowTerminalFields(fs, source)
       case Err(_) => false
       case Ok(resolvedSource) =>
         match ResolvePathForRenameDestinationFields(fs, target)
         case Err(_) => false
         case Ok(resolvedTarget) =>
           InodeSameObject(fs, resolvedSource, resolvedTarget) ||
           (!HasPathPrefix(resolvedSource, resolvedTarget) && RenameKindCompatible(fs, resolvedSource, resolvedTarget)))
    case StdoutTimesRequest(before, _, atime, mtime) =>
      before.StdoutTimestampAvailable? && TimestampUpdateValidFields(atime) && TimestampUpdateValidFields(mtime)
    case OpenDirectoryStatusRequest(_, fs, handles, handle) =>
      handle in handles && GetFileStatusResultFields(fs, handles[handle].path, true).Ok?
    case OpenDirectoryRequest(fs, _, path, _) => OpenDirFailureErrFields(fs, path) == 0
    case ReadDirectoryRequest(_, handles, handle) => handle in handles
    case CloseDirectoryRequest(handles, handle) => handle in handles
  }

  ghost predicate ValidNativeFailureObservation(request: NativeFailureRequest, err: int)
  {
    0 <= err && (if err == 0 then NativeRequestCanSucceedFields(request) else err in NativeFailureErrnosFields(request))
  }

  lemma NativeFailureDomainContainsError(request: NativeFailureRequest)
    ensures Errno.EIO in NativeFailureErrnosFields(request) || Errno.EINVAL in NativeFailureErrnosFields(request) ||
            Errno.ENOENT in NativeFailureErrnosFields(request) || Errno.EBADF in NativeFailureErrnosFields(request)
  {
    hide *;
    reveal NativeFailureErrnosFields(), NativeRequestHasInvalidAbiPath(), MetadataFailureErrnosFields(), NativeStatusFailureErrnosFields();
    reveal LookupFailureErrnosFields(), EntryRemovalFailureErrnosFields(), RenameFailureErrnosFields();
    reveal NativeLookupFaultErrnos, NativeMutationFaultErrnos, LookupAtDirFailureErrnosFields();
    reveal CwdLookupFailureErrnosFields(), AtDirContextLookupFailureErrnosFields(), UnknownDirectoryParentErrnoFields();
    if !NativeRequestHasInvalidAbiPath(request) {
      match request
      case StatusAtDirRequest(_, _, _, _, _, _) =>
      case SetModeAtDirRequest(_, _, _, _, _, _, _) =>
      case OpenDirectoryAtDirRequest(_, _, _, _, _) =>
      case StatusAtCwdRequest(_, _, _, _, _) =>
      case ReadLinkAtCwdRequest(_, _, _) =>
      case SetModeAtCwdRequest(_, _, _, _, _, _) =>
      case OpenDirectoryAtCwdRequest(_, _, _, _) =>
      case CapabilityStatusRequest(_, _, _, _) =>
      case StatusRequest(_, _, _, _) =>
      case MetadataQueryRequest(_, _, _, _) =>
      case ReadLinkRequest(_, _) =>
      case ResolveIdentityRequest(_, _, _) =>
      case CreateSymlinkRequest(_, _, _, _) =>
      case DeletePathRequest(_, _) =>
      case SetModeRequest(_, _, _, _, _) =>
      case RenameRequest(_, _, _, _) =>
      case StdoutTimesRequest(_, _, _, _) =>
      case OpenDirectoryStatusRequest(_, _, _, _) =>
      case OpenDirectoryRequest(_, _, _, _) =>
      case ReadDirectoryRequest(_, _, _) =>
      case CloseDirectoryRequest(_, _) =>
    }
  }

  ghost function NativeFailureWitness(request: NativeFailureRequest): (err: int)
    ensures ValidNativeFailureObservation(request, err)
  {
    NativeFailureDomainContainsError(request);
    if Errno.EIO in NativeFailureErrnosFields(request) then Errno.EIO
    else if Errno.EINVAL in NativeFailureErrnosFields(request) then Errno.EINVAL
    else if Errno.ENOENT in NativeFailureErrnosFields(request) then Errno.ENOENT else Errno.EBADF
  }

  type ValidNativeFailureObservations = observations: ((NativeFailureRequest) -> int) |
      (forall request :: ValidNativeFailureObservation(request, observations(request)))
    ghost witness (request: NativeFailureRequest) => NativeFailureWitness(request)

  ghost function ObservedNativeStatusResultFields(
    observations: StatusTimeObservations, failures: (NativeFailureRequest) -> int,
    ordinal: nat, fs: FileSystem, path: Path, follow: bool
  ): IOResult<FileStatus>
  {
    var err := failures(StatusRequest(ordinal, fs, path, follow));
    if err != 0 then Result.Err(NativeFailure(err, CLocaleErrnoTextResult(err)))
    else
      match GetFileStatusResultFields(fs, path, follow)
      case Err(error) => Result.Err(error)
      case Ok(status) => Result.Ok(status.(times := observations(ordinal, fs, path, follow)))
  }

  ghost function ObservedNativeStatusAtCwdResultFields(
    observations: StatusTimeObservations, failures: (NativeFailureRequest) -> int,
    ordinal: nat, fs: FileSystem, context: CwdContext, path: Path, follow: bool
  ): IOResult<FileStatus>
  {
    var err := failures(StatusAtCwdRequest(ordinal,fs,context,path,follow));
    if err != 0 then Result.Err(NativeFailure(err,CLocaleErrnoTextResult(err)))
    else match GetFileStatusFromCwdContextResultFields(fs,context,path,follow)
         case Err(error) => Result.Err(error)
         case Ok(status) => Result.Ok(status.(times := observations(ordinal,fs,CwdStatusObservationPathFields(context,path),follow)))
  }

  ghost predicate ObservedNativeFileStatusAtCwdContractFields(
    observations: StatusTimeObservations, failures: (NativeFailureRequest) -> int,
    ordinal: nat, fs: FileSystem, context: CwdContext, path: Path, follow: bool,
    ok: bool, status: FileStatus, err: int)
  {
    NativeFailureContractFields(failures,StatusAtCwdRequest(ordinal,fs,context,path,follow),err) &&
    match ObservedNativeStatusAtCwdResultFields(observations,failures,ordinal,fs,context,path,follow)
    case Ok(expected) => ok && status == expected && err == 0
    case Err(error) => !ok && err == IOErrorErrno(error)
  }

  ghost function ObservedNativeStatusAtDirResultFields(
    observations: StatusTimeObservations, failures: (NativeFailureRequest) -> int,
    ordinal: nat, fs: FileSystem, context: CwdContext, parent: int, path: Path, follow: bool
  ): IOResult<FileStatus>
  {
    var err := failures(StatusAtDirRequest(ordinal,fs,context,parent,path,follow));
    if err != 0 then Result.Err(NativeFailure(err,CLocaleErrnoTextResult(err)))
    else match GetFileStatusAtDirContextResultFields(fs,context,parent,path,follow)
         case Err(error) => Result.Err(error)
         case Ok(status) => Result.Ok(status.(times := observations(ordinal,fs,AtDirContextStatusObservationPathFields(context,parent,path),follow)))
  }

  ghost predicate ObservedNativeFileStatusAtDirContractFields(
    observations: StatusTimeObservations, failures: (NativeFailureRequest) -> int,
    ordinal: nat, fs: FileSystem, context: CwdContext, parent: int, path: Path, follow: bool,
    ok: bool, status: FileStatus, err: int)
  {
    NativeFailureContractFields(failures,StatusAtDirRequest(ordinal,fs,context,parent,path,follow),err) &&
    match ObservedNativeStatusAtDirResultFields(observations,failures,ordinal,fs,context,parent,path,follow)
    case Ok(expected) => ok && status == expected && err == 0
    case Err(error) => !ok && err == IOErrorErrno(error)
  }

  ghost predicate NativeFailureContractFields(
    observations: (NativeFailureRequest) -> int, request: NativeFailureRequest, err: int
  )
  {
    ValidNativeFailureObservation(request, err) && err == observations(request)
  }

  function GetCwdResultFields(cwd: Path): Path { cwd }





  function GetUmaskResultFields(props: map<string, string>): bv32 { ParsedUmaskFromProps(props) }

  predicate GetEnvContractFields(env: map<string, string>, key: string, r: IOResult<string>)
  {
    if key in env then
      r == Result.Ok(env[key])
    else
      match r
      case Err(_) => true
      case Ok(_) => false
  }

  predicate EnvironmentKey(key: string)
  {
    |key| > 0 &&
    (forall i :: 0 <= i < |key| ==>
                   key[i] != '=' && key[i] != (0 as char))
  }

  predicate ValidEnvironment(env: map<string, string>)
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

  predicate GetLoginNameContractFields(props: map<string, string>, r: IOResult<string>)
  {
    if "loginName" in props then
      r == Result.Ok(props["loginName"])
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

  // A native successful parse always has normalized nanoseconds. Failed parses
  // retain all observed fields, and missing requests retain the default failure.
  ghost predicate TimeParseObservationsValid(parses: map<TimeParseRequest, ParsedTimeResult>)
  {
    forall request | request in parses ::
      parses[request].ok ==> 0 <= parses[request].nsec < 1000000000
  }

  type ValidTimeParseObservations = parses: map<TimeParseRequest, ParsedTimeResult> |
      TimeParseObservationsValid(parses)
    witness map[]

  lemma TimeParseObservationAdmitsRequest(parses: ValidTimeParseObservations, request: TimeParseRequest)
    ensures match request
            case TimestampParseRequest(text, sec, nsec) =>
              var result := TrustedTimeParseResultFields(parses, request);
              ParseTimestampSpec(parses, text, sec, nsec, result.ok, result.sec, result.nsec)
            case DateParseRequest(text, sec, nsec) =>
              var result := TrustedTimeParseResultFields(parses, request);
              ParseDateSpec(parses, text, sec, nsec, result.ok, result.sec, result.nsec)
  {
  }

  // Resolves a path component-by-component so symlinked directories are
  // traversed before the terminal symlink decision.
  ghost function ResolvePathThroughSymlinkComponentsFields(
    fs: FileSystem,
    path: Path,
    followTerminalSymlink: bool
  ): IOResult<Path>
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

  ghost function ResolvePathThroughSymlinkComponentsWithVisitedFields(
    fs: FileSystem,
    path: Path,
    seen: set<Path>,
    fuel: nat,
    followTerminalSymlink: bool
  ): IOResult<Path>
    decreases fuel
  {
    if fuel == 0 then
      Result.Err(InvalidPath)
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

  ghost function ResolvePathThroughSymlinkExactWithVisitedFields(
    fs: FileSystem,
    path: Path,
    seen: set<Path>,
    fuel: nat,
    followTerminalSymlink: bool
  ): IOResult<Path>
    decreases fuel
  {
    if fuel == 0 then
      Result.Err(InvalidPath)
    else if path in seen then
      Result.Err(InvalidPath)
    else if !FsContainsPath(fs, path) then
      Result.Err(NoSuchFile)
    else
      match FsNodeAt(fs, path)
      case Regular(_, _, _, _) => Result.Ok(path)
      case Directory(_, _, _) => Result.Ok(path)
      case Inaccessible(_) => Result.Err(PermissionDenied)
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
          Result.Ok(path)
  }

  ghost function DirectNoFollowResultFields(
    fs: FileSystem,
    path: Path
  ): IOResult<Path>
  {
    if path == "" then
      Result.Err(NoSuchFile)
    else
      match FsLookupNode(fs, path)
      case Err(error) => Result.Err(error)
      case Ok(node) =>
        match node
        case Inaccessible(_) => Result.Err(PermissionDenied)
        case _ => Result.Ok(path)
  }

  ghost function TerminalNoFollowResultFields(
    fs: FileSystem,
    path: Path
  ): IOResult<Path>
  {
    if path != "" then
      DirectNoFollowResultFields(fs, path)
    else
      match FsLookupNode(fs, path)
      case Err(error) => Result.Err(error)
      case Ok(node) =>
        match node
        case Inaccessible(_) => Result.Err(PermissionDenied)
        case _ => Result.Ok(path)
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

  ghost function ResolveRawSymlinkSegmentsFields(
    fs: FileSystem,
    segs: seq<string>,
    i: nat,
    current: Path,
    seen: set<Path>,
    fuel: nat,
    followTerminalSymlink: bool,
    allowMissingTerminal: bool,
    requireDirectory: bool
  ): (result: IOResult<Path>)
    requires i <= |segs|
    ensures !allowMissingTerminal && result.Ok? ==>
              FsContainsPath(fs, result.v) && !FsNodeAt(fs, result.v).Inaccessible?
    decreases fuel, |segs| - i
  {
    if i == |segs| then
      match TerminalNoFollowResultFields(fs, current)
      case Err(error) => Result.Err(error)
      case Ok(_) =>
        match FsNodeAt(fs, current)
        case Regular(_, _, _, _) =>
          if requireDirectory then Result.Err(NotDirectory) else Result.Ok(current)
        case Directory(_, _, _) => Result.Ok(current)
        case Inaccessible(_) => Result.Err(PermissionDenied)
        case Symlink(target, _, _, _) =>
          if !followTerminalSymlink && !requireDirectory then
            Result.Ok(current)
          else if target == "" then
            Result.Err(NoSuchFile)
          else if fuel == 0 then
            Result.Err(InvalidPath)
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
      Result.Err(PermissionDenied)
    else if segs[i] == "." || segs[i] == ".." then
      match TerminalNoFollowResultFields(fs, current)
      case Err(error) => Result.Err(error)
      case Ok(_) =>
        match FsNodeAt(fs, current)
        case Regular(_, _, _, _) => Result.Err(NotDirectory)
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
        case Inaccessible(_) => Result.Err(PermissionDenied)
        case Symlink(target, _, _, _) =>
          if target == "" then
            Result.Err(NoSuchFile)
          else if fuel == 0 then
            Result.Err(InvalidPath)
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
          Result.Ok(next)
        else
          Result.Err(NoSuchFile)
      case Err(error) => Result.Err(error)
      case Ok(_) =>
        match FsNodeAt(fs, next)
        case Regular(_, _, _, _) =>
          if i + 1 == |segs| && !requireDirectory then
            Result.Ok(next)
          else
            Result.Err(NotDirectory)
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
        case Inaccessible(_) => Result.Err(PermissionDenied)
        case Symlink(target, _, _, _) =>
          if i + 1 == |segs| &&
             !followTerminalSymlink && !requireDirectory then
            Result.Ok(next)
          else if target == "" then
            Result.Err(NoSuchFile)
          else if fuel == 0 then
            Result.Err(InvalidPath)
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

  // Expose one successful symlink step in a single filesystem before comparing
  // two filesystems. This keeps recursive-call obligations local.
  lemma ResolveRawNextSymlinkStepFields(
    fs: FileSystem, segs: seq<string>, i: nat, current: Path,
    seen: set<Path>, fuel: nat, followTerminalSymlink: bool,
    requireDirectory: bool, link: Path, target: Path
  )
    requires i < |segs|
    requires segs[i] != "." && segs[i] != ".."
    requires fuel > 0 && link != ""
    requires FsContainsPath(fs, AppendPath(current, segs[i]))
    requires FsNodeAt(fs, AppendPath(current, segs[i])).Symlink?
    requires FsNodeAt(fs, AppendPath(current, segs[i])).target == link
    requires DirectNoFollowResultFields(fs, AppendPath(current, segs[i])).Ok?
    requires i + 1 < |segs| || followTerminalSymlink || requireDirectory
    requires ResolveRawSymlinkSegmentsFields(
               fs, segs, i, current, seen, fuel, followTerminalSymlink, false,
               requireDirectory) == Result.Ok(target)
    ensures ResolveRawSymlinkSegmentsFields(
              fs, RawPathSegmentsFields(link) + segs[i + 1..], 0,
              if IsAbsolutePath(link) then "/" else ParentPath(AppendPath(current, segs[i])),
              seen + {AppendPath(current, segs[i])}, fuel - 1, followTerminalSymlink, false,
              requireDirectory || (i + 1 == |segs| && HasTrailingSlash(link))) == Result.Ok(target)
  {
    reveal ResolveRawSymlinkSegmentsFields();
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
             ) == Result.Ok(beforeTarget)
    requires ResolveRawSymlinkSegmentsFields(
               after, segs, i, current, seen, fuel,
               followTerminalSymlink, false, requireDirectory
             ) == Result.Ok(afterTarget)
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
          ResolveRawNextSymlinkStepFields(
            before, segs, i, current, seen, fuel,
            followTerminalSymlink, requireDirectory, beforeLink, beforeTarget);
          ResolveRawNextSymlinkStepFields(
            after, segs, i, current, seen, fuel,
            followTerminalSymlink, requireDirectory, beforeLink, afterTarget);
          var restarted := RawPathSegmentsFields(beforeLink) + remaining;
          var restartCurrent := if IsAbsolutePath(beforeLink) then "/" else ParentPath(next);
          var restartDirectory := requireDirectory ||
                                  (|remaining| == 0 && HasTrailingSlash(beforeLink));
          assert (|remaining| == 0) == (i + 1 == |segs|);
          hide *;
          assert ResolveRawSymlinkSegmentsFields(
              before, restarted, 0, restartCurrent, seen + {next}, fuel - 1,
              followTerminalSymlink, false, restartDirectory) == Result.Ok(beforeTarget);
          assert ResolveRawSymlinkSegmentsFields(
              after, restarted, 0, restartCurrent, seen + {next}, fuel - 1,
              followTerminalSymlink, false, restartDirectory) == Result.Ok(afterTarget);
          ResolveRawSuccessfulTargetsEqualExceptModeFieldsInternal(
            before,
            after,
            restarted,
            0,
            restartCurrent,
            seen + {next},
            fuel - 1,
            followTerminalSymlink,
            restartDirectory,
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

  ghost function ResolvePathThroughSymlinkSegmentsWithVisitedFields(
    fs: FileSystem,
    segs: seq<string>,
    i: nat,
    current: Path,
    seen: set<Path>,
    fuel: nat,
    followTerminalSymlink: bool
  ): IOResult<Path>
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

  ghost function ResolvePathThroughSymlinkSegmentsWithTrailingFields(
    fs: FileSystem,
    segs: seq<string>,
    i: nat,
    current: Path,
    seen: set<Path>,
    fuel: nat,
    followTerminalSymlink: bool,
    requireDirectory: bool
  ): IOResult<Path>
    requires 0 <= i <= |segs|
    decreases fuel, |segs| - i
  {
    if fuel == 0 then
      Result.Err(InvalidPath)
    else if i >= |segs| then
      if current in seen then
        Result.Err(InvalidPath)
      else if current == "" then
        Result.Err(NoSuchFile)
      else
        match DirectNoFollowResultFields(fs, current)
        case Err(error) => Result.Err(error)
        case Ok(_) =>
          match FsNodeAt(fs, current)
          case Regular(_, _, _, _) =>
            if requireDirectory then Result.Err(NotDirectory) else Result.Ok(current)
          case Directory(_, _, _) => Result.Ok(current)
          case Inaccessible(_) => Result.Err(PermissionDenied)
          case Symlink(target, _, _, _) =>
            if !followTerminalSymlink && !requireDirectory then
              Result.Ok(current)
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
        Result.Err(InvalidPath)
      else
        match DirectNoFollowResultFields(fs, next)
        case Err(error) => Result.Err(error)
        case Ok(_) =>
          match FsNodeAt(fs, next)
          case Regular(_, _, _, _) =>
            if i + 1 == |segs| && !requireDirectory then
              Result.Ok(next)
            else
              Result.Err(NotDirectory)
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
          case Inaccessible(_) => Result.Err(PermissionDenied)
          case Symlink(target, _, _, _) =>
            if i + 1 == |segs| && !followTerminalSymlink && !requireDirectory then
              Result.Ok(next)
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

  ghost function ResolvePathForMetadataFields(fs: FileSystem, path: Path, followSymlink: bool): (result: IOResult<Path>)
    ensures result.Ok? ==>
              FsContainsPath(fs, result.v) && !FsNodeAt(fs, result.v).Inaccessible?
  {
    if path == "" then
      Result.Err(NoSuchFile)
    else
      var result := ResolvePathThroughSymlinkComponentsFields(fs, path, followSymlink);
      if path[|path| - 1] != '/' then
        result
      else
        match result
        case Err(e) => Result.Err(e)
        case Ok(resolved) =>
          if !FsContainsPath(fs, resolved) then
            Result.Err(NoSuchFile)
          else
            match FsNodeAt(fs, resolved)
            case Directory(_, _, _) => Result.Ok(resolved)
            case Regular(_, _, _, _) | Symlink(_, _, _, _) => Result.Err(NotDirectory)
            case Inaccessible(_) => Result.Err(PermissionDenied)
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
             Result.Ok(beforeTarget)
    requires ResolvePathForMetadataFields(after, path, follow) ==
             Result.Ok(afterTarget)
    ensures beforeTarget == afterTarget
  {
    assert path != "";
    assert ResolvePathThroughSymlinkComponentsFields(
        before, path, follow
      ) == Result.Ok(beforeTarget) by {
      reveal ResolvePathForMetadataFields();
    }
    assert ResolvePathThroughSymlinkComponentsFields(
        after, path, follow
      ) == Result.Ok(afterTarget) by {
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
      ) == Result.Ok(beforeTarget) by {
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
      ) == Result.Ok(afterTarget) by {
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

  ghost function ModeledReadFileResultFields(fs: FileSystem, path: Path): IOResult<Bytes>
  {
    match ResolvePathThroughSymlinkComponentsFields(fs, path, true)
    case Ok(resolved) =>
      if FsContainsPath(fs, resolved) then
        match FsNodeAt(fs, resolved)
        case Regular(data, _, _, _) => Result.Ok(data)
        case Directory(_, _, _) => Result.Err(IsDirectory)
        case Symlink(_, _, _, _) => Result.Err(InvalidPath)
        case Inaccessible(_) => Result.Err(PermissionDenied)
      else
        Result.Err(NoSuchFile)
    case Err(e) => Result.Err(e)
  }

  predicate BytesPrefix(prefix: Bytes, whole: Bytes)
  {
    |prefix| <= |whole| && prefix == whole[..|prefix|]
  }

  function FileReadResultFromOutcome(
    data: Bytes, err: int, stage: FileReadStage, message: string
  ): IOResult<Bytes>
  {
    if err == 0 then Result.Ok(data)
    else Result.Err(ReadFailure(err, message, data, stage))
  }

  function ResultErrno<T>(result: IOResult<T>): int
  {
    match result
    case Ok(_) => 0
    case Err(error) => IOErrorErrno(error)
  }

  function ResultValue<T>(result: IOResult<T>, fallback: T): T
  {
    match result
    case Ok(value) => value
    case Err(_) => fallback
  }

  function ReadResultData(result: IOResult<Bytes>): Bytes
  {
    match result
    case Ok(data) => data
    case Err(error) => if error.ReadFailure? || error.StreamFailure? then error.partial else []
  }

  function ReadResultStage(result: IOResult<Bytes>): FileReadStage
  {
    if result.Err? && result.e.ReadFailure? then result.e.readStage else ReadSucceeded
  }

  function WriteResultCommitted(result: IOResult<WriteReceipt>): nat
  {
    match result
    case Ok(receipt) => receipt.committed
    case Err(error) => if error.WriteFailure? || error.StreamFailure? then error.committed else 0
  }

  function WriteResultStage(result: IOResult<WriteReceipt>): FileWriteStage
  {
    if result.Err? && result.e.WriteFailure? then result.e.writeStage else WriteSucceeded
  }

  function ParsedResultValue(result: IOResult<ParsedInstant>): ParsedInstant
  {
    match result
    case Ok(value) => value
    case Err(error) => if error.TimeParseFailure? then ParsedInstant(error.sec, error.nsec)
    else ParsedInstant(0, 0)
  }

  function IOErrorIsDirectory(error: IOError): bool
  {
    error.IsDirectory? || (error.ReadFailure? && error.errno == Errno.EISDIR)
  }

  function IOErrorIsReadFailure(error: IOError): bool
  {
    error.IsDirectory? ||
    (error.ReadFailure? && error.readStage != OpenFailed)
  }

  function ReadFailureData(error: IOError): Bytes
  {
    if error.ReadFailure? then error.partial else []
  }

  function StreamReadResultFromOutcome(data: Bytes, err: int, message: string): IOResult<Bytes>
  {
    if err == 0 then Result.Ok(data)
    else Result.Err(StreamFailure(err, message, data, |data|))
  }

  function StreamWriteResultFromOutcome(committed: nat, err: int, message: string): IOResult<WriteReceipt>
  {
    if err == 0 then Result.Ok(WriteReceipt(committed))
    else Result.Err(StreamFailure(err, message, [], committed))
  }

  // One bounded native read: short successes are allowed, failures consume no
  // bytes, and an empty successful read denotes EOF for finite captured stdin.
  ghost function ObservedReadStdinChunkResultFields(
    beforeStdin: Bytes, observations: (TrustedStreamRequest) -> TrustedStreamResult,
    limit: nat
  ): IOResult<Bytes>
  {
    match observations(StreamReadStdinChunk(beforeStdin, limit))
    case StreamReadStdinResult(data, _, err) =>
      StreamReadResultFromOutcome(data, err, CLocaleErrnoTextResult(err))
    case _ => Result.Err(Other("invalid bounded stdin observation"))
  }

  ghost function ObservedReadStdinChunkRemainingFields(
    beforeStdin: Bytes, observations: (TrustedStreamRequest) -> TrustedStreamResult,
    limit: nat
  ): Bytes
  {
    match observations(StreamReadStdinChunk(beforeStdin, limit))
    case StreamReadStdinResult(_, remaining, _) => remaining
    case _ => beforeStdin
  }

  ghost predicate ReadStdinChunkSpec(
    beforeStdin: Bytes, observations: (TrustedStreamRequest) -> TrustedStreamResult,
    afterStdin: Bytes, limit: nat, data: Bytes, err: int
  )
  {
    0 < limit <= 9223372036854775806 &&
    observations(StreamReadStdinChunk(beforeStdin, limit)) ==
    StreamReadStdinResult(data, afterStdin, err) &&
    0 <= err && |data| <= limit && data + afterStdin == beforeStdin &&
    (err != 0 ==> data == []) &&
    (err == 0 && data == [] ==> afterStdin == [])
  }

  // Whole-stdin reads are derived from exact fixed-size chunk observations.
  // Cuts describe a finite byte partition, independent of the wrapper's loop.
  const StdinReadChunkSize: nat := 64 * 1024

  ghost predicate ReadStdinPositiveChunkFields(
    beforeStdin: Bytes, observations: (TrustedStreamRequest) -> TrustedStreamResult,
    start: nat, stop: nat
  )
  {
    start < stop <= |beforeStdin| &&
    ReadStdinChunkSpec(beforeStdin[start..], observations, beforeStdin[stop..],
                       StdinReadChunkSize, beforeStdin[start..stop], 0)
  }

  ghost predicate ReadStdinPrefixFields(
    beforeStdin: Bytes, observations: (TrustedStreamRequest) -> TrustedStreamResult,
    cuts: seq<nat>
  )
  {
    0 < |cuts| && cuts[0] == 0 && |cuts| <= cuts[|cuts| - 1] + 1 &&
    (forall i: nat | i < |cuts| :: cuts[i] <= |beforeStdin|) &&
    (forall i: nat | i + 1 < |cuts| ::
       ReadStdinPositiveChunkFields(beforeStdin, observations, cuts[i], cuts[i + 1]))
  }

  ghost function ReadStdinTerminalErrFields(
    beforeStdin: Bytes, observations: (TrustedStreamRequest) -> TrustedStreamResult,
    position: nat
  ): int
    requires position <= |beforeStdin|
  {
    ResultErrno(ObservedReadStdinChunkResultFields(
                  beforeStdin[position..], observations, StdinReadChunkSize))
  }

  ghost predicate ReadStdinPartitionFields(
    beforeStdin: Bytes, observations: (TrustedStreamRequest) -> TrustedStreamResult,
    cuts: seq<nat>
  )
  {
    ReadStdinPrefixFields(beforeStdin, observations, cuts) &&
    var position := cuts[|cuts| - 1];
    ReadStdinChunkSpec(beforeStdin[position..], observations, beforeStdin[position..],
                       StdinReadChunkSize, [], ReadStdinTerminalErrFields(beforeStdin, observations, position))
  }

  lemma ReadStdinPartitionPropertiesFields(
    beforeStdin: Bytes, observations: (TrustedStreamRequest) -> TrustedStreamResult,
    cuts: seq<nat>
  )
    requires ReadStdinPartitionFields(beforeStdin, observations, cuts)
    ensures 0 <= ReadStdinTerminalErrFields(beforeStdin, observations, cuts[|cuts| - 1])
    ensures beforeStdin[..cuts[|cuts| - 1]] + beforeStdin[cuts[|cuts| - 1]..] == beforeStdin
    ensures ReadStdinTerminalErrFields(beforeStdin, observations, cuts[|cuts| - 1]) == 0 ==>
              beforeStdin[cuts[|cuts| - 1]..] == []
  {
  }

  ghost function ReadStdinOutcomeFields(
    beforeStdin: Bytes, observations: (TrustedStreamRequest) -> TrustedStreamResult
  ): (outcome: (bool, Bytes, Bytes, int))
    ensures outcome.0 <==> exists cuts: seq<nat> :: ReadStdinPartitionFields(beforeStdin, observations, cuts)
    ensures outcome.0 ==> exists cuts: seq<nat> ::
                ReadStdinPartitionFields(beforeStdin, observations, cuts) &&
                outcome == (true, beforeStdin[..cuts[|cuts| - 1]], beforeStdin[cuts[|cuts| - 1]..],
                            ReadStdinTerminalErrFields(beforeStdin, observations, cuts[|cuts| - 1]))
    ensures !outcome.0 ==> outcome == (false, [], beforeStdin, 0)
  {
    if exists cuts: seq<nat> :: ReadStdinPartitionFields(beforeStdin, observations, cuts) then
      var cuts: seq<nat> :| ReadStdinPartitionFields(beforeStdin, observations, cuts);
      var position := cuts[|cuts| - 1];
      (true, beforeStdin[..position], beforeStdin[position..],
       ReadStdinTerminalErrFields(beforeStdin, observations, position))
    else
      (false, [], beforeStdin, 0)
  }

  ghost function ObservedReadStdinResultFields(
    beforeStdin: Bytes,
    observations: (TrustedStreamRequest) -> TrustedStreamResult
  ): IOResult<Bytes>
  {
    var outcome := ReadStdinOutcomeFields(beforeStdin, observations);
    if outcome.0 then StreamReadResultFromOutcome(outcome.1, outcome.3, CLocaleErrnoTextResult(outcome.3))
    else Result.Err(Other("invalid stdin observation"))
  }

  ghost function ObservedReadStdinRemainingFields(
    beforeStdin: Bytes,
    observations: (TrustedStreamRequest) -> TrustedStreamResult
  ): Bytes
  {
    ReadStdinOutcomeFields(beforeStdin, observations).2
  }

  lemma ReadStdinPrefixAgreementFields(
    beforeStdin: Bytes, observations: (TrustedStreamRequest) -> TrustedStreamResult,
    first: seq<nat>, second: seq<nat>, index: nat
  )
    requires ReadStdinPrefixFields(beforeStdin, observations, first)
    requires ReadStdinPrefixFields(beforeStdin, observations, second)
    requires index < |first| && index < |second|
    ensures first[index] == second[index]
    decreases index
  {
    if index > 0 {
      ReadStdinPrefixAgreementFields(beforeStdin, observations, first, second, index - 1);
      assert ReadStdinPositiveChunkFields(beforeStdin, observations, first[index - 1], first[index]);
      assert ReadStdinPositiveChunkFields(beforeStdin, observations, second[index - 1], second[index]);
      assert beforeStdin[first[index - 1]..first[index]] == beforeStdin[second[index - 1]..second[index]];
      assert first[index] - first[index - 1] == second[index] - second[index - 1];
    }
  }

  lemma ReadStdinPartitionDeterministicFields(
    beforeStdin: Bytes, observations: (TrustedStreamRequest) -> TrustedStreamResult,
    first: seq<nat>, second: seq<nat>
  )
    requires ReadStdinPartitionFields(beforeStdin, observations, first)
    requires ReadStdinPartitionFields(beforeStdin, observations, second)
    ensures |first| == |second|
    ensures first[|first| - 1] == second[|second| - 1]
    ensures ReadStdinTerminalErrFields(beforeStdin, observations, first[|first| - 1]) ==
            ReadStdinTerminalErrFields(beforeStdin, observations, second[|second| - 1])
  {
    var index := (if |first| <= |second| then |first| else |second|) - 1;
    ReadStdinPrefixAgreementFields(beforeStdin, observations, first, second, index);
    if |first| < |second| {
      assert ReadStdinPositiveChunkFields(beforeStdin, observations, second[index], second[index + 1]);
      assert beforeStdin[second[index]..second[index + 1]] == [];
      assert false;
    } else if |second| < |first| {
      assert ReadStdinPositiveChunkFields(beforeStdin, observations, first[index], first[index + 1]);
      assert beforeStdin[first[index]..first[index + 1]] == [];
      assert false;
    }
  }

  lemma ReadStdinPrefixAppendFields(
    beforeStdin: Bytes, observations: (TrustedStreamRequest) -> TrustedStreamResult,
    cuts: seq<nat>, chunk: Bytes, remaining: Bytes
  )
    requires ReadStdinPrefixFields(beforeStdin, observations, cuts)
    requires chunk != []
    requires ReadStdinChunkSpec(beforeStdin[cuts[|cuts| - 1]..], observations,
                                remaining, StdinReadChunkSize, chunk, 0)
    ensures ReadStdinPrefixFields(beforeStdin, observations, cuts + [cuts[|cuts| - 1] + |chunk|])
    ensures chunk == beforeStdin[cuts[|cuts| - 1]..cuts[|cuts| - 1] + |chunk|]
    ensures remaining == beforeStdin[cuts[|cuts| - 1] + |chunk|..]
  {
    var start := cuts[|cuts| - 1];
    var stop := start + |chunk|;
    var next := cuts + [stop];
    assert beforeStdin[start..] == chunk + remaining;
    assert stop <= |beforeStdin|;
    assert chunk == beforeStdin[start..stop];
    assert remaining == beforeStdin[stop..];
    assert ReadStdinPositiveChunkFields(beforeStdin, observations, start, stop);
    forall i: nat | i < |next|
      ensures next[i] <= |beforeStdin|
    {
      if i < |cuts| { assert next[i] == cuts[i]; }
      else { assert i == |cuts|; }
    }
    forall i: nat | i + 1 < |next|
      ensures ReadStdinPositiveChunkFields(beforeStdin, observations, next[i], next[i + 1])
    {
      if i + 1 < |cuts| {
        assert next[i] == cuts[i] && next[i + 1] == cuts[i + 1];
      } else {
        assert i == |cuts| - 1;
      }
    }
  }

  lemma ReadStdinDerivedOutcomeFields(
    beforeStdin: Bytes, observations: (TrustedStreamRequest) -> TrustedStreamResult,
    cuts: seq<nat>, err: int
  )
    requires ReadStdinPrefixFields(beforeStdin, observations, cuts)
    requires ReadStdinChunkSpec(beforeStdin[cuts[|cuts| - 1]..], observations,
                                beforeStdin[cuts[|cuts| - 1]..], StdinReadChunkSize, [], err)
    ensures ReadStdinSpec(beforeStdin, observations, beforeStdin[cuts[|cuts| - 1]..],
                          beforeStdin[..cuts[|cuts| - 1]], err)
    ensures ObservedReadStdinResultFields(beforeStdin, observations) ==
            StreamReadResultFromOutcome(beforeStdin[..cuts[|cuts| - 1]], err, CLocaleErrnoTextResult(err))
    ensures ObservedReadStdinRemainingFields(beforeStdin, observations) == beforeStdin[cuts[|cuts| - 1]..]
  {
    var position := cuts[|cuts| - 1];
    assert ReadStdinTerminalErrFields(beforeStdin, observations, position) == err;
    assert ReadStdinPartitionFields(beforeStdin, observations, cuts);
    ReadStdinPartitionPropertiesFields(beforeStdin, observations, cuts);
    var outcome := ReadStdinOutcomeFields(beforeStdin, observations);
    assert outcome.0;
    var selected: seq<nat> :| ReadStdinPartitionFields(beforeStdin, observations, selected) &&
                              outcome == (true, beforeStdin[..selected[|selected| - 1]], beforeStdin[selected[|selected| - 1]..],
                                          ReadStdinTerminalErrFields(beforeStdin, observations, selected[|selected| - 1]));
    ReadStdinPartitionDeterministicFields(beforeStdin, observations, cuts, selected);
    assert outcome == (true, beforeStdin[..position], beforeStdin[position..], err);
  }

  ghost function ObservedReadFileResultFields(
    fs: FileSystem,
    observations: (TrustedStreamRequest) -> TrustedStreamResult,
    path: Path
  ): IOResult<Bytes>
  {
    match observations(StreamReadFile(fs, path))
    case StreamReadFileResult(data, err, stage) =>
      FileReadResultFromOutcome(data, err, stage, CLocaleErrnoTextResult(err))
    case _ => Result.Err(NoSuchFile)
  }

  ghost predicate TrustedReadFileContractFields(
    observations: (TrustedStreamRequest) -> TrustedStreamResult,
    fs: FileSystem,
    path: Path,
    data: Bytes,
    err: int,
    stage: FileReadStage
  )
  {
    match observations(StreamReadFile(fs, path))
    case StreamReadFileResult(observedData, observedErr, observedStage) =>
      data == observedData && err == observedErr && stage == observedStage &&
      0 <= err && (err == 0 <==> stage == ReadSucceeded) &&
      (stage == OpenFailed ==> data == []) &&
      // The Linux read-only stream reports EISDIR only for a directory.
      (err == Errno.EISDIR ==>
         ModeledReadFileResultFields(fs, path) == Result.Err(IsDirectory)) &&
      (match ModeledReadFileResultFields(fs, path)
       case Ok(contents) =>
         BytesPrefix(data, contents) && (err == 0 ==> data == contents)
       case Err(_) => data == [] && err != 0)
    case _ => false
  }

  // A read-only open followed by close observes access failures without reading data.
  ghost function ObservedOpenReadFileResultFields(
    fs: FileSystem,
    observations: (TrustedStreamRequest) -> TrustedStreamResult,
    path: Path
  ): IOResult<Bytes>
  {
    match observations(StreamOpenReadFile(fs, path))
    case StreamReadFileResult(data, err, stage) =>
      FileReadResultFromOutcome(data, err, stage, CLocaleErrnoTextResult(err))
    case _ => Result.Err(NoSuchFile)
  }

  ghost predicate TrustedOpenReadFileContractFields(
    observations: (TrustedStreamRequest) -> TrustedStreamResult,
    fs: FileSystem,
    path: Path,
    data: Bytes,
    err: int,
    stage: FileReadStage
  )
  {
    match observations(StreamOpenReadFile(fs, path))
    case StreamReadFileResult(observedData, observedErr, observedStage) =>
      data == observedData && err == observedErr && stage == observedStage &&
      data == [] && 0 <= err && (err == 0 <==> stage == ReadSucceeded) &&
      stage in {ReadSucceeded, OpenFailed, CloseFailed} &&
      (stage != OpenFailed ==>
         match ResolvePathForMetadataFields(fs, path, true)
         case Err(_) => false
         case Ok(target) => FsContainsPath(fs, target) && !FsNodeAt(fs, target).Inaccessible?)
    case _ => false
  }

  // Compatibility name: this relation is derived entirely from chunk observations.
  ghost predicate TrustedReadStdinWithOutcomeContractFields(
    observations: (TrustedStreamRequest) -> TrustedStreamResult,
    beforeStdin: Bytes,
    afterStdin: Bytes,
    data: Bytes,
    err: int
  )
  {
    0 <= err && data + afterStdin == beforeStdin && (err == 0 ==> afterStdin == []) &&
    exists cuts: seq<nat> :: ReadStdinPartitionFields(beforeStdin, observations, cuts) &&
                             data == beforeStdin[..cuts[|cuts| - 1]] && afterStdin == beforeStdin[cuts[|cuts| - 1]..] &&
                             err == ReadStdinTerminalErrFields(beforeStdin, observations, cuts[|cuts| - 1])
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
      (err == 0 ==> committed == |requested|)
    case StreamReadFileResult(_, _, _) => false
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

  // Validity is precisely the existing operation relation for the supplied
  // request and observation. Raw request/result datatypes remain unrestricted.
  ghost predicate ValidStreamObservation(request: TrustedStreamRequest, observed: TrustedStreamResult)
  {
    match request
    case StreamReadFile(fs, path) =>
      observed.StreamReadFileResult? &&
      TrustedReadFileContractFields((_: TrustedStreamRequest) => observed,
                                    fs, path, observed.data, observed.err, observed.stage)
    case StreamOpenReadFile(fs, path) =>
      observed.StreamReadFileResult? &&
      TrustedOpenReadFileContractFields((_: TrustedStreamRequest) => observed,
                                        fs, path, observed.data, observed.err, observed.stage)
    case StreamReadStdinChunk(before, limit) =>
      0 < limit <= 9223372036854775806 ==>
        observed.StreamReadStdinResult? &&
        ReadStdinChunkSpec(before, (_: TrustedStreamRequest) => observed,
                           observed.remaining, limit, observed.data, observed.err)
    case StreamWriteStdout(before, requested) =>
      observed.StreamWriteResult? &&
      TrustedWriteWithOutcomeFields(observed, before, observed.postOutput,
                                    requested, observed.committed, observed.err)
    case StreamWriteStderr(before, requested) =>
      observed.StreamWriteResult? &&
      TrustedWriteWithOutcomeFields(observed, before, observed.postOutput,
                                    requested, observed.committed, observed.err)
  }

  ghost predicate StreamObservationsValid(observations: (TrustedStreamRequest) -> TrustedStreamResult)
  {
    forall request :: ValidStreamObservation(request, observations(request))
  }

  // This witness proves inhabitance; executable adapters still report their
  // actual data, committed prefix and errno rather than using this ghost value.
  ghost function StreamFailureWitness(request: TrustedStreamRequest): (observed: TrustedStreamResult)
    ensures ValidStreamObservation(request, observed)
  {
    match request
    case StreamReadFile(_, _) => StreamReadFileResult([], Errno.EIO, OpenFailed)
    case StreamOpenReadFile(_, _) => StreamReadFileResult([], Errno.EIO, OpenFailed)
    case StreamReadStdinChunk(before, _) => StreamReadStdinResult([], before, Errno.EIO)
    case StreamWriteStdout(before, _) => StreamWriteResult(0, before, Errno.EIO)
    case StreamWriteStderr(before, _) => StreamWriteResult(0, before, Errno.EIO)
  }

  type ValidStreamObservations = observations: ((TrustedStreamRequest) -> TrustedStreamResult) |
      StreamObservationsValid(observations)
    ghost witness (request: TrustedStreamRequest) => StreamFailureWitness(request)

  // The observation's fields construct an outcome of each unchanged full Spec.
  lemma StreamObservationAdmitsRequest(observations: ValidStreamObservations, request: TrustedStreamRequest)
    ensures match request
            case StreamReadFile(fs, path) =>
              var observed := observations(request);
              observed.StreamReadFileResult? &&
              ReadFileSpec(fs, observations, path, observed.data, observed.err, observed.stage)
            case StreamOpenReadFile(fs, path) =>
              var observed := observations(request);
              observed.StreamReadFileResult? &&
              OpenReadFileSpec(fs, observations, path, observed.data, observed.err, observed.stage)
            case StreamReadStdinChunk(before, limit) =>
              var observed := observations(request);
              0 < limit <= 9223372036854775806 ==>
                observed.StreamReadStdinResult? &&
                ReadStdinChunkSpec(before, observations, observed.remaining, limit, observed.data, observed.err)
            case StreamWriteStdout(before, requested) =>
              var observed := observations(request);
              observed.StreamWriteResult? &&
              WriteStdoutSpec(before, observations, observed.postOutput, requested, observed.committed, observed.err)
            case StreamWriteStderr(before, requested) =>
              var observed := observations(request);
              observed.StreamWriteResult? &&
              WriteStderrSpec(before, observations, observed.postOutput, requested, observed.committed, observed.err)
  {
  }

  ghost function ReadLinkResultFields(fs: FileSystem, path: Path): IOResult<Path>
  {
    match ResolvePathForMetadataFields(fs, path, false)
    case Ok(resolved) =>
      if FsContainsPath(fs, resolved) then
        match FsNodeAt(fs, resolved)
        case Symlink(target, _, _, _) => Result.Ok(target)
        case _ => Result.Err(InvalidPath)
      else
        Result.Err(NoSuchFile)
    case Err(e) => Result.Err(e)
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
    case NoSuchFile => Errno.ENOENT
    case PermissionDenied => Errno.EACCES
    case NotDirectory => Errno.ENOTDIR
    case IsDirectory => Errno.EISDIR
    case InvalidPath => Errno.ELOOP
    case Other(_) => Errno.EIO
    case ReadFailure(errno, _, _, _) => errno
    case NativeFailure(errno, _) => errno
    case WriteFailure(errno, _, _, _) => errno
    case StreamFailure(errno, _, _, _) => errno
    case TimeParseFailure(_, _, _) => Errno.EINVAL
  }

  ghost function MetadataFailureErrFields(fs: FileSystem, path: Path, followSymlink: bool): int
  {
    match ResolvePathForMetadataFields(fs, path, followSymlink)
    case Err(e) => IOErrorErrno(e)
    case Ok(resolved) => if FsContainsPath(fs, resolved) then 0 else Errno.ENOENT
  }

  ghost function OpenDirFailureErrFields(fs: FileSystem, path: Path): int
  {
    match ResolvePathForMetadataFields(fs, path, true)
    case Err(e) => IOErrorErrno(e)
    case Ok(resolved) =>
      if !FsContainsPath(fs, resolved) then
        Errno.ENOENT
      else
        match FsNodeAt(fs, resolved)
        case Directory(_, _, _) => 0
        case _ => Errno.ENOTDIR
  }

  ghost predicate PathExistsContractFields(fs: FileSystem, path: Path, followSymlink: bool, found: bool, err: int)
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
    ValidFilesystemObservation(FilesystemQuery(fs, path, followSymlink), observed) &&
    observed.postFs == fs &&
    ok == observed.ok &&
    err == observed.err &&
    (ok ==> (atimeSec == observed.atimeSec &&
             atimeNsec == observed.atimeNsec &&
             mtimeSec == observed.mtimeSec &&
             mtimeNsec == observed.mtimeNsec &&
             isDir == observed.isDir &&
             isSymlink == observed.isSymlink &&
             device == observed.device &&
             inode == observed.inode &&
             linkCount == observed.linkCount))
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
    ValidFilesystemObservation(FilesystemQuery(fs, path, followSymlink), observed) &&
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
    ValidFilesystemObservation(FilesystemCreate(fs, path, now), observed) &&
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
    ValidFilesystemObservation(request, observed) &&
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

  ghost predicate GetFileModeContractFields(fs: FileSystem, path: Path, followSymlink: bool, ok: bool, mode: bv32, err: int)
  {
    0 <= err && (ok <==> err == 0) &&
    (!ok ==> err in NativeStatusFailureErrnosFields(fs, path, followSymlink)) &&
    (ok ==>
       match ResolvePathForMetadataFields(fs, path, followSymlink)
       case Ok(resolved) =>
         FsContainsPath(fs, resolved) && mode == NodeMode(FsNodeAt(fs, resolved))
       case Err(_) => false)
  }

  ghost function GetFileStatusResultFields(
    fs: FileSystem,
    path: Path,
    followSymlink: bool
  ): IOResult<FileStatus>
  {
    match ResolvePathForMetadataFields(fs, path, followSymlink)
    case Err(error) => Result.Err(error)
    case Ok(resolved) =>
      if !FsContainsPath(fs, resolved) then
        Result.Err(NoSuchFile)
      else
        var record := fs.inodes[FsIdAt(fs, resolved)];
        match record.node
        case Inaccessible(_) => Result.Err(PermissionDenied)
        case _ =>
          match record.links
          case LinkCountUnknown => Result.Err(Other("unknown link count"))
          case LinkCountKnown(_) => Result.Ok(FileStatusForRecord(record))
  }

  predicate FileStatusObservationFields(expected: FileStatus, observed: FileStatus)
  {
    observed == expected
  }

  ghost function ObservedFileStatusResultFields(
    observations: StatusTimeObservations,
    ordinal: nat,
    fs: FileSystem,
    path: Path,
    followSymlink: bool
  ): IOResult<FileStatus>
  {
    match GetFileStatusResultFields(fs, path, followSymlink)
    case Err(error) => Result.Err(error)
    case Ok(status) =>
      Result.Ok(status.(times := observations(ordinal, fs, path, followSymlink)))
  }

  ghost predicate ObservedFileStatusContractFields(
    observations: StatusTimeObservations,
    ordinal: nat,
    fs: FileSystem,
    path: Path,
    followSymlink: bool,
    ok: bool,
    status: FileStatus,
    err: int
  )
  {
    match ObservedFileStatusResultFields(observations, ordinal, fs, path, followSymlink)
    case Ok(expected) => ok && status == expected && err == 0
    case Err(error) => !ok && err == IOErrorErrno(error)
  }

  ghost predicate ObservedNativeFileStatusContractFields(
    observations: StatusTimeObservations,
    failures: (NativeFailureRequest) -> int,
    ordinal: nat, fs: FileSystem, path: Path, followSymlink: bool,
    ok: bool, status: FileStatus, err: int
  )
  {
    NativeFailureContractFields(failures, StatusRequest(ordinal, fs, path, followSymlink), err) &&
    match ObservedNativeStatusResultFields(observations, failures, ordinal, fs, path, followSymlink)
    case Ok(expected) => ok && status == expected && err == 0
    case Err(error) => !ok && err == IOErrorErrno(error)
  }

  // A structural projection never identifies an observed time with a stale
  // filesystem timestamp. Time-consuming clients use the ordered relation above.
  ghost predicate FileStatusStructureContractFields(
    fs: FileSystem, path: Path, followSymlink: bool,
    ok: bool, status: FileStatus, err: int
  )
  {
    0 <= err && (ok <==> err == 0) &&
    (!ok ==> err in NativeStatusFailureErrnosFields(fs, path, followSymlink)) &&
    (ok ==>
       match GetFileStatusResultFields(fs, path, followSymlink)
       case Ok(expected) => status.(times := expected.times) == expected
       case Err(_) => false)
  }

  lemma ObservedFileStatusImpliesStructure(
    observations: StatusTimeObservations,
    ordinal: nat,
    fs: FileSystem,
    path: Path,
    followSymlink: bool,
    ok: bool,
    status: FileStatus,
    err: int
  )
    requires ObservedFileStatusContractFields(
               observations, ordinal, fs, path, followSymlink, ok, status, err)
    requires ok || 0 < err
    ensures FileStatusStructureContractFields(fs, path, followSymlink, ok, status, err)
  {
  }

  ghost predicate GetFileStatusContractFields(
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
    requires FileStatusStructureContractFields(
               fs, path, followSymlink, ok, status, err
             )
    ensures GetFileModeContractFields(fs, path, followSymlink, ok, status.mode, err)
  {
    var resolved := ResolvePathForMetadataFields(fs, path, followSymlink);
    if ok && resolved.Ok? {
      var id := FsIdAt(fs, resolved.v);
      assert fs.inodes[id].links.LinkCountKnown?;
      assert FsNodeAt(fs, resolved.v) == fs.inodes[id].node;
    }
  }

  // Structural metadata excludes timestamps, which may vary between ordered
  // observations of the same path.
  lemma FileStatusStructureImpliesMetadata(
    fs: FileSystem, path: Path, followSymlink: bool,
    ok: bool, status: FileStatus, err: int
  )
    requires FileStatusStructureContractFields(
               fs, path, followSymlink, ok, status, err
             )
    ensures ok ==> PathExistsContractFields(fs, path, followSymlink, ok, err)
    ensures IsDirectoryStrictContractFields(
              fs, path, followSymlink, ok, status.kind == DirectoryKind, err)
    ensures !followSymlink ==>
              IsSymlinkContractFields(fs, path, ok, status.kind == SymlinkKind, err)
  {
    var resolved := ResolvePathForMetadataFields(fs, path, followSymlink);
    if ok && resolved.Ok? {
      var id := FsIdAt(fs, resolved.v);
      assert fs.inodes[id].links.LinkCountKnown?;
      assert FsNodeAt(fs, resolved.v) == fs.inodes[id].node;
      assert InodeKindConsistent(fs.inodes[id]);
    }
  }

  // These are ghost consequences of stat fields, not executable convenience calls.
  lemma FileStatusImpliesMetadata(
    fs: FileSystem, path: Path, followSymlink: bool,
    ok: bool, status: FileStatus, err: int
  )
    requires GetFileStatusContractFields(fs, path, followSymlink, ok, status, err)
    requires ok || 0 < err
    ensures ok ==> PathExistsContractFields(fs, path, followSymlink, ok, err)
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
    if ok && resolved.Ok? {
      var id := FsIdAt(fs, resolved.v);
      assert fs.inodes[id].links.LinkCountKnown?;
      assert FsNodeAt(fs, resolved.v) == fs.inodes[id].node;
      assert InodeKindConsistent(fs.inodes[id]);
    }
  }

  ghost predicate IsDirectoryContractFields(fs: FileSystem, path: Path, followSymlink: bool, ok: bool, isDir: bool, err: int)
  {
    0 <= err && (ok <==> err == 0) &&
    (!ok ==> err in NativeStatusFailureErrnosFields(fs, path, followSymlink)) &&
    (ok ==>
       match ResolvePathForMetadataFields(fs, path, followSymlink)
       case Ok(resolved) =>
         FsContainsPath(fs, resolved) && isDir == FsNodeAt(fs, resolved).Directory?
       case Err(_) => false)
  }

  ghost predicate IsDirectoryStrictContractFields(fs: FileSystem, path: Path, followSymlink: bool, ok: bool, isDir: bool, err: int)
  {
    IsDirectoryContractFields(fs, path, followSymlink, ok, isDir, err)
  }

  ghost predicate IsSymlinkContractFields(fs: FileSystem, path: Path, ok: bool, isSymlink: bool, err: int)
  {
    0 <= err && (ok <==> err == 0) &&
    (!ok ==> err in NativeStatusFailureErrnosFields(fs, path, false)) &&
    (ok ==>
       match ResolvePathForMetadataFields(fs, path, false)
       case Ok(resolved) =>
         FsContainsPath(fs, resolved) && isSymlink == FsNodeAt(fs, resolved).Symlink?
       case Err(_) => false)
  }

  ghost function ResolvePathForCreateNoFollowTerminalFields(fs: FileSystem, path: Path): IOResult<Path>
  {
    if path == "" then
      Result.Err(InvalidPath)
    else if HasTrailingSlash(path) ||
            HasRawTerminalSpecialFields(path)
    then
      ResolvePathThroughSymlinkComponentsFields(fs, path, false)
    else
      var segments := RawPathSegmentsFields(path);
      if |segments| == 0 then
        Result.Err(InvalidPath)
      else
        var child := segments[|segments| - 1];
        var parentSegments := segments[..|segments| - 1];
        var root := if IsAbsolutePath(path) then "/" else "";
        if |parentSegments| == 0 then
          Result.Ok(AppendPath(root, child))
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
              case Directory(_, _, _) => Result.Ok(AppendPath(resolvedParent, child))
              case _ => Result.Err(NotDirectory)
            else
              Result.Err(NoSuchFile)
          case Err(e) => Result.Err(e)
  }

  ghost function ResolvePathForCreateFields(fs: FileSystem, path: Path): IOResult<Path>
  {
    if path == "" then
      Result.Err(InvalidPath)
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

  ghost function CreateFileFailureErrFields(fs: FileSystem, path: Path): int
  {
    if (0 as char) in path then
      Errno.EINVAL
    else if path == "" then
      Errno.ENOENT
    else
      match ResolvePathForCreateFields(fs, path)
      case Err(e) => IOErrorErrno(e)
      case Ok(target) =>
        if FsContainsPath(fs, target) then
          match FsNodeAt(fs, target)
          case Directory(_, _, _) => Errno.EISDIR
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

  ghost function RefreshParentDirectoryStorageFields(
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

  ghost function CreationOwnershipFields(
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

  ghost predicate CreatedRegularRequestedModeFields(
    fs: FileSystem,
    props: map<string, string>,
    path: Path,
    ok: bool,
    fs2: FileSystem,
    requestedMode: bv32
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
            requestedMode &
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

  ghost function FsWithoutPath(fs: FileSystem, path: Path): FileSystem
  {
    FsRemovePath(fs, path)
  }

  ghost function DeleteFsWithMetadataFields(
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

  ghost function WriteFileFailureErrFields(fs: FileSystem, path: Path): int
  {
    if (0 as char) in path then
      Errno.EINVAL
    else if path == "" then
      Errno.ENOENT
    else
      match ResolvePathForCreateFields(fs, path)
      case Err(e) => IOErrorErrno(e)
      case Ok(target) =>
        if FsContainsPath(fs, target) then
          match FsNodeAt(fs, target)
          case Regular(_, _, _, _) => 0
          case Directory(_, _, _) => Errno.EISDIR
          case Inaccessible(_) => Errno.EACCES
          case Symlink(_, _, _, _) => Errno.ELOOP
        else
          0
  }

  ghost predicate CompletedWriteFileEffectFields(
    fs: FileSystem, now: int, path: Path, data: Bytes, fs2: FileSystem
  )
  {
    (0 as char) !in path && !HasTrailingSlash(path) &&
    !HasRawTerminalSpecialFields(path) &&
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
    case Err(_) => false
  }

  ghost function WriteOpenFailureErrnosFields(fs: FileSystem, path: Path): set<int>
  {
    if (0 as char) in path then {Errno.EINVAL} else
    NativeLookupFaultErrnos + NativeMutationFaultErrnos + {Errno.ENFILE, Errno.EMFILE} +
    (if WriteFileFailureErrFields(fs, path) == 0 then {}
     else {WriteFileFailureErrFields(fs, path)})
  }

  ghost predicate WriteFileOutcomeFields(
    fs: FileSystem, now: int, path: Path, data: Bytes, append: bool,
    ok: bool, err: int, committed: nat, stage: FileWriteStage, fs2: FileSystem
  )
  {
    0 <= err && (ok <==> err == 0) && (ok <==> stage == WriteSucceeded) &&
    committed <= |data| &&
    (if stage == WriteOpenFailed then
       !ok && committed == 0 && err in WriteOpenFailureErrnosFields(fs, path) &&
       FailedFilesystemEffectFields(fs, fs2)
     else
       (stage == WriteFailed ==> (committed < |data| &&
                                  err in {Errno.EIO, Errno.EBADF, Errno.EFBIG, Errno.ENOSPC, Errno.EROFS, Errno.EPIPE, Errno.EDQUOT})) &&
       (stage == WriteCloseFailed ==> (committed == |data| &&
                                       err in {Errno.EINTR, Errno.EIO, Errno.EBADF, Errno.ENOSPC, Errno.EDQUOT})) &&
       (stage == WriteSucceeded ==> committed == |data|) &&
       (if append then CompletedAppendEffectFields(fs, now, path, data[..committed], fs2)
        else CompletedWriteFileEffectFields(fs, now, path, data[..committed], fs2)))
  }

  ghost predicate WriteFileContractFields(
    fs: FileSystem, now: int, path: Path, data: Bytes,
    ok: bool, err: int, fs2: FileSystem
  )
  {
    exists committed: nat, stage: FileWriteStage ::
      WriteFileOutcomeFields(fs, now, path, data, false, ok, err, committed, stage, fs2)
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

  // Opening an existing regular file for append does not touch it at EOF when
  // no bytes are supplied. A nonempty append updates only the referent inode;
  // the native observation supplies host-specific mode and timestamp effects.
  ghost predicate ExistingAppendEffectFields(
    fs: FileSystem,
    target: Path,
    data: Bytes,
    fs2: FileSystem
  )
    requires FsContainsPath(fs, target)
  {
    if |data| == 0 then
      fs2 == fs
    else
      var id := FsIdAt(fs, target);
      fs2.namespace == fs.namespace &&
      fs2.inodes.Keys == fs.inodes.Keys &&
      (forall other :: other in fs.inodes && other != id ==>
                         fs2.inodes[other] == fs.inodes[other]) &&
      fs2.inodes[id].hostKey == fs.inodes[id].hostKey &&
      fs2.inodes[id].links == fs.inodes[id].links &&
      fs2.inodes[id].ownership == fs.inodes[id].ownership &&
      fs2.inodes[id].kind == fs.inodes[id].kind &&
      fs2.inodes[id].storage.size == fs.inodes[id].storage.size + |data| &&
      (match (fs.inodes[id].node, fs2.inodes[id].node)
       case (Regular(oldData, _, _, _), Regular(newData, _, _, _)) =>
         newData == oldData + data
       case _ => false)
  }

  ghost predicate CompletedAppendEffectFields(
    fs: FileSystem, now: int, path: Path, data: Bytes, fs2: FileSystem
  )
  {
    (0 as char) !in path && !HasTrailingSlash(path) && !HasRawTerminalSpecialFields(path) &&
    match ResolvePathForCreateFields(fs, path)
    case Err(_) => false
    case Ok(target) =>
      if FsContainsPath(fs, target) then
        FsNodeAt(fs, target).Regular? && ExistingAppendEffectFields(fs, target, data, fs2)
      else CompletedWriteFileEffectFields(fs, now, path, data, fs2)
  }

  ghost predicate AppendFileContractFields(
    fs: FileSystem, now: int, path: Path, data: Bytes,
    ok: bool, err: int, fs2: FileSystem
  )
  {
    exists committed: nat, stage: FileWriteStage ::
      WriteFileOutcomeFields(fs, now, path, data, true, ok, err, committed, stage, fs2)
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

  ghost function CreateSymlinkFailureErrFields(
    fs: FileSystem,
    path: Path,
    target: Path
  ): int
  {
    if path == "" then
      Errno.ENOENT
    else if target == "" then
      Errno.ENOENT
    else
      match ResolvePathForCreateNoFollowTerminalFields(fs, path)
      case Err(e) => IOErrorErrno(e)
      case Ok(linkPath) => if FsContainsPath(fs, linkPath) then Errno.EEXIST else 0
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
    0 <= err && (ok <==> err == 0) &&
    (!ok ==> fs2 == fs && err in NativeFailureErrnosFields(CreateSymlinkRequest(fs, now, path, target))) &&
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
       case Err(_) => false)
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

  ghost function DeletePathFailureErrFields(fs: FileSystem, path: Path): int
  {
    match ResolvePathForMetadataFields(fs, path, false)
    case Err(e) => IOErrorErrno(e)
    case Ok(target) =>
      if FsContainsPath(fs, target) then
        match FsNodeAt(fs, target)
        case Directory(_, _, _) => Errno.EISDIR
        case _ => 0
      else
        Errno.ENOENT
  }

  ghost predicate DeletePathContractFields(fs: FileSystem, path: Path, ok: bool, err: int, fs2: FileSystem)
  {
    0 <= err && (ok <==> err == 0) &&
    (!ok ==> fs2 == fs && err in NativeFailureErrnosFields(DeletePathRequest(fs, path))) &&
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
       case Err(_) => false)
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
    0 <= err && (ok <==> err == 0) &&
    (!ok ==> fs2 == fs && err in NativeFailureErrnosFields(SetModeRequest(fs, 0, path, followSymlink, mode))) &&
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
       case Err(_) => false)
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

  ghost predicate GetFileTimesContractFields(
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
    ValidFilesystemObservation(
      FilesystemSetTimes(fs, path, followSymlink, now, atime, mtime), observed) &&
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
  )  {
    0 <= err && (ok <==> err == 0) &&
    (!ok ==> after == before &&
             err in NativeFailureErrnosFields(StdoutTimesRequest(before, now, atime, mtime))) &&
    (ok ==> before.StdoutTimestampAvailable? &&
            TimestampUpdateValidFields(atime) && TimestampUpdateValidFields(mtime) &&
            exists afterTimes: AccessModificationTimes ::
              after == StdoutTimestampAvailable(afterTimes) &&
              StdoutTimestampUpdateFields(before.times, afterTimes, atime, mtime, now))
  }

  predicate ValidLeafName(name: string)
  {
    name != "" && !IsAbsolutePath(name) && PathSegments(name) == [name]
  }

  function EntryForNode(path: Path, node: FsNode): DirEntry
  {
    match node
    case Directory(_, _, _) => DirEntry(LeafName(path), true, false)
    case Symlink(_, _, _, _) => DirEntry(LeafName(path), false, true)
    case _ => DirEntry(LeafName(path), false, false)
  }

  function InodeTreeChildNodeFields(
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

  function DirectoryEntriesForTreeFields(
    fs: FileSystem,
    tree: InodeTree
  ): set<DirEntry>
    requires InodeTreeWellFormed(tree, fs.inodes)
  {
    set name: string |
      name in tree.children && ValidLeafName(name) ::
      EntryForNode(name, InodeTreeChildNodeFields(fs, tree, name))
  }

  function DirectoryEntriesForPathFields(
    fs: FileSystem,
    path: Path
  ): set<DirEntry>
    requires FsContainsPath(fs, path)
  {
    var tree := InodeFsLookupTreeSegments(
                  fs.inodes, fs.namespace, PathSegments(path)
                ).v;
    KernelLookupTreeWellFormed(
      fs.inodes, fs.namespace, PathSegments(path), tree
    );
    DirectoryEntriesForTreeFields(fs, tree)
  }

  function DirectoryEntriesIncludingDotsForPathFields(
    fs: FileSystem,
    path: Path
  ): set<DirEntry>
    requires FsContainsPath(fs, path)
  {
    DirectoryEntriesForPathFields(fs, path) +
    {DirEntry(".", true, false), DirEntry("..", true, false)}
  }

  ghost predicate OpenDirOutcomeFields(fs: FileSystem, path: Path, ok: bool, err: int)
  {
    (if (0 as char) in path then !ok && err == Errno.EINVAL
     else if ok then
       err == 0 && OpenDirFailureErrFields(fs,path) == 0
     else
       err > 0 &&
       (err == OpenDirFailureErrFields(fs,path) ||
        err in NativeLookupFaultErrnos + {Errno.ENFILE, Errno.EMFILE}))
  }

  ghost predicate OpenDirContractFields(
    fs: FileSystem,
    dirHandles: map<int, DirHandleState>,
    path: Path,
    includeDots: bool,
    ok: bool,
    handle: int,
    err: int,
    dirHandles2: map<int, DirHandleState>
  )
  {
    (!ok ==> dirHandles2 == dirHandles) &&
    OpenDirOutcomeFields(fs,path,ok,err) &&
    (ok ==>
       err == 0 &&
       !(handle in dirHandles) &&
       match ResolvePathForMetadataFields(fs, path, true)
       case Ok(resolved) =>
         FsContainsPath(fs, resolved) &&
         (match FsNodeAt(fs, resolved)
          case Directory(_, _, _) =>
            dirHandles2 == dirHandles[handle :=
            if includeDots then
              DotDirHandleState(resolved, DirectoryEntriesIncludingDotsForPathFields(fs, resolved))
            else
              DirHandleState(resolved, DirectoryEntriesForPathFields(fs, resolved))]
          case _ => false)
       case Err(_) => false) &&
    (match ResolvePathForMetadataFields(fs, path, true)
     case Err(_) => !ok
     case Ok(resolved) =>
       FsContainsPath(fs, resolved) &&
       (match FsNodeAt(fs, resolved)
        case Directory(_, _, _) => true
        case _ => !ok))
  }

  ghost predicate ResolvePathIdentityContractFields(
    fs: FileSystem, cwd: Path, path: Path,
    ok: bool, resolvedPath: Path, err: int
  )
  {
    var absolutePath := if IsAbsolutePath(path) then path
                        else AppendPath(BuildPath(true, PathSegments(cwd)), path);
    0 <= err && (ok <==> err == 0) &&
    (!ok ==> resolvedPath == "" && err in MetadataFailureErrnosFields(fs, absolutePath, true)) &&
    (ok ==>
       match ResolvePathForMetadataFields(fs, absolutePath, true)
       case Err(_) => false
       case Ok(resolved) =>
         resolvedPath == resolved && FsContainsPath(fs, resolved) &&
         NormalizePath(resolved) == resolved && IsAbsolutePath(resolved))
  }

  function DirectoryEntryKindForFileKind(kind: FileKind): DirectoryEntryKind
  {
    match kind
    case RegularKind => RegularDirentKind
    case DirectoryKind => DirectoryDirentKind
    case SymlinkKind => SymlinkDirentKind
    case FifoKind => FifoDirentKind
    case BlockDeviceKind => BlockDeviceDirentKind
    case CharacterDeviceKind => CharacterDeviceDirentKind
    case SocketKind => SocketDirentKind
  }

  predicate DirectoryEntryKindMatchesEntry(kind: DirectoryEntryKind, entry: DirEntry)
  {
    kind == UnknownDirentKind ||
    (entry.isDir == (kind == DirectoryDirentKind) &&
     entry.isSymlink == (kind == SymlinkDirentKind))
  }

  ghost predicate DirectoryEntryKindMatchesFilesystemFields(
    fs: FileSystem,
    parent: Path,
    name: string,
    kind: DirectoryEntryKind
  )
  {
    ValidLeafName(name) &&
    FsContainsPath(fs, parent) &&
    FsContainsPath(fs, AppendPath(parent, name)) &&
    (kind == UnknownDirentKind ||
     kind == DirectoryEntryKindForFileKind(
       fs.inodes[FsIdAt(fs, AppendPath(parent, name))].kind))
  }

  ghost predicate DirectoryDotEntryMatchesFilesystemFields(
    fs: FileSystem,
    parent: Path,
    name: string
  )
  {
    (name == "." || name == "..") &&
    FsContainsPath(fs, parent) && FsNodeAt(fs, parent).Directory? &&
    FsContainsPath(fs, ParentPath(parent)) &&
    FsNodeAt(fs, ParentPath(parent)).Directory?
  }

  // A handle determines whether dot entries are included. Known native kinds
  // agree with the filesystem; DT_UNKNOWN remains an explicit result.
  ghost predicate ReadDirContractFields(
    fs: FileSystem,
    dirHandles: map<int, DirHandleState>,
    handle: int,
    hasMore: bool,
    name: string,
    kind: DirectoryEntryKind,
    err: int,
    dirHandles2: map<int, DirHandleState>
  )
  {
    0 <= err &&
    (if !(handle in dirHandles) then
       !hasMore && name == "" && kind == UnknownDirentKind &&
       err != 0 && dirHandles2 == dirHandles
     else
       var state := dirHandles[handle];
       if err != 0 then
         !hasMore && name == "" && kind == UnknownDirentKind &&
         dirHandles2 == dirHandles
       else if |state.remaining| == 0 then
         !hasMore && name == "" && kind == UnknownDirentKind &&
         dirHandles2 == dirHandles
       else
         exists entry ::
           entry in state.remaining &&
           hasMore && err == 0 && name == entry.name &&
           (if state.DotDirHandleState? && (name == "." || name == "..") then
              entry == DirEntry(name, true, false) &&
              kind == DirectoryDirentKind &&
              DirectoryDotEntryMatchesFilesystemFields(fs, state.path, name)
            else
              DirectoryEntryKindMatchesEntry(kind, entry) &&
              DirectoryEntryKindMatchesFilesystemFields(
                fs, state.path, name, kind)) &&
           dirHandles2 == dirHandles[handle :=
           if state.DotDirHandleState? then
             DotDirHandleState(state.path, state.remaining - {entry})
           else
             DirHandleState(state.path, state.remaining - {entry})])
  }

  ghost predicate ReadDirInodeFields(fs: FileSystem, handles: map<int,DirHandleState>,
                                     handle: int, name: string, hasMore: bool, inode: int)
  {
    hasMore && handle in handles && name != "." && name != ".." ==>
      var path := AppendPath(handles[handle].path,name);
      FsContainsPath(fs,path) && inode == fs.inodes[FsIdAt(fs,path)].hostKey.inode
  }

  // Inspect the opened directory descriptor, which remains available to the
  // caller even if fstat fails. A successful result is an ordered status
  // observation of the path authenticated by that handle.
  ghost predicate GetOpenDirectoryStatusContractFields(
    observations: StatusTimeObservations,
    beforeCursor: nat,
    afterCursor: nat,
    fs: FileSystem,
    dirHandles: map<int, DirHandleState>,
    handle: int,
    ok: bool,
    status: FileStatus,
    err: int
  )
  {
    if !(handle in dirHandles) then
      !ok && err == Errno.EINVAL &&
      afterCursor == beforeCursor
    else if ok then
      err == 0 && afterCursor == beforeCursor + 1 &&
      ObservedFileStatusContractFields(
        observations, beforeCursor, fs, dirHandles[handle].path,
        true, true, status, 0) &&
      FileStatusStructureContractFields(
        fs, dirHandles[handle].path, true, true, status, 0)
    else
      err > 0 &&
      afterCursor == beforeCursor
  }

  ghost predicate CloseDirContractFields(
    dirHandles: map<int, DirHandleState>, handle: int,
    ok: bool, err: int, dirHandles2: map<int, DirHandleState>
  )
  {
    dirHandles2 == (if handle in dirHandles then dirHandles - {handle} else dirHandles) &&
    0 <= err && (ok <==> err == 0) &&
    (if handle in dirHandles then
       !ok ==> err in {Errno.EBADF, Errno.EINTR, Errno.EIO}
     else !ok && err == Errno.EINVAL)
  }

  function HasPathPrefix(root: Path, path: Path): bool { path == root || (root != "" && root != "/" && |root| < |path| && path[..|root|] == root && path[|root|] == '/') }

  ghost function ResolvePathForRenameNoFollowTerminalFields(
    fs: FileSystem,
    path: Path
  ): IOResult<Path>
  {
    var entryPath := BuildPath(
                       IsAbsolutePath(path),
                       RawPathSegmentsFields(path)
                     );
    match ResolvePathThroughSymlinkComponentsFields(fs, entryPath, false)
    case Err(error) => Result.Err(error)
    case Ok(resolved) =>
      if !HasTrailingSlash(path) then
        Result.Ok(resolved)
      else if !FsContainsPath(fs, resolved) then
        Result.Err(NoSuchFile)
      else
        match FsNodeAt(fs, resolved)
        case Directory(_, _, _) => Result.Ok(resolved)
        case Regular(_, _, _, _) | Symlink(_, _, _, _) =>
          Result.Err(NotDirectory)
        case Inaccessible(_) => Result.Err(PermissionDenied)
  }

  ghost function ResolvePathForRenameDestinationFields(fs: FileSystem, path: Path): IOResult<Path>
  {
    match ResolvePathForRenameNoFollowTerminalFields(fs, path)
    case Err(NoSuchFile) =>
      if HasTrailingSlash(path) ||
         HasRawTerminalSpecialFields(path)
      then
        Result.Err(NoSuchFile)
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

  ghost function RenameFs(
    fs: FileSystem,
    source: Path,
    target: Path
  ): FileSystem
    requires FsContainsPath(fs, source)
  {
    var candidate := InodeFsRename(fs, source, target);
    if ValidInodeFileSystemData(candidate) then candidate else fs
  }

  ghost function RenameDirectoryParentLinksFields(
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

  ghost function RefreshRenameParentStorageFields(
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

  ghost function RenameFsWithMetadataFields(
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

  ghost function RenameFailureErrnosFields(fs: FileSystem, source: Path, target: Path): set<int>
  {
    if (0 as char) in source || (0 as char) in target then {Errno.EINVAL}
    else if source == "" || target == "" then NativeLookupFaultErrnos + {Errno.ENOENT}
    else if !IsNonRootRawEntryPathFields(source) || !IsNonRootRawEntryPathFields(target) then
      NativeMutationFaultErrnos + {Errno.EBUSY, Errno.EINVAL}
    else
      match ResolvePathForRenameNoFollowTerminalFields(fs, source)
      case Err(error) => NativeLookupFaultErrnos + {IOErrorErrno(error)}
      case Ok(resolvedSource) =>
        match ResolvePathForRenameDestinationFields(fs, target)
        case Err(error) => NativeLookupFaultErrnos + {IOErrorErrno(error)}
        case Ok(resolvedTarget) =>
          NativeMutationFaultErrnos + {Errno.EBUSY, Errno.EXDEV, Errno.EINVAL, Errno.EMLINK} +
          (if !FsContainsPath(fs, resolvedTarget) then {}
           else if FsNodeAt(fs, resolvedSource).Directory? && !FsNodeAt(fs, resolvedTarget).Directory? then {Errno.ENOTDIR}
           else if !FsNodeAt(fs, resolvedSource).Directory? && FsNodeAt(fs, resolvedTarget).Directory? then {Errno.EISDIR}
           else if FsNodeAt(fs, resolvedTarget).Directory? && !HasNoDescendants(fs, resolvedTarget) then {Errno.EEXIST, Errno.ENOTEMPTY}
           else {})
  }

  ghost predicate RenamePathContractFields(fs: FileSystem, source: Path, target: Path, ok: bool, err: int, fs2: FileSystem)  {
    0 <= err && (ok <==> err == 0) &&
    (!ok ==> fs2 == fs && err in RenameFailureErrnosFields(fs, source, target)) &&
    (ok ==>
       (0 as char) !in source && (0 as char) !in target &&
       IsNonRootRawEntryPathFields(source) && IsNonRootRawEntryPathFields(target) &&
       match ResolvePathForRenameNoFollowTerminalFields(fs, source)
       case Err(_) => false
       case Ok(resolvedSource) =>
         match ResolvePathForRenameDestinationFields(fs, target)
         case Err(_) => false
         case Ok(resolvedTarget) =>
           FsContainsPath(fs, resolvedSource) &&
           if InodeSameObject(fs, resolvedSource, resolvedTarget) then fs2 == fs
           else
             resolvedSource != resolvedTarget &&
             !HasPathPrefix(resolvedSource, resolvedTarget) &&
             RenameKindCompatible(fs, resolvedSource, resolvedTarget) &&
             exists transitionNow: int, sourceParentStorage: StorageInfo, targetParentStorage: StorageInfo ::
               DirectoryStorageObservationFields(sourceParentStorage) &&
               DirectoryStorageObservationFields(targetParentStorage) &&
               fs2 == RenameFsWithMetadataFields(fs, resolvedSource, resolvedTarget,
                                                 transitionNow, sourceParentStorage, targetParentStorage))
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
  ghost predicate ReadFileSpec(
    beforeFs: FileSystem,
    beforeTrustedStreams: (TrustedStreamRequest) -> TrustedStreamResult,
    path: Path,
    data: Bytes,
    err: int,
    stage: FileReadStage
  )
  {
    TrustedReadFileContractFields(
      beforeTrustedStreams, beforeFs, path, data, err, stage
    )
  }

  ghost predicate OpenReadFileSpec(
    beforeFs: FileSystem,
    beforeTrustedStreams: (TrustedStreamRequest) -> TrustedStreamResult,
    path: Path,
    data: Bytes,
    err: int,
    stage: FileReadStage
  )
  {
    TrustedOpenReadFileContractFields(
      beforeTrustedStreams, beforeFs, path, data, err, stage
    )
  }

  ghost function ObservedReadLinkResultFields(
    fs: FileSystem, failures: (NativeFailureRequest) -> int, path: Path
  ): IOResult<Path>
  {
    var err := failures(ReadLinkRequest(fs, path));
    if err == 0 then ReadLinkResultFields(fs, path)
    else Result.Err(NativeFailure(err, CLocaleErrnoTextResult(err)))
  }

  ghost function ObservedReadLinkAtCwdResultFields(
    fs: FileSystem, context: CwdContext, failures: (NativeFailureRequest) -> int, path: Path
  ): IOResult<Path>
  {
    var err := failures(ReadLinkAtCwdRequest(fs,context,path));
    if err == 0 then ReadLinkFromCwdContextResultFields(fs,context,path)
    else Result.Err(NativeFailure(err,CLocaleErrnoTextResult(err)))
  }

  ghost predicate ReadLinkAtCwdSpec(
    beforeFs: FileSystem, beforeContext: CwdContext, failures: (NativeFailureRequest) -> int,
    path: Path, result: IOResult<Path>)
  {
    NativeFailureContractFields(failures,ReadLinkAtCwdRequest(beforeFs,beforeContext,path),ResultErrno(result)) &&
    result == ObservedReadLinkAtCwdResultFields(beforeFs,beforeContext,failures,path)
  }

  ghost predicate ReadLinkSpec(
    beforeFs: FileSystem, failures: (NativeFailureRequest) -> int,
    path: Path, r: IOResult<Path>
  )
  {
    NativeFailureContractFields(failures, ReadLinkRequest(beforeFs, path), ResultErrno(r)) &&
    r == ObservedReadLinkResultFields(beforeFs, failures, path)
  }

  ghost predicate ReadStdinAllSpec(beforeStdin: Bytes, afterStdin: Bytes, b: Bytes)
  {
    ReadStdinAllFields(beforeStdin, afterStdin, b)
  }

  ghost predicate ReadStdinSpec(
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

  ghost predicate WriteStdoutSpec(
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

  ghost predicate WriteStderrSpec(
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



  ghost predicate GetEnvSpec(beforeEnv: Environment, key: string, r: IOResult<string>)
  {
    GetEnvContractFields(beforeEnv, key, r)
  }

  ghost predicate GetEnvironmentSpec(beforeEnv: Environment, entries: seq<string>)
    requires ValidEnvironment(beforeEnv)
  {
    GetEnvironmentContractFields(beforeEnv, entries)
  }

  ghost predicate GetLoginNameSpec(beforeProps: map<string, string>, r: IOResult<string>)
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
    beforeFs: FileSystem, beforeProps: map<string, string>, beforeNow: int,
    beforeCredentials: ProcessCredentials,
    beforeTrustedFilesystem: (TrustedFilesystemRequest) -> TrustedFilesystemResult,
    afterFs: FileSystem, path: Path, data: Bytes, ok: bool, err: int,
    committed: nat, stage: FileWriteStage,
    requestedCreateMode: bv32 := CREATE_FILE_MODE
  )
  {
    var request := FilesystemWrite(beforeFs, path, data, beforeNow, beforeProps, beforeCredentials, requestedCreateMode);
    var observed := beforeTrustedFilesystem(request);
    ValidFilesystemObservation(request, observed) &&
    ok == observed.ok && err == observed.err && afterFs == observed.postFs &&
    committed == observed.writeCommitted && stage == observed.writeStage
  }

  ghost predicate AppendFileSpec(
    beforeFs: FileSystem, beforeProps: map<string, string>, beforeNow: int,
    beforeCredentials: ProcessCredentials,
    beforeTrustedFilesystem: (TrustedFilesystemRequest) -> TrustedFilesystemResult,
    afterFs: FileSystem, path: Path, data: Bytes, ok: bool, err: int,
    committed: nat, stage: FileWriteStage
  )
  {
    var request := FilesystemAppend(beforeFs, path, data, beforeNow, beforeProps, beforeCredentials);
    var observed := beforeTrustedFilesystem(request);
    ValidFilesystemObservation(request, observed) &&
    ok == observed.ok && err == observed.err && afterFs == observed.postFs &&
    committed == observed.writeCommitted && stage == observed.writeStage
  }

  ghost predicate CreateSymlinkSpec(
    beforeFs: FileSystem,
    beforeNow: int,
    beforeCredentials: ProcessCredentials,
    failures: (NativeFailureRequest) -> int,
    afterFs: FileSystem,
    path: Path,
    target: Path,
    ok: bool,
    err: int
  )
  {
    NativeFailureContractFields(failures, CreateSymlinkRequest(beforeFs, beforeNow, path, target), err) &&
    CreateSymlinkWithCredentialsContractFields(
      beforeFs, beforeNow, beforeCredentials, path, target, ok, err, afterFs
    ) &&
    CreateSymlinkContractFields(beforeFs, beforeNow, path, target, ok, err, afterFs)
  }

  ghost predicate DeletePathSpec(
    beforeFs: FileSystem,
    beforeNow: int,
    failures: (NativeFailureRequest) -> int,
    afterFs: FileSystem,
    path: Path,
    ok: bool,
    err: int
  )
  {
    NativeFailureContractFields(failures, DeletePathRequest(beforeFs, path), err) &&
    DeletePathWithChangeTimeContractFields(
      beforeFs, beforeNow, path, ok, err, afterFs
    ) &&
    DeletePathContractFields(beforeFs, path, ok, err, afterFs)
  }

  // mkdir accepts trailing slashes, but does not follow a terminal symlink.
  // Preserve raw dot components until the existing resolver processes them.
  ghost function ResolveDirectoryCreationPathFields(fs: FileSystem, path: Path): IOResult<Path>
  {
    if path == "" || (0 as char) in path then
      Result.Err(InvalidPath)
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

  // Path lookup may read a symlink without changing its target or inode identity.
  ghost predicate TraversalRecordEffectFields(before: InodeRecord, after: InodeRecord)
  {
    if before.node.Symlink? then
      var times := NodeTimes(before.node);
      var observed := NodeTimes(after.node);
      after == before.(node := WithNodeTimes(before.node,
                                             times.(atimeSec := observed.atimeSec, atimeNsec := observed.atimeNsec)))
    else after == before
  }

  ghost predicate ParentDirectoryEffectFields(before: InodeRecord, after: InodeRecord)
  {
    before.node.Directory? && after.node.Directory? &&
    after.hostKey == before.hostKey && after.ownership == before.ownership &&
    after.kind == before.kind && after.node.mode == before.node.mode &&
    after.node.ext == before.node.ext
  }

  // Successful removal changes one namespace entry, preserving surviving aliases.
  // Parent metadata and the removed inode's ctime remain native observations.
  ghost predicate EntryRemovalEffectFields(
    before: FileSystem, path: Path, directory: bool, after: FileSystem
  )
  {
    var resolved := if directory then ResolveDirectoryCreationPathFields(before, path)
                    else ResolvePathForMetadataFields(before, path, false);
    match resolved
    case Err(_) => false
    case Ok(target) =>
      FsContainsPath(before, target) &&
      FsContainsPath(before, ParentPath(target)) &&
      InodeTreeCanRemove(before.inodes, before.namespace, PathSegments(target)) &&
      (if directory then
         FsNodeAt(before, target).Directory? && HasNoDescendants(before, target)
       else !FsNodeAt(before, target).Directory?) &&
      var id := FsIdAt(before, target);
      var parentId := FsIdAt(before, ParentPath(target));
      id != parentId &&
      after.namespace == InodeTreeRemoveSegments(before.namespace, PathSegments(target)) &&
      after.inodes.Keys == (if InodeNamespaceRefCount(before.namespace, id) == 1
                            then before.inodes.Keys - {id} else before.inodes.Keys) &&
      (forall oldId | oldId in after.inodes ::
         if oldId == parentId then
           ParentDirectoryEffectFields(before.inodes[oldId], after.inodes[oldId])
         else if oldId == id then
           var prior := before.inodes[oldId];
           var observed := after.inodes[oldId];
           var times := NodeTimes(prior.node);
           var observedTimes := NodeTimes(observed.node);
           observed == prior.(
           links := (match prior.links
                               case LinkCountUnknown => LinkCountUnknown
                               case LinkCountKnown(count) => LinkCountKnown(if count == 0 then 0 else count - 1)),
           node := WithNodeTimes(prior.node,
                                 times.(ctimeSec := observedTimes.ctimeSec, ctimeNsec := observedTimes.ctimeNsec,
                                 atimeSec := (if prior.node.Symlink? then observedTimes.atimeSec else times.atimeSec),
                                 atimeNsec := (if prior.node.Symlink? then observedTimes.atimeNsec else times.atimeNsec))))
         else TraversalRecordEffectFields(before.inodes[oldId], after.inodes[oldId]))
  }

  // link/linkat add a namespace alias to the selected existing inode.
  ghost predicate HardLinkEffectFields(before: FileSystem, source: Path, target: Path,
                                       followSource: bool, after: FileSystem)
  {
    match ResolvePathForMetadataFields(before,source,followSource)
    case Err(_) => false
    case Ok(existing) =>
      match ResolvePathForCreateNoFollowTerminalFields(before,target)
      case Err(_) => false
      case Ok(destination) =>
        FsContainsPath(before,existing) && !FsNodeAt(before,existing).Directory? &&
        !FsContainsPath(before,destination) && FsContainsPath(before,ParentPath(destination)) &&
        InodeTreeCanInsert(before.inodes,before.namespace,PathSegments(destination)) &&
        var id := FsIdAt(before,existing);
        var parentId := FsIdAt(before,ParentPath(destination));
        after.namespace == InodeTreeSetSubtreeSegments(before.namespace,PathSegments(destination),InodeTreeNode(id,map[])) &&
        after.inodes.Keys == before.inodes.Keys &&
        (forall oldId | oldId in before.inodes ::
           if oldId == id then
             var prior := before.inodes[id];
             var observed := after.inodes[id];
             var times := NodeTimes(prior.node);
             var observedTimes := NodeTimes(observed.node);
             observed == prior.(
             links := (match prior.links
                                 case LinkCountUnknown => LinkCountUnknown
                                 case LinkCountKnown(count) => LinkCountKnown(count + 1)),
             node := WithNodeTimes(prior.node,
                                   times.(ctimeSec := observedTimes.ctimeSec,ctimeNsec := observedTimes.ctimeNsec,
                                   atimeSec := (if prior.node.Symlink? then observedTimes.atimeSec else times.atimeSec),
                                   atimeNsec := (if prior.node.Symlink? then observedTimes.atimeNsec else times.atimeNsec))))
           else if oldId == parentId then ParentDirectoryEffectFields(before.inodes[oldId],after.inodes[oldId])
           else TraversalRecordEffectFields(before.inodes[oldId],after.inodes[oldId]))
  }

  ghost predicate TruncatedContentsFields(before: Bytes, size: nat, after: Bytes)
  {
    |after| == size &&
    (forall i :: 0 <= i < size ==>
                   after[i] == (if i < |before| then before[i] else (0 as char)))
  }

  // Truncation changes the existing inode, so every hard-link alias sees the
  // same preserved prefix or zero-filled extension. It never creates a path.
  ghost predicate TruncationEffectFields(
    before: FileSystem, path: Path, size: nat, after: FileSystem
  )
  {
    match ResolvePathForMetadataFields(before, path, true)
    case Err(_) => false
    case Ok(target) =>
      FsContainsPath(before, target) && FsNodeAt(before, target).Regular? &&
      after.namespace == before.namespace && after.inodes.Keys == before.inodes.Keys &&
      var id := FsIdAt(before, target);
      var prior := before.inodes[id];
      var observed := after.inodes[id];
      observed.node.Regular? && observed.hostKey == prior.hostKey &&
      observed.links == prior.links && observed.ownership == prior.ownership &&
      observed.kind == prior.kind && observed.node.ext == prior.node.ext &&
      TruncatedContentsFields(prior.node.data, size, observed.node.data) &&
      // Linux may clear set-ID bits. The other permission bits are preserved.
      (observed.node.mode & (1023 as bv32)) == (prior.node.mode & (1023 as bv32)) &&
      (observed.node.mode & (3072 as bv32) & (prior.node.mode ^ ALL_MODE_BITS)) == (0 as bv32) &&
      observed.node.times.atimeSec == prior.node.times.atimeSec &&
      observed.node.times.atimeNsec == prior.node.times.atimeNsec &&
      (forall other | other in before.inodes && other != id ::
         TraversalRecordEffectFields(before.inodes[other], after.inodes[other]))
  }

  // Lookup may fail because of storage, allocation, access-control or name-limit
  // conditions absent from the inode model. These are Linux lookup errors, not
  // an arbitrary substitute for a modeled ENOENT/ENOTDIR/ELOOP cause.
  const NativeLookupFaultErrnos: set<int> := {Errno.EIO, Errno.ENOMEM, Errno.EACCES, Errno.ENAMETOOLONG}
  const NativeMutationFaultErrnos: set<int> := {Errno.EPERM, Errno.EIO, Errno.ENOMEM, Errno.EACCES, Errno.ENOSPC, Errno.EROFS, Errno.EDQUOT}

  ghost function LookupFailureErrnosFields(fs: FileSystem, path: Path, follow: bool): set<int>
  {
    NativeLookupFaultErrnos +
    (match ResolvePathForMetadataFields(fs, path, follow)
     case Err(error) => {IOErrorErrno(error)}
     case Ok(_) => {})
  }

  ghost function HardLinkFailureErrnosFields(fs: FileSystem, source: Path, target: Path, followSource: bool := false): set<int>
  {
    if (0 as char) in source || (0 as char) in target then {Errno.EINVAL}
    else
      match ResolvePathForMetadataFields(fs, source, followSource)
      case Err(error) => NativeLookupFaultErrnos + {IOErrorErrno(error)}
      case Ok(resolvedSource) =>
        if target == "" then NativeLookupFaultErrnos + {Errno.ENOENT}
        else
          match ResolvePathForCreateNoFollowTerminalFields(fs, target)
          case Err(error) => NativeLookupFaultErrnos + {IOErrorErrno(error)}
          case Ok(resolvedTarget) =>
            if FsContainsPath(fs, resolvedTarget) then NativeLookupFaultErrnos + {Errno.EEXIST}
            else if FsNodeAt(fs, resolvedSource).Directory? then NativeLookupFaultErrnos + {Errno.EPERM}
            else NativeMutationFaultErrnos + {Errno.EXDEV, Errno.EMLINK}
  }

  ghost function EntryRemovalFailureErrnosFields(fs: FileSystem, path: Path, directory: bool): set<int>
  {
    if path == "" then NativeLookupFaultErrnos + {Errno.ENOENT}
    else if (0 as char) in path then {Errno.EINVAL}
    else
      var entry := BuildPath(IsAbsolutePath(path), RawPathSegmentsFields(path));
      match ResolvePathForMetadataFields(fs, entry, false)
      case Err(error) => NativeLookupFaultErrnos + {IOErrorErrno(error)}
      case Ok(target) =>
        if directory then
          if !FsNodeAt(fs, target).Directory? then NativeLookupFaultErrnos + {Errno.ENOTDIR}
          else NativeMutationFaultErrnos + {Errno.EBUSY, Errno.EINVAL, Errno.ENOTEMPTY}
        else if HasTrailingSlash(path) && FsNodeAt(fs, target).Symlink? then
          NativeLookupFaultErrnos + {Errno.ENOTDIR}
        else if HasTrailingSlash(path) && !FsNodeAt(fs, target).Directory? then
          NativeLookupFaultErrnos + {Errno.ENOTDIR}
        else if FsNodeAt(fs, target).Directory? then NativeLookupFaultErrnos + {Errno.EISDIR}
        else NativeMutationFaultErrnos + {Errno.EBUSY}
  }

  function FilesystemRequestHasInvalidAbiPath(request: TrustedFilesystemRequest): bool
  {
    if request.FilesystemCreateHardLink? then
      (0 as char) in request.source || (0 as char) in request.hardLinkTarget
    else if request.FilesystemSync? then
      request.syncTarget.PathSyncTarget? && (0 as char) in request.syncTarget.path
    else (0 as char) in request.path
  }

  ghost function FilesystemFailureErrnosFields(request: TrustedFilesystemRequest): set<int>
  {
    if FilesystemRequestHasInvalidAbiPath(request) then {Errno.EINVAL} else
    match request
    case FilesystemQuery(fs, path, follow) => LookupFailureErrnosFields(fs, path, follow) + {Errno.EOVERFLOW}
    case FilesystemCreate(fs, path, _) =>
      NativeMutationFaultErrnos + NativeLookupFaultErrnos + {Errno.EINTR, Errno.EBADF, Errno.ENFILE, Errno.EMFILE} +
      (if CreateFileFailureErrFields(fs, path) == 0 then {}
       else {CreateFileFailureErrFields(fs, path)})
    case FilesystemSetTimes(fs, path, follow, _, atime, mtime) =>
      LookupFailureErrnosFields(fs, path, follow) + NativeMutationFaultErrnos + {Errno.EINVAL, Errno.EOVERFLOW} +
      (if !TimestampUpdateValidFields(atime) || !TimestampUpdateValidFields(mtime) then {Errno.EINVAL} else {})
    case FilesystemCreateHardLink(fs, source, target, _, followSource) =>
      HardLinkFailureErrnosFields(fs, source, target, followSource)
    case FilesystemUnlink(fs, path, _) => EntryRemovalFailureErrnosFields(fs, path, false)
    case FilesystemRemoveDirectory(fs, path, _) => EntryRemovalFailureErrnosFields(fs, path, true)
    case FilesystemCreateDirectory(fs, path, _, _, _) =>
      NativeMutationFaultErrnos + NativeLookupFaultErrnos +
      (if path == "" then {Errno.ENOENT}
       else match ResolveDirectoryCreationPathFields(fs, path)
            case Err(error) => {IOErrorErrno(error)}
            case Ok(target) => if FsContainsPath(fs, target) then {Errno.EEXIST} else {})
    case FilesystemTruncate(fs, path, _, _) =>
      LookupFailureErrnosFields(fs, path, true) + NativeMutationFaultErrnos + {Errno.EINVAL, Errno.EFBIG} +
      (match ResolvePathForMetadataFields(fs, path, true)
       case Err(_) => {}
       case Ok(target) => if FsNodeAt(fs, target).Directory? then {Errno.EISDIR} else {})
    case FilesystemCreateSpecialNode(fs, path, _, _, _, _, _, _) =>
      NativeMutationFaultErrnos + NativeLookupFaultErrnos + {Errno.EINVAL} +
      (if path == "" then {Errno.ENOENT}
       else match ResolveDirectoryCreationPathFields(fs, path)
            case Err(error) => {IOErrorErrno(error)}
            case Ok(target) => if FsContainsPath(fs, target) then {Errno.EEXIST} else {})
    case FilesystemWrite(fs, path, _, _, _, _, _) =>
      WriteOpenFailureErrnosFields(fs, path) + {Errno.EINTR, Errno.EIO, Errno.EBADF, Errno.EFBIG, Errno.ENOSPC, Errno.EROFS, Errno.EPIPE, Errno.EDQUOT}
    case FilesystemAppend(fs, path, _, _, _, _) =>
      WriteOpenFailureErrnosFields(fs, path) + {Errno.EINTR, Errno.EIO, Errno.EBADF, Errno.EFBIG, Errno.ENOSPC, Errno.EROFS, Errno.EPIPE, Errno.EDQUOT}
    case FilesystemSync(fs, target, _) =>
      {Errno.EINTR, Errno.EIO, Errno.EBADF, Errno.EINVAL, Errno.ENFILE, Errno.EMFILE, Errno.ENOSPC, Errno.EROFS} +
      (if target.PathSyncTarget? then LookupFailureErrnosFields(fs, target.path, true) else {})
  }

  // Failed atomic mutations preserve entries and inode records. Path traversal
  // can refresh symlink access times even when the terminal mutation fails.
  ghost predicate FailedFilesystemEffectFields(before: FileSystem, after: FileSystem)
  {
    before.namespace == after.namespace && before.inodes.Keys == after.inodes.Keys &&
    (forall id | id in before.inodes ::
       if before.inodes[id].node.Symlink? then
         var times := NodeTimes(before.inodes[id].node);
         var observedTimes := NodeTimes(after.inodes[id].node);
         after.inodes[id] == before.inodes[id].(
         node := WithNodeTimes(before.inodes[id].node,
                               times.(atimeSec := observedTimes.atimeSec, atimeNsec := observedTimes.atimeNsec)))
       else after.inodes[id] == before.inodes[id])
  }

  ghost predicate FilesystemRequestCanSucceedFields(request: TrustedFilesystemRequest)
  {
    !FilesystemRequestHasInvalidAbiPath(request) &&
    match request
    case FilesystemQuery(fs, path, follow) =>
      ResolvePathForMetadataFields(fs, path, follow).Ok?
    case FilesystemCreate(fs, path, _) => CreateFileFailureErrFields(fs, path) == 0
    case FilesystemSetTimes(fs, path, follow, _, atime, mtime) =>
      ResolvePathForMetadataFields(fs, path, follow).Ok? &&
      TimestampUpdateValidFields(atime) && TimestampUpdateValidFields(mtime)
    case FilesystemCreateHardLink(fs, source, target, _, followSource) =>
      target != "" && (0 as char) !in source && (0 as char) !in target &&
      (match ResolvePathForMetadataFields(fs, source, followSource)
       case Err(_) => false
       case Ok(resolvedSource) =>
         !FsNodeAt(fs, resolvedSource).Directory? &&
         (match ResolvePathForCreateNoFollowTerminalFields(fs, target)
          case Err(_) => false
          case Ok(resolvedTarget) => !FsContainsPath(fs, resolvedTarget)))
    case FilesystemUnlink(fs, path, _) =>
      path != "" && !HasTrailingSlash(path) &&
      (match ResolvePathForMetadataFields(fs, path, false)
       case Err(_) => false
       case Ok(target) => !FsNodeAt(fs, target).Directory?)
    case FilesystemRemoveDirectory(fs, path, _) =>
      path != "" && !HasRawTerminalSpecialFields(path) &&
      (match ResolveDirectoryCreationPathFields(fs, path)
       case Err(_) => false
       case Ok(target) =>
         FsContainsPath(fs, target) && FsNodeAt(fs, target).Directory? &&
         HasNoDescendants(fs, target))
    case FilesystemCreateDirectory(fs, path, _, _, _) =>
      path != "" &&
      (match ResolveDirectoryCreationPathFields(fs, path)
       case Err(_) => false
       case Ok(target) => !FsContainsPath(fs, target))
    case FilesystemCreateSpecialNode(fs, path, _, _, _, _, _, _) =>
      path != "" &&
      (match ResolveDirectoryCreationPathFields(fs, path)
       case Err(_) => false
       case Ok(target) => !FsContainsPath(fs, target))
    case FilesystemTruncate(fs, path, _, _) =>
      (match ResolvePathForMetadataFields(fs, path, true)
       case Err(_) => false
       case Ok(target) => FsNodeAt(fs, target).Regular?)
    case FilesystemWrite(fs, path, _, _, _, _, _) => WriteFileFailureErrFields(fs, path) == 0
    case FilesystemAppend(fs, path, _, _, _, _) => WriteFileFailureErrFields(fs, path) == 0
    case FilesystemSync(fs, target, mode) =>
      if target.AllSyncTargets? then mode == SyncAllFilesystems
      else mode != SyncAllFilesystems && ResolvePathForMetadataFields(fs, target.path, true).Ok?
  }

  // Metadata observations may refresh times, but cannot invent an identity or kind.
  ghost predicate FilesystemQueryShapeFields(request: TrustedFilesystemRequest,
                                             result: TrustedFilesystemResult)
  {
    request.FilesystemQuery? && result.ok ==>
      match ResolvePathForMetadataFields(request.preFs, request.path, request.followSymlink)
      case Err(_) => false
      case Ok(target) =>
        FsContainsPath(request.preFs, target) &&
        var record := request.preFs.inodes[FsIdAt(request.preFs, target)];
        result.isDir == record.node.Directory? &&
        result.isSymlink == record.node.Symlink? &&
        HostInodeKey(result.device, result.inode) == record.hostKey &&
        0 <= result.linkCount && record.links == LinkCountKnown(result.linkCount as nat)
  }

  ghost predicate ValidFilesystemObservation(
    request: TrustedFilesystemRequest, result: TrustedFilesystemResult
  )
  {
    0 <= result.err && (result.ok <==> result.err == 0) &&
    FilesystemQueryShapeFields(request, result) &&
    (result.ok ==> FilesystemRequestCanSucceedFields(request)) &&
    (!result.ok ==> result.err in FilesystemFailureErrnosFields(request)) &&
    (request.FilesystemQuery? || request.FilesystemSync? ==> result.postFs == request.preFs) &&
    (request.FilesystemCreate? ==>
       if result.ok then
         CreateFileContractFields(request.preFs, request.now, request.path, true, 0, result.postFs)
       else
         FailedFilesystemEffectFields(request.preFs, result.postFs) ||
         (result.err in {Errno.EINTR, Errno.EIO, Errno.EBADF, Errno.ENOSPC, Errno.EDQUOT} &&
          CreateFileContractFields(request.preFs, request.now, request.path, true, 0, result.postFs))) &&
    ((!result.ok && !request.FilesystemAppend? && !request.FilesystemWrite? && !request.FilesystemCreate?) ==>
       FailedFilesystemEffectFields(request.preFs, result.postFs)) &&
    (request.FilesystemCreateHardLink? && result.ok ==>
       HardLinkEffectFields(request.preFs,request.source,request.hardLinkTarget,request.followSource,result.postFs)) &&
    (request.FilesystemCreateDirectory? && result.ok ==>
       DirectoryCreationEffectFields(request.preFs, request.path, result.postFs)) &&
    (request.FilesystemUnlink? && result.ok ==>
       EntryRemovalEffectFields(request.preFs, request.path, false, result.postFs)) &&
    (request.FilesystemRemoveDirectory? && result.ok ==>
       EntryRemovalEffectFields(request.preFs, request.path, true, result.postFs)) &&
    (request.FilesystemTruncate? && result.ok ==>
       TruncationEffectFields(request.preFs, request.path, request.size, result.postFs)) &&
    (request.FilesystemWrite? || request.FilesystemAppend? ==>
       WriteFileOutcomeFields(request.preFs, request.now, request.path, request.data,
                              request.FilesystemAppend?, result.ok, result.err, result.writeCommitted, result.writeStage, result.postFs) &&
       CreatedRegularOwnershipFields(request.preFs, request.credentials, request.path,
                                     result.writeStage != WriteOpenFailed, result.postFs) &&
       (if request.FilesystemWrite? then
          CreatedRegularRequestedModeFields(request.preFs, request.props, request.path,
                                            result.writeStage != WriteOpenFailed, result.postFs, request.requestedCreateMode)
        else CreatedRegularModeFields(request.preFs, request.props, request.path,
                                      result.writeStage != WriteOpenFailed, result.postFs)))
  }

  // Construct an admissible failure for the subtype witness. This ghost choice
  // never replaces the native errno returned by an executable operation.
  ghost function FilesystemFailureWitness(request: TrustedFilesystemRequest): (result: TrustedFilesystemResult)
    ensures ValidFilesystemObservation(request, result)
  {
    TrustedFilesystemResult(false,
                            if Errno.EIO in FilesystemFailureErrnosFields(request) then Errno.EIO else Errno.EINVAL,
                            request.preFs, 0, 0, 0, 0, false, false, 0, 0, 0, 0, WriteOpenFailed)
  }

  // Validate the provider itself so stronger extern contracts do not silently
  // contradict arbitrary observations. EIO represents an actual native I/O fault.
  type ValidFilesystemObservations =
    observations: ((TrustedFilesystemRequest) -> TrustedFilesystemResult) |
      (forall request :: ValidFilesystemObservation(request, observations(request)))
    ghost witness (request: TrustedFilesystemRequest) => FilesystemFailureWitness(request)

  ghost predicate CreateDirectorySpec(
    beforeFs: FileSystem,
    beforeNow: int,
    beforeTrustedFilesystem: ValidFilesystemObservations,
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
    err: int,
    followSource: bool := false
  )
  {
    TrustedFilesystemEffectContractFields(
      beforeTrustedFilesystem,
      FilesystemCreateHardLink(beforeFs, source, target, beforeNow, followSource),
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
    failures: (NativeFailureRequest) -> int,
    afterStdoutTimestamp: StdoutTimestampState,
    ok: bool,
    err: int
  )
  {
    NativeFailureContractFields(failures, StdoutTimesRequest(beforeStdoutTimestamp, beforeNow, Current, Current), err) &&
    SetStdoutTimesContractFields(
      beforeStdoutTimestamp, afterStdoutTimestamp, beforeNow, Current, Current,
      ok, err
    )
  }

  ghost predicate SetStdoutAccessTimeNowSpec(
    beforeNow: int,
    beforeStdoutTimestamp: StdoutTimestampState,
    failures: (NativeFailureRequest) -> int,
    afterStdoutTimestamp: StdoutTimestampState,
    ok: bool,
    err: int
  )
  {
    NativeFailureContractFields(failures, StdoutTimesRequest(beforeStdoutTimestamp, beforeNow, Current, Keep), err) &&
    SetStdoutTimesContractFields(
      beforeStdoutTimestamp, afterStdoutTimestamp, beforeNow, Current, Keep,
      ok, err
    )
  }

  ghost predicate SetStdoutModificationTimeNowSpec(
    beforeNow: int,
    beforeStdoutTimestamp: StdoutTimestampState,
    failures: (NativeFailureRequest) -> int,
    afterStdoutTimestamp: StdoutTimestampState,
    ok: bool,
    err: int
  )
  {
    NativeFailureContractFields(failures, StdoutTimesRequest(beforeStdoutTimestamp, beforeNow, Keep, Current), err) &&
    SetStdoutTimesContractFields(
      beforeStdoutTimestamp, afterStdoutTimestamp, beforeNow, Keep, Current,
      ok, err
    )
  }

  ghost predicate SetStdoutTimesSpec(
    beforeNow: int,
    beforeStdoutTimestamp: StdoutTimestampState,
    failures: (NativeFailureRequest) -> int,
    afterStdoutTimestamp: StdoutTimestampState,
    atime: TimestampUpdate,
    mtime: TimestampUpdate,
    ok: bool,
    err: int
  )
  {
    NativeFailureContractFields(failures, StdoutTimesRequest(beforeStdoutTimestamp, beforeNow, atime, mtime), err) &&
    SetStdoutTimesContractFields(
      beforeStdoutTimestamp, afterStdoutTimestamp, beforeNow,
      atime, mtime, ok, err
    )
  }

  ghost predicate GetFileModeSpec(
    beforeFs: FileSystem,
    beforeNativeFailures: (NativeFailureRequest) -> int,
    path: Path,
    followSymlink: bool,
    ok: bool,
    mode: bv32,
    err: int
  )
  {
    NativeFailureContractFields(beforeNativeFailures,
                                MetadataQueryRequest(beforeFs, path, followSymlink, ModeQuery), err) &&
    GetFileModeContractFields(beforeFs, path, followSymlink, ok, mode, err)
  }

  ghost predicate GetFileStatusAtDirSpec(
    observations: StatusTimeObservations, failures: (NativeFailureRequest) -> int,
    beforeCursor: nat, afterCursor: nat, beforeFs: FileSystem, beforeContext: CwdContext,
    parent: int, path: Path, followSymlink: bool, ok: bool, status: FileStatus, err: int)
  {
    afterCursor == beforeCursor+1 &&
    ObservedNativeFileStatusAtDirContractFields(observations,failures,beforeCursor,
                                                beforeFs,beforeContext,parent,path,followSymlink,ok,status,err) &&
    GetFileStatusAtDirContextStructureContractFields(
      beforeFs,beforeContext,parent,path,followSymlink,ok,status,err)
  }

  ghost predicate SetFileModeAtDirSpec(
    beforeFs: FileSystem, beforeContext: CwdContext, beforeNow: int,
    failures: (NativeFailureRequest) -> int, afterFs: FileSystem, afterContext: CwdContext,
    parent: int, path: Path, followSymlink: bool, mode: bv32, ok: bool, err: int)
  {
    NativeFailureContractFields(failures,SetModeAtDirRequest(beforeFs,beforeNow,beforeContext,parent,path,followSymlink,mode),err) &&
    SetFileModeFromCwdTargetContractFields(beforeFs,beforeContext,beforeNow,afterFs,afterContext,
                                           ResolvePathAtDirContextForMetadataFields(beforeFs,beforeContext,parent,path,followSymlink),mode,ok,err)
  }

  ghost predicate OpenDirAtDirSpec(
    beforeFs: FileSystem, beforeContext: CwdContext, failures: (NativeFailureRequest) -> int,
    afterContext: CwdContext, parent: int, path: Path, includeDots: bool, ok: bool, handle: int, err: int)
  {
    NativeFailureContractFields(failures,OpenDirectoryAtDirRequest(beforeFs,beforeContext,parent,path,includeDots),err) &&
    OpenDirFromCwdTargetContractFields(beforeFs,beforeContext,afterContext,
                                       ResolvePathAtDirContextForMetadataFields(beforeFs,beforeContext,parent,path,true),includeDots,ok,handle,err)
  }

  ghost predicate GetFileStatusAtCwdSpec(
    observations: StatusTimeObservations, failures: (NativeFailureRequest) -> int,
    beforeCursor: nat, afterCursor: nat, beforeFs: FileSystem, beforeContext: CwdContext,
    path: Path, followSymlink: bool, ok: bool, status: FileStatus, err: int)
  {
    afterCursor == beforeCursor+1 &&
    ObservedNativeFileStatusAtCwdContractFields(observations,failures,beforeCursor,
                                                beforeFs,beforeContext,path,followSymlink,ok,status,err) &&
    GetFileStatusAtCwdStructureContractFields(
      beforeFs,beforeContext,path,followSymlink,ok,status,err)
  }

  ghost predicate SetFileModeAtCwdSpec(
    beforeFs: FileSystem, beforeContext: CwdContext, beforeNow: int,
    failures: (NativeFailureRequest) -> int, afterFs: FileSystem, afterContext: CwdContext,
    path: Path, followSymlink: bool, mode: bv32, ok: bool, err: int)
  {
    NativeFailureContractFields(failures,SetModeAtCwdRequest(beforeFs,beforeContext,beforeNow,path,followSymlink,mode),err) &&
    SetFileModeFromCwdTargetContractFields(beforeFs,beforeContext,beforeNow,afterFs,afterContext,
                                           ResolvePathAtCwdForMetadataFields(beforeFs,beforeContext,path,followSymlink),mode,ok,err)
  }

  ghost predicate OpenDirAtCwdSpec(
    beforeFs: FileSystem, beforeContext: CwdContext, failures: (NativeFailureRequest) -> int,
    afterContext: CwdContext, path: Path, includeDots: bool, ok: bool, handle: int, err: int)
  {
    NativeFailureContractFields(failures,OpenDirectoryAtCwdRequest(beforeFs,beforeContext,path,includeDots),err) &&
    OpenDirFromCwdTargetContractFields(beforeFs,beforeContext,afterContext,
                                       ResolvePathAtCwdForMetadataFields(beforeFs,beforeContext,path,true),includeDots,ok,handle,err)
  }

  ghost function CapabilityStatusObservationPathFields(context: CwdContext, handle: int): Path
  {
    if handle in context.capabilities && context.capabilities[handle].position in context.topology.nodes &&
       |context.topology.nodes[context.capabilities[handle].position].pathname| == 1
    then context.topology.nodes[context.capabilities[handle].position].pathname[0] else ""
  }

  ghost function ObservedOpenDirectoryCapabilityResultFields(observations: StatusTimeObservations,
                                                             failures: (NativeFailureRequest) -> int, ordinal: nat, fs: FileSystem, context: CwdContext,
                                                             handle: int): IOResult<FileStatus>
  {
    var err := failures(CapabilityStatusRequest(ordinal,fs,context,handle));
    if err != 0 then Result.Err(NativeFailure(err,CLocaleErrnoTextResult(err)))
    else match GetOpenDirectoryCapabilityResultFields(fs,context,handle)
         case Err(error) => Result.Err(error)
         case Ok(status) => Result.Ok(status.(times :=
                                      observations(ordinal,fs,CapabilityStatusObservationPathFields(context,handle),true)))
  }

  ghost predicate GetOpenDirectoryCapabilityStatusSpec(observations: StatusTimeObservations,
                                                       failures: (NativeFailureRequest) -> int, beforeCursor: nat, afterCursor: nat,
                                                       fs: FileSystem, context: CwdContext, handle: int, ok: bool, status: FileStatus, err: int)
  {
    0 <= err && (ok <==> err == 0) && afterCursor == beforeCursor+1 &&
    NativeFailureContractFields(failures,CapabilityStatusRequest(beforeCursor,fs,context,handle),err) &&
    match ObservedOpenDirectoryCapabilityResultFields(observations,failures,beforeCursor,fs,context,handle)
    case Ok(expected) => ok && status == expected && err == 0
    case Err(error) => !ok && err == IOErrorErrno(error)
  }

  ghost predicate GetFileStatusSpec(
    observations: StatusTimeObservations,
    failures: (NativeFailureRequest) -> int,
    beforeCursor: nat,
    afterCursor: nat,
    beforeFs: FileSystem,
    path: Path,
    followSymlink: bool,
    ok: bool,
    status: FileStatus,
    err: int
  )
  {
    afterCursor == beforeCursor + 1 &&
    ObservedNativeFileStatusContractFields(
      observations, failures, beforeCursor, beforeFs, path, followSymlink, ok, status, err) &&
    FileStatusStructureContractFields(beforeFs, path, followSymlink, ok, status, err)
  }

  ghost predicate SetFileModeSpec(
    beforeFs: FileSystem,
    beforeNow: int,
    failures: (NativeFailureRequest) -> int,
    afterFs: FileSystem,
    path: Path,
    followSymlink: bool,
    mode: bv32,
    ok: bool,
    err: int
  )
  {
    NativeFailureContractFields(failures, SetModeRequest(beforeFs, beforeNow, path, followSymlink, mode), err) &&
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
    failures: (NativeFailureRequest) -> int,
    afterDirHandles: map<int, DirHandleState>,
    path: Path,
    includeDots: bool,
    ok: bool,
    handle: int,
    err: int
  )
  {
    NativeFailureContractFields(failures, OpenDirectoryRequest(beforeFs, beforeDirHandles, path, includeDots), err) &&
    OpenDirContractFields(
      beforeFs, beforeDirHandles, path, includeDots,
      ok, handle, err, afterDirHandles
    )
  }

  ghost predicate ResolvePathIdentitySpec(
    beforeFs: FileSystem,
    beforeCwd: Path,
    failures: (NativeFailureRequest) -> int,
    path: Path,
    ok: bool,
    resolvedPath: Path,
    err: int
  )
  {
    NativeFailureContractFields(failures, ResolveIdentityRequest(beforeFs, beforeCwd, path), err) &&
    ResolvePathIdentityContractFields(
      beforeFs, beforeCwd, path, ok, resolvedPath, err
    )
  }

  ghost predicate ReadDirSpec(
    beforeFs: FileSystem,
    beforeDirHandles: map<int, DirHandleState>,
    failures: (NativeFailureRequest) -> int,
    afterDirHandles: map<int, DirHandleState>,
    handle: int,
    hasMore: bool,
    name: string,
    kind: DirectoryEntryKind,
    err: int
  )
  {
    NativeFailureContractFields(failures, ReadDirectoryRequest(beforeFs, beforeDirHandles, handle), err) &&
    ReadDirContractFields(
      beforeFs, beforeDirHandles, handle, hasMore, name, kind, err,
      afterDirHandles)
  }

  ghost predicate GetOpenDirectoryStatusSpec(
    observations: StatusTimeObservations,
    failures: (NativeFailureRequest) -> int,
    beforeCursor: nat,
    afterCursor: nat,
    beforeFs: FileSystem,
    beforeDirHandles: map<int, DirHandleState>,
    handle: int,
    ok: bool,
    status: FileStatus,
    err: int
  )
  {
    NativeFailureContractFields(failures,
                                OpenDirectoryStatusRequest(beforeCursor, beforeFs, beforeDirHandles, handle), err) &&
    GetOpenDirectoryStatusContractFields(
      observations, beforeCursor, afterCursor, beforeFs,
      beforeDirHandles, handle, ok, status, err)
  }

  ghost predicate CloseDirSpec(
    beforeDirHandles: map<int, DirHandleState>,
    failures: (NativeFailureRequest) -> int,
    afterDirHandles: map<int, DirHandleState>,
    handle: int, ok: bool, err: int
  )
  {
    NativeFailureContractFields(failures, CloseDirectoryRequest(beforeDirHandles, handle), err) &&
    CloseDirContractFields(beforeDirHandles, handle, ok, err, afterDirHandles)
  }

  ghost predicate IsDirectorySpec(
    beforeFs: FileSystem,
    failures: (NativeFailureRequest) -> int,
    path: Path,
    followSymlink: bool,
    ok: bool,
    isDir: bool,
    err: int
  )
  {
    NativeFailureContractFields(failures, MetadataQueryRequest(beforeFs, path, followSymlink, DirectoryQuery), err) &&
    IsDirectoryStrictContractFields(beforeFs, path, followSymlink, ok, isDir, err)
  }

  ghost predicate IsSymlinkSpec(
    beforeFs: FileSystem,
    failures: (NativeFailureRequest) -> int,
    path: Path,
    ok: bool,
    isSymlink: bool,
    err: int
  )
  {
    NativeFailureContractFields(failures, MetadataQueryRequest(beforeFs, path, false, SymlinkQuery), err) &&
    IsSymlinkContractFields(beforeFs, path, ok, isSymlink, err)
  }

  ghost predicate RenamePathSpec(
    beforeFs: FileSystem,
    beforeNow: int,
    failures: (NativeFailureRequest) -> int,
    afterFs: FileSystem,
    source: Path,
    target: Path,
    ok: bool,
    err: int
  )
  {
    NativeFailureContractFields(failures, RenameRequest(beforeFs, beforeNow, source, target), err) &&
    RenamePathWithChangeTimeContractFields(
      beforeFs, beforeNow, source, target, ok, err, afterFs
    ) &&
    RenamePathContractFields(beforeFs, source, target, ok, err, afterFs)
  }


  function FilesystemObjectRecordsFields(fs: FileSystem): (objects: map<HostInodeKey, InodeRecord>)
    ensures forall id | id in fs.inodes :: fs.inodes[id].hostKey in objects && objects[fs.inodes[id].hostKey] == fs.inodes[id]
    ensures LiveObjectRecordsFields(fs,objects)
  {
    hide *;
    reveal ValidInodeFileSystemData(), InodeUniqueHostKeys(), InodeValidLinkObservations();
    var objects := map id | id in fs.inodes :: fs.inodes[id].hostKey := fs.inodes[id];
    forall key | key in objects
      ensures objects[key].hostKey == key && objects[key].links.LinkCountKnown?
      ensures InodeStorageConsistent(objects[key]) && InodeKindConsistent(objects[key])
    {
      var id :| id in fs.inodes && fs.inodes[id].hostKey == key;
      assert objects[key] == fs.inodes[id];
    }
    reveal LiveObjectRecordsFields();
    objects
  }

  ghost predicate LiveObjectRecordsFields(fs: FileSystem, objects: map<HostInodeKey, InodeRecord>)
  {
    (forall key | key in objects ::
       objects[key].hostKey == key && objects[key].links.LinkCountKnown? &&
       InodeStorageConsistent(objects[key]) && InodeKindConsistent(objects[key])) &&
    (forall id | id in fs.inodes ::
       fs.inodes[id].hostKey in objects && objects[fs.inodes[id].hostKey] == fs.inodes[id])
  }

  predicate LiveRecordStatusFields(objects: map<HostInodeKey, InodeRecord>, status: FileStatus)
  {
    status.hostKey in objects &&
    DirectoryStatusSameStructure(FileStatusForRecord(objects[status.hostKey]), status)
  }

  ghost predicate LiveDirectoryTopologyFields(fs: FileSystem, topology: LiveDirectoryTopology)
  {
    LiveObjectRecordsFields(fs, topology.objects) &&
    topology.root in topology.nodes &&
    topology.nodes[topology.root].parent == topology.root &&
    topology.nodes[topology.root].pathname == ["/"] &&
    (forall position | position in topology.nodes ::
       var node := topology.nodes[position];
       node.status.kind == DirectoryKind && node.parent in topology.nodes &&
       (node.selfRawInode != 0 ==> node.selfRawInode == node.status.hostKey.inode) &&
       (!node.parentMountBoundary && node.parentRawInode != 0 &&
        node.status.hostKey.device == topology.nodes[node.parent].status.hostKey.device ==>
          node.parentRawInode == topology.nodes[node.parent].status.hostKey.inode) &&
       LiveRecordStatusFields(topology.objects, node.status) &&
       topology.objects[node.status.hostKey].node.Directory? &&
       |node.pathname| <= 1 &&
       (forall name | name in node.entries ::
          InodeChildNameValid(name) && node.entries[name].rawInode >= 0 &&
          LiveRecordStatusFields(topology.objects, node.entries[name].status) &&
          |node.entries[name].directory| <= 1 &&
          (node.pathname == [] && node.entries[name].status.kind == DirectoryKind ==>
             |node.entries[name].directory| == 1) &&
          (node.entries[name].kind == UnknownDirentKind ||
           node.entries[name].kind == DirectoryEntryKindForFileKind(node.entries[name].status.kind)) &&
          (!node.entries[name].mountBoundary &&
           node.status.hostKey.device == node.entries[name].status.hostKey.device &&
           node.entries[name].rawInode != 0 ==>
             node.entries[name].rawInode == node.entries[name].status.hostKey.inode) &&
          (|node.entries[name].directory| == 1 ==>
             node.entries[name].directory[0] in topology.nodes &&
             node.entries[name].status.kind == DirectoryKind &&
             topology.nodes[node.entries[name].directory[0]].status.hostKey == node.entries[name].status.hostKey &&
             topology.nodes[node.entries[name].directory[0]].parent == position)) &&
       (|node.pathname| == 1 ==>
          var path := node.pathname[0];
          IsAbsolutePath(path) && NormalizePath(path) == path &&
          FsContainsPath(fs,path) && FsNodeAt(fs,path).Directory? &&
          node.status.hostKey == fs.inodes[FsIdAt(fs,path)].hostKey &&
          DirectoryStatusSameStructure(FileStatusForRecord(fs.inodes[FsIdAt(fs,path)]), node.status) &&
          (position == topology.root || topology.nodes[node.parent].pathname == [ParentPath(path)]) &&
          node.entries.Keys == (set entry | entry in DirectoryEntriesForPathFields(fs,path) :: entry.name) &&
          (forall name | name in node.entries ::
             FsContainsPath(fs,AppendPath(path,name)) &&
             node.entries[name].status.hostKey == fs.inodes[FsIdAt(fs,AppendPath(path,name))].hostKey &&
             DirectoryStatusSameStructure(FileStatusForRecord(fs.inodes[FsIdAt(fs,AppendPath(path,name))]),
                                          node.entries[name].status) &&
             (|node.entries[name].directory| == 1 ==>
                topology.nodes[node.entries[name].directory[0]].pathname == [AppendPath(path,name)]))))
  }

  function DirectoryCapabilityNamesFields(topology: LiveDirectoryTopology,
                                          position: DirectoryPosition, includeDots: bool): set<string>
    requires position in topology.nodes
  {
    topology.nodes[position].entries.Keys + (if includeDots then {".",".."} else {})
  }

  ghost predicate DirectoryCapabilityAnchorCurrentFields(
    topology: LiveDirectoryTopology, capability: DirectoryCapabilityState)
  {
    capability.position in topology.nodes &&
    capability.position in capability.anchorTopology.nodes &&
    topology.nodes[capability.position].status.hostKey ==
    capability.anchorTopology.nodes[capability.position].status.hostKey
  }

  ghost predicate DirectoryCapabilityReadCurrentFields(
    topology: LiveDirectoryTopology, capability: DirectoryCapabilityState)
  {
    DirectoryCapabilityAnchorCurrentFields(topology,capability) &&
    capability.remaining <= DirectoryCapabilityNamesFields(topology,
                                                           capability.position,capability.includeDots)
  }

  ghost predicate DirectoryOperationCapabilitiesCurrentFields(
    topology: LiveDirectoryTopology, capabilities: map<int,DirectoryCapabilityState>,
    operation: DirectoryOperation, handle: int, fd: int)
  {
    (operation == DirectoryReadNext && handle in capabilities ==>
       DirectoryCapabilityReadCurrentFields(topology,capabilities[handle])) &&
    ((operation == DirectoryFchdir || operation == DirectoryFstat) ==>
       forall item | item in capabilities && capabilities[item].descriptor == [fd] ::
         DirectoryCapabilityAnchorCurrentFields(topology,capabilities[item]))
  }

  ghost predicate LiveDirectoryCapabilitiesFields(topology: LiveDirectoryTopology,
                                                  capabilities: map<int, DirectoryCapabilityState>)
  {
    (forall handle | handle in capabilities ::
       var state := capabilities[handle];
       LiveDirectoryTopologyFields(state.anchorFs,state.anchorTopology) &&
       state.anchorTopology.nodes.Keys <= topology.nodes.Keys &&
       state.position in topology.nodes && state.position in state.anchorTopology.nodes &&
       state.remaining <= DirectoryCapabilityNamesFields(state.anchorTopology,state.position,state.includeDots) &&
       |state.descriptor| <= 1 && (|state.descriptor| == 1 ==> state.descriptor[0] >= 0)
    ) &&
    (forall left, right | left in capabilities && right in capabilities ::
       |capabilities[left].descriptor| == 1 && capabilities[left].descriptor == capabilities[right].descriptor ==> left == right)
  }

  function DirectoryOperationErrnos(operation: DirectoryOperation): set<int>
  {
    match operation
    case DirectoryGetCwd =>
      NativeLookupFaultErrnos + {Errno.ENOENT,Errno.ENOTDIR,Errno.ERANGE,
                                 Errno.EMFILE,Errno.ENFILE,Errno.EINTR,Errno.EOVERFLOW,Errno.ELOOP}
    case DirectoryCurrentStatus => NativeLookupFaultErrnos + {Errno.EOVERFLOW,Errno.EINTR,Errno.ENOTDIR}
    case DirectoryOpenParent => NativeLookupFaultErrnos + {Errno.ENFILE,Errno.EMFILE,Errno.ENOTDIR}
    case DirectoryGetDescriptor => {Errno.EBADF,Errno.EOPNOTSUPP}
    case DirectoryFchdir => {Errno.EACCES,Errno.EBADF,Errno.EINTR,Errno.ENOTDIR,Errno.ENOENT,Errno.EIO}
    case DirectoryChdirParent => NativeLookupFaultErrnos + {Errno.ENOENT,Errno.ENOTDIR,Errno.ELOOP}
    case DirectoryFstat => {Errno.EBADF,Errno.EINTR,Errno.EIO,Errno.ENOMEM,Errno.EOVERFLOW}
    case DirectoryReadNext => {Errno.EBADF,Errno.EIO,Errno.EINTR,Errno.ENOENT,Errno.ENOMEM,Errno.EOVERFLOW}
    case DirectoryEntryLstat => NativeLookupFaultErrnos + {Errno.ENOENT,Errno.ENOTDIR,Errno.ELOOP,Errno.EOVERFLOW,Errno.EINTR}
    case DirectoryClose => {Errno.EBADF,Errno.EINTR,Errno.EIO}
  }

  ghost predicate DirectoryRequestFields(request: DirectoryRequest)
  {
    LiveDirectoryTopologyFields(request.fs,request.topology) &&
    request.position in request.topology.nodes &&
    LiveDirectoryCapabilitiesFields(request.topology,request.capabilities) &&
    request.occupiedLegacyHandles !! request.capabilities.Keys &&
    (request.operation == DirectoryEntryLstat ==> InodeChildNameValid(request.name)) &&
    DirectoryOperationCapabilitiesCurrentFields(request.topology,request.capabilities,
                                                request.operation,request.handle,request.fd)
  }

  predicate DirectoryStatusSameStructure(expected: FileStatus, observed: FileStatus)
  {
    observed.(times := expected.times) == expected
  }

  ghost predicate DirectoryResponseFields(request: DirectoryRequest, response: DirectoryResponse)
  {
    DirectoryRequestFields(request) &&
    0 <= response.err &&
    (if response.err != 0 then
       response.err in DirectoryOperationErrnos(request.operation) &&
       (request.operation == DirectoryReadNext && request.handle in request.capabilities ==>
          response.remainingAfterReadError <= request.capabilities[request.handle].remaining)
     else
       match request.operation
       case DirectoryGetCwd =>
         request.topology.nodes[request.position].pathname == [response.path]
       case DirectoryCurrentStatus =>
         DirectoryStatusSameStructure(request.topology.nodes[request.position].status,response.status)
       case DirectoryOpenParent => response.handle !in request.capabilities &&
                                   response.handle !in request.occupiedLegacyHandles
       case DirectoryGetDescriptor =>
         request.handle in request.capabilities && response.fd >= 0 &&
         (forall other | other in request.capabilities && other != request.handle ::
            request.capabilities[other].descriptor != [response.fd])
       case DirectoryFchdir =>
         exists handle | handle in request.capabilities ::
           request.capabilities[handle].descriptor == [request.fd]
       case DirectoryChdirParent => true
       case DirectoryFstat =>
         exists handle | handle in request.capabilities ::
           request.capabilities[handle].descriptor == [request.fd] &&
           DirectoryStatusSameStructure(
             request.topology.nodes[request.capabilities[handle].position].status,response.status)
       case DirectoryReadNext =>
         request.handle in request.capabilities &&
         var capability := request.capabilities[request.handle];
         if |capability.remaining| == 0 then response.read.DirectoryEnd?
         else response.read.DirectoryItem? && response.read.name in capability.remaining &&
              var node := request.topology.nodes[capability.position];
              if response.read.name == "." then
                capability.includeDots && response.read.kind == DirectoryDirentKind &&
                response.read.inode == node.selfRawInode
              else if response.read.name == ".." then
                capability.includeDots && response.read.kind == DirectoryDirentKind &&
                response.read.inode == node.parentRawInode
              else response.read.name in node.entries &&
                   var entry := node.entries[response.read.name];
                   response.read.kind == entry.kind && response.read.inode == entry.rawInode
       case DirectoryEntryLstat =>
         request.name in request.topology.nodes[request.position].entries &&
         DirectoryStatusSameStructure(request.topology.nodes[request.position].entries[request.name].status,response.status) &&
         (|request.topology.nodes[request.position].pathname| == 1 ==>
            GetFileStatusResultFields(request.fs,
                                      AppendPath(request.topology.nodes[request.position].pathname[0],request.name),false).Ok?)
       case DirectoryClose => request.handle in request.capabilities) &&
    (request.operation == DirectoryGetDescriptor && request.handle in request.capabilities &&
     |request.capabilities[request.handle].descriptor| == 1 && response.err == 0 ==>
       request.capabilities[request.handle].descriptor == [response.fd])
  }

  ghost predicate DirectoryOperationSpec(request: DirectoryRequest,
                                         observations: DirectoryObservations, response: DirectoryResponse,
                                         afterPosition: DirectoryPosition, afterCapabilities: map<int,DirectoryCapabilityState>,
                                         afterOrdinal: nat, afterStatusOrdinal: nat, afterCwdHint: Path)
  {
    response == observations(request) && DirectoryResponseFields(request,response) &&
    afterOrdinal == request.ordinal + 1 &&
    afterStatusOrdinal == request.statusOrdinal +
    (if request.operation == DirectoryCurrentStatus || request.operation == DirectoryFstat ||
        request.operation == DirectoryEntryLstat then 1 else 0) &&
    afterPosition == DirectoryNextPositionFields(request,response) &&
    afterCapabilities == DirectoryNextCapabilitiesFields(request,response) &&
    afterCwdHint ==
    (if response.err == 0 &&
        (request.operation == DirectoryFchdir || request.operation == DirectoryChdirParent) &&
        |request.topology.nodes[afterPosition].pathname| == 1
     then request.topology.nodes[afterPosition].pathname[0]
     else request.cwdHint)
  }

  ghost function DirectoryPathResultFields(response: DirectoryResponse): IOResult<Path>
  {
    if response.err == 0 then Result.Ok(response.path)
    else Result.Err(NativeFailure(response.err,CLocaleErrnoTextResult(response.err)))
  }

  ghost function DirectoryStatusResultFields(response: DirectoryResponse): IOResult<FileStatus>
  {
    if response.err == 0 then Result.Ok(response.status)
    else Result.Err(NativeFailure(response.err,CLocaleErrnoTextResult(response.err)))
  }

  ghost function DirectoryHandleResultFields(response: DirectoryResponse): IOResult<int>
  {
    if response.err == 0 then Result.Ok(response.handle)
    else Result.Err(NativeFailure(response.err,CLocaleErrnoTextResult(response.err)))
  }

  ghost function DirectoryDescriptorResultFields(response: DirectoryResponse): IOResult<int>
  {
    if response.err == 0 then Result.Ok(response.fd)
    else Result.Err(NativeFailure(response.err,CLocaleErrnoTextResult(response.err)))
  }

  ghost function DirectoryReadResultFields(response: DirectoryResponse): IOResult<DirectoryRead>
  {
    if response.err == 0 then Result.Ok(response.read)
    else Result.Err(NativeFailure(response.err,CLocaleErrnoTextResult(response.err)))
  }

  ghost function DirectoryUnitResultFields(response: DirectoryResponse): IOResult<Unit>
  {
    if response.err == 0 then Result.Ok(Unit)
    else Result.Err(NativeFailure(response.err,CLocaleErrnoTextResult(response.err)))
  }

  ghost predicate DirectoryModelFields(model: DirectoryModel)
  {
    (forall fs: FileSystem ::
       LiveDirectoryTopologyFields(fs,model.views(fs)) &&
       model.views(fs).nodes.Keys == model.positions) &&
    (forall request: DirectoryRequest :: DirectoryRequestFields(request) ==>
                                           DirectoryResponseFields(request,model.observations(request)))
  }

  ghost predicate DirectoryStateFields(state: DirectoryState)
  {
    DirectoryModelFields(state.model) && state.position in state.model.positions &&
    (forall handle | handle in state.capabilities ::
       var capability := state.capabilities[handle];
       LiveDirectoryTopologyFields(capability.anchorFs,capability.anchorTopology) &&
       capability.anchorTopology.nodes.Keys <= state.model.positions &&
       capability.position in state.model.positions && capability.position in capability.anchorTopology.nodes &&
       capability.remaining <= DirectoryCapabilityNamesFields(capability.anchorTopology,capability.position,capability.includeDots) &&
       |capability.descriptor| <= 1 &&
       (|capability.descriptor| == 1 ==> capability.descriptor[0] >= 0)) &&
    (forall left, right | left in state.capabilities && right in state.capabilities ::
       (|state.capabilities[left].descriptor| == 1 &&
        state.capabilities[left].descriptor == state.capabilities[right].descriptor) ==> left == right)
  }

  lemma RootDirectorySnapshotFields(fs: FileSystem)
    ensures FsContainsPath(fs,"/")
    ensures FsNodeAt(fs,"/").Directory?
    ensures FsIdAt(fs,"/") == fs.namespace.id
    ensures fs.namespace.id in fs.inodes && fs.inodes[fs.namespace.id].kind == DirectoryKind
    ensures fs.inodes[fs.namespace.id].node.Directory?
    ensures InodeTreeWellFormed(fs.namespace,fs.inodes)
    ensures PathSegments("/") == []
    ensures InodeFsLookupTreeSegments(fs.inodes,fs.namespace,[]) == Result.Ok(fs.namespace)
    ensures GetFileStatusResultFields(fs,"/",false).Ok?
    ensures GetFileStatusResultFields(fs,"/",false).v.kind == DirectoryKind
    ensures forall entry | entry in DirectoryEntriesForPathFields(fs,"/") ::
              InodeChildNameValid(entry.name)
  {
    reveal ValidInodeFileSystemData(), InodeNamespaceWellFormed();
    reveal FsContainsPath(), InodeFsContainsPath(), InodeFsLookupId();
    reveal InodeFsLookupTreeSegments(), PathSegments();
    assert PathSegments("/") == [];
    assert InodeFsLookupTreeSegments(fs.inodes,fs.namespace,[]) == Result.Ok(fs.namespace);
    reveal FsNodeAt(), InodeFsNodeAt(), InodeFsLookupNode();
    reveal GetFileStatusResultFields(), ResolvePathForMetadataFields();
    reveal ResolvePathThroughSymlinkComponentsFields(), ResolvePathThroughSymlinkComponentsWithVisitedFields();
    reveal ResolveRawSymlinkSegmentsFields(), RawPathSegmentsFields();
    reveal StripLeadingSlash(), SplitSegments();
    assert RawPathSegmentsFields("/") == [];
    assert ResolvePathForMetadataFields(fs,"/",false) == Result.Ok("/");
    reveal FsIdAt(), InodeKindConsistent(), InodeValidLinkObservations();
    assert fs.inodes[fs.namespace.id].kind == DirectoryKind;
    assert fs.inodes[fs.namespace.id].links.LinkCountKnown?;
    reveal FileStatusForRecord();
    reveal DirectoryEntriesForPathFields(), DirectoryEntriesForTreeFields();
    forall entry | entry in DirectoryEntriesForPathFields(fs,"/")
      ensures InodeChildNameValid(entry.name)
    {
      var name :| name in fs.namespace.children && ValidLeafName(name) &&
                  entry == EntryForNode(name,InodeTreeChildNodeFields(fs,fs.namespace,name));
      reveal InodeTreeWellFormed(), EntryForNode(), LeafName();
      assert InodeChildNameValid(name);
      assert LeafName(name) == name;
    }
  }

  lemma RootDirectoryNamedEntryFields(fs: FileSystem, name: string)
    requires name in (set entry | entry in DirectoryEntriesForPathFields(fs,"/") :: entry.name)
    ensures name in fs.namespace.children
    ensures fs.namespace.children[name].id in fs.inodes
    ensures FsContainsPath(fs,AppendPath("/",name))
    ensures FsIdAt(fs,AppendPath("/",name)) == fs.namespace.children[name].id
    ensures FsIdAt(fs,AppendPath("/",name)) in fs.inodes
    ensures InodeChildNameValid(name)
  {
    hide *;
    RootDirectorySnapshotFields(fs);
    reveal InodeTreeWellFormed();
    reveal DirectoryEntriesForPathFields(), DirectoryEntriesForTreeFields();
    var entry :| entry in DirectoryEntriesForPathFields(fs,"/") && entry.name == name;
    var original :| original in fs.namespace.children && ValidLeafName(original) &&
                    entry == EntryForNode(original,InodeTreeChildNodeFields(fs,fs.namespace,original));
    reveal EntryForNode(), LeafName(), ValidLeafName();
    assert LeafName(original) == original;
    assert original == name;
    reveal ValidInodeFileSystemData(), InodeNamespaceWellFormed(), InodeTreeWellFormed();
    assert InodeTreeWellFormed(fs.namespace.children[name],fs.inodes);
    reveal AppendPath(), PathSegments(), StripLeadingSlash(), IsAbsolutePath();
    assert StripLeadingSlash(AppendPath("/",name)) == StripLeadingSlash(name);
    assert PathSegments(AppendPath("/",name)) == [name];
    reveal FsContainsPath(), InodeFsContainsPath(), InodeFsLookupId(), InodeFsLookupTreeSegments(), FsLookupSegments(), FsIdAt();
    assert InodeFsLookupTreeSegments(fs.inodes,fs.namespace.children[name],[]) == Result.Ok(fs.namespace.children[name]);
    assert InodeFsLookupTreeSegments(fs.inodes,fs.namespace,[name]) == Result.Ok(fs.namespace.children[name]);
  }

  ghost function DefaultLiveDirectoryTopology(fs: FileSystem): (topology: LiveDirectoryTopology)
    ensures LiveDirectoryTopologyFields(fs,topology)
    ensures topology.nodes.Keys == {DirectoryPosition(0)}
  {
    hide *;
    RootDirectorySnapshotFields(fs);
    var names := set entry | entry in DirectoryEntriesForPathFields(fs,"/") :: entry.name;
    var objects := FilesystemObjectRecordsFields(fs);
    forall name | name in names
      ensures name in fs.namespace.children && fs.namespace.children[name].id in fs.inodes
    {
      RootDirectoryNamedEntryFields(fs,name);
    }
    var entries := map name | name in names ::
                     LiveDirectoryEntry(0,UnknownDirentKind,FileStatusForRecord(fs.inodes[fs.namespace.children[name].id]),[]);
    var position := DirectoryPosition(0);
    var node := LiveDirectoryNode(FileStatusForRecord(fs.inodes[fs.namespace.id]),position,entries,["/"]);
    var topology := LiveDirectoryTopology(position,map[position := node],objects);
    reveal LiveDirectoryTopologyFields(), LiveRecordStatusFields(), DirectoryStatusSameStructure();
    reveal ValidInodeFileSystemData(), InodeNamespaceWellFormed();
    reveal FileStatusForRecord();
    forall name | name in entries
      ensures InodeChildNameValid(name)
      ensures FsContainsPath(fs,AppendPath("/",name))
      ensures FsIdAt(fs,AppendPath("/",name)) in fs.inodes
      ensures entries[name].status.hostKey == fs.inodes[FsIdAt(fs,AppendPath("/",name))].hostKey
      ensures DirectoryStatusSameStructure(FileStatusForRecord(fs.inodes[FsIdAt(fs,AppendPath("/",name))]),entries[name].status)
      ensures LiveRecordStatusFields(objects,entries[name].status)
    {
      RootDirectoryNamedEntryFields(fs,name);
    }
    reveal IsAbsolutePath(), NormalizePath(), BuildPath(), ParentPath(), PathSegments(), StripLeadingSlash();
    reveal SplitSegments(), NormalizeSegments(), JoinSegments();
    assert NormalizePath("/") == "/";
    topology
  }

  ghost function DefaultDirectoryResponse(request: DirectoryRequest): (response: DirectoryResponse)
    requires DirectoryRequestFields(request)
    ensures DirectoryResponseFields(request,response)
  {
    DirectoryResponse(if request.operation == DirectoryGetDescriptor then Errno.EBADF else Errno.EIO,
                      "",DEFAULT_FILE_STATUS,0,0,DirectoryEnd,{})
  }

  ghost function DefaultDirectoryState(): (state: DirectoryState)
    ensures DirectoryStateFields(state)
  {
    var observations := (request: DirectoryRequest) =>
                          if DirectoryRequestFields(request) then DefaultDirectoryResponse(request)
                          else DirectoryResponse(Errno.EIO,"",DEFAULT_FILE_STATUS,0,0,DirectoryEnd,{});
    var model := DirectoryModel({DirectoryPosition(0)},
                                (fs: FileSystem) => DefaultLiveDirectoryTopology(fs),observations);
    DirectoryState(model,DirectoryPosition(0),map[],0)
  }

  type ValidDirectoryState = state: DirectoryState | DirectoryStateFields(state)
    ghost witness DefaultDirectoryState()

  // Both registries share one ownership state. Handle keys remain arbitrary
  // integers; no allocator-sign restriction is imposed on legacy inputs.
  datatype DirectoryResources = DirectoryResources(
    legacy: map<int, DirHandleState>, origins: map<int, FileSystem>,
    live: ValidDirectoryState)

  predicate DirectoryResourcesFields(resources: DirectoryResources)
  {
    resources.origins.Keys <= resources.legacy.Keys &&
    resources.legacy.Keys !! resources.live.capabilities.Keys
  }

  ghost function DirectoryResourcesFromLegacy(handles: map<int, DirHandleState>):
    (resources: DirectoryResources)
    ensures DirectoryResourcesFields(resources)
    ensures resources.legacy == handles && resources.origins == map[]
    ensures resources.live.capabilities == map[]
  {
    var state := DefaultDirectoryState();
    DirectoryResources(handles,map[],state)
  }

  type ValidDirectoryResources = resources: DirectoryResources | DirectoryResourcesFields(resources)
    ghost witness DirectoryResourcesFromLegacy(map[])

  ghost function DirectoryResourcesReplaceLegacy(resources: ValidDirectoryResources,
                                                 handles: map<int, DirHandleState>, origins: map<int, FileSystem>):
    (after: DirectoryResources)
    requires origins.Keys <= handles.Keys
    requires handles.Keys !! resources.live.capabilities.Keys
    ensures DirectoryResourcesFields(after)
    ensures after.legacy == handles && after.origins == origins
    ensures after.live == resources.live
  {
    DirectoryResources(handles,origins,resources.live)
  }

  ghost function DirectoryResourcesReplaceLive(resources: ValidDirectoryResources,
                                               state: ValidDirectoryState): (after: DirectoryResources)
    requires resources.legacy.Keys !! state.capabilities.Keys
    ensures DirectoryResourcesFields(after)
    ensures after.legacy == resources.legacy && after.origins == resources.origins
    ensures after.live == state
  {
    DirectoryResources(resources.legacy,resources.origins,state)
  }

  lemma DirectoryResourcesLegacyDomainPreserved(handles: map<int, DirHandleState>, handle: int)
    ensures DirectoryResourcesFromLegacy(handles).legacy == handles
    ensures handle in DirectoryResourcesFromLegacy(handles).legacy <==> handle in handles
    ensures handle in handles ==> DirectoryResourcesFromLegacy(handles).legacy[handle] == handles[handle]
    ensures DirectoryResourcesFields(DirectoryResourcesFromLegacy(handles))
  {
  }

  lemma DirectoryStateAdmitsRequest(state: ValidDirectoryState, fs: FileSystem,
                                    operation: DirectoryOperation, handle: int, fd: int, name: string,
                                    statusOrdinal: nat, cwdHint: Path, occupiedLegacyHandles: set<int> := {})
    requires occupiedLegacyHandles !! state.capabilities.Keys
    requires operation == DirectoryEntryLstat ==> InodeChildNameValid(name)
    requires DirectoryOperationCapabilitiesCurrentFields(state.model.views(fs),
                                                         state.capabilities,operation,handle,fd)
    ensures DirectoryRequestFields(DirectoryRequest(operation,state.ordinal,fs,
                                                    state.model.views(fs),state.position,state.capabilities,handle,fd,name,statusOrdinal,cwdHint,occupiedLegacyHandles))
  {
    reveal DirectoryStateFields(), DirectoryModelFields();
    reveal DirectoryRequestFields(), LiveDirectoryCapabilitiesFields();
    forall item | item in state.capabilities
      ensures LiveDirectoryTopologyFields(state.capabilities[item].anchorFs,
                                          state.capabilities[item].anchorTopology)
      ensures state.capabilities[item].anchorTopology.nodes.Keys <= state.model.views(fs).nodes.Keys
    {
      assert state.capabilities[item].anchorTopology.nodes.Keys <= state.model.positions;
    }
  }

  ghost predicate DirectoryStateRequestFields(state: ValidDirectoryState, request: DirectoryRequest)
  {
    request.ordinal == state.ordinal && request.position == state.position &&
    request.capabilities == state.capabilities &&
    request.topology == state.model.views(request.fs) && DirectoryRequestFields(request)
  }

  ghost function DirectoryNextPositionFields(request: DirectoryRequest, response: DirectoryResponse): DirectoryPosition
    requires DirectoryResponseFields(request,response)
  {
    if response.err != 0 then request.position
    else if request.operation == DirectoryChdirParent then request.topology.nodes[request.position].parent
    else if request.operation == DirectoryFchdir then
      var handles := set handle | handle in request.capabilities &&
                                  request.capabilities[handle].descriptor == [request.fd];
      var handle :| handle in handles;
      request.capabilities[handle].position
    else request.position
  }

  ghost function DirectoryNextCapabilitiesFields(request: DirectoryRequest,
                                                 response: DirectoryResponse): map<int,DirectoryCapabilityState>
    requires DirectoryResponseFields(request,response)
  {
    if request.operation == DirectoryClose then request.capabilities - {request.handle}
    else if request.operation == DirectoryReadNext && response.err != 0 &&
            request.handle in request.capabilities then
      request.capabilities[request.handle :=
      request.capabilities[request.handle].(remaining := response.remainingAfterReadError)]
    else if response.err != 0 then request.capabilities
    else if request.operation == DirectoryOpenParent then
      var parent := request.topology.nodes[request.position].parent;
      request.capabilities[response.handle := DirectoryCapabilityState(
        parent,request.topology.nodes[parent].entries.Keys,[],request.fs,request.topology)]
    else if request.operation == DirectoryGetDescriptor then
      request.capabilities[request.handle :=
      request.capabilities[request.handle].(descriptor := [response.fd])]
    else if request.operation == DirectoryReadNext && response.read.DirectoryItem? then
      request.capabilities[request.handle :=
      request.capabilities[request.handle].(remaining :=
      request.capabilities[request.handle].remaining - {response.read.name})]
    else request.capabilities
  }

  lemma DirectoryTransitionStateFields(state: ValidDirectoryState,
                                       request: DirectoryRequest, response: DirectoryResponse)
    requires DirectoryStateRequestFields(state,request)
    requires DirectoryResponseFields(request,response)
    ensures DirectoryStateFields(DirectoryState(state.model,
                                                DirectoryNextPositionFields(request,response),
                                                DirectoryNextCapabilitiesFields(request,response),state.ordinal + 1))
  {
    hide *;
    reveal DirectoryStateRequestFields(), DirectoryStateFields(), DirectoryModelFields();
    reveal DirectoryResponseFields(), DirectoryRequestFields();
    reveal DirectoryNextPositionFields(), DirectoryNextCapabilitiesFields();
    var afterCapabilities := DirectoryNextCapabilitiesFields(request,response);
    if response.err == 0 && request.operation == DirectoryChdirParent {
      reveal LiveDirectoryTopologyFields();
      assert request.topology.nodes[request.position].parent in request.topology.nodes;
    }
    forall handle | handle in afterCapabilities
      ensures var capability := afterCapabilities[handle];
              LiveDirectoryTopologyFields(capability.anchorFs,capability.anchorTopology) &&
              capability.anchorTopology.nodes.Keys <= state.model.positions &&
              capability.position in state.model.positions && capability.position in capability.anchorTopology.nodes &&
              capability.remaining <= DirectoryCapabilityNamesFields(capability.anchorTopology,capability.position,capability.includeDots) &&
              |capability.descriptor| <= 1 &&
              (|capability.descriptor| == 1 ==> capability.descriptor[0] >= 0)
    {
      if response.err == 0 && request.operation == DirectoryOpenParent && handle == response.handle {
        reveal LiveDirectoryTopologyFields(), DirectoryCapabilityNamesFields();
        var parent := request.topology.nodes[request.position].parent;
        assert parent in request.topology.nodes;
        var openedCapability := afterCapabilities[handle];
        assert openedCapability.anchorTopology == request.topology;
        assert openedCapability.position == parent;
        assert !openedCapability.includeDots;
        assert openedCapability.remaining == request.topology.nodes[parent].entries.Keys;
        assert openedCapability.remaining <= DirectoryCapabilityNamesFields(
                                               openedCapability.anchorTopology,openedCapability.position,openedCapability.includeDots);
      } else {
        assert handle in state.capabilities;
        var prior := state.capabilities[handle];
        assert prior.remaining <= DirectoryCapabilityNamesFields(prior.anchorTopology,prior.position,prior.includeDots);
        assert afterCapabilities[handle].anchorTopology == prior.anchorTopology;
        assert afterCapabilities[handle].position == prior.position;
        assert afterCapabilities[handle].includeDots == prior.includeDots;
        assert afterCapabilities[handle].remaining <= prior.remaining;
        if response.err == 0 && request.operation == DirectoryGetDescriptor && handle == request.handle {
          assert response.fd >= 0;
        }
      }
    }
    forall left, right | left in afterCapabilities && right in afterCapabilities &&
                         |afterCapabilities[left].descriptor| == 1 &&
                         afterCapabilities[left].descriptor == afterCapabilities[right].descriptor
      ensures left == right
    {
      if response.err == 0 && request.operation == DirectoryGetDescriptor &&
         (left == request.handle || right == request.handle) {
        if left != right {
          var other := if left == request.handle then right else left;
          assert other in request.capabilities && other != request.handle;
          assert request.capabilities[other].descriptor != [response.fd];
          assert false;
        }
      } else {
        assert left in state.capabilities && right in state.capabilities;
        assert state.capabilities[left].descriptor == state.capabilities[right].descriptor;
      }
    }
  }

  ghost function DirectoryNextStateFields(state: ValidDirectoryState,
                                          request: DirectoryRequest, response: DirectoryResponse): (next: ValidDirectoryState)
    requires DirectoryStateRequestFields(state,request)
    requires DirectoryResponseFields(request,response)
    ensures next == DirectoryState(state.model,DirectoryNextPositionFields(request,response),
                                   DirectoryNextCapabilitiesFields(request,response),state.ordinal + 1)
  {
    hide *;
    DirectoryTransitionStateFields(state,request,response);
    DirectoryState(state.model,DirectoryNextPositionFields(request,response),
                   DirectoryNextCapabilitiesFields(request,response),state.ordinal + 1)
  }


  lemma DirectoryTransitionOwnershipFields(request: DirectoryRequest, response: DirectoryResponse)
    requires DirectoryResponseFields(request,response)
    ensures DirectoryNextCapabilitiesFields(request,response).Keys !! request.occupiedLegacyHandles
  {
    hide *;
    reveal DirectoryResponseFields(), DirectoryRequestFields(), DirectoryNextCapabilitiesFields();
    var after := DirectoryNextCapabilitiesFields(request,response);
    forall handle | handle in after
      ensures handle !in request.occupiedLegacyHandles
    {
      if response.err == 0 && request.operation == DirectoryOpenParent && handle == response.handle {
        assert handle !in request.occupiedLegacyHandles;
      } else {
        assert handle in request.capabilities;
      }
    }
  }

  ghost function DirectoryResourcesNextStateFields(resources: ValidDirectoryResources,
                                                   request: DirectoryRequest, response: DirectoryResponse): (after: ValidDirectoryResources)
    requires DirectoryStateRequestFields(resources.live,request)
    requires request.occupiedLegacyHandles == resources.legacy.Keys
    requires DirectoryResponseFields(request,response)
    ensures after.legacy == resources.legacy && after.origins == resources.origins
    ensures after.live == DirectoryNextStateFields(resources.live,request,response)
  {
    var next := DirectoryNextStateFields(resources.live,request,response);
    DirectoryTransitionOwnershipFields(request,response);
    DirectoryResourcesReplaceLive(resources,next)
  }

  // A native mode effect may update an unnamed object while the visible
  // filesystem stays equal. Captured descriptor anchors remain authenticated
  // snapshots, independent of the current model view at that same FS value.
  ghost function DirectoryStateAtSnapshotFields(state: ValidDirectoryState,
                                                fs: FileSystem, topology: LiveDirectoryTopology): (after: ValidDirectoryState)
    requires LiveDirectoryTopologyFields(fs,topology)
    requires topology.nodes.Keys == state.model.positions
    ensures after.position == state.position && after.capabilities == state.capabilities
    ensures after.ordinal == state.ordinal && after.model.positions == state.model.positions
    ensures after.model.observations == state.model.observations
    ensures after.model.views(fs) == topology
    ensures forall other: FileSystem | other != fs :: after.model.views(other) == state.model.views(other)
  {
    hide *;
    reveal DirectoryStateFields(), DirectoryModelFields();
    var views := (other: FileSystem) => if other == fs then topology else state.model.views(other);
    var model := DirectoryModel(state.model.positions,views,state.model.observations);
    assert forall other: FileSystem :: LiveDirectoryTopologyFields(other,views(other)) &&
                                       views(other).nodes.Keys == model.positions;
    assert DirectoryModelFields(model);
    DirectoryState(model,state.position,state.capabilities,state.ordinal)
  }

  predicate SimpleSegments(segments: seq<string>)
  {
    forall i: nat | i < |segments| :: InodeChildNameValid(segments[i])
  }

  lemma SplitOffset(prefix: string, suffix: string, i: nat, start: nat)
    requires start <= i <= |suffix|
    ensures SplitSegments(prefix+suffix,|prefix|+i,|prefix|+start) ==
            SplitSegments(suffix,i,start)
    decreases |suffix|-i
  {
    assert (prefix+suffix)[|prefix|+start..|prefix|+i] == suffix[start..i];
    assert (prefix+suffix)[|prefix|+start..] == suffix[start..];
    if i < |suffix| {
      assert (prefix+suffix)[|prefix|+i] == suffix[i];
      if suffix[i] == '/' {
        SplitOffset(prefix,suffix,i+1,i+1);
      } else {
        SplitOffset(prefix,suffix,i+1,start);
      }
    }
  }

  lemma SplitSlashFreeHead(head: string, tail: string, i: nat)
    requires i <= |head|
    requires '/' !in head
    ensures SplitSegments(head+tail,i,0) == SplitSegments(head+tail,|head|,0)
    decreases |head|-i
  {
    if i < |head| {
      assert (head+tail)[i] == head[i];
      SplitSlashFreeHead(head,tail,i+1);
    }
  }

  lemma JoinedSegmentsSplit(segments: seq<string>)
    requires SimpleSegments(segments)
    ensures SplitSegments(JoinSegments(segments),0,0) == segments
    decreases |segments|
  {
    hide SplitSegments();
    if |segments| > 0 {
      var head := segments[0];
      assert InodeChildNameValid(head);
      assert |head| > 0;
      if |segments| == 1 {
        SplitSlashFreeHead(head,"",0);
        assert head+"" == head;
        assert SplitSegments(head+"",0,0) == SplitSegments(head+"",|head|,0);
        assert JoinSegments(segments) == head;
        assert SplitSegments(head,|head|,0) == [head] by {
          reveal SplitSegments();
          assert head[..|head|] == head;
        }
        assert segments == [head];
        calc {
           SplitSegments(JoinSegments(segments),0,0);
        == SplitSegments(head,0,0);
        == SplitSegments(head,|head|,0);
        == [head];
        == segments;
        }
      } else {
        var tail := JoinSegments(segments[1..]);
        assert SimpleSegments(segments[1..]);
        JoinedSegmentsSplit(segments[1..]);
        SplitSlashFreeHead(head,"/"+tail,0);
        assert head+("/"+tail) == head+"/"+tail;
        SplitOffset(head+"/",tail,0,0);
        assert JoinSegments(segments) == head+"/"+tail;
        assert (head+"/"+tail)[..|head|] == head;
        assert (head+"/"+tail)[|head|] == '/';
        assert SplitSegments(head+"/"+tail,|head|,0) ==
               [head]+SplitSegments(head+"/"+tail,|head|+1,|head|+1) by {
          reveal SplitSegments();
        }
        assert segments == [head]+segments[1..];
      }
    } else {
      assert JoinSegments(segments) == "";
      assert SplitSegments("",0,0) == [] by { reveal SplitSegments(); }
    }
  }

  lemma NormalizeSimpleSegments(segments: seq<string>, i: nat, prefix: seq<string>)
    requires i <= |segments|
    requires SimpleSegments(segments)
    ensures NormalizeSegments(segments,i,prefix) == prefix+segments[i..]
    decreases |segments|-i
  {
    if i < |segments| {
      NormalizeSimpleSegments(segments,i+1,prefix+[segments[i]]);
      assert segments[i..] == [segments[i]]+segments[i+1..];
    }
  }

  lemma BuiltSegmentsFields(segments: seq<string>)
    requires SimpleSegments(segments)
    ensures IsAbsolutePath(BuildPath(true,segments))
    ensures PathSegments(BuildPath(true,segments)) == segments
    ensures NormalizePath(BuildPath(true,segments)) == BuildPath(true,segments)
    ensures ParentPath(BuildPath(true,segments)) ==
            BuildPath(true,if |segments| == 0 then [] else segments[..|segments|-1])
  {
    JoinedSegmentsSplit(segments);
    NormalizeSimpleSegments(segments,0,[]);
    if |segments| == 0 {
      assert BuildPath(true,segments) == "/";
    } else {
      assert |segments[0]| > 0;
      assert |JoinSegments(segments)| > 0;
      assert BuildPath(true,segments) == "/"+JoinSegments(segments);
    }
    assert StripLeadingSlash(BuildPath(true,segments)) == JoinSegments(segments);
  }

  lemma CanonicalPathFields(path: Path)
    requires IsAbsolutePath(path)
    requires NormalizePath(path) == path
    ensures BuildPath(true,PathSegments(path)) == path
  {
  }

  lemma LookupSegmentsSimple(inodes: map<InodeId,InodeRecord>, tree: InodeTree,
                             segments: seq<string>, found: InodeTree)
    requires InodeTreeWellFormed(tree,inodes)
    requires InodeFsLookupTreeSegments(inodes,tree,segments) == Result.Ok(found)
    ensures SimpleSegments(segments)
    decreases |segments|
  {
    if |segments| > 0 {
      LookupSegmentsSimple(inodes,tree.children[segments[0]],segments[1..],found);
      assert InodeChildNameValid(segments[0]);
      forall i: nat | i < |segments|
        ensures InodeChildNameValid(segments[i])
      {
        if i > 0 {
          assert segments[i] == segments[1..][i-1];
        }
      }
    }
  }

  lemma LookupPrefix(inodes: map<InodeId,InodeRecord>, tree: InodeTree,
                     segments: seq<string>, found: InodeTree, n: nat)
    requires InodeTreeWellFormed(tree,inodes)
    requires InodeFsLookupTreeSegments(inodes,tree,segments) == Result.Ok(found)
    requires n <= |segments|
    ensures InodeFsLookupTreeSegments(inodes,tree,segments[..n]).Ok?
    ensures InodeTreeWellFormed(InodeFsLookupTreeSegments(inodes,tree,segments[..n]).v,inodes)
    ensures n < |segments| ==>
              inodes[InodeFsLookupTreeSegments(inodes,tree,segments[..n]).v.id].node.Directory?
    decreases n
  {
    if n == 0 {
      assert InodeFsLookupTreeSegments(inodes,tree,[]) == Result.Ok(tree);
    } else {
      LookupPrefix(inodes,tree.children[segments[0]],segments[1..],found,n-1);
      assert segments[..n][1..] == segments[1..][..n-1];
    }
    if n == |segments| {
      LookupProof.InodeLookupTreeWellFormed(inodes,tree,segments,found);
    }
  }

  lemma LeafNameFields(name: string)
    requires InodeChildNameValid(name)
    ensures ValidLeafName(name)
    ensures PathSegments(name) == [name]
    ensures LeafName(name) == name
  {
    SplitSlashFreeHead(name,"",0);
    assert name+"" == name;
    assert SplitSegments(name+"",0,0) == SplitSegments(name+"",|name|,0);
    assert SplitSegments(name,|name|,0) == [name] by { reveal SplitSegments(); }
    assert SplitSegments(name,0,0) == [name];
    assert !IsAbsolutePath(name);
    NormalizeSimpleSegments([name],0,[]);
  }

  lemma JoinSegmentsSnoc(segments: seq<string>, name: string)
    ensures JoinSegments(segments+[name]) ==
            (if |segments| == 0 then name else JoinSegments(segments)+"/"+name)
    decreases |segments|
  {
    if |segments| > 1 {
      JoinSegmentsSnoc(segments[1..],name);
      assert (segments+[name])[1..] == segments[1..]+[name];
    }
  }

  lemma AppendBuiltPathFields(segments: seq<string>, name: string)
    requires SimpleSegments(segments)
    requires InodeChildNameValid(name)
    ensures BuildPath(true,segments+[name]) == AppendPath(BuildPath(true,segments),name)
    ensures PathSegments(AppendPath(BuildPath(true,segments),name)) == segments+[name]
    ensures NormalizePath(AppendPath(BuildPath(true,segments),name)) == AppendPath(BuildPath(true,segments),name)
  {
    JoinSegmentsSnoc(segments,name);
    assert SimpleSegments(segments+[name]);
    BuiltSegmentsFields(segments);
    BuiltSegmentsFields(segments+[name]);
  }

  lemma LookupAppend(inodes: map<InodeId,InodeRecord>, tree: InodeTree,
                     segments: seq<string>, parent: InodeTree, name: string)
    requires InodeTreeWellFormed(tree,inodes)
    requires InodeFsLookupTreeSegments(inodes,tree,segments) == Result.Ok(parent)
    requires inodes[parent.id].node.Directory?
    requires name in parent.children
    ensures InodeFsLookupTreeSegments(inodes,tree,segments+[name]) == Result.Ok(parent.children[name])
    decreases |segments|
  {
    if |segments| == 0 {
      assert parent == tree;
      assert InodeFsLookupTreeSegments(inodes,parent.children[name],[]) == Result.Ok(parent.children[name]);
    } else {
      LookupAppend(inodes,tree.children[segments[0]],segments[1..],parent,name);
      assert (segments+[name])[1..] == segments[1..]+[name];
    }
  }

  lemma NamedDirectorySnapshotFields(fs: FileSystem, path: Path)
    requires IsAbsolutePath(path)
    requires NormalizePath(path) == path
    requires FsContainsPath(fs,path)
    requires FsNodeAt(fs,path).Directory?
    ensures InodeFsLookupTreeSegments(fs.inodes,fs.namespace,PathSegments(path)).Ok?
    ensures InodeTreeWellFormed(InodeFsLookupTreeSegments(fs.inodes,fs.namespace,PathSegments(path)).v,fs.inodes)
    ensures FsIdAt(fs,path) in fs.inodes
    ensures fs.inodes[FsIdAt(fs,path)].node.Directory?
    ensures fs.inodes[FsIdAt(fs,path)].kind == DirectoryKind
    ensures SimpleSegments(PathSegments(path))
  {
    reveal ValidInodeFileSystemData(), InodeNamespaceWellFormed();
    reveal FsContainsPath(), InodeFsContainsPath(), InodeFsLookupId();
    var tree := InodeFsLookupTreeSegments(fs.inodes,fs.namespace,PathSegments(path)).v;
    LookupProof.InodeLookupTreeWellFormed(fs.inodes,fs.namespace,PathSegments(path),tree);
    LookupSegmentsSimple(fs.inodes,fs.namespace,PathSegments(path),tree);
    reveal FsNodeAt(), InodeFsNodeAt(), InodeFsLookupNode(), FsIdAt();
    reveal InodeTreeWellFormed(), InodeKindConsistent();
  }

  lemma NamedDirectoryChildFields(fs: FileSystem, path: Path, name: string)
    requires IsAbsolutePath(path)
    requires NormalizePath(path) == path
    requires FsContainsPath(fs,path)
    requires FsNodeAt(fs,path).Directory?
    requires name in InodeFsLookupTreeSegments(fs.inodes,fs.namespace,PathSegments(path)).v.children
    ensures InodeChildNameValid(name)
    ensures FsContainsPath(fs,AppendPath(path,name))
    ensures FsIdAt(fs,AppendPath(path,name)) in fs.inodes
    ensures FsIdAt(fs,AppendPath(path,name)) ==
            InodeFsLookupTreeSegments(fs.inodes,fs.namespace,PathSegments(path)).v.children[name].id
  {
    NamedDirectorySnapshotFields(fs,path);
    var tree := InodeFsLookupTreeSegments(fs.inodes,fs.namespace,PathSegments(path)).v;
    assert InodeChildNameValid(name);
    LookupAppend(fs.inodes,fs.namespace,PathSegments(path),tree,name);
    CanonicalPathFields(path);
    AppendBuiltPathFields(PathSegments(path),name);
    reveal FsContainsPath(), InodeFsContainsPath(), InodeFsLookupId(), FsIdAt();
  }

  ghost function NamedDirectoryEntriesFields(fs: FileSystem,
                                             objects: map<HostInodeKey,InodeRecord>, path: Path): (entries: map<string,LiveDirectoryEntry>)
    requires LiveObjectRecordsFields(fs,objects)
    requires IsAbsolutePath(path)
    requires NormalizePath(path) == path
    requires FsContainsPath(fs,path)
    requires FsNodeAt(fs,path).Directory?
    ensures entries.Keys == (set entry | entry in DirectoryEntriesForPathFields(fs,path) :: entry.name)
    ensures forall name | name in entries ::
              InodeChildNameValid(name) && entries[name].rawInode == 0 &&
              entries[name].kind == UnknownDirentKind && entries[name].directory == [] &&
              LiveRecordStatusFields(objects,entries[name].status) &&
              FsContainsPath(fs,AppendPath(path,name)) && FsIdAt(fs,AppendPath(path,name)) in fs.inodes &&
              entries[name].status == FileStatusForRecord(fs.inodes[FsIdAt(fs,AppendPath(path,name))])
  {
    NamedDirectorySnapshotFields(fs,path);
    var tree := InodeFsLookupTreeSegments(fs.inodes,fs.namespace,PathSegments(path)).v;
    forall name | name in tree.children
      ensures InodeChildNameValid(name)
      ensures ValidLeafName(name) && LeafName(name) == name
      ensures FsContainsPath(fs,AppendPath(path,name))
      ensures FsIdAt(fs,AppendPath(path,name)) in fs.inodes
      ensures FsIdAt(fs,AppendPath(path,name)) == tree.children[name].id
    {
      NamedDirectoryChildFields(fs,path,name);
      LeafNameFields(name);
    }
    var entries := map name | name in tree.children ::
                     LiveDirectoryEntry(0,UnknownDirentKind,FileStatusForRecord(fs.inodes[tree.children[name].id]),[]);
    reveal DirectoryEntriesForPathFields(), DirectoryEntriesForTreeFields(), EntryForNode();
    assert entries.Keys == (set entry | entry in DirectoryEntriesForPathFields(fs,path) :: entry.name) by {
      forall entry | entry in DirectoryEntriesForPathFields(fs,path)
        ensures entry.name in entries
      {
        var name :| name in tree.children && ValidLeafName(name) &&
                    entry == EntryForNode(name,InodeTreeChildNodeFields(fs,tree,name));
        assert entry.name == name;
      }
      forall name | name in entries
        ensures name in (set entry | entry in DirectoryEntriesForPathFields(fs,path) :: entry.name)
      {
        var entry := EntryForNode(name,InodeTreeChildNodeFields(fs,tree,name));
        assert entry in DirectoryEntriesForPathFields(fs,path);
        assert entry.name == name;
      }
    }
    reveal LiveRecordStatusFields(), LiveObjectRecordsFields(), DirectoryStatusSameStructure();
    entries
  }

  ghost function FreshPosition(positions: set<DirectoryPosition>): (position: DirectoryPosition)
    ensures position !in positions
    ensures forall prior | prior in positions :: prior.token < position.token
    decreases |positions|
  {
    if positions == {} then DirectoryPosition(0)
    else
      var prior :| prior in positions;
      var nextPosition := FreshPosition(positions-{prior});
      DirectoryPosition(if nextPosition.token > prior.token then nextPosition.token else prior.token+1)
  }

  ghost predicate Extends(before: LiveDirectoryTopology, after: LiveDirectoryTopology)
  {
    after.root == before.root && after.objects == before.objects &&
    before.nodes.Keys <= after.nodes.Keys &&
    forall position | position in before.nodes :: after.nodes[position] == before.nodes[position]
  }

  ghost function AddNamedDirectoryFields(fs: FileSystem,
                                         before: LiveDirectoryTopology, path: Path, parent: DirectoryPosition): (after: LiveDirectoryTopology)
    requires LiveDirectoryTopologyFields(fs,before)
    requires IsAbsolutePath(path)
    requires NormalizePath(path) == path
    requires FsContainsPath(fs,path) && FsNodeAt(fs,path).Directory?
    requires parent in before.nodes && before.nodes[parent].pathname == [ParentPath(path)]
    ensures LiveDirectoryTopologyFields(fs,after)
    ensures Extends(before,after)
    ensures exists position | position in after.nodes :: after.nodes[position].pathname == [path]
  {
    NamedDirectorySnapshotFields(fs,path);
    var entries := NamedDirectoryEntriesFields(fs,before.objects,path);
    var nextPosition := FreshPosition(before.nodes.Keys);
    var status := FileStatusForRecord(fs.inodes[FsIdAt(fs,path)]);
    var node := before.nodes[before.root].(status := status,parent := parent,
                entries := entries,pathname := [path],selfRawInode := 0,parentRawInode := 0,
                parentMountBoundary := false);
    var after := before.(nodes := before.nodes[nextPosition := node]);
    reveal LiveDirectoryTopologyFields(), LiveRecordStatusFields(), LiveObjectRecordsFields();
    reveal DirectoryStatusSameStructure(), FileStatusForRecord();
    assert status.kind == DirectoryKind;
    assert LiveRecordStatusFields(after.objects,status);
    assert before.objects[status.hostKey] == fs.inodes[FsIdAt(fs,path)];
    assert after.nodes.Keys == before.nodes.Keys+{nextPosition};
    forall position | position in before.nodes
      ensures after.nodes[position] == before.nodes[position]
    {
      assert position != nextPosition;
    }
    assert LiveDirectoryTopologyFields(fs,after);
    assert after.nodes[nextPosition].pathname == [path];
    after
  }

  ghost function ExtendNamedDirectoryTopologyFields(fs: FileSystem,
                                                    before: LiveDirectoryTopology, path: Path): (after: LiveDirectoryTopology)
    requires LiveDirectoryTopologyFields(fs,before)
    requires IsAbsolutePath(path)
    requires NormalizePath(path) == path
    requires FsContainsPath(fs,path) && FsNodeAt(fs,path).Directory?
    ensures LiveDirectoryTopologyFields(fs,after)
    ensures Extends(before,after)
    ensures exists position | position in after.nodes :: after.nodes[position].pathname == [path]
    decreases |PathSegments(path)|
  {
    if exists position | position in before.nodes :: before.nodes[position].pathname == [path] then
      before
    else
      NamedDirectorySnapshotFields(fs,path);
      CanonicalPathFields(path);
      var segments := PathSegments(path);
      assert path != "/";
      assert |segments| > 0;
      var prefix := segments[..|segments|-1];
      assert SimpleSegments(prefix);
      BuiltSegmentsFields(segments);
      BuiltSegmentsFields(prefix);
      var parentPath := BuildPath(true,prefix);
      var found := InodeFsLookupTreeSegments(fs.inodes,fs.namespace,segments).v;
      LookupPrefix(fs.inodes,fs.namespace,segments,found,|segments|-1);
      assert FsContainsPath(fs,parentPath) by {
        reveal FsContainsPath(), InodeFsContainsPath(), InodeFsLookupId();
      }
      assert FsNodeAt(fs,parentPath).Directory? by {
        reveal FsNodeAt(), InodeFsNodeAt(), InodeFsLookupNode();
      }
      var middle := ExtendNamedDirectoryTopologyFields(fs,before,parentPath);
      var parent :| parent in middle.nodes && middle.nodes[parent].pathname == [parentPath];
      var after := AddNamedDirectoryFields(fs,middle,path,parent);
      assert Extends(before,after) by {
        forall position | position in before.nodes
          ensures after.nodes[position] == before.nodes[position]
        {
          assert position in middle.nodes;
        }
      }
      after
  }

  ghost function ExtendTopologyDomainFields(fs: FileSystem,
                                            before: LiveDirectoryTopology, positions: set<DirectoryPosition>): (after: LiveDirectoryTopology)
    requires LiveDirectoryTopologyFields(fs,before)
    requires before.nodes.Keys <= positions
    ensures LiveDirectoryTopologyFields(fs,after)
    ensures Extends(before,after)
    ensures after.nodes.Keys == positions
  {
    var empty := before.nodes[before.root].(parent := before.root,pathname := [],
                 entries := map[],selfRawInode := 0,parentRawInode := 0,parentMountBoundary := false);
    var nodes := map position | position in positions ::
                   if position in before.nodes then before.nodes[position] else empty;
    var after := before.(nodes := nodes);
    reveal LiveDirectoryTopologyFields();
    forall position | position in before.nodes
      ensures after.nodes[position] == before.nodes[position]
    {
      assert position in positions;
    }
    assert LiveDirectoryTopologyFields(fs,after);
    after
  }

  ghost function ExtendDirectoryModelFields(model: DirectoryModel,
                                            fs: FileSystem, topology: LiveDirectoryTopology): (after: DirectoryModel)
    requires DirectoryModelFields(model)
    requires LiveDirectoryTopologyFields(fs,topology)
    requires model.positions <= topology.nodes.Keys
    ensures DirectoryModelFields(after)
    ensures after.positions == topology.nodes.Keys
    ensures after.observations == model.observations
    ensures after.views(fs) == topology
  {
    var positions := topology.nodes.Keys;
    var views := (other: FileSystem) =>
                   if other == fs then topology
                   else ExtendTopologyDomainFields(other,model.views(other),positions);
    var after := DirectoryModel(positions,views,model.observations);
    reveal DirectoryModelFields();
    assert after.views(fs) == topology;
    assert forall other: FileSystem ::
        LiveDirectoryTopologyFields(other,after.views(other)) &&
        after.views(other).nodes.Keys == after.positions;
    after
  }

  ghost function DirectoryStateAtExpandedSnapshotFields(state: ValidDirectoryState,
                                                        fs: FileSystem, topology: LiveDirectoryTopology): (after: ValidDirectoryState)
    requires LiveDirectoryTopologyFields(fs,topology)
    requires state.model.positions <= topology.nodes.Keys
    ensures after.position == state.position && after.capabilities == state.capabilities
    ensures after.ordinal == state.ordinal && after.model.positions == topology.nodes.Keys
    ensures after.model.observations == state.model.observations
    ensures after.model.views(fs) == topology
  {
    var model := ExtendDirectoryModelFields(state.model,fs,topology);
    reveal DirectoryStateFields();
    DirectoryState(model,state.position,state.capabilities,state.ordinal)
  }

  function CanonicalExistingPathFields(fs: FileSystem,path: Path): (canonical: Path)
    requires FsContainsPath(fs,path)
    ensures canonical == BuildPath(true,PathSegments(path))
    ensures IsAbsolutePath(canonical)
    ensures NormalizePath(canonical) == canonical
    ensures FsContainsPath(fs,canonical)
    ensures FsIdAt(fs,canonical) == FsIdAt(fs,path)
    ensures FsNodeAt(fs,canonical) == FsNodeAt(fs,path)
  {
    reveal ValidInodeFileSystemData(), InodeNamespaceWellFormed();
    reveal FsContainsPath(), InodeFsContainsPath(), InodeFsLookupId();
    var segments := PathSegments(path);
    var tree := InodeFsLookupTreeSegments(fs.inodes,fs.namespace,segments).v;
    LookupSegmentsSimple(fs.inodes,fs.namespace,segments,tree);
    BuiltSegmentsFields(segments);
    var canonical := BuildPath(true,segments);
    assert PathSegments(canonical) == segments;
    reveal FsIdAt(),FsNodeAt(),InodeFsNodeAt(),InodeFsLookupNode();
    canonical
  }

  function ModeChangedRecordFields(record:InodeRecord,mode:bv32,now:int):InodeRecord
  {
    InodeRecordWithNode(record,WithNodeChangeTime(WithNodeMode(record.node,mode),now,0))
  }

  function ModeChangedRecordsFields<K>(records:map<K,InodeRecord>,key:HostInodeKey,mode:bv32,now:int):map<K,InodeRecord>
  {
    map id | id in records ::
      if records[id].hostKey==key then ModeChangedRecordFields(records[id],mode,now) else records[id]
  }

  function ModeChangedStatusFields(status:FileStatus,key:HostInodeKey,mode:bv32,now:int):FileStatus
  {
    if status.hostKey==key then
      status.(mode:=NormalizeMode(mode),times:=status.times.(ctimeSec:=now,ctimeNsec:=0))
    else status
  }

  function ModeChangedEntryFields(entry:LiveDirectoryEntry,key:HostInodeKey,mode:bv32,now:int):LiveDirectoryEntry
  {
    entry.(status:=ModeChangedStatusFields(entry.status,key,mode,now))
  }

  function ModeChangedDirectoryFields(node:LiveDirectoryNode,key:HostInodeKey,mode:bv32,now:int):LiveDirectoryNode
  {
    node.(status:=ModeChangedStatusFields(node.status,key,mode,now),
    entries:=map name | name in node.entries :: ModeChangedEntryFields(node.entries[name],key,mode,now))
  }

  ghost function ModeChangedTopologyFields(topology:LiveDirectoryTopology,key:HostInodeKey,mode:bv32,now:int):LiveDirectoryTopology
  {
    topology.(objects:=ModeChangedRecordsFields(topology.objects,key,mode,now),
    nodes:=map position | position in topology.nodes :: ModeChangedDirectoryFields(topology.nodes[position],key,mode,now))
  }

  lemma {:isolate_assertions} ModeChangedRecordFacts(record:InodeRecord,mode:bv32,now:int)
    requires InodeStorageConsistent(record) && InodeKindConsistent(record)
    ensures var after:=ModeChangedRecordFields(record,mode,now);
            after.hostKey==record.hostKey && after.links==record.links && after.kind==record.kind &&
            after.ownership==record.ownership && after.storage==record.storage &&
            InodeStorageConsistent(after) && InodeKindConsistent(after) &&
            InodeSameNodeKind(record.node,after.node) && NodeShapeUnchangedExceptMode(record.node,after.node)
    ensures !record.node.Inaccessible? ==> var after:=ModeChangedRecordFields(record,mode,now);
                                           NodeMode(after.node)==NormalizeMode(mode) && NodeTimes(after.node)==NodeTimes(record.node).(ctimeSec:=now,ctimeNsec:=0)
  {
    hide *;
    reveal ModeChangedRecordFields(),InodeRecordWithNode(),WithNodeMode(),WithNodeChangeTime(),WithNodeTimes(),NodeTimes(),NodeMode();
    reveal InodeStorageConsistent(),InodeKindConsistent(),NodeStorageSize(),InodeSameNodeKind(),NodeShapeUnchangedExceptMode(),NormalizeMode();
    assert NormalizeMode(NormalizeMode(mode)) == NormalizeMode(mode);
    if !record.node.Inaccessible? {
      var after := ModeChangedRecordFields(record,mode,now);
      assert NodeMode(after.node) == NormalizeMode(mode) by {
        match record.node
        case Regular(_,_,_,_) =>
        case Directory(_,_,_) =>
        case Symlink(_,_,_,_) =>
        case Inaccessible(_) =>
      }
    }
  }

  lemma NodeModeShapeReflexive(node:FsNode)
    ensures InodeSameNodeKind(node,node) && NodeShapeUnchangedExceptMode(node,node)
  {
    hide *;
    reveal InodeSameNodeKind(),NodeShapeUnchangedExceptMode();
  }

  lemma {:isolate_assertions} ModeChangedFilesystemValid(fs:FileSystem,key:HostInodeKey,mode:bv32,now:int)
    ensures var after:=fs.(inodes:=ModeChangedRecordsFields(fs.inodes,key,mode,now));
            ValidInodeFileSystemData(after)
    ensures var after:=fs.(inodes:=ModeChangedRecordsFields(fs.inodes,key,mode,now));
            FileSystemTopologyUnchangedExceptMode(fs,after)
  {
    hide *;
    reveal ModeChangedRecordsFields();
    assert ValidInodeFileSystemData(fs);
    reveal ValidInodeFileSystemData(),InodeNamespaceWellFormed(),InodeUniqueHostKeys(),InodeValidLinkObservations();
    var records:=ModeChangedRecordsFields(fs.inodes,key,mode,now);
    var after:=fs.(inodes:=records);
    forall id | id in fs.inodes
      ensures records[id].hostKey==fs.inodes[id].hostKey && records[id].links==fs.inodes[id].links &&
              records[id].ownership==fs.inodes[id].ownership && records[id].storage==fs.inodes[id].storage && records[id].kind==fs.inodes[id].kind
      ensures InodeStorageConsistent(records[id]) && InodeKindConsistent(records[id])
      ensures InodeSameNodeKind(fs.inodes[id].node,records[id].node) && NodeShapeUnchangedExceptMode(fs.inodes[id].node,records[id].node)
    {
      if fs.inodes[id].hostKey==key {
        assert records[id]==ModeChangedRecordFields(fs.inodes[id],mode,now);
        ModeChangedRecordFacts(fs.inodes[id],mode,now);
      } else {
        assert records[id]==fs.inodes[id];
        NodeModeShapeReflexive(fs.inodes[id].node);
      }
    }
    if exists id | id in fs.inodes :: fs.inodes[id].hostKey==key {
      var id :| id in fs.inodes && fs.inodes[id].hostKey==key;
      var record:=ModeChangedRecordFields(fs.inodes[id],mode,now);
      assert records==fs.inodes[id:=record] by {
        forall other | other in fs.inodes
          ensures records[other]==(fs.inodes[id:=record])[other]
        {
          if other!=id { assert fs.inodes[other].hostKey!=key; }
        }
      }
      LookupProof.InodeTreeWellFormedAfterNodeUpdate(fs.namespace,fs.inodes,id,record);
    } else { assert records==fs.inodes; }
    forall id | id in records && FsNodeCanHaveChildren(records[id].node)
      ensures InodeNamespaceRefCount(after.namespace,id)==1
    {
      assert FsNodeCanHaveChildren(fs.inodes[id].node) by { reveal FsNodeCanHaveChildren(),InodeSameNodeKind(); }
    }
    assert InodeNamespaceWellFormed(after);
    assert InodeUniqueHostKeys(after);
    assert InodeValidLinkObservations(after);
    assert after.inodes[after.namespace.id].node.Directory? by { reveal InodeSameNodeKind(); }
    assert ValidInodeFileSystemData(after);
    reveal FileSystemTopologyUnchangedExceptMode();
  }

  ghost function ModeChangedFilesystemFields(fs:FileSystem,key:HostInodeKey,mode:bv32,now:int):(after:FileSystem)
    ensures after.namespace==fs.namespace
    ensures after.inodes==ModeChangedRecordsFields(fs.inodes,key,mode,now)
    ensures FileSystemTopologyUnchangedExceptMode(fs,after)
  {
    ModeChangedFilesystemValid(fs,key,mode,now);
    fs.(inodes:=ModeChangedRecordsFields(fs.inodes,key,mode,now))
  }

  lemma {:isolate_assertions} ModeChangedRecordStatus(fs:FileSystem,objects:map<HostInodeKey,InodeRecord>,key:HostInodeKey,
                                                      mode:bv32,now:int,status:FileStatus)
    requires LiveObjectRecordsFields(fs,objects)
    requires key in objects && !objects[key].node.Inaccessible?
    requires LiveRecordStatusFields(objects,status)
    ensures LiveRecordStatusFields(ModeChangedRecordsFields(objects,key,mode,now),ModeChangedStatusFields(status,key,mode,now))
    ensures ModeChangedStatusFields(status,key,mode,now).hostKey==status.hostKey
    ensures ModeChangedStatusFields(status,key,mode,now).kind==status.kind
  {
    hide *;
    reveal LiveObjectRecordsFields(),LiveRecordStatusFields(),DirectoryStatusSameStructure(),ModeChangedRecordsFields(),ModeChangedStatusFields();
    if status.hostKey==key {
      ModeChangedRecordFacts(objects[key],mode,now);
      reveal FileStatusForRecord();
    }
  }

  lemma {:isolate_assertions} ModeChangedObjectsValid(fs:FileSystem,topology:LiveDirectoryTopology,key:HostInodeKey,mode:bv32,now:int)
    requires LiveObjectRecordsFields(fs,topology.objects)
    ensures LiveObjectRecordsFields(ModeChangedFilesystemFields(fs,key,mode,now),ModeChangedRecordsFields(topology.objects,key,mode,now))
  {
    hide *;
    reveal LiveObjectRecordsFields(),ModeChangedRecordsFields();
    var after:=ModeChangedFilesystemFields(fs,key,mode,now);
    var objects:=ModeChangedRecordsFields(topology.objects,key,mode,now);
    forall id | id in topology.objects
      ensures objects[id].hostKey==id && objects[id].links.LinkCountKnown?
      ensures InodeStorageConsistent(objects[id]) && InodeKindConsistent(objects[id])
    {
      if id==key { ModeChangedRecordFacts(topology.objects[id],mode,now); }
    }
    forall id | id in fs.inodes
      ensures after.inodes[id].hostKey in objects && objects[after.inodes[id].hostKey]==after.inodes[id]
    {
      assert topology.objects[fs.inodes[id].hostKey]==fs.inodes[id];
      if fs.inodes[id].hostKey==key { ModeChangedRecordFacts(fs.inodes[id],mode,now); }
    }
  }

  lemma {:isolate_assertions} ModeChangedPath(fs:FileSystem,key:HostInodeKey,mode:bv32,now:int,path:Path)
    requires FsContainsPath(fs,path)
    ensures var after:=ModeChangedFilesystemFields(fs,key,mode,now);
            FsContainsPath(after,path) && FsIdAt(after,path)==FsIdAt(fs,path)
    ensures var after:=ModeChangedFilesystemFields(fs,key,mode,now);
            NodeShapeUnchangedExceptMode(FsNodeAt(fs,path),FsNodeAt(after,path))
  {
    hide *;
    var after:=ModeChangedFilesystemFields(fs,key,mode,now);
    FileSystemTopologyPathFields(fs,after,path);
    FileSystemTopologyLookupSegmentsFields(fs,after,PathSegments(path));
    reveal FsIdAt(),InodeFsLookupId(),FsLookupSegments();
  }

  lemma DirectoryEntryShapeFields(path:Path,before:FsNode,after:FsNode)
    requires NodeShapeUnchangedExceptMode(before,after)
    ensures EntryForNode(path,before)==EntryForNode(path,after)
  {
    hide *;
    reveal NodeShapeUnchangedExceptMode(),EntryForNode();
  }

  lemma {:isolate_assertions} DirectorySnapshotShape(before:FileSystem,after:FileSystem,path:Path)
    requires FileSystemTopologyUnchangedExceptMode(before,after)
    requires FsContainsPath(before,path)
    ensures FsContainsPath(after,path)
    ensures DirectoryEntriesForPathFields(before,path)==DirectoryEntriesForPathFields(after,path)
  {
    hide *;
    FileSystemTopologyPathFields(before,after,path);
    FileSystemTopologyLookupSegmentsFields(before,after,PathSegments(path));
    reveal DirectoryEntriesForPathFields(),FsLookupSegments(),FsContainsPath(),InodeFsContainsPath(),InodeFsLookupId();
    var tree:=InodeFsLookupTreeSegments(before.inodes,before.namespace,PathSegments(path)).v;
    assert InodeTreeWellFormed(before.namespace,before.inodes) && InodeTreeWellFormed(after.namespace,after.inodes) by {
      reveal ValidInodeFileSystemData(),InodeNamespaceWellFormed();
    }
    LookupProof.InodeLookupTreeWellFormed(before.inodes,before.namespace,PathSegments(path),tree);
    LookupProof.InodeLookupTreeWellFormed(after.inodes,after.namespace,PathSegments(path),tree);
    reveal DirectoryEntriesForTreeFields();
    forall name | name in tree.children && ValidLeafName(name)
      ensures EntryForNode(name,InodeTreeChildNodeFields(before,tree,name))==EntryForNode(name,InodeTreeChildNodeFields(after,tree,name))
    {
      reveal InodeTreeChildNodeFields(),FileSystemTopologyUnchangedExceptMode();
      var child:=tree.children[name].id;
      assert child in before.inodes && child in after.inodes by {
        reveal InodeTreeWellFormed();
        assert InodeTreeWellFormed(tree.children[name],before.inodes) && InodeTreeWellFormed(tree.children[name],after.inodes);
      }
      assert NodeShapeUnchangedExceptMode(before.inodes[child].node,after.inodes[child].node);
      assert InodeTreeChildNodeFields(before,tree,name)==before.inodes[child].node;
      assert InodeTreeChildNodeFields(after,tree,name)==after.inodes[child].node;
      assert NodeShapeUnchangedExceptMode(InodeTreeChildNodeFields(before,tree,name),InodeTreeChildNodeFields(after,tree,name));
      DirectoryEntryShapeFields(name,InodeTreeChildNodeFields(before,tree,name),InodeTreeChildNodeFields(after,tree,name));
    }
  }

  lemma {:isolate_assertions} ModeChangedTopologyValid(fs:FileSystem,topology:LiveDirectoryTopology,key:HostInodeKey,mode:bv32,now:int)
    requires LiveDirectoryTopologyFields(fs,topology)
    requires key in topology.objects
    requires !topology.objects[key].node.Inaccessible? && !topology.objects[key].node.Symlink?
    ensures LiveDirectoryTopologyFields(ModeChangedFilesystemFields(fs,key,mode,now),ModeChangedTopologyFields(topology,key,mode,now))
  {
    hide *;
    reveal LiveDirectoryTopologyFields(),LiveRecordStatusFields(),LiveObjectRecordsFields(),ModeChangedRecordsFields();
    reveal ModeChangedTopologyFields(),ModeChangedDirectoryFields(),ModeChangedEntryFields(),ModeChangedStatusFields();
    reveal FsIdAt(),FsContainsPath(),InodeFsContainsPath(),InodeFsLookupId();
    var afterFs:=ModeChangedFilesystemFields(fs,key,mode,now);
    var after:=ModeChangedTopologyFields(topology,key,mode,now);
    ModeChangedObjectsValid(fs,topology,key,mode,now);
    assert after.root==topology.root && after.nodes.Keys==topology.nodes.Keys;
    forall position | position in after.nodes
      ensures var node := after.nodes[position];
              node.status.kind == DirectoryKind && node.parent in after.nodes &&
              (node.selfRawInode != 0 ==> node.selfRawInode == node.status.hostKey.inode) &&
              (!node.parentMountBoundary && node.parentRawInode != 0 &&
               node.status.hostKey.device == after.nodes[node.parent].status.hostKey.device ==>
                 node.parentRawInode == after.nodes[node.parent].status.hostKey.inode) &&
              LiveRecordStatusFields(after.objects, node.status) &&
              after.objects[node.status.hostKey].node.Directory? &&
              |node.pathname| <= 1 &&
              (forall name | name in node.entries ::
                 InodeChildNameValid(name) && node.entries[name].rawInode >= 0 &&
                 LiveRecordStatusFields(after.objects, node.entries[name].status) &&
                 |node.entries[name].directory| <= 1 &&
                 (node.pathname == [] && node.entries[name].status.kind == DirectoryKind ==>
                    |node.entries[name].directory| == 1) &&
                 (node.entries[name].kind == UnknownDirentKind ||
                  node.entries[name].kind == DirectoryEntryKindForFileKind(node.entries[name].status.kind)) &&
                 (!node.entries[name].mountBoundary &&
                  node.status.hostKey.device == node.entries[name].status.hostKey.device &&
                  node.entries[name].rawInode != 0 ==>
                    node.entries[name].rawInode == node.entries[name].status.hostKey.inode) &&
                 (|node.entries[name].directory| == 1 ==>
                    node.entries[name].directory[0] in after.nodes &&
                    node.entries[name].status.kind == DirectoryKind &&
                    after.nodes[node.entries[name].directory[0]].status.hostKey == node.entries[name].status.hostKey &&
                    after.nodes[node.entries[name].directory[0]].parent == position)) &&
              (|node.pathname| == 1 ==>
                 var path := node.pathname[0];
                 IsAbsolutePath(path) && NormalizePath(path) == path &&
                 FsContainsPath(afterFs,path) && FsNodeAt(afterFs,path).Directory? &&
                 node.status.hostKey == afterFs.inodes[FsIdAt(afterFs,path)].hostKey &&
                 DirectoryStatusSameStructure(FileStatusForRecord(afterFs.inodes[FsIdAt(afterFs,path)]), node.status) &&
                 (position == after.root || after.nodes[node.parent].pathname == [ParentPath(path)]) &&
                 node.entries.Keys == (set entry | entry in DirectoryEntriesForPathFields(afterFs,path) :: entry.name) &&
                 (forall name | name in node.entries ::
                    FsContainsPath(afterFs,AppendPath(path,name)) &&
                    node.entries[name].status.hostKey == afterFs.inodes[FsIdAt(afterFs,AppendPath(path,name))].hostKey &&
                    DirectoryStatusSameStructure(FileStatusForRecord(afterFs.inodes[FsIdAt(afterFs,AppendPath(path,name))]),
                                                 node.entries[name].status) &&
                    (|node.entries[name].directory| == 1 ==>
                       after.nodes[node.entries[name].directory[0]].pathname == [AppendPath(path,name)])))
    {
      var priorNode:=topology.nodes[position];
      var node:=after.nodes[position];
      ModeChangedRecordStatus(fs,topology.objects,key,mode,now,priorNode.status);
      assert after.objects[node.status.hostKey].node.Directory? by {
        reveal ModeChangedRecordsFields();
        if node.status.hostKey==key { ModeChangedRecordFacts(topology.objects[key],mode,now); }
        reveal InodeSameNodeKind();
      }
      forall name | name in priorNode.entries
        ensures LiveRecordStatusFields(after.objects,node.entries[name].status)
      {
        ModeChangedRecordStatus(fs,topology.objects,key,mode,now,priorNode.entries[name].status);
      }
      if |priorNode.pathname|==1 {
        var path:=priorNode.pathname[0];
        ModeChangedPath(fs,key,mode,now,path);
        DirectorySnapshotShape(fs,afterFs,path);
        assert FsNodeAt(afterFs,path).Directory? by { reveal NodeShapeUnchangedExceptMode(); }
        assert DirectoryStatusSameStructure(FileStatusForRecord(afterFs.inodes[FsIdAt(afterFs,path)]),node.status) by {
          reveal LiveRecordStatusFields(),LiveObjectRecordsFields();
        }
        forall name | name in priorNode.entries
          ensures FsContainsPath(afterFs,AppendPath(path,name))
          ensures node.entries[name].status.hostKey==afterFs.inodes[FsIdAt(afterFs,AppendPath(path,name))].hostKey
          ensures DirectoryStatusSameStructure(FileStatusForRecord(afterFs.inodes[FsIdAt(afterFs,AppendPath(path,name))]),node.entries[name].status)
        {
          ModeChangedPath(fs,key,mode,now,AppendPath(path,name));
          reveal LiveRecordStatusFields(),LiveObjectRecordsFields();
        }
      }
    }
    assert LiveObjectRecordsFields(afterFs,after.objects);
    assert after.root in after.nodes && after.nodes[after.root].parent==after.root && after.nodes[after.root].pathname==["/"];
    assert LiveDirectoryTopologyFields(afterFs,after) by {
      hide *;
      reveal LiveDirectoryTopologyFields();
    }
  }

  ghost predicate CwdContextReadStepFields(before: CwdContext, after: CwdContext)
  {
    after == before.(ordinal := before.ordinal + 1)
  }

  ghost predicate DirectoryParentAnchorForContextRequestFields(
    fs: FileSystem, context: CwdContext, parent: int, path: Path)
  {
    path == "" || (0 as char) in path || IsAbsolutePath(path) ||
    (parent !in context.capabilities && parent !in context.legacyHandles) ||
    (if parent in context.capabilities then
       DirectoryCapabilityAnchorCurrentFields(context.topology,context.capabilities[parent])
     else DirectoryParentAnchorCurrentFields(fs,context.legacyHandles,context.legacyOrigins,parent))
  }

  function UnknownDirectoryParentErrnoFields(parent: int): int
  {
    if parent < 0 then Errno.EBADF else Errno.EINVAL
  }

  ghost function ResolvePathAtDirContextForMetadataFields(
    fs: FileSystem, context: CwdContext, parent: int, path: Path, follow: bool
  ): (result: IOResult<CwdTarget>)
    ensures result.Ok? ==> CwdTargetFields(fs,context,result.v)
  {
    if !CwdContextFields(fs,context) then Result.Err(InvalidPath)
    else if path == "" || (0 as char) in path || IsAbsolutePath(path) then
      ResolvePathAtCwdForMetadataFields(fs,context,path,follow)
    else if parent in context.capabilities then
      if !DirectoryCapabilityAnchorCurrentFields(context.topology,context.capabilities[parent]) then
        Result.Err(InvalidPath)
      else ResolveLiveDirectorySegmentsFields(fs,context,context.capabilities[parent].position,
                                              RawPathSegmentsFields(path),0,SYMLINK_MAX_DEPTH,follow,HasTrailingSlash(path))
    else if parent in context.legacyHandles then
      if !DirectoryParentAnchorCurrentFields(fs,context.legacyHandles,context.legacyOrigins,parent) then
        Result.Err(InvalidPath)
      else CwdNamedResultFields(fs,context,
                                ResolvePathAtDirForMetadataFields(fs,context.legacyHandles,parent,path,follow))
    else Result.Err(NativeFailure(UnknownDirectoryParentErrnoFields(parent),
                                  CLocaleErrnoTextResult(UnknownDirectoryParentErrnoFields(parent))))
  }

  ghost function GetFileStatusAtDirContextResultFields(
    fs: FileSystem, context: CwdContext, parent: int, path: Path, follow: bool): IOResult<FileStatus>
  {
    match ResolvePathAtDirContextForMetadataFields(fs,context,parent,path,follow)
    case Err(error) => Result.Err(error)
    case Ok(target) => Result.Ok(FileStatusForRecord(CwdTargetRecordFields(fs,context,target)))
  }

  function CwdStatusObservationPathFields(context: CwdContext, path: Path): Path
  {
    if path == "" || IsAbsolutePath(path) || context.position !in context.topology.nodes ||
       |context.topology.nodes[context.position].pathname| == 0 then path
    else AtCwdPathFields(context.topology.nodes[context.position].pathname[0],path)
  }

  ghost function AtDirContextStatusObservationPathFields(context: CwdContext, parent: int, path: Path): Path
  {
    if path == "" || IsAbsolutePath(path) then path
    else if parent in context.capabilities &&
            context.capabilities[parent].position in context.topology.nodes &&
            |context.topology.nodes[context.capabilities[parent].position].pathname| == 1 then
      AtCwdPathFields(context.topology.nodes[context.capabilities[parent].position].pathname[0],path)
    else if parent in context.legacyHandles then AtDirPathFields(context.legacyHandles,parent,path)
    else path
  }

  ghost function CwdLookupFailureErrnosFields(
    fs: FileSystem, context: CwdContext, path: Path, follow: bool): set<int>
  {
    if (0 as char) in path then {Errno.EINVAL}
    else if path == "" then {Errno.ENOENT}
    else NativeLookupFaultErrnos + {Errno.EINTR,Errno.EOVERFLOW} +
         (match ResolvePathAtCwdForMetadataFields(fs,context,path,follow)
          case Err(error) => {IOErrorErrno(error)}
          case Ok(_) => {})
  }

  ghost function AtDirContextLookupFailureErrnosFields(
    fs: FileSystem, context: CwdContext, parent: int, path: Path, follow: bool): set<int>
  {
    if (0 as char) in path then {Errno.EINVAL}
    else if path == "" then {Errno.ENOENT}
    else if !IsAbsolutePath(path) && parent !in context.capabilities && parent !in context.legacyHandles then
      {UnknownDirectoryParentErrnoFields(parent)}
    else NativeLookupFaultErrnos + {Errno.EBADF,Errno.EINTR,Errno.EOVERFLOW} +
         (match ResolvePathAtDirContextForMetadataFields(fs,context,parent,path,follow)
          case Err(error) => {IOErrorErrno(error)}
          case Ok(_) => {})
  }

  ghost predicate CwdResolvedModeCanSucceedFields(fs: FileSystem, context: CwdContext,
                                                  resolved: IOResult<CwdTarget>)
  {
    resolved.Ok? && CwdTargetFields(fs,context,resolved.v) &&
    !CwdTargetRecordFields(fs,context,resolved.v).node.Inaccessible? &&
    !CwdTargetRecordFields(fs,context,resolved.v).node.Symlink?
  }

  ghost function CwdResolvedOpenFailureErrFields(fs: FileSystem, context: CwdContext,
                                                 resolved: IOResult<CwdTarget>): int
  {
    match resolved
    case Err(error) => IOErrorErrno(error)
    case Ok(target) =>
      if !CwdTargetFields(fs,context,target) then Errno.EINVAL
      else if CwdTargetRecordFields(fs,context,target).node.Directory? then 0 else Errno.ENOTDIR
  }

  ghost predicate GetFileStatusAtCwdStructureContractFields(fs: FileSystem, context: CwdContext,
                                                            path: Path, follow: bool, ok: bool, status: FileStatus, err: int)
  {
    0 <= err && (ok <==> err == 0) &&
    (ok ==> GetFileStatusFromCwdContextResultFields(fs,context,path,follow).Ok? &&
            DirectoryStatusSameStructure(GetFileStatusFromCwdContextResultFields(fs,context,path,follow).v,status))
  }

  ghost predicate GetFileStatusAtDirContextStructureContractFields(fs: FileSystem, context: CwdContext,
                                                                   parent: int, path: Path, follow: bool, ok: bool, status: FileStatus, err: int)
  {
    0 <= err && (ok <==> err == 0) &&
    (ok ==> GetFileStatusAtDirContextResultFields(fs,context,parent,path,follow).Ok? &&
            DirectoryStatusSameStructure(GetFileStatusAtDirContextResultFields(fs,context,parent,path,follow).v,status))
  }

  ghost predicate SetFileModeFromCwdTargetContractFields(
    fs: FileSystem, before: CwdContext, now: int, afterFs: FileSystem, after: CwdContext,
    resolved: IOResult<CwdTarget>, mode: bv32, ok: bool, err: int)
  {
    CwdContextFields(fs,before) && CwdContextFields(afterFs,after) &&
    0 <= err && (ok <==> err == 0) &&
    (if !ok then afterFs == fs && CwdContextReadStepFields(before,after)
     else CwdResolvedModeCanSucceedFields(fs,before,resolved) &&
          var key := CwdTargetRecordFields(fs,before,resolved.v).hostKey;
          afterFs == ModeChangedFilesystemFields(fs,key,mode,now) &&
          after == before.(topology := ModeChangedTopologyFields(before.topology,key,mode,now),
          ordinal := before.ordinal+1))
  }

  ghost function CwdOpenedTopologyFields(fs: FileSystem, context: CwdContext,
                                         target: CwdTarget): (topology: LiveDirectoryTopology)
    requires CwdContextFields(fs,context) && CwdTargetFields(fs,context,target)
    requires CwdTargetRecordFields(fs,context,target).node.Directory?
    ensures LiveDirectoryTopologyFields(fs,topology)
    ensures Extends(context.topology,topology)
    ensures target.CwdNamedTarget? ==>
              exists position | position in topology.nodes :: topology.nodes[position].pathname == [target.path]
  {
    if target.CwdNamedTarget? then ExtendNamedDirectoryTopologyFields(fs,context.topology,target.path)
    else context.topology
  }

  ghost function CwdOpenedPositionFields(fs: FileSystem, context: CwdContext,
                                         target: CwdTarget): (position: DirectoryPosition)
    requires CwdContextFields(fs,context) && CwdTargetFields(fs,context,target)
    requires CwdTargetRecordFields(fs,context,target).node.Directory?
    ensures position in CwdOpenedTopologyFields(fs,context,target).nodes
    ensures CwdOpenedTopologyFields(fs,context,target).nodes[position].status.hostKey ==
            CwdTargetRecordFields(fs,context,target).hostKey
    ensures target.CwdDirectoryTarget? ==> position == target.position
    ensures target.CwdNamedTarget? ==>
              CwdOpenedTopologyFields(fs,context,target).nodes[position].pathname == [target.path]
  {
    var topology := CwdOpenedTopologyFields(fs,context,target);
    if target.CwdNamedTarget? then
      var position :| position in topology.nodes && topology.nodes[position].pathname == [target.path];
      position
    else if target.CwdDirectoryTarget? then target.position
    else
      assert false;
      context.position
  }

  ghost predicate OpenDirFromCwdTargetContractFields(fs: FileSystem, before: CwdContext,
                                                     after: CwdContext, resolved: IOResult<CwdTarget>, dots: bool, ok: bool, handle: int, err: int)
  {
    CwdContextFields(fs,before) && CwdContextFields(fs,after) &&
    0 <= err && (ok <==> err == 0) &&
    (if !ok then CwdContextReadStepFields(before,after)
     else resolved.Ok? && CwdTargetFields(fs,before,resolved.v) &&
          CwdTargetRecordFields(fs,before,resolved.v).node.Directory? &&
          handle !in before.capabilities && handle !in before.legacyHandles &&
          var topology := CwdOpenedTopologyFields(fs,before,resolved.v);
          var position := CwdOpenedPositionFields(fs,before,resolved.v);
          after == before.(topology := topology,ordinal := before.ordinal+1,
          capabilities := before.capabilities[handle :=
          DirectoryCapabilityState(position,DirectoryCapabilityNamesFields(topology,position,dots),
                                   [],fs,topology,dots)]))
  }

  ghost function GetOpenDirectoryCapabilityResultFields(fs: FileSystem, context: CwdContext,
                                                        handle: int): IOResult<FileStatus>
  {
    if !CwdContextFields(fs,context) then Result.Err(InvalidPath)
    else if handle !in context.capabilities then Result.Err(NativeFailure(Errno.EBADF,
                                                                          CLocaleErrnoTextResult(Errno.EBADF)))
    else if !DirectoryCapabilityAnchorCurrentFields(context.topology,context.capabilities[handle]) then
      Result.Err(InvalidPath)
    else Result.Ok(FileStatusForRecord(context.topology.objects[
                                       context.topology.nodes[context.capabilities[handle].position].status.hostKey]))
  }

  ghost function DirectoryRequestForContextFields(fs: FileSystem, context: CwdContext,
                                                  operation: DirectoryOperation, handle: int, fd: int, name: string,
                                                  statusOrdinal: nat): DirectoryRequest
  {
    DirectoryRequest(operation,context.ordinal,fs,context.topology,context.position,
                     context.capabilities,handle,fd,name,statusOrdinal,context.hint,context.legacyHandles.Keys)
  }

  ghost predicate ContextOperationSpec(fs: FileSystem, before: CwdContext,
                                       observations: DirectoryObservations, operation: DirectoryOperation,
                                       handle: int, fd: int, name: string, beforeStatus: nat, afterStatus: nat,
                                       response: DirectoryResponse, after: CwdContext)
  {
    DirectoryOperationSpec(DirectoryRequestForContextFields(fs,before,operation,handle,fd,name,beforeStatus),
                           observations,response,after.position,after.capabilities,after.ordinal,afterStatus,after.hint) &&
    after.topology == before.topology && after.legacyHandles == before.legacyHandles &&
    after.legacyOrigins == before.legacyOrigins
  }

  lemma CwdTargetRecordIsObservedFields(fs: FileSystem,context: CwdContext,target: CwdTarget)
    requires CwdContextFields(fs,context)
    requires CwdTargetFields(fs,context,target)
    ensures CwdTargetRecordFields(fs,context,target).hostKey in context.topology.objects
    ensures context.topology.objects[CwdTargetRecordFields(fs,context,target).hostKey] ==
            CwdTargetRecordFields(fs,context,target)
  {
    reveal CwdContextFields(), CwdTargetFields(), CwdTargetRecordFields();
    reveal LiveDirectoryTopologyFields(), LiveObjectRecordsFields();
    match target
    case CwdNamedTarget(path) =>
      reveal ValidInodeFileSystemData(),InodeNamespaceWellFormed();
             reveal FsContainsPath(),InodeFsContainsPath(),InodeFsLookupId();
                    var tree := InodeFsLookupTreeSegments(fs.inodes,fs.namespace,PathSegments(path)).v;
                    LookupProof.InodeLookupTreeWellFormed(fs.inodes,fs.namespace,PathSegments(path),tree);
                    reveal InodeTreeWellFormed(),FsIdAt();
    case CwdDirectoryTarget(position) =>
    case CwdEntryTarget(parent,name) =>
  }

  lemma CwdModeContextValidityFields(fs: FileSystem,context: CwdContext,target: CwdTarget,
                                     mode: bv32,now: int)
    requires CwdContextFields(fs,context)
    requires CwdTargetFields(fs,context,target)
    requires !CwdTargetRecordFields(fs,context,target).node.Inaccessible?
    requires !CwdTargetRecordFields(fs,context,target).node.Symlink?
    ensures var key := CwdTargetRecordFields(fs,context,target).hostKey;
            CwdContextFields(ModeChangedFilesystemFields(fs,key,mode,now),
                             context.(topology := ModeChangedTopologyFields(context.topology,key,mode,now),
                             ordinal := context.ordinal+1))
    ensures var key := CwdTargetRecordFields(fs,context,target).hostKey;
            SetFileModeFromCwdTargetContractFields(fs,context,now,
                                                   ModeChangedFilesystemFields(fs,key,mode,now),
                                                   context.(topology := ModeChangedTopologyFields(context.topology,key,mode,now),
                                                   ordinal := context.ordinal+1),Result.Ok(target),mode,true,0)
  {
    hide *;
    CwdTargetRecordIsObservedFields(fs,context,target);
    var record := CwdTargetRecordFields(fs,context,target);
    var key := record.hostKey;
    assert context.topology.objects[key] == record;
    assert LiveDirectoryTopologyFields(fs,context.topology) by { reveal CwdContextFields(); }
    ModeChangedTopologyValid(fs,context.topology,key,mode,now);
    var afterFs := ModeChangedFilesystemFields(fs,key,mode,now);
    var after := context.(topology := ModeChangedTopologyFields(context.topology,key,mode,now),
    ordinal := context.ordinal+1);
    assert after.topology.nodes.Keys == context.topology.nodes.Keys by {
      reveal ModeChangedTopologyFields();
    }
    assert LiveDirectoryCapabilitiesFields(after.topology,after.capabilities) by {
      reveal LiveDirectoryCapabilitiesFields(),CwdContextFields();
    }
    assert CwdContextFields(afterFs,after) by { reveal CwdContextFields(); }
    assert CwdResolvedModeCanSucceedFields(fs,context,Result.Ok(target)) by {
      reveal CwdResolvedModeCanSucceedFields();
    }
    assert SetFileModeFromCwdTargetContractFields(fs,context,now,afterFs,after,Result.Ok(target),mode,true,0) by {
      reveal SetFileModeFromCwdTargetContractFields();
    }
  }

  ghost function DirectoryResourcesContextViewFields(fs: FileSystem,
                                                     resources: ValidDirectoryResources, hint: Path): (context: CwdContext)
    ensures CwdContextFields(fs,context)
    ensures context == CwdContext(hint,resources.live.model.views(fs),resources.live.position,
                                  resources.live.ordinal,resources.live.capabilities,resources.legacy,resources.origins)
  {
    hide *;
    reveal DirectoryResourcesFields(), DirectoryOperationCapabilitiesCurrentFields();
    DirectoryStateAdmitsRequest(resources.live,fs,DirectoryGetCwd,0,0,"",0,hint,resources.legacy.Keys);
    reveal DirectoryRequestFields(), CwdContextFields();
    CwdContext(hint,resources.live.model.views(fs),resources.live.position,
               resources.live.ordinal,resources.live.capabilities,resources.legacy,resources.origins)
  }

  ghost function DirectoryResourcesAdvanceFields(resources: ValidDirectoryResources):
    (after: ValidDirectoryResources)
    ensures after.legacy == resources.legacy && after.origins == resources.origins
    ensures after.live == resources.live.(ordinal := resources.live.ordinal+1)
  {
    var next := resources.live.(ordinal := resources.live.ordinal+1);
    reveal DirectoryStateFields();
    DirectoryResourcesReplaceLive(resources,next)
  }

  ghost function DirectoryResourcesOpenedFields(fs: FileSystem,
                                                resources: ValidDirectoryResources, hint: Path, target: CwdTarget, handle: int, dots: bool):
    (after: ValidDirectoryResources)
    requires CwdTargetFields(fs,DirectoryResourcesContextViewFields(fs,resources,hint),target)
    requires CwdTargetRecordFields(fs,DirectoryResourcesContextViewFields(fs,resources,hint),target).node.Directory?
    requires handle !in resources.legacy && handle !in resources.live.capabilities
    ensures after.legacy == resources.legacy && after.origins == resources.origins
    ensures after.live.model.observations == resources.live.model.observations
    ensures OpenDirFromCwdTargetContractFields(fs,DirectoryResourcesContextViewFields(fs,resources,hint),
                                               DirectoryResourcesContextViewFields(fs,after,hint),Result.Ok(target),dots,true,handle,0)
  {
    hide *;
    reveal DirectoryStateFields(), DirectoryModelFields(), DirectoryResourcesFields(), Extends();
    var before := DirectoryResourcesContextViewFields(fs,resources,hint);
    var topology := CwdOpenedTopologyFields(fs,before,target);
    var position := CwdOpenedPositionFields(fs,before,target);
    var model := ExtendDirectoryModelFields(resources.live.model,fs,topology);
    var capability := DirectoryCapabilityState(position,DirectoryCapabilityNamesFields(topology,position,dots),
                                               [],fs,topology,dots);
    var capabilities := resources.live.capabilities[handle := capability];
    var state := DirectoryState(model,resources.live.position,capabilities,resources.live.ordinal+1);
    reveal DirectoryStateFields(), DirectoryModelFields(), DirectoryResourcesFields();
    reveal Extends();
    assert resources.live.model.positions == before.topology.nodes.Keys;
    forall item | item in capabilities
      ensures var cap := capabilities[item];
              LiveDirectoryTopologyFields(cap.anchorFs,cap.anchorTopology) &&
              cap.anchorTopology.nodes.Keys <= model.positions &&
              cap.position in model.positions && cap.position in cap.anchorTopology.nodes &&
              cap.remaining <= DirectoryCapabilityNamesFields(cap.anchorTopology,cap.position,cap.includeDots) &&
              |cap.descriptor| <= 1 && (|cap.descriptor| == 1 ==> cap.descriptor[0] >= 0)
    {
      if item == handle {
        assert capabilities[item] == capability;
      } else {
        assert item in resources.live.capabilities;
        assert capabilities[item] == resources.live.capabilities[item];
      }
    }
    forall left,right | left in capabilities && right in capabilities &&
                        |capabilities[left].descriptor| == 1 && capabilities[left].descriptor == capabilities[right].descriptor
      ensures left == right
    {
      assert left != handle && right != handle;
      assert left in resources.live.capabilities && right in resources.live.capabilities;
    }
    assert DirectoryStateFields(state);
    var after := DirectoryResourcesReplaceLive(resources,state);
    var afterContext := DirectoryResourcesContextViewFields(fs,after,hint);
    assert afterContext == before.(topology := topology,ordinal := before.ordinal+1,
                           capabilities := before.capabilities[handle := capability]);
    reveal OpenDirFromCwdTargetContractFields();
    after
  }

  ghost function DirectoryResourcesModeFields(fs: FileSystem,
                                              resources: ValidDirectoryResources, hint: Path, target: CwdTarget, mode: bv32, now: int):
    (after: ValidDirectoryResources)
    requires CwdTargetFields(fs,DirectoryResourcesContextViewFields(fs,resources,hint),target)
    requires !CwdTargetRecordFields(fs,DirectoryResourcesContextViewFields(fs,resources,hint),target).node.Inaccessible?
    requires !CwdTargetRecordFields(fs,DirectoryResourcesContextViewFields(fs,resources,hint),target).node.Symlink?
    ensures after.legacy == resources.legacy && after.origins == resources.origins
    ensures after.live.model.observations == resources.live.model.observations
    ensures var before := DirectoryResourcesContextViewFields(fs,resources,hint);
            var key := CwdTargetRecordFields(fs,before,target).hostKey;
            var afterFs := ModeChangedFilesystemFields(fs,key,mode,now);
            SetFileModeFromCwdTargetContractFields(fs,before,now,afterFs,
                                                   DirectoryResourcesContextViewFields(afterFs,after,hint),Result.Ok(target),mode,true,0)
  {
    hide *;
    var before := DirectoryResourcesContextViewFields(fs,resources,hint);
    var key := CwdTargetRecordFields(fs,before,target).hostKey;
    CwdModeContextValidityFields(fs,before,target,mode,now);
    var afterFs := ModeChangedFilesystemFields(fs,key,mode,now);
    var topology := ModeChangedTopologyFields(before.topology,key,mode,now);
    assert topology.nodes.Keys == resources.live.model.positions by {
      reveal ModeChangedTopologyFields(), DirectoryStateFields(), DirectoryModelFields();
    }
    assert LiveDirectoryTopologyFields(afterFs,topology) by {
      reveal CwdContextFields();
    }
    var next := DirectoryStateAtSnapshotFields(resources.live,afterFs,topology);
    reveal DirectoryResourcesFields();
    var changed := DirectoryResourcesReplaceLive(resources,next);
    var after := DirectoryResourcesAdvanceFields(changed);
    var afterContext := DirectoryResourcesContextViewFields(afterFs,after,hint);
    assert afterContext == before.(topology := topology,ordinal := before.ordinal+1);
    after
  }

  ghost predicate CwdContextFields(fs: FileSystem, context: CwdContext)
  {
    LiveDirectoryTopologyFields(fs, context.topology) &&
    context.position in context.topology.nodes &&
    LiveDirectoryCapabilitiesFields(context.topology,context.capabilities) &&
    context.legacyOrigins.Keys <= context.legacyHandles.Keys &&
    context.legacyHandles.Keys !! context.capabilities.Keys
  }

  ghost predicate CwdTargetFields(fs: FileSystem, context: CwdContext, target: CwdTarget)
  {
    match target
    case CwdNamedTarget(path) => IsAbsolutePath(path) && NormalizePath(path) == path &&
                                 FsContainsPath(fs,path) && !FsNodeAt(fs,path).Inaccessible?
    case CwdDirectoryTarget(position) =>
      position in context.topology.nodes &&
      context.topology.nodes[position].status.hostKey in context.topology.objects &&
      context.topology.objects[context.topology.nodes[position].status.hostKey].node.Directory?
    case CwdEntryTarget(parent,name) =>
      parent in context.topology.nodes && name in context.topology.nodes[parent].entries &&
      context.topology.nodes[parent].entries[name].status.hostKey in context.topology.objects &&
      !context.topology.objects[context.topology.nodes[parent].entries[name].status.hostKey].node.Inaccessible? &&
      !context.topology.objects[context.topology.nodes[parent].entries[name].status.hostKey].node.Directory?
  }

  ghost function CwdTargetRecordFields(fs: FileSystem, context: CwdContext, target: CwdTarget): InodeRecord
    requires CwdTargetFields(fs,context,target)
  {
    match target
    case CwdNamedTarget(path) => fs.inodes[FsIdAt(fs,path)]
    case CwdDirectoryTarget(position) =>
      context.topology.objects[context.topology.nodes[position].status.hostKey]
    case CwdEntryTarget(parent,name) =>
      context.topology.objects[context.topology.nodes[parent].entries[name].status.hostKey]
  }

  function CwdTargetNamedPathFields(context: CwdContext, target: CwdTarget): seq<Path>
  {
    match target
    case CwdNamedTarget(path) => [path]
    case CwdDirectoryTarget(position) =>
      if position in context.topology.nodes then context.topology.nodes[position].pathname else []
    case CwdEntryTarget(parent,name) =>
      if parent in context.topology.nodes && |context.topology.nodes[parent].pathname| == 1
      then [AppendPath(context.topology.nodes[parent].pathname[0],name)] else []
  }

  function CwdNamedResultFields(fs: FileSystem, context: CwdContext, result: IOResult<Path>): (target: IOResult<CwdTarget>)
    requires result.Ok? ==> FsContainsPath(fs,result.v) && !FsNodeAt(fs,result.v).Inaccessible?
    ensures target.Ok? ==> CwdTargetFields(fs,context,target.v)
  {
    match result
    case Err(error) => Result.Err(error)
    case Ok(path) => Result.Ok(CwdNamedTarget(CanonicalExistingPathFields(fs,path)))
  }

  ghost function ResolveLiveDirectorySegmentsFields(
    fs: FileSystem, context: CwdContext, position: DirectoryPosition,
    segments: seq<string>, index: nat, fuel: nat, follow: bool, requireDirectory: bool
  ): (result: IOResult<CwdTarget>)
    requires CwdContextFields(fs,context)
    requires position in context.topology.nodes
    requires index <= |segments|
    ensures result.Ok? ==> CwdTargetFields(fs,context,result.v)
    decreases fuel, |segments| - index
  {
    var node := context.topology.nodes[position];
    if |node.pathname| == 1 then
      CwdNamedResultFields(fs,context,
                           ResolveRawSymlinkSegmentsFields(fs,segments,index,node.pathname[0],{},fuel,follow,false,requireDirectory))
    else if index == |segments| then
      Result.Ok(CwdDirectoryTarget(position))
    else if !FixtureOwnerCanSearch(context.topology.objects[node.status.hostKey].node) then
      Result.Err(PermissionDenied)
    else if segments[index] == "." || segments[index] == ".." then
      ResolveLiveDirectorySegmentsFields(fs,context,
                                         if segments[index] == ".." then node.parent else position,
                                         segments,index+1,fuel,follow,requireDirectory)
    else if segments[index] !in node.entries then Result.Err(NoSuchFile)
    else
      var name := segments[index];
      var entry := node.entries[name];
      var record := context.topology.objects[entry.status.hostKey];
      match record.node
      case Inaccessible(_) => Result.Err(PermissionDenied)
      case Regular(_,_,_,_) =>
        if index+1 == |segments| && !requireDirectory then Result.Ok(CwdEntryTarget(position,name))
        else Result.Err(NotDirectory)
      case Directory(_,_,_) =>
        ResolveLiveDirectorySegmentsFields(fs,context,entry.directory[0],segments,index+1,fuel,follow,requireDirectory)
      case Symlink(target,_,_,_) =>
        if index+1 == |segments| && !follow && !requireDirectory then Result.Ok(CwdEntryTarget(position,name))
        else if target == "" then Result.Err(NoSuchFile)
        else if fuel == 0 then Result.Err(InvalidPath)
        else
          var tail := segments[index+1..];
          var substituted := RawPathSegmentsFields(target) + tail;
          var directoryRequired := requireDirectory || (|tail| == 0 && HasTrailingSlash(target));
          if IsAbsolutePath(target) then
            CwdNamedResultFields(fs,context,
                                 ResolveRawSymlinkSegmentsFields(fs,substituted,0,"/",{},fuel-1,follow,false,directoryRequired))
          else ResolveLiveDirectorySegmentsFields(fs,context,position,substituted,0,fuel-1,follow,directoryRequired)
  }

  ghost function ResolvePathAtCwdForMetadataFields(
    fs: FileSystem, context: CwdContext, path: Path, follow: bool
  ): (result: IOResult<CwdTarget>)
    ensures result.Ok? ==> CwdTargetFields(fs,context,result.v)
  {
    if !CwdContextFields(fs,context) then Result.Err(InvalidPath)
    else if (0 as char) in path then Result.Err(NativeFailure(Errno.EINVAL,CLocaleErrnoTextResult(Errno.EINVAL)))
    else if path == "" then Result.Err(NoSuchFile)
    else if IsAbsolutePath(path) then
      CwdNamedResultFields(fs,context,ResolvePathForMetadataFields(fs,path,follow))
    else ResolveLiveDirectorySegmentsFields(fs,context,context.position,
                                            RawPathSegmentsFields(path),0,SYMLINK_MAX_DEPTH,follow,HasTrailingSlash(path))
  }

  ghost function GetFileStatusFromCwdContextResultFields(
    fs: FileSystem, context: CwdContext, path: Path, follow: bool): IOResult<FileStatus>
  {
    match ResolvePathAtCwdForMetadataFields(fs,context,path,follow)
    case Err(error) => Result.Err(error)
    case Ok(target) =>
      var record := CwdTargetRecordFields(fs,context,target);
      if record.links.LinkCountKnown? then Result.Ok(FileStatusForRecord(record))
      else Result.Err(Other("unknown link count"))
  }

  ghost function ReadLinkFromCwdContextResultFields(
    fs: FileSystem, context: CwdContext, path: Path): IOResult<Path>
  {
    match ResolvePathAtCwdForMetadataFields(fs,context,path,false)
    case Err(error) => Result.Err(error)
    case Ok(target) =>
      match CwdTargetRecordFields(fs,context,target).node
      case Symlink(value,_,_,_) => Result.Ok(value)
      case _ => Result.Err(InvalidPath)
  }

  // This intrinsic bridge is required to type the directory-entry model.
  // The generic lookup proof and its other consequences remain private.
  lemma KernelLookupTreeWellFormed(inodes: map<InodeId, InodeRecord>, tree: InodeTree,
                                   segments: seq<string>, found: InodeTree)
    requires InodeTreeWellFormed(tree, inodes)
    requires InodeFsLookupTreeSegments(inodes, tree, segments) == Result.Ok(found)
    ensures InodeTreeWellFormed(found, inodes)
  {
    LookupProof.InodeLookupTreeWellFormed(inodes, tree, segments, found);
  }

  module KernelLookup {
    import Result = Results
    import opened BenchWorld

    lemma InodeLookupTreePathWitness(
      inodes: map<InodeId, InodeRecord>,
      tree: InodeTree,
      segs: seq<string>,
      found: InodeTree
    )
      requires InodeFsLookupTreeSegments(inodes, tree, segs) == Result.Ok(found)
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
               Result.Ok(subtree)
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
               Result.Ok(subtree)
      ensures InodePrefixPaths(
                segs, InodeNamespaceIdPaths(subtree, id)
              ) <= InodeNamespaceIdPaths(tree, id)
      decreases |segs|
    {
      if |segs| == 0 {
        assert tree.id in inodes;
        assert InodeFsLookupTreeSegments(inodes, tree, []) ==
               Result.Ok(tree);
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
               ) == Result.Ok(found)
      requires InodeTreeCanInsert(inodes, tree, target)
      requires InodeSegmentsDisjoint(source, target)
      ensures InodeFsLookupTreeSegments(
                inodes,
                InodeTreeSetSubtreeSegments(tree, target, subtree),
                source
              ) == Result.Ok(found)
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
               ) == Result.Ok(removedTree)
      requires InodeFsLookupTreeSegments(
                 inodes, tree, retained
               ) == Result.Ok(retainedTree)
      requires InodeSegmentsDisjoint(removed, retained)
      ensures InodeFsLookupTreeSegments(
                inodes,
                InodeTreeRemoveSegments(tree, removed),
                retained
              ) == Result.Ok(retainedTree)
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

  module KernelRemove {
    import Result = Results
    import opened BenchWorld
    import Lookup = KernelLookup

    lemma InodeTreeCanRemoveFindsLeaf(
      inodes: map<InodeId, InodeRecord>,
      tree: InodeTree,
      segs: seq<string>
    )
      requires InodeTreeCanRemove(inodes, tree, segs)
      ensures exists id ::
                InodeFsLookupTreeSegments(inodes, tree, segs) ==
                Result.Ok(InodeTreeNode(id, map[]))
      decreases |segs|
    {
      reveal InodeTreeCanRemove();
      if |segs| == 1 {
        var child := tree.children[segs[0]];
        assert child.children == map[];
        assert InodeFsLookupTreeSegments(inodes, tree, segs).Ok?;
        assert InodeFsLookupTreeSegments(inodes, tree, segs) ==
               Result.Ok(child);
        assert child == InodeTreeNode(child.id, map[]);
      } else {
        InodeTreeCanRemoveFindsLeaf(
          inodes, tree.children[segs[0]], segs[1..]
        );
        var id :|
          InodeFsLookupTreeSegments(
            inodes, tree.children[segs[0]], segs[1..]
          ) == Result.Ok(InodeTreeNode(id, map[]));
        assert InodeFsLookupTreeSegments(inodes, tree, segs) ==
               Result.Ok(InodeTreeNode(id, map[]));
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
               Result.Ok(InodeTreeNode(removedId, map[]))
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
               Result.Ok(InodeTreeNode(removedId, map[]))
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
               Result.Ok(InodeTreeNode(removedId, map[]))
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
               Result.Ok(InodeTreeNode(removedId, map[]))
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
          ) == Result.Ok(InodeTreeNode(id, map[]));
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

        assert InodeUniqueHostKeys(fs);
        assert forall liveId :: liveId in result.inodes ==>
                                  liveId in fs.inodes &&
                                  result.inodes[liveId].hostKey == fs.inodes[liveId].hostKey by {
          forall liveId | liveId in result.inodes
            ensures liveId in fs.inodes &&
                    result.inodes[liveId].hostKey == fs.inodes[liveId].hostKey
          {
            if liveId == id && oldRefs != 1 {
              assert result.inodes[id] ==
                     InodeRecordAfterUnlink(fs.inodes[id]);
            } else {
              assert result.inodes[liveId] == fs.inodes[liveId];
            }
          }
        }
        assert InodeUniqueHostKeys(result) by {
          hide *;
          reveal InodeUniqueHostKeys();
        }
        assert InodeValidLinkObservations(fs);
        assert fs.inodes[id].links.LinkCountKnown?;
        assert oldRefs <= fs.inodes[id].links.count;
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
            assert liveId in fs.inodes;
            assert fs.inodes[liveId].links.LinkCountKnown?;
            assert 0 < fs.inodes[liveId].links.count;
            assert InodeNamespaceRefCount(fs.namespace, liveId) <=
                   fs.inodes[liveId].links.count;
            if liveId == id {
              assert oldRefs > 1;
              assert result.inodes[id] ==
                     InodeRecordAfterUnlink(fs.inodes[id]);
              assert InodeNamespaceRefCount(result.namespace, id) ==
                     oldRefs - 1;
              hide *;
              reveal InodeRecordAfterUnlink();
            } else {
              assert result.inodes[liveId] == fs.inodes[liveId];
              assert InodeNamespaceIdPaths(
                  result.namespace, liveId
                ) == InodeNamespaceIdPaths(fs.namespace, liveId);
              assert InodeNamespaceRefCount(result.namespace, liveId) ==
                     InodeNamespaceRefCount(fs.namespace, liveId);
              hide *;
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
        hide *;
        reveal ValidInodeFileSystemData();
        assert ValidInodeFileSystemData(result);
      } else {
        assert InodeFsRemovePath(fs, path) == fs;
      }
      hide *;
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

  module KernelRename {
    import Result = Results
    import opened BenchWorld
    import Lookup = KernelLookup
    import Remove = KernelRemove

    lemma {:isolate_assertions} InodeTreeDetachSubtreeProperties(
      tree: InodeTree,
      inodes: map<InodeId, InodeRecord>,
      segs: seq<string>,
      subtree: InodeTree
    )
      requires InodeTreeWellFormed(tree, inodes)
      requires |segs| > 0
      requires InodeFsLookupTreeSegments(inodes, tree, segs) ==
               Result.Ok(subtree)
      ensures InodeTreeWellFormed(
                InodeTreeRemoveSegments(tree, segs), inodes
              )
      ensures InodeFsLookupTreeSegments(
                inodes, InodeTreeRemoveSegments(tree, segs), segs
              ) == Result.Err(NoSuchFile)
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
              ) == Result.Ok(subtree)
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
          assert InodeNamespaceIdPaths(
              InodeTreeSetSubtreeSegments(tree.children[segs[0]], segs[1..], subtree), id
            ) == InodeNamespaceIdPaths(tree.children[segs[0]], id) +
                      InodePrefixPaths(segs[1..], InodeNamespaceIdPaths(subtree, id));
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
               Result.Ok(subtree)
      requires InodeTreeCanInsert(inodes, tree, target)
      requires InodeSegmentsDisjoint(source, target)
      requires InodeFsLookupTreeSegments(
                 inodes,
                 InodeTreeSetSubtreeSegments(tree, target, subtree),
                 source
               ) == Result.Ok(subtree)
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
          ) == Result.Ok(sourceTree);
        var attached := InodeTreeSetSubtreeSegments(
          withoutTarget.namespace, targetSegs, sourceTree
        );
        assert InodeFsLookupTreeSegments(
            withoutTarget.inodes, attached, sourceSegs
          ) == Result.Ok(sourceTree);
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
        assert InodeValidLinkObservations(withoutTarget);
        assert InodeValidLinkObservations(result) by {
          forall liveId | liveId in result.inodes
            ensures result.inodes[liveId].links.LinkCountKnown? &&
                    0 < result.inodes[liveId].links.count &&
                    InodeNamespaceRefCount(result.namespace, liveId) <=
                    result.inodes[liveId].links.count
          {
            assert result.inodes[liveId] == withoutTarget.inodes[liveId];
            assert InodeNamespaceRefCount(result.namespace, liveId) ==
                   InodeNamespaceRefCount(withoutTarget.namespace, liveId);
            assert withoutTarget.inodes[liveId].links.LinkCountKnown?;
            assert 0 < withoutTarget.inodes[liveId].links.count;
            assert InodeNamespaceRefCount(withoutTarget.namespace, liveId) <=
                   withoutTarget.inodes[liveId].links.count;
            hide *;
          }
        }
        assert result.namespace.id == withoutTarget.namespace.id;
        assert result.namespace.id in result.inodes;
        assert result.inodes[result.namespace.id].node.Directory?;
        hide *;
        reveal ValidInodeFileSystemData();
        assert ValidInodeFileSystemData(result);
      }
      hide *;
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
}
