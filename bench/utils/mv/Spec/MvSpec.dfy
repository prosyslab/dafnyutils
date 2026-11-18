include "../../../core/StringEscaping.dfy"
include "MvPathSpec.dfy"
include "../../../core/Errno.dfy"
include "../../../core/World.dfy"
include "../../../core/Utf8.dfy"
include "../../../core/IO.dfy"
include "../../../core/IOContract.dfy"
include "MvSchema.dfy"
module MvSpec {
  import Errno = Errnos
  import Result = Results
  import BenchIO
  import IOContract
  import BenchWorld
  import Basename = MvPathSpec
  import Quote = StringEscaping
  import Dirname = MvPathSpec
  import Schema = MvSchema
  import Utf8 = Utf8Semantics

  /** Returns the diagnostic text for a supported filesystem errno. */
  function ErrnoTextSpec(err: int): string
  {
    if err == Errno.ENOENT then
      "No such file or directory"
    else if err == Errno.EACCES then
      "Permission denied"
    else if err == Errno.EBUSY then
      "Device or resource busy"
    else if err == Errno.EEXIST then
      "File exists"
    else if err == Errno.ENOTDIR then
      "Not a directory"
    else if err == Errno.EISDIR then
      "Is a directory"
    else if err == Errno.EINVAL then
      "Invalid argument"
    else if err == Errno.ENOTEMPTY then
      "Directory not empty"
    else if err == Errno.ELOOP then
      "Too many levels of symbolic links"
    else if err == Errno.EPERM then
      "Operation not permitted"
    else if err == Errno.EIO then
      "Input/output error"
    else if err == Errno.ENOMEM then
      "Cannot allocate memory"
    else if err == Errno.ENAMETOOLONG then
      "File name too long"
    else if err == Errno.EOVERFLOW then
      "Value too large for defined data type"
    else if err == Errno.EXDEV then
      "Invalid cross-device link"
    else if err == Errno.EMLINK then
      "Too many links"
    else if err == Errno.ENOSPC then
      "No space left on device"
    else if err == Errno.EROFS then
      "Read-only file system"
    else if err == Errno.EDQUOT then
      "Disk quota exceeded"
    else
      "unknown error"
  }

  /** Returns the help text for the supported mv options. */
  function HelpTextSpec(): BenchWorld.Bytes
  {
    "Usage: mv [OPTION]... [-T] SOURCE DEST\n"
    + "  or:  mv [OPTION]... SOURCE... DIRECTORY\n"
    + "  or:  mv [OPTION]... -t DIRECTORY SOURCE...\n"
    + "Rename SOURCE to DEST, or move SOURCE(s) to DIRECTORY.\n"
    + "\n"
    + "      --backup[=CONTROL]       make a backup of each existing destination file\n"
    + "  -b                           like --backup but does not accept an argument\n"
    + "      --debug                  explain how a file is moved; implies -v\n"
    + "  -f, --force                  do not prompt before overwriting\n"
    + "  -n, --no-clobber             do not overwrite an existing file\n"
    + "      --no-copy                do not copy if a rename cannot be performed\n"
    + "  -S, --suffix=SUFFIX          override the usual backup suffix\n"
    + "      --strip-trailing-slashes remove any trailing slashes from each SOURCE\n"
    + "  -t, --target-directory=DIR   move all SOURCE arguments into DIR\n"
    + "  -T, --no-target-directory    treat DEST as a normal file\n"
    + "      --update[=UPDATE]        control which existing files are updated\n"
    + "  -u                           equivalent to --update=older\n"
    + "  -v, --verbose                explain what is being done\n"
    + "      --help                   display this help and exit\n"
    + "      --version                output version information and exit\n"
    + "\n"
    + "This benchmark models rename-style moves over regular files, directories,\n"
    + "and symlinks already represented in the benchmark IO filesystem.\n"
    + "\n"
    + "Report bugs to: bug-coreutils@gnu.org\n"
    + "GNU coreutils home page: <https://www.gnu.org/software/coreutils/>\n"
    + "Full documentation <https://www.gnu.org/software/coreutils/mv>\n"
    + "or available locally via: info '(coreutils) mv invocation'\n"
  }

  /** Returns the mv version and copyright text. */
  function VersionTextSpec(): BenchWorld.Bytes
  {
    "mv (GNU coreutils) 9.10.13-2cf49\n"
    + "Copyright (C) 2026 Free Software Foundation, Inc.\n"
    + "License GPLv3+: GNU GPL version 3 or later <https://gnu.org/licenses/gpl.html>.\n"
    + "This is free software: you are free to change and redistribute it.\n"
    + "There is NO WARRANTY, to the extent permitted by law.\n"
    + "\n"
    + "Written by Mike Parker, David MacKenzie, and Jim Meyering.\n"
  }

  /** Encodes and quotes text for use in mv diagnostics. */
  function Q(text: string): BenchWorld.Bytes
  {
    Quote.SpecQuoteAfBytes(Utf8.Encode(text))
  }
  /** Returns the diagnostic for a command without file operands. */
  function MissingFileOperandMessageSpec(): BenchWorld.Bytes
  {
    "mv: missing file operand\nTry 'mv --help' for more information.\n"
  }

  /** Formats the diagnostic for a source without a destination operand. */
  function MissingDestinationMessageSpec(source: string): BenchWorld.Bytes
  {
    "mv: missing destination file operand after " + Q(source) + "\n"
    + "Try 'mv --help' for more information.\n"
  }

  /** Formats the diagnostic for an unexpected extra operand. */
  function ExtraOperandMessageSpec(operand: string): BenchWorld.Bytes
  {
    "mv: extra operand " + Q(operand) +
    "\nTry 'mv --help' for more information.\n"
  }

  /** Returns the diagnostic for combining target-directory and no-target-directory options. */
  function TargetDirectoryConflictMessageSpec(): BenchWorld.Bytes
  {
    "mv: cannot combine --target-directory (-t) and --no-target-directory (-T)\n"
  }

  /** Formats an invalid backup-control diagnostic and lists the accepted values. */
  function InvalidBackupArgumentMessageSpec(value: string): BenchWorld.Bytes
  {
    "mv: invalid argument " + Quote.SpecLocaleQuoteBytes(Utf8.Encode(value)) +
    " for 'backup type'\n"
    + "Valid arguments are:\n"
    + "  - 'none', 'off'\n"
    + "  - 'simple', 'never'\n"
    + "  - 'existing', 'nil'\n"
    + "  - 'numbered', 't'\n"
    + "Try 'mv --help' for more information.\n"
  }

  /** Formats an invalid update-control diagnostic and lists the accepted values. */
  function InvalidUpdateArgumentMessageSpec(value: string): BenchWorld.Bytes
  {
    "mv: invalid argument " + Quote.SpecLocaleQuoteBytes(Utf8.Encode(value)) +
    " for '--update'\n"
    + "Valid arguments are:\n"
    + "  - 'all'\n"
    + "  - 'none'\n"
    + "  - 'none-fail'\n"
    + "  - 'older'\n"
    + "Try 'mv --help' for more information.\n"
  }

  /** Formats a target validation error, distinguishing an explicit target directory. */
  function TargetFailureMessageSpec(path: string, explicitTargetDirectory: bool, err: int): BenchWorld.Bytes
  {
    if explicitTargetDirectory then
      "mv: target directory " + Q(path) +
      ": " + ErrnoTextSpec(err) + "\n"
    else
      "mv: target " + Q(path) +
      ": " + ErrnoTextSpec(err) + "\n"
  }

  /** Formats the diagnostic for a failed source metadata lookup. */
  function SourceStatFailureMessageSpec(source: string, err: int): BenchWorld.Bytes
  {
    "mv: cannot stat " + Q(source) +
    ": " + ErrnoTextSpec(err) + "\n"
  }

  /** Formats the diagnostic for a failed parent-directory metadata lookup. */
  function ParentStatFailureMessageSpec(path: string, err: int): BenchWorld.Bytes
  {
    "mv: " + Utf8.Encode(path) + ": " + ErrnoTextSpec(err) + "\n"
  }

  /** Formats a rename error, including destination directory conflicts. */
  function RenameFailureMessageSpec(source: string, target: string, err: int): BenchWorld.Bytes
  {
    if err == Errno.EISDIR then
      "mv: cannot overwrite directory " + Q(target) +
      " with non-directory " + Q(source) + "\n"
    else if err == Errno.ENOTEMPTY then
      "mv: cannot overwrite " + Q(target) +
      ": " + ErrnoTextSpec(err) + "\n"
    else
      "mv: cannot move " + Q(source) +
      " to " + Q(target) +
      ": " + ErrnoTextSpec(err) + "\n"
  }

  /** Formats a source rename error, including directory and self-subdirectory conflicts. */
  function SourceRenameFailureMessageSpec(
    source: string,
    target: string,
    err: int,
    directorySourceWithExistingTarget: bool
  ): BenchWorld.Bytes
  {
    if directorySourceWithExistingTarget && err == Errno.ENOTDIR then
      "mv: cannot overwrite non-directory " + Q(target) +
      " with directory " + Q(source) + "\n"
    else if err == Errno.EINVAL then
      "mv: cannot move " + Q(source) +
      " to a subdirectory of itself, " + Q(target) + "\n"
    else
      RenameFailureMessageSpec(source, target, err)
  }

  /** Selects the diagnostic errno for a source rename, handling an empty target path. */
  function SourceRenameDiagnosticErrSpec(
    target: string,
    sourceIsDir: bool,
    renameErr: int
  ): int
  {
    if target == "" then
      if sourceIsDir then Errno.EBUSY else Errno.EISDIR
    else
      renameErr
  }

  /** Formats the diagnostic for source and target naming the same file. */
  function SameFileMessageSpec(source: string, target: string): BenchWorld.Bytes
  {
    "mv: " + Q(source) +
    " and " + Q(target) +
    " are the same file\n"
  }

  /** Formats the diagnostic for a backup that could overwrite the source. */
  function BackupWouldDestroySourceMessageSpec(
    source: string,
    target: string
  ): BenchWorld.Bytes
  {
    "mv: backing up " +
    Q(target) +
    " might destroy source;  " +
    Q(source) +
    " not moved\n"
  }

  /** Formats the diagnostic for refusing to replace an existing target. */
  function NotReplacingMessageSpec(target: string): BenchWorld.Bytes
  {
    "mv: not replacing " + Q(target) + "\n"
  }

  /** Returns the skipped-target message when debug output is enabled. */
  function SkipStdoutSpec(target: string, debug: bool): BenchWorld.Bytes
  {
    if debug then
      "skipped " + Q(target) + "\n"
    else
      []
  }

  /** Returns the path text with all trailing slashes removed. */
  function TrimTrailingSlashesSpec(text: string): string
    decreases |text|
  {
    if |text| == 0 then
      ""
    else if text[|text| - 1] == '/' then
      TrimTrailingSlashesSpec(text[..|text| - 1])
    else
      text
  }

  /** Optionally strips trailing source slashes while preserving a root path as a slash. */
  function NormalizeSourceSpec(source: string, stripTrailingSlashes: bool): string
  {
    if !stripTrailingSlashes || source == "" then
      source
    else
      var trimmed := TrimTrailingSlashesSpec(source);
      if trimmed == "" then "/" else trimmed
  }

  /** Returns the destination path for a source moved into a directory. */
  function TargetInDirectorySpec(directory: string, source: string): string
  {
    var leaf := BenchWorld.LeafName(source);
    BenchWorld.AppendPath(directory, if leaf == "" then source else leaf)
  }

  /** Requires both paths to identify the same inode without following final symlinks. */
  ghost predicate SameInode(
    fs: BenchWorld.FileSystem,
    left: BenchWorld.Path,
    right: BenchWorld.Path
  )
  {
    var leftStat := IOContract.ResolvePathForMetadataFields(fs, left, false);
    var rightStat := IOContract.ResolvePathForMetadataFields(fs, right, false);
    leftStat.Ok? && rightStat.Ok? &&
    BenchWorld.InodeSameObject(fs, leftStat.Extract(), rightStat.Extract())
  }
  /** Requires equal leaf names in parent directories identifying the same inode. */
  ghost predicate SameDirectoryEntry(
    fs: BenchWorld.FileSystem,
    left: BenchWorld.Path,
    right: BenchWorld.Path
  )
  {
    var leftName := EntryNameSpec(left);
    var rightName := EntryNameSpec(right);
    leftName.leaf == rightName.leaf &&
    SameInode(fs, leftName.parent, rightName.parent)
  }
  /** Requires the source symlink's referent and target to name the same directory entry. */
  ghost predicate SourceSymlinkReferentHasTargetName(
    fs: BenchWorld.FileSystem,
    preCwd: BenchWorld.Path,
    source: BenchWorld.Path,
    target: BenchWorld.Path
  )
  {
    var sourceStat := IOContract.ResolvePathForMetadataFields(fs, source, false);
    sourceStat.Ok? &&
    var resolvedSource := sourceStat.Extract();
    BenchWorld.FsContainsPath(fs, resolvedSource) &&
    BenchWorld.FsNodeAt(fs, resolvedSource).Symlink? &&
    exists resolvedReferent: BenchWorld.Path ::
      IOContract.ResolvePathIdentityContractFields(
        fs, preCwd, source, true, resolvedReferent, 0
      ) &&
      SameDirectoryEntry(fs, resolvedReferent, target)
  }
  /** Identifies same-file moves rejected under the selected backup policy. */
  ghost predicate SameFileMustBeRejected(
    cmd: Schema.MvCmd,
    fs: BenchWorld.FileSystem,
    preCwd: BenchWorld.Path,
    source: BenchWorld.Path,
    target: BenchWorld.Path
  )
  {
    SameDirectoryEntry(fs, source, target) ||
    (cmd.backupMode == Schema.BackupOff &&
     (SameInode(fs, source, target) ||
      SourceSymlinkReferentHasTargetName(
        fs, preCwd, source, target
      )))
  }
  /** Checks whether the source modification timestamp is strictly newer than the target's. */
  function SourceNewerSpec(srcSec: int, srcNsec: int, dstSec: int, dstNsec: int): bool
  {
    srcSec > dstSec || (srcSec == dstSec && srcNsec > dstNsec)
  }

  /** Returns ENOTDIR for a successful lookup of a non-directory, or the lookup errno. */
  function TargetDirectoryErrSpec(statOk: bool, isDir: bool, statErr: int): int
  {
    if statOk && !isDir then Errno.ENOTDIR else statErr
  }

  /** Formats enabled verbose or debug output for a successful move and optional backup. */
  function StepSuccessStdoutSpec(source: string, target: string, backupPath: string, verbose: bool, debug: bool): BenchWorld.Bytes
  {
    if !verbose && !debug then
      []
    else
      "renamed " + Q(source) + " -> " + Q(target) +
      (if backupPath == "" then "\n" else " (backup: " + Q(backupPath) + ")\n")
  }

  datatype MoveOutcome = MoveOutcome(
    stdoutFragment: BenchWorld.Bytes,
    stderrFragment: BenchWorld.Bytes,
    failed: bool
  )
  datatype StatusCallEvidence = StatusCallEvidence(
    fs: BenchWorld.FileSystem,
    path: string,
    followSymlink: bool,
    ok: bool,
    status: BenchWorld.FileStatus,
    err: int
  )
  datatype NativeStatusInputs = NativeStatusInputs(
    times: BenchWorld.StatusTimeObservations,
    failures: (BenchWorld.NativeFailureRequest) -> int,
    now: int
  )
  /** Relates a path existence result to the filesystem metadata contract. */
  ghost predicate StatusExistsOutcomeFields(fs: BenchWorld.FileSystem, path: string,
                                            followSymlink: bool, found: bool, err: int)
  {
    if found then IOContract.PathExistsContractFields(fs, path, followSymlink, true, err)
    else err > 0 && err in IOContract.NativeStatusFailureErrnosFields(fs, path, followSymlink)
  }
  /** Requires the status calls to match consecutive trusted observations. */
  ghost predicate StatusCallsFor(
    observations: NativeStatusInputs,
    first: nat,
    calls: seq<StatusCallEvidence>
  )
  {
    forall i: nat | i < |calls| ::
      IOContract.ObservedNativeFileStatusContractFields(
        observations.times, observations.failures, first + i, calls[i].fs, calls[i].path,
        calls[i].followSymlink, calls[i].ok, calls[i].status, calls[i].err
      )
  }
  /** Matches a status call to its filesystem, path, and symlink-following policy. */
  ghost predicate StatusRequest(
    call: StatusCallEvidence,
    fs: BenchWorld.FileSystem,
    path: string,
    followSymlink: bool
  )
  {
    call.fs == fs && call.path == path && call.followSymlink == followSymlink
  }
  /** Specifies the backup-name lookup sequence required by the selected backup mode. */
  ghost predicate BackupStatusSuffix(
    backupMode: Schema.BackupMode,
    fs: BenchWorld.FileSystem,
    target: string,
    calls: seq<StatusCallEvidence>
  )
  {
    if backupMode == Schema.BackupOff || backupMode == Schema.BackupSimple then
      |calls| == 0
    else if backupMode == Schema.BackupExisting then
      |calls| >= 1 &&
      StatusRequest(calls[0], fs, Basename.NumberedBackupPathSpec(target, 1), false) &&
      (if !calls[0].ok then
         |calls| == 1
       else
         |calls| >= 2 &&
         (forall i: nat | 1 <= i < |calls| ::
            StatusRequest(calls[i], fs, Basename.NumberedBackupPathSpec(target, i), false)) &&
         (forall i: nat | 1 <= i + 1 < |calls| :: calls[i].ok) &&
         !calls[|calls| - 1].ok)
    else
      |calls| >= 1 &&
      (forall i: nat | i < |calls| ::
         StatusRequest(calls[i], fs, Basename.NumberedBackupPathSpec(target, i + 1), false)) &&
      (forall i: nat | i + 1 < |calls| :: calls[i].ok) &&
      !calls[|calls| - 1].ok
  }
  /** Identifies same-file rejection from observed inode identities and resolved names. */
  ghost predicate ObservedSameFileRejection(
    cmd: Schema.MvCmd, calls: seq<StatusCallEvidence>, sourceLeaf: string,
    targetLeaf: string, resolveOk: bool, resolvedSource: string
  )
  {
    |calls| >= 4 &&
    ((sourceLeaf == targetLeaf && calls[2].ok && calls[3].ok &&
      calls[2].status.hostKey == calls[3].status.hostKey) ||
     (cmd.backupMode == Schema.BackupOff &&
      (calls[0].status.hostKey == calls[1].status.hostKey ||
       (resolveOk && |calls| >= 6 && calls[3].ok && calls[5].ok &&
        calls[3].status.hostKey == calls[5].status.hostKey &&
        Basename.BasenameRelation(resolvedSource, targetLeaf)))))
  }
  /** Identifies a relevant parent lookup failure for a resolved source symlink. */
  ghost predicate ObservedReferentParentFailure(
    calls: seq<StatusCallEvidence>, targetLeaf: string,
    resolveOk: bool, resolvedSource: string
  )
  {
    resolveOk && |calls| >= 6 && (!calls[5].ok || !calls[3].ok) &&
    Basename.BasenameRelation(resolvedSource, targetLeaf)
  }
  /** Relates source, target, parent, and symlink observations used to compare file identities. */
  ghost predicate MoveComparisonObservations(
    fs: BenchWorld.FileSystem,
    cwd: BenchWorld.Path,
    source: string,
    target: string,
    calls: seq<StatusCallEvidence>,
    sourceParent: string,
    targetParent: string,
    sourceLeaf: string,
    targetLeaf: string,
    resolveOk: bool,
    resolvedSource: string,
    resolveErr: int,
    afterEntries: nat,
    inputs: NativeStatusInputs
  )
  {
    |calls| >= 4 &&
    calls[0].ok && calls[1].ok &&
    StatusRequest(calls[0], fs, source, false) &&
    StatusRequest(calls[1], fs, target, false) &&
    Dirname.DirnameRelation(source, sourceParent) &&
    Dirname.DirnameRelation(target, targetParent) &&
    Basename.BasenameRelation(source, sourceLeaf) &&
    Basename.BasenameRelation(target, targetLeaf) &&
    StatusRequest(calls[2], fs, sourceParent, false) &&
    StatusRequest(calls[3], fs, targetParent, false) &&
    (if sourceLeaf == targetLeaf && (!calls[2].ok || !calls[3].ok) then
       afterEntries == 4 && |calls| == 4 &&
       !resolveOk && resolvedSource == "" && resolveErr == 0
     else (if calls[0].status.kind == BenchWorld.SymlinkKind then
             IOContract.ResolvePathIdentitySpec(
               fs, cwd, inputs.failures, source, resolveOk, resolvedSource, resolveErr
             ) &&
             |calls| >= 5 &&
             StatusRequest(calls[4], fs, source, true) &&
             (if resolveOk then
                var referentName := EntryNameSpec(resolvedSource);
                afterEntries == 6 && |calls| >= 6 &&
                StatusRequest(calls[5], fs, referentName.parent, false)
              else
                afterEntries == 5)
           else
             afterEntries == 4 && !resolveOk && resolvedSource == "" && resolveErr == 0))
  }
  /** Returns the byte fragments concatenated in order. */
  function ConcatenateFragments(fragments: seq<BenchWorld.Bytes>): (combined: BenchWorld.Bytes)
    ensures |fragments| == 0 ==> combined == []
    ensures |fragments| == 1 ==> combined == fragments[0]
    decreases |fragments|
  {
    if |fragments| == 0 then
      []
    else
      fragments[0] + ConcatenateFragments(fragments[1..])
  }
  /** Relates a target to the first numbered backup path whose lookup fails. */
  ghost predicate NumberedBackupTargetSpecFields(preFs: BenchWorld.FileSystem, target: string, backupPath: string)
  {
    exists index: nat, missErr: int ::
      index >= 1 &&
      backupPath == Basename.NumberedBackupPathSpec(target, index) &&
      StatusExistsOutcomeFields(preFs, backupPath, false, false, missErr) &&
      forall j: nat | 1 <= j < index ::
        StatusExistsOutcomeFields(preFs, Basename.NumberedBackupPathSpec(target, j), false, true, 0)
  }
  /** Relates a target and backup policy to the selected backup path. */
  ghost predicate BackupTargetSpecFields(preFs: BenchWorld.FileSystem, target: string, backupMode: Schema.BackupMode, suffix: string, backupPath: string)
  {
    if backupMode == Schema.BackupOff then
      backupPath == ""
    else if backupMode == Schema.BackupSimple then
      backupPath == Basename.SimpleBackupPathSpec(target, suffix)
    else if backupMode == Schema.BackupExisting then
      ((exists hitErr: int ::
          StatusExistsOutcomeFields(preFs, Basename.NumberedBackupPathSpec(target, 1), false, true, hitErr) &&
          NumberedBackupTargetSpecFields(preFs, target, backupPath)) ||
       (exists missErr: int ::
          StatusExistsOutcomeFields(preFs, Basename.NumberedBackupPathSpec(target, 1), false, false, missErr) &&
          backupPath == Basename.SimpleBackupPathSpec(target, suffix)))
    else
      NumberedBackupTargetSpecFields(preFs, target, backupPath)
  }
  /** Identifies a simple backup path that resolves to the source inode. */
  ghost predicate BackupWouldDestroySource(
    cmd: Schema.MvCmd,
    fs: BenchWorld.FileSystem,
    source: string,
    target: string
  )
  {
    var sourceName := EntryNameSpec(source);
    var targetName := EntryNameSpec(target);
    (cmd.backupMode == Schema.BackupSimple ||
     cmd.backupMode == Schema.BackupExisting) &&
    sourceName.leaf == targetName.leaf + cmd.backupSuffix &&
    var sourceStat := IOContract.ResolvePathForMetadataFields(fs, source, false);
    var backupStat := IOContract.ResolvePathForMetadataFields(
      fs, Basename.SimpleBackupPathSpec(target, cmd.backupSuffix), true
    );
    sourceStat.Ok? && backupStat.Ok? &&
    BenchWorld.InodeSameObject(fs, sourceStat.Extract(), backupStat.Extract())
  }
  /** Relates backup lookup observations to the selected backup path. */
  ghost predicate BackupPathFromObservations(
    cmd: Schema.MvCmd, fs: BenchWorld.FileSystem, target: string,
    calls: seq<StatusCallEvidence>, path: string
  )
  {
    BackupStatusSuffix(cmd.backupMode, fs, target, calls) &&
    (if cmd.backupMode == Schema.BackupOff then path == ""
     else if cmd.backupMode == Schema.BackupSimple then
       path == Basename.SimpleBackupPathSpec(target, cmd.backupSuffix)
     else if cmd.backupMode == Schema.BackupExisting && !calls[0].ok then
       path == Basename.SimpleBackupPathSpec(target, cmd.backupSuffix)
     else if cmd.backupMode == Schema.BackupExisting then
       |calls| >= 2 && path == Basename.NumberedBackupPathSpec(target, |calls| - 1)
     else |calls| >= 1 && path == Basename.NumberedBackupPathSpec(target, |calls|))
  }
  /** Identifies observed metadata or identity-resolution failures requiring fault-specific behavior. */
  ghost predicate ObservedMetadataFault(
    source: string, fs: BenchWorld.FileSystem, cwd: BenchWorld.Path,
    calls: seq<StatusCallEvidence>, inputs: NativeStatusInputs
  )
  {
    (exists i: nat :: i < |calls| && !calls[i].ok &&
                      StatusExistsOutcomeFields(calls[i].fs, calls[i].path, calls[i].followSymlink, true, 0)) ||
    (|calls| >= 4 && calls[0].ok && calls[1].ok &&
     (!calls[2].ok || !calls[3].ok) &&
     EntryNameSpec(source).leaf == EntryNameSpec(calls[1].path).leaf) ||
    (|calls| >= 6 && calls[0].ok && calls[0].status.kind == BenchWorld.SymlinkKind &&
     (!calls[3].ok || !calls[5].ok)) ||
    (|calls| >= 5 && calls[0].ok && calls[0].status.kind == BenchWorld.SymlinkKind &&
     inputs.failures(BenchWorld.ResolveIdentityRequest(fs, cwd, source)) != 0)
  }
  /** Relates target-directory validation to its success flag and diagnostic errno. */
  ghost predicate TargetDirectoryCheckSpecFields(directory: string, preFs: BenchWorld.FileSystem, ok: bool, err: int)
  {
    exists statOk: bool, isDir: bool, statErr: int ::
      IOContract.IsDirectoryContractFields(
        preFs, directory, true, statOk, isDir, statErr
      ) &&
      ok == (statOk && isDir) &&
      err == TargetDirectoryErrSpec(statOk, isDir, statErr)
  }
  datatype MoveStep = MoveStep(state: BenchWorld.FileSystem, outcome: MoveOutcome)
  datatype MoveEdge = MoveEdge(start: BenchWorld.FileSystem, result: MoveStep)
  datatype EntryName = EntryName(parent: string, leaf: string)
  /** Selects the parent and final component characterized by the path relations. */
  opaque ghost function EntryNameSpec(path: string): (name: EntryName)
    ensures Dirname.DirnameRelation(path, name.parent)
    ensures Basename.BasenameRelation(path, name.leaf)
  {
    Basename.EntryNameExists(path);
    var parent: string, leaf: string :|
      Dirname.DirnameRelation(path, parent) && Basename.BasenameRelation(path, leaf);
    EntryName(parent, leaf)
  }
  /** Relates a rename and optional backup to its file effects and outcome, including partial failure. */
  ghost predicate RenameAllowed(edge: MoveEdge,
                                source: string, target: string, backupPath: string,
                                verbose: bool, debug: bool)
  {
    var fs := edge.start;
    var result := edge.result;
    (backupPath == "" &&
     IOContract.RenamePathContractFields(fs, source, target, true, 0, result.state) &&
     result.outcome == MoveOutcome(StepSuccessStdoutSpec(source, target, "", verbose, debug), [], false)) ||
    (backupPath == "" &&
     exists err: int, sourceIsDir: bool, statErr: int ::
       IOContract.IsDirectoryStrictContractFields(fs, source, false, true, sourceIsDir, statErr) &&
       IOContract.RenamePathContractFields(fs, source, target, false, err, result.state) &&
       result.outcome == MoveOutcome([], SourceRenameFailureMessageSpec(source, target,
                                                                        SourceRenameDiagnosticErrSpec(target, sourceIsDir, err),
                                                                        sourceIsDir && StatusExistsOutcomeFields(fs, target, false, true, 0)), true)) ||
    (backupPath != "" &&
     exists err: int ::
       IOContract.RenamePathContractFields(fs, target, backupPath, false, err, result.state) &&
       result.outcome == MoveOutcome([], RenameFailureMessageSpec(source, target, err), true)) ||
    (backupPath != "" &&
     exists backupFs: BenchWorld.FileSystem ::
       IOContract.RenamePathContractFields(fs, target, backupPath, true, 0, backupFs) &&
       IOContract.RenamePathContractFields(backupFs, source, target, true, 0, result.state) &&
       result.outcome == MoveOutcome(StepSuccessStdoutSpec(source, target, backupPath, verbose, debug), [], false)) ||
    (backupPath != "" &&
     exists err: int, sourceIsDir: bool, statErr: int ::
       IOContract.IsDirectoryStrictContractFields(fs, source, false, true, sourceIsDir, statErr) &&
       IOContract.RenamePathContractFields(fs, target, backupPath, true, 0, result.state) &&
       IOContract.RenamePathContractFields(result.state, source, target, false, err, result.state) &&
       result.outcome == MoveOutcome([], SourceRenameFailureMessageSpec(source, target,
                                                                        SourceRenameDiagnosticErrSpec(target, sourceIsDir, err), false), true))
  }

  /** Relates a rename and optional backup to the trusted native outcomes. */
  ghost predicate ObservedRenameAllowed(edge: MoveEdge,
                                        source: string, target: string, backupPath: string,
                                        cmd: Schema.MvCmd, sourceIsDir: bool, targetWasFound: bool,
                                        inputs: NativeStatusInputs)
  {
    var fs := edge.start;
    var result := edge.result;
    (backupPath == "" &&
     IOContract.RenamePathSpec(fs, inputs.now, inputs.failures, result.state, source, target, true, 0) &&
     result.outcome == MoveOutcome(StepSuccessStdoutSpec(source, target, "", cmd.verbose, cmd.debug), [], false)) ||
    (backupPath == "" && exists err: int ::
       IOContract.RenamePathSpec(fs, inputs.now, inputs.failures, result.state, source, target, false, err) &&
       result.outcome == MoveOutcome([], SourceRenameFailureMessageSpec(source, target,
                                                                        SourceRenameDiagnosticErrSpec(target, sourceIsDir, err), sourceIsDir && targetWasFound), true)) ||
    (backupPath != "" && exists err: int ::
       IOContract.RenamePathSpec(fs, inputs.now, inputs.failures, result.state, target, backupPath, false, err) &&
       result.outcome == MoveOutcome([], RenameFailureMessageSpec(source, target, err), true)) ||
    (backupPath != "" && exists backupFs: BenchWorld.FileSystem ::
       IOContract.RenamePathSpec(fs, inputs.now, inputs.failures, backupFs, target, backupPath, true, 0) &&
       IOContract.RenamePathSpec(backupFs, inputs.now, inputs.failures, result.state, source, target, true, 0) &&
       result.outcome == MoveOutcome(StepSuccessStdoutSpec(source, target, backupPath, cmd.verbose, cmd.debug), [], false)) ||
    (backupPath != "" && exists err: int ::
       IOContract.RenamePathSpec(fs, inputs.now, inputs.failures, result.state, target, backupPath, true, 0) &&
       IOContract.RenamePathSpec(result.state, inputs.now, inputs.failures, result.state, source, target, false, err) &&
       result.outcome == MoveOutcome([], SourceRenameFailureMessageSpec(source, target,
                                                                        SourceRenameDiagnosticErrSpec(target, sourceIsDir, err), false), true))
  }

  /** Specifies replacement of an existing target under the selected backup policy. */
  ghost predicate ExistingTargetRenameAllowed(edge: MoveEdge,
                                              source: string, target: string, cmd: Schema.MvCmd)
  {
    var fs := edge.start;
    var result := edge.result;
    if BackupWouldDestroySource(cmd, fs, source, target) then
      result.state == fs && result.outcome == MoveOutcome([], BackupWouldDestroySourceMessageSpec(source, target), true)
    else if cmd.backupMode == Schema.BackupOff then
      RenameAllowed(edge, source, target, "", cmd.verbose, cmd.debug)
    else
      exists backupPath: string ::
        BackupTargetSpecFields(fs, target, cmd.backupMode, cmd.backupSuffix, backupPath) &&
        RenameAllowed(edge, source, target, backupPath, cmd.verbose, cmd.debug)
  }

  /** Allows a parent lookup error when equal leaf names require directory-entry comparison. */
  ghost predicate ParentMetadataFailure(edge: MoveEdge,
                                        source: string, target: string, cmd: Schema.MvCmd)
  {
    var fs := edge.start;
    var result := edge.result;
    var sourceName := EntryNameSpec(source);
    var targetName := EntryNameSpec(target);
    cmd.overwriteMode != Schema.OverwriteSkip &&
    cmd.updateMode != Schema.UpdateNone && cmd.updateMode != Schema.UpdateNoneFail &&
    sourceName.leaf == targetName.leaf &&
    exists failedPath: string, status: BenchWorld.FileStatus, err: int ::
      failedPath in {sourceName.parent, targetName.parent} &&
      IOContract.FileStatusStructureContractFields(fs, failedPath, false, false, status, err) &&
      err > 0 && result.state == fs &&
      result.outcome == MoveOutcome([], ParentStatFailureMessageSpec(failedPath, err), true)
  }
  /** Specifies a move under abstract metadata, overwrite, update, and backup contracts. */
  ghost predicate OriginalMoveAllowed(edge: MoveEdge,
                                      source: string, target: string, cmd: Schema.MvCmd, cwd: BenchWorld.Path)
  {
    var fs := edge.start;
    var result := edge.result;
    exists sourceOk: bool, sourceIsDir: bool, sourceErr: int ::
      IOContract.IsDirectoryStrictContractFields(fs, source, false, sourceOk, sourceIsDir, sourceErr) &&
      if !sourceOk then
        result.state == fs && result.outcome == MoveOutcome([], SourceStatFailureMessageSpec(source, sourceErr), true)
      else
        exists found: bool, existsErr: int ::
          StatusExistsOutcomeFields(fs, target, false, found, existsErr) &&
          if !found then
            RenameAllowed(edge, source, target, "", cmd.verbose, cmd.debug)
          else if cmd.overwriteMode == Schema.OverwriteSkip || cmd.updateMode == Schema.UpdateNone then
            result.state == fs && result.outcome == MoveOutcome(SkipStdoutSpec(target, cmd.debug), [], false)
          else if cmd.updateMode == Schema.UpdateNoneFail then
            result.state == fs && result.outcome == MoveOutcome([], NotReplacingMessageSpec(target), true)
          else if SameFileMustBeRejected(cmd, fs, cwd, source, target) then
            result.state == fs && result.outcome == MoveOutcome([], SameFileMessageSpec(source, target), true)
          else if cmd.updateMode == Schema.UpdateOlder then
            // The abstract relation has no timestamp constraint; observations below
            // determine whether this command skips or attempts the rename.
            (result.state == fs && result.outcome == MoveOutcome(SkipStdoutSpec(target, cmd.debug), [], false)) ||
            ExistingTargetRenameAllowed(edge, source, target, cmd)
          else ExistingTargetRenameAllowed(edge, source, target, cmd)
  }

  /** Allows an abstract move or a move justified by observed metadata failures. */
  ghost predicate MoveAllowed(edge: MoveEdge,
                              source: string, target: string, cmd: Schema.MvCmd, cwd: BenchWorld.Path)
  {
    var fs := edge.start;
    OriginalMoveAllowed(edge, source, target, cmd, cwd) ||
    ParentMetadataFailure(edge, source, target, cmd) ||
    (exists inputs: NativeStatusInputs, first: nat, calls: seq<StatusCallEvidence> ::
       StatusCallsFor(inputs, first, calls) &&
       ObservedMoveAllowed(edge, source, target, cmd, cwd, calls, inputs) &&
       ObservedMetadataFault(source, fs, cwd, calls, inputs))
  }
  /** Specifies the move outcome after identity, timestamp, and backup-collision checks. */
  ghost predicate ObservedClassificationAllowed(edge: MoveEdge,
                                                source: string, target: string, cmd: Schema.MvCmd, cwd: BenchWorld.Path,
                                                calls: seq<StatusCallEvidence>, inputs: NativeStatusInputs,
                                                sourceName: EntryName, targetName: EntryName,
                                                resolveOk: bool, resolvedSource: string, resolveErr: int, afterEntries: nat)
  {
    var fs := edge.start;
    var result := edge.result;
    |calls| >= 4 &&
    MoveComparisonObservations(fs, cwd, source, target, calls,
                               sourceName.parent, targetName.parent, sourceName.leaf, targetName.leaf,
                               resolveOk, resolvedSource, resolveErr, afterEntries, inputs) &&
    (if sourceName.leaf == targetName.leaf && (!calls[2].ok || !calls[3].ok) then
       result.state == fs && result.outcome == MoveOutcome([], ParentStatFailureMessageSpec(
                                                             if !calls[2].ok then sourceName.parent else targetName.parent,
                                                             if !calls[2].ok then calls[2].err else calls[3].err), true)
     else if ObservedReferentParentFailure(calls, targetName.leaf, resolveOk, resolvedSource) then
       |calls| == afterEntries &&
       result.state == fs &&
       var referentName := EntryNameSpec(resolvedSource);
       result.outcome == MoveOutcome([], ParentStatFailureMessageSpec(
                                           if !calls[5].ok then referentName.parent else targetName.parent,
                                           if !calls[5].ok then calls[5].err else calls[3].err), true)
     else if ObservedSameFileRejection(cmd, calls, sourceName.leaf, targetName.leaf, resolveOk, resolvedSource) then
       |calls| == afterEntries &&
       result.state == fs && result.outcome == MoveOutcome([], SameFileMessageSpec(source, target), true)
     else if cmd.updateMode == Schema.UpdateOlder &&
             !SourceNewerSpec(calls[0].status.times.mtimeSec, calls[0].status.times.mtimeNsec,
                              calls[1].status.times.mtimeSec, calls[1].status.times.mtimeNsec) then
       |calls| == afterEntries &&
       result.state == fs && result.outcome == MoveOutcome(SkipStdoutSpec(target, cmd.debug), [], false)
     else
       var collisionNeeded :=
         (cmd.backupMode == Schema.BackupSimple || cmd.backupMode == Schema.BackupExisting) &&
         sourceName.leaf == targetName.leaf + cmd.backupSuffix;
       var afterCollision := afterEntries + (if collisionNeeded then 1 else 0);
       afterCollision <= |calls| &&
       (collisionNeeded ==>
          StatusRequest(calls[afterEntries], fs,
                        Basename.SimpleBackupPathSpec(target, cmd.backupSuffix), true)) &&
       (if collisionNeeded && calls[afterEntries].ok && calls[afterEntries].status.hostKey == calls[0].status.hostKey then
          |calls| == afterCollision &&
          result.state == fs && result.outcome == MoveOutcome([], BackupWouldDestroySourceMessageSpec(source, target), true)
        else
          BackupStatusSuffix(cmd.backupMode, fs, target, calls[afterCollision..]) &&
          exists backupPath: string ::
            BackupPathFromObservations(cmd, fs, target, calls[afterCollision..], backupPath) &&
            ObservedRenameAllowed(edge, source, target, backupPath, cmd,
                                  calls[0].status.kind == BenchWorld.DirectoryKind, true, inputs)))
  }

  /** Relates observed source and target metadata to a move, skip, or error outcome. */
  ghost predicate ObservedMoveAllowed(edge: MoveEdge,
                                      source: string, target: string, cmd: Schema.MvCmd, cwd: BenchWorld.Path,
                                      calls: seq<StatusCallEvidence>, inputs: NativeStatusInputs)
  {
    var fs := edge.start;
    var result := edge.result;
    |calls| >= 1 && StatusRequest(calls[0], fs, source, false) &&
    (if !calls[0].ok then
       |calls| == 1 &&
       result.state == fs && result.outcome == MoveOutcome([], SourceStatFailureMessageSpec(source, calls[0].err), true)
     else
       |calls| >= 2 && StatusRequest(calls[1], fs, target, false) &&
       (if !calls[1].ok then
          |calls| == 2 &&
          ObservedRenameAllowed(edge, source, target, "", cmd,
                                calls[0].status.kind == BenchWorld.DirectoryKind, false, inputs)
        else if cmd.overwriteMode == Schema.OverwriteSkip || cmd.updateMode == Schema.UpdateNone then
          |calls| == 2 &&
          result.state == fs && result.outcome == MoveOutcome(SkipStdoutSpec(target, cmd.debug), [], false)
        else if cmd.updateMode == Schema.UpdateNoneFail then
          |calls| == 2 &&
          result.state == fs && result.outcome == MoveOutcome([], NotReplacingMessageSpec(target), true)
        else
          var sourceName := EntryNameSpec(source);
          var targetName := EntryNameSpec(target);
          exists resolveOk: bool, resolvedSource: string, resolveErr: int, afterEntries: nat ::
            ObservedClassificationAllowed(edge, source, target, cmd, cwd, calls, inputs,
                                          sourceName, targetName, resolveOk, resolvedSource, resolveErr, afterEntries)))
  }

  /** Combines observed move behavior with its status interval and fault-free abstract contract. */
  ghost predicate ObservedStepAllowed(edge: MoveEdge,
                                      source: string, target: string, cmd: Schema.MvCmd, cwd: BenchWorld.Path, observations: NativeStatusInputs,
                                      firstStatus: nat, afterStatus: nat, calls: seq<StatusCallEvidence>)
  {
    var fs := edge.start;
    afterStatus == firstStatus + |calls| && StatusCallsFor(observations, firstStatus, calls) &&
    ObservedMoveAllowed(edge, source, target, cmd, cwd, calls, observations) &&
    (!ObservedMetadataFault(source, fs, cwd, calls, observations) ==>
       OriginalMoveAllowed(edge, source, target, cmd, cwd))
  }

  /** Combines the outputs and failure flags of two consecutive moves or batches. */
  ghost function JoinOutcomes(first: MoveOutcome, rest: MoveOutcome): MoveOutcome
  {
    MoveOutcome(first.stdoutFragment + rest.stdoutFragment,
                first.stderrFragment + rest.stderrFragment, first.failed || rest.failed)
  }

  /** Composes the allowed moves of the ordered sources between two filesystems. */
  ghost opaque predicate BatchMovesAllowed(
    sources: seq<string>, directory: string, cmd: Schema.MvCmd,
    beforeFs: BenchWorld.FileSystem, cwd: BenchWorld.Path, afterFs: BenchWorld.FileSystem,
    outcome: MoveOutcome
  )
    decreases |sources|
  {
    if sources == [] then
      beforeFs == afterFs && outcome == MoveOutcome([], [], false)
    else
      var source := NormalizeSourceSpec(sources[0], cmd.stripTrailingSlashes);
      exists step: MoveStep, rest: MoveOutcome ::
        MoveAllowed(MoveEdge(beforeFs, step), source, TargetInDirectorySpec(directory, source), cmd, cwd) &&
        BatchMovesAllowed(sources[1..], directory, cmd, step.state, cwd, afterFs, rest) &&
        outcome == JoinOutcomes(step.outcome, rest)
  }

  /** Composes the observed moves and their consecutive status intervals in source order. */
  ghost opaque predicate ObservedBatchMovesAllowed(
    sources: seq<string>, directory: string, cmd: Schema.MvCmd,
    beforeFs: BenchWorld.FileSystem, cwd: BenchWorld.Path, afterFs: BenchWorld.FileSystem,
    outcome: MoveOutcome, observations: NativeStatusInputs, firstStatus: nat, calls: seq<StatusCallEvidence>
  )
    decreases |sources|
  {
    if sources == [] then
      beforeFs == afterFs && outcome == MoveOutcome([], [], false) && calls == []
    else
      var source := NormalizeSourceSpec(sources[0], cmd.stripTrailingSlashes);
      exists step: MoveStep, rest: MoveOutcome, count: nat ::
        count <= |calls| &&
        ObservedStepAllowed(MoveEdge(beforeFs, step), source, TargetInDirectorySpec(directory, source), cmd, cwd,
                            observations, firstStatus, firstStatus + count, calls[..count]) &&
        ObservedBatchMovesAllowed(sources[1..], directory, cmd, step.state, cwd, afterFs, rest,
                                  observations, firstStatus + count, calls[count..]) &&
        outcome == JoinOutcomes(step.outcome, rest)
  }

  /** Specifies target selection, file effects, and planned output for a two-operand move. */
  twostate predicate CandidateRunTwoOperand(io: BenchIO.IO, cmd: Schema.MvCmd,
                                            plannedStdout: BenchWorld.Bytes, plannedStderr: BenchWorld.Bytes, exit: int)
    reads io.fsRegion
    requires |cmd.operands| == 2
  {
    var source := NormalizeSourceSpec(cmd.operands[0], cmd.stripTrailingSlashes);
    var destination := cmd.operands[1];
    exists target: string, outcome: MoveOutcome ::
      (if cmd.noTargetDirectory then target == destination
       else exists ok: bool, isDirectory: bool, err: int ::
              IOContract.IsDirectoryContractFields(old(io.fs()), destination, true, ok, isDirectory, err) &&
              target == (if ok && isDirectory then TargetInDirectorySpec(destination, source) else destination)) &&
      MoveAllowed(MoveEdge(old(io.fs()), MoveStep(io.fs(), outcome)), source, target, cmd, old(io.cwd())) &&
      plannedStdout == outcome.stdoutFragment &&
      plannedStderr == outcome.stderrFragment &&
      exit == (if outcome.failed then 1 else 0)
  }

  /** Relates command execution to consumed status observations and planned output. */
  twostate predicate ObservedStatusSpec(io: BenchIO.IO, raw: Schema.MvCmdRaw,
                                        plannedStdout: BenchWorld.Bytes, plannedStderr: BenchWorld.Bytes, exit: int,
                                        observations: NativeStatusInputs, calls: seq<StatusCallEvidence>)
    reads io.statusObservationsRegion, io.fsRegion
  {
    var cmd := Schema.Command(raw);
    io.statusCursor() == old(io.statusCursor()) + |calls| &&
    StatusCallsFor(observations, old(io.statusCursor()), calls) &&
    (if cmd.mode != Schema.ModeRun ||
        (cmd.targetDirectory != "" && cmd.noTargetDirectory) || |cmd.operands| == 0 ||
        (cmd.targetDirectory == "" && |cmd.operands| == 1) ||
        (cmd.targetDirectory == "" && cmd.noTargetDirectory && |cmd.operands| > 2) then
       |calls| == 0
     else if cmd.targetDirectory != "" then
       |calls| >= 1 && StatusRequest(calls[0], old(io.fs()), cmd.targetDirectory, true) &&
       (if calls[0].ok && calls[0].status.kind == BenchWorld.DirectoryKind then
          exists failed: bool ::
            ObservedBatchMovesAllowed(cmd.operands, cmd.targetDirectory, cmd, old(io.fs()), old(io.cwd()), io.fs(),
                                      MoveOutcome(plannedStdout, plannedStderr, failed),
                                      observations, old(io.statusCursor()) + 1, calls[1..]) &&
            exit == (if failed then 1 else 0)
        else |calls| == 1)
     else if |cmd.operands| == 2 then
       var source := NormalizeSourceSpec(cmd.operands[0], cmd.stripTrailingSlashes);
       var destination := cmd.operands[1];
       if cmd.noTargetDirectory then
         exists outcome: MoveOutcome ::
           ObservedStepAllowed(MoveEdge(old(io.fs()), MoveStep(io.fs(), outcome)),
                               source, destination, cmd, old(io.cwd()), observations,
                               old(io.statusCursor()), io.statusCursor(), calls) &&
           exit == (if outcome.failed then 1 else 0) &&
           plannedStdout == outcome.stdoutFragment &&
           plannedStderr == outcome.stderrFragment
       else
         |calls| >= 1 && StatusRequest(calls[0], old(io.fs()), destination, true) &&
         var target := if calls[0].ok && calls[0].status.kind == BenchWorld.DirectoryKind
                       then TargetInDirectorySpec(destination, source) else destination;
         exists outcome: MoveOutcome ::
           ObservedStepAllowed(MoveEdge(old(io.fs()), MoveStep(io.fs(), outcome)),
                               source, target, cmd, old(io.cwd()), observations,
                               old(io.statusCursor()) + 1, io.statusCursor(), calls[1..]) &&
           exit == (if outcome.failed then 1 else 0) &&
           plannedStdout == outcome.stdoutFragment &&
           plannedStderr == outcome.stderrFragment
     else
       var directory := cmd.operands[|cmd.operands| - 1];
       var sources := cmd.operands[..|cmd.operands| - 1];
       |calls| >= 1 && StatusRequest(calls[0], old(io.fs()), directory, true) &&
       (if calls[0].ok && calls[0].status.kind == BenchWorld.DirectoryKind then
          exists failed: bool ::
            ObservedBatchMovesAllowed(sources, directory, cmd, old(io.fs()), old(io.cwd()), io.fs(),
                                      MoveOutcome(plannedStdout, plannedStderr, failed),
                                      observations, old(io.statusCursor()) + 1, calls[1..]) &&
            exit == (if failed then 1 else 0)
        else |calls| == 1))
  }

  /** Specifies a batch move into a validated directory or a target validation error. */
  twostate predicate CandidateRunIntoDirectory(
    io: BenchIO.IO,
    sources: seq<string>,
    directory: string,
    explicitTargetDirectory: bool,
    cmd: Schema.MvCmd,
    plannedStdout: BenchWorld.Bytes,
    plannedStderr: BenchWorld.Bytes,
    exit: int
  )
    reads io.fsRegion
  {
    (TargetDirectoryCheckSpecFields(directory, old(io.fs()), true, 0) &&
     exists failed: bool ::
       BatchMovesAllowed(sources, directory, cmd, old(io.fs()), old(io.cwd()), io.fs(),
                         MoveOutcome(plannedStdout, plannedStderr, failed)) &&
       exit == (if failed then 1 else 0)) ||
    (exists directoryErr: int ::
       TargetDirectoryCheckSpecFields(
         directory, old(io.fs()), false, directoryErr
       ) &&
       io.fs() == old(io.fs()) &&
       exit == 1 &&
       plannedStdout == [] &&
       plannedStderr == TargetFailureMessageSpec(
         directory, explicitTargetDirectory, directoryErr
       ))
  }

  /** Relates a decoded command to file effects, planned output, diagnostics, and exit status. */
  twostate predicate CandidateSpec(
    io: BenchIO.IO,
    raw: Schema.MvCmdRaw,
    plannedStdout: BenchWorld.Bytes,
    plannedStderr: BenchWorld.Bytes,
    exit: int
  )
    reads io.fsRegion
  {
    var cmd := Schema.Command(raw);
    if cmd.mode == Schema.ModeInvalidBackup then
      io.fs() == old(io.fs()) &&
      exit == 1 &&
      plannedStdout == [] &&
      plannedStderr ==
      InvalidBackupArgumentMessageSpec(cmd.invalidBackupArg)
    else if cmd.mode == Schema.ModeInvalidUpdate then
      io.fs() == old(io.fs()) &&
      exit == 1 &&
      plannedStdout == [] &&
      plannedStderr ==
      InvalidUpdateArgumentMessageSpec(cmd.invalidUpdateArg)
    else if cmd.mode == Schema.ModeHelp then
      io.fs() == old(io.fs()) &&
      exit == 0 &&
      plannedStdout == HelpTextSpec() &&
      plannedStderr == []
    else if cmd.mode == Schema.ModeVersion then
      io.fs() == old(io.fs()) &&
      exit == 0 &&
      plannedStdout == VersionTextSpec() &&
      plannedStderr == []
    else if cmd.targetDirectory != "" && cmd.noTargetDirectory then
      io.fs() == old(io.fs()) &&
      exit == 1 &&
      plannedStdout == [] &&
      plannedStderr == TargetDirectoryConflictMessageSpec()
    else if |cmd.operands| == 0 then
      io.fs() == old(io.fs()) &&
      exit == 1 &&
      plannedStdout == [] &&
      plannedStderr == MissingFileOperandMessageSpec()
    else if cmd.targetDirectory != "" then
      CandidateRunIntoDirectory(io, cmd.operands, cmd.targetDirectory, true, cmd, plannedStdout, plannedStderr, exit)
    else if |cmd.operands| == 1 then
      io.fs() == old(io.fs()) &&
      exit == 1 &&
      plannedStdout == [] &&
      plannedStderr ==
      MissingDestinationMessageSpec(cmd.operands[0])
    else if cmd.noTargetDirectory && |cmd.operands| > 2 then
      io.fs() == old(io.fs()) &&
      exit == 1 &&
      plannedStdout == [] &&
      plannedStderr == ExtraOperandMessageSpec(cmd.operands[2])
    else if |cmd.operands| == 2 then
      CandidateRunTwoOperand(io, cmd, plannedStdout, plannedStderr, exit)
    else
      CandidateRunIntoDirectory(io, cmd.operands[..|cmd.operands| - 1], cmd.operands[|cmd.operands| - 1], false, cmd, plannedStdout, plannedStderr, exit)
  }

  /** Formats a diagnostic for a standard output write failure. */
  function WriteErrorText(reason: string): BenchWorld.Bytes
  {
    "mv: write error: " + Utf8.Encode(reason) + "\n"
  }

  /** Relates planned output to stream writes and the exit status, including write failures. */
  twostate predicate Emit(
    io: BenchIO.IO,
    output: BenchWorld.Bytes, diagnostics: BenchWorld.Bytes,
    normalExit: int, exit: int
  )
    reads io.stdoutRegion, io.stderrRegion, io.trustedStreamsRegion
  {
    var observations := io.trustedStreams();
    var stdoutResult := if output == [] then BenchWorld.StreamWriteResult(0, old(io.stdout()), 0)
                        else observations(BenchWorld.StreamWriteStdout(old(io.stdout()), output));
    stdoutResult.StreamWriteResult? &&
    var finalDiagnostics := diagnostics +
                            (if stdoutResult.err == 0 then [] else WriteErrorText(IOContract.CLocaleErrnoTextResult(stdoutResult.err)));
    var stderrResult := if finalDiagnostics == [] then BenchWorld.StreamWriteResult(0, old(io.stderr()), 0)
                        else observations(BenchWorld.StreamWriteStderr(old(io.stderr()), finalDiagnostics));
    stderrResult.StreamWriteResult? &&
    (if output == [] then io.stdout() == old(io.stdout())
     else IOContract.WriteStdoutSpec(old(io.stdout()), observations, io.stdout(), output, stdoutResult.committed, stdoutResult.err)) &&
    (if finalDiagnostics == [] then io.stderr() == old(io.stderr())
     else IOContract.WriteStderrSpec(old(io.stderr()), observations, io.stderr(), finalDiagnostics, stderrResult.committed, stderrResult.err)) &&
    exit == (if stdoutResult.err != 0 || stderrResult.err != 0 then 1 else normalExit)
  }

  /** Specifies mv file effects, status observations, output streams, and exit status. */
  opaque twostate predicate Spec(raw: Schema.MvCmdRaw, io: BenchIO.IO, exit: int)
    reads io.Footprint()
  {
    exists output: BenchWorld.Bytes, diagnostics: BenchWorld.Bytes, normalExit: int ::
      CandidateSpec(io, raw, output, diagnostics, normalExit) &&
      (exists calls: seq<StatusCallEvidence> ::
         ObservedStatusSpec(io, raw, output, diagnostics, normalExit, NativeStatusInputs(io.statusObservations(), io.trustedNativeFailures(), io.now()), calls)) &&
      Emit(io, output, diagnostics, normalExit, exit)
  }
}
