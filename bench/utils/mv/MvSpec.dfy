include "../../core/World.dfy"
include "../../core/Utf8.dfy"
include "../../core/IO.dfy"
include "../../core/IOContract.dfy"
include "MvPathSpec.dfy"
include "MvQuoteSpec.dfy"
include "MvSchema.dfy"

module MvSpec {
  import BenchIO
  import IOContract
  import BenchWorld
  import Basename = MvPathSpec
  import Quote = MvQuoteSpec
  import Dirname = MvPathSpec
  import Schema = MvSchema
  import Utf8 = Utf8Semantics




  const ENOTDIR: int := 20
  const EISDIR: int := 21
  const EINVAL: int := 22
  const ENOTEMPTY: int := 39
  const EBUSY: int := 16

  function ErrnoTextSpec(err: int): string
  {
    if err == 2 then
      "No such file or directory"
    else if err == 13 then
      "Permission denied"
    else if err == 16 then
      "Device or resource busy"
    else if err == 17 then
      "File exists"
    else if err == 20 then
      "Not a directory"
    else if err == 21 then
      "Is a directory"
    else if err == 22 then
      "Invalid argument"
    else if err == 39 then
      "Directory not empty"
    else if err == 40 then
      "Too many levels of symbolic links"
    else
      "unknown error"
  }

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

  function MissingFileOperandMessageSpec(): BenchWorld.Bytes
  {
    "mv: missing file operand\nTry 'mv --help' for more information.\n"
  }

  function MissingDestinationMessageSpec(source: string): BenchWorld.Bytes
  {
    Utf8.Encode("mv: missing destination file operand after '" + source + "'\n")
    + "Try 'mv --help' for more information.\n"
  }

  function ExtraOperandMessageSpec(operand: string): BenchWorld.Bytes
  {
    Utf8.Encode("mv: extra operand '" + operand + "'\nTry 'mv --help' for more information.\n")
  }

  function TargetDirectoryConflictMessageSpec(): BenchWorld.Bytes
  {
    "mv: cannot combine --target-directory (-t) and --no-target-directory (-T)\n"
  }

  function InvalidBackupArgumentMessageSpec(value: string): BenchWorld.Bytes
  {
    Utf8.Encode("mv: invalid argument '" + value + "' for 'backup type'\n")
    + "Valid arguments are:\n"
    + "  - 'none', 'off'\n"
    + "  - 'simple', 'never'\n"
    + "  - 'existing', 'nil'\n"
    + "  - 'numbered', 't'\n"
    + "Try 'mv --help' for more information.\n"
  }

  function InvalidUpdateArgumentMessageSpec(value: string): BenchWorld.Bytes
  {
    Utf8.Encode("mv: invalid argument '" + value + "' for '--update'\n")
    + "Valid arguments are:\n"
    + "  - 'all'\n"
    + "  - 'none'\n"
    + "  - 'none-fail'\n"
    + "  - 'older'\n"
    + "Try 'mv --help' for more information.\n"
  }

  function TargetFailureMessageSpec(path: string, explicitTargetDirectory: bool, err: int): BenchWorld.Bytes
  {
    if explicitTargetDirectory then
      Utf8.Encode("mv: target directory '" + path + "': " + ErrnoTextSpec(err) + "\n")
    else
      Utf8.Encode("mv: target '" + path + "': " + ErrnoTextSpec(err) + "\n")
  }

  function SourceStatFailureMessageSpec(source: string, err: int): BenchWorld.Bytes
  {
    Utf8.Encode("mv: cannot stat '" + source + "': " + ErrnoTextSpec(err) + "\n")
  }

  function RenameFailureMessageSpec(source: string, target: string, err: int): BenchWorld.Bytes
  {
    if err == EISDIR then
      Utf8.Encode("mv: cannot overwrite directory '" + target + "' with non-directory '" + source + "'\n")
    else if err == ENOTEMPTY then
      Utf8.Encode("mv: cannot overwrite '" + target + "': " + ErrnoTextSpec(err) + "\n")
    else
      Utf8.Encode("mv: cannot move '" + source + "' to '" + target + "': " + ErrnoTextSpec(err) + "\n")
  }

  function SourceRenameFailureMessageSpec(
    source: string,
    target: string,
    err: int
  ): BenchWorld.Bytes
  {
    if err == EINVAL then
      Utf8.Encode("mv: cannot move '" + source + "' to a subdirectory of itself, '" + target + "'\n")
    else
      RenameFailureMessageSpec(source, target, err)
  }

  function SourceRenameDiagnosticErrSpec(
    target: string,
    sourceIsDir: bool,
    renameErr: int
  ): int
  {
    if target == "" then
      if sourceIsDir then EBUSY else EISDIR
    else
      renameErr
  }

  function SameFileMessageSpec(source: string, target: string): BenchWorld.Bytes
  {
    "mv: " + Quote.SpecQuoteAfBytes(Utf8.Encode(source)) +
    " and " + Quote.SpecQuoteAfBytes(Utf8.Encode(target)) +
    " are the same file\n"
  }

  function BackupWouldDestroySourceMessageSpec(
    source: string,
    target: string
  ): BenchWorld.Bytes
  {
    "mv: backing up " +
    Quote.SpecQuoteAfBytes(Utf8.Encode(target)) +
    " might destroy source;  " +
    Quote.SpecQuoteAfBytes(Utf8.Encode(source)) +
    " not moved\n"
  }

  function VerboseRenameMessageSpec(source: string, target: string): BenchWorld.Bytes
  {
    "renamed '" + source + "' -> '" + target + "'\n"
  }

  function VerboseRenameWithBackupMessageSpec(source: string, target: string, backup: string): BenchWorld.Bytes
  {
    "renamed '" + source + "' -> '" + target + "' (backup: '" + backup + "')\n"
  }

  function DebugSkipMessageSpec(target: string): BenchWorld.Bytes
  {
    "skipped '" + target + "'\n"
  }

  function NotReplacingMessageSpec(target: string): BenchWorld.Bytes
  {
    Utf8.Encode("mv: not replacing '" + target + "'\n")
  }




















  function ShowActionMessageSpec(verbose: bool, debug: bool): bool
  {
    verbose || debug
  }

  function SkipStdoutSpec(target: string, debug: bool): BenchWorld.Bytes
  {
    if debug then DebugSkipMessageSpec(target) else []
  }

  function SourceLeafNameSpec(source: string): string
  {
    var leaf := BenchWorld.LeafName(source);
    if leaf == "" then source else leaf
  }

  // Both stay compilable structural recursions rather than quantifiers: a
  // quantifier is ghost in Dafny, and the non-ghost `NormalizeSourceSpec`
  // below calls these.
  function AllSlashesSpec(text: string): bool
    decreases |text|
  {
    |text| == 0 ||
    (text[0] == '/' && AllSlashesSpec(text[1..]))
  }

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

  function NormalizeSourceSpec(source: string, stripTrailingSlashes: bool): string
  {
    if !stripTrailingSlashes then
      source
    else if source == "" then
      source
    else if AllSlashesSpec(source) then
      "/"
    else
      TrimTrailingSlashesSpec(source)
  }

  function TargetInDirectorySpec(directory: string, source: string): string
  {
    BenchWorld.AppendPath(directory, SourceLeafNameSpec(source))
  }

  ghost predicate SameInode(
    fs: BenchWorld.FileSystem,
    left: BenchWorld.Path,
    right: BenchWorld.Path
  )
  {
    exists resolvedLeft: BenchWorld.Path, resolvedRight: BenchWorld.Path ::
      IOContract.ResolvePathForMetadataFields(fs, left, false) ==
      BenchWorld.Ok(resolvedLeft) &&
      IOContract.ResolvePathForMetadataFields(fs, right, false) ==
      BenchWorld.Ok(resolvedRight) &&
      BenchWorld.InodeSameObject(fs, resolvedLeft, resolvedRight)
  }

  ghost predicate SameDirectoryEntry(
    fs: BenchWorld.FileSystem,
    left: BenchWorld.Path,
    right: BenchWorld.Path
  )
  {
    exists
      leftParent: string,
      rightParent: string,
      leftLeaf: string,
      rightLeaf: string,
      resolvedLeftParent: BenchWorld.Path,
      resolvedRightParent: BenchWorld.Path
      ::
        Dirname.DirnameRelation(left, leftParent) &&
        Dirname.DirnameRelation(right, rightParent) &&
        Basename.BasenameRelation(left, leftLeaf) &&
        Basename.BasenameRelation(right, rightLeaf) &&
        leftLeaf == rightLeaf &&
        IOContract.ResolvePathForMetadataFields(fs, leftParent, false) ==
        BenchWorld.Ok(resolvedLeftParent) &&
        IOContract.ResolvePathForMetadataFields(fs, rightParent, false) ==
        BenchWorld.Ok(resolvedRightParent) &&
        BenchWorld.InodeSameObject(
          fs, resolvedLeftParent, resolvedRightParent
        )
  }

  ghost predicate SourceSymlinkReferentHasTargetName(
    fs: BenchWorld.FileSystem,
    preCwd: BenchWorld.Path,
    source: BenchWorld.Path,
    target: BenchWorld.Path
  )
  {
    exists
      resolvedSource: BenchWorld.Path,
      resolvedReferent: BenchWorld.Path
      ::
        IOContract.ResolvePathForMetadataFields(fs, source, false) ==
        BenchWorld.Ok(resolvedSource) &&
        BenchWorld.FsContainsPath(fs, resolvedSource) &&
        BenchWorld.FsNodeAt(fs, resolvedSource).Symlink? &&
        IOContract.ResolvePathIdentityContractFields(
          fs, preCwd, source, true, resolvedReferent, 0
        ) &&
        SameDirectoryEntry(fs, resolvedReferent, target)
  }

  datatype SameFileDecision =
    | ContinueMove
    | RejectSameFile

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

  ghost predicate SameFilePolicyRelation(
    cmd: Schema.MvCmd,
    fs: BenchWorld.FileSystem,
    preCwd: BenchWorld.Path,
    source: BenchWorld.Path,
    target: BenchWorld.Path,
    decision: SameFileDecision
  )
  {
    decision ==
    if SameFileMustBeRejected(cmd, fs, preCwd, source, target)
    then RejectSameFile
    else ContinueMove
  }

  lemma SameFilePolicyTotal(
    cmd: Schema.MvCmd,
    fs: BenchWorld.FileSystem,
    preCwd: BenchWorld.Path,
    source: BenchWorld.Path,
    target: BenchWorld.Path
  )
    ensures exists decision: SameFileDecision ::
              SameFilePolicyRelation(
                cmd, fs, preCwd, source, target, decision
              )
  {
    var decision :=
      if SameFileMustBeRejected(cmd, fs, preCwd, source, target)
      then RejectSameFile
      else ContinueMove;
    assert SameFilePolicyRelation(
        cmd, fs, preCwd, source, target, decision
      );
  }

  lemma SameFilePolicyFunctional(
    cmd: Schema.MvCmd,
    fs: BenchWorld.FileSystem,
    preCwd: BenchWorld.Path,
    source: BenchWorld.Path,
    target: BenchWorld.Path,
    left: SameFileDecision,
    right: SameFileDecision
  )
    requires SameFilePolicyRelation(
               cmd, fs, preCwd, source, target, left
             )
    requires SameFilePolicyRelation(
               cmd, fs, preCwd, source, target, right
             )
    ensures left == right
  {
  }

  function DigitCharSpec(d: nat): char
    requires d < 10
  {
    if d == 0 then '0'
    else if d == 1 then '1'
    else if d == 2 then '2'
    else if d == 3 then '3'
    else if d == 4 then '4'
    else if d == 5 then '5'
    else if d == 6 then '6'
    else if d == 7 then '7'
    else if d == 8 then '8'
    else '9'
  }

  function DecimalNatSpec(n: nat): string
    decreases n
  {
    if n < 10 then
      [DigitCharSpec(n)]
    else
      DecimalNatSpec(n / 10) + [DigitCharSpec(n % 10)]
  }

  function NumberedBackupPathSpec(target: string, index: nat): string
    requires index >= 1
  {
    target + ".~" + DecimalNatSpec(index) + "~"
  }

  function SimpleBackupPathSpec(target: string, suffix: string): string
  {
    target + suffix
  }

  function SourceNewerSpec(srcSec: int, srcNsec: int, dstSec: int, dstNsec: int): bool
  {
    srcSec > dstSec || (srcSec == dstSec && srcNsec > dstNsec)
  }

  function TargetDirectoryErrSpec(statOk: bool, isDir: bool, statErr: int): int
  {
    if statOk then
      if !isDir then ENOTDIR else statErr
    else
      statErr
  }

  function StepSuccessStdoutSpec(source: string, target: string, backupPath: string, verbose: bool, debug: bool): BenchWorld.Bytes
  {
    if !ShowActionMessageSpec(verbose, debug) then
      []
    else if backupPath == "" then
      VerboseRenameMessageSpec(source, target)
    else
      VerboseRenameWithBackupMessageSpec(source, target, backupPath)
  }

  datatype MoveOutcome = MoveOutcome(
    stdoutFragment: BenchWorld.Bytes,
    stderrFragment: BenchWorld.Bytes,
    failed: bool
  )

  ghost function ConcatenateFragments(fragments: seq<BenchWorld.Bytes>): BenchWorld.Bytes
    decreases |fragments|
  {
    if |fragments| == 0 then
      []
    else
      fragments[0] + ConcatenateFragments(fragments[1..])
  }

  ghost predicate NumberedBackupTargetSpecFromFields(preFs: BenchWorld.FileSystem, target: string, start: nat, backupPath: string)
  {
    start >= 1 &&
    exists index: nat, missErr: int ::
      index >= start &&
      backupPath == NumberedBackupPathSpec(target, index) &&
      IOContract.PathExistsContractFields(preFs, backupPath, false, false, missErr) &&
      forall j: nat | start <= j < index ::
        IOContract.PathExistsContractFields(preFs, NumberedBackupPathSpec(target, j), false, true, 0)
  }

  ghost predicate NumberedBackupTargetSpecFields(preFs: BenchWorld.FileSystem, target: string, backupPath: string)
  {
    NumberedBackupTargetSpecFromFields(preFs, target, 1, backupPath)
  }

  ghost predicate BackupTargetSpecFields(preFs: BenchWorld.FileSystem, target: string, backupMode: Schema.BackupMode, suffix: string, backupPath: string)
  {
    if backupMode == Schema.BackupOff then
      backupPath == ""
    else if backupMode == Schema.BackupSimple then
      backupPath == SimpleBackupPathSpec(target, suffix)
    else if backupMode == Schema.BackupExisting then
      ((exists hitErr: int ::
          IOContract.PathExistsContractFields(preFs, NumberedBackupPathSpec(target, 1), false, true, hitErr) &&
          NumberedBackupTargetSpecFields(preFs, target, backupPath)) ||
       (exists missErr: int ::
          IOContract.PathExistsContractFields(preFs, NumberedBackupPathSpec(target, 1), false, false, missErr) &&
          backupPath == SimpleBackupPathSpec(target, suffix)))
    else
      NumberedBackupTargetSpecFields(preFs, target, backupPath)
  }

  ghost predicate BackupWouldDestroySource(
    cmd: Schema.MvCmd,
    fs: BenchWorld.FileSystem,
    source: string,
    target: string
  )
  {
    (cmd.backupMode == Schema.BackupSimple ||
     cmd.backupMode == Schema.BackupExisting) &&
    (exists sourceLeaf: string, targetLeaf: string ::
       Basename.BasenameRelation(source, sourceLeaf) &&
       Basename.BasenameRelation(target, targetLeaf) &&
       sourceLeaf == targetLeaf + cmd.backupSuffix) &&
    exists
      resolvedSource: BenchWorld.Path,
      resolvedBackup: BenchWorld.Path
      ::
        IOContract.ResolvePathForMetadataFields(
          fs, source, false
        ) == BenchWorld.Ok(resolvedSource) &&
        IOContract.ResolvePathForMetadataFields(
          fs, SimpleBackupPathSpec(target, cmd.backupSuffix), true
        ) == BenchWorld.Ok(resolvedBackup) &&
        BenchWorld.InodeSameObject(
          fs, resolvedSource, resolvedBackup
        )
  }

  ghost predicate RenameEffectRelation(
    source: string,
    target: string,
    backupPath: string,
    verbose: bool,
    debug: bool,
    beforeFs: BenchWorld.FileSystem,
    preCwd: BenchWorld.Path,
    afterFs: BenchWorld.FileSystem,
    outcome: MoveOutcome
  )
  {
    (backupPath == "" &&
     IOContract.RenamePathContractFields(beforeFs, source, target, true, 0, afterFs) &&
     outcome == MoveOutcome(StepSuccessStdoutSpec(source, target, "", verbose, debug), [], false)) ||
    (backupPath == "" &&
     exists
       renameErr: int,
       sourceIsDir: bool,
       sourceStatErr: int
       ::
         IOContract.IsDirectoryStrictContractFields(
           beforeFs,
           source,
           false,
           true,
           sourceIsDir,
           sourceStatErr
         ) &&
         IOContract.RenamePathContractFields(beforeFs, source, target, false, renameErr, afterFs) &&
         outcome == MoveOutcome(
           [],
           SourceRenameFailureMessageSpec(
             source,
             target,
             SourceRenameDiagnosticErrSpec(
               target, sourceIsDir, renameErr
             )
           ),
           true
         )) ||
    (backupPath != "" &&
     exists backupErr: int ::
       IOContract.RenamePathContractFields(beforeFs, target, backupPath, false, backupErr, afterFs) &&
       outcome == MoveOutcome([], RenameFailureMessageSpec(source, target, backupErr), true)) ||
    (backupPath != "" &&
     exists backupFs: BenchWorld.FileSystem ::
       IOContract.RenamePathContractFields(beforeFs, target, backupPath, true, 0, backupFs) &&
       IOContract.RenamePathContractFields(backupFs, source, target, true, 0, afterFs) &&
       outcome == MoveOutcome(StepSuccessStdoutSpec(source, target, backupPath, verbose, debug), [], false)) ||
    (backupPath != "" &&
     exists
       backupFs: BenchWorld.FileSystem,
       renameErr: int,
       sourceIsDir: bool,
       sourceStatErr: int
       ::
         IOContract.IsDirectoryStrictContractFields(
           beforeFs,
           source,
           false,
           true,
           sourceIsDir,
           sourceStatErr
         ) &&
         IOContract.RenamePathContractFields(beforeFs, target, backupPath, true, 0, backupFs) &&
         IOContract.RenamePathContractFields(backupFs, source, target, false, renameErr, afterFs) &&
         outcome == MoveOutcome(
           [],
           SourceRenameFailureMessageSpec(
             source,
             target,
             SourceRenameDiagnosticErrSpec(
               target, sourceIsDir, renameErr
             )
           ),
           true
         ))
  }

  ghost predicate ExistingTargetRenameEffectRelation(
    source: string,
    target: string,
    cmd: Schema.MvCmd,
    beforeFs: BenchWorld.FileSystem,
    preCwd: BenchWorld.Path,
    afterFs: BenchWorld.FileSystem,
    outcome: MoveOutcome
  )
  {
    if BackupWouldDestroySource(cmd, beforeFs, source, target) then
      afterFs == beforeFs &&
      outcome == MoveOutcome(
        [],
        BackupWouldDestroySourceMessageSpec(source, target),
        true
      )
    else if cmd.backupMode == Schema.BackupOff then
      RenameEffectRelation(
        source, target, "", cmd.verbose, cmd.debug,
        beforeFs, preCwd, afterFs, outcome
      )
    else
      exists backupPath: string ::
        BackupTargetSpecFields(
          beforeFs, target, cmd.backupMode, cmd.backupSuffix, backupPath
        ) &&
        RenameEffectRelation(
          source, target, backupPath, cmd.verbose, cmd.debug,
          beforeFs, preCwd, afterFs, outcome
        )
  }

  ghost predicate MoveEffectRelation(
    source: string,
    target: string,
    cmd: Schema.MvCmd,
    beforeFs: BenchWorld.FileSystem,
    preCwd: BenchWorld.Path,
    afterFs: BenchWorld.FileSystem,
    outcome: MoveOutcome
  )
  {
    exists sourceOk: bool, sourceIsDir: bool, sourceErr: int ::
      IOContract.IsDirectoryStrictContractFields(
        beforeFs, source, false, sourceOk, sourceIsDir, sourceErr
      ) &&
      if !sourceOk then
        afterFs == beforeFs &&
        outcome == MoveOutcome(
          [], SourceStatFailureMessageSpec(source, sourceErr), true
        )
      else
        exists found: bool, existsErr: int ::
          IOContract.PathExistsContractFields(
            beforeFs, target, false, found, existsErr
          ) &&
          if !found then
            RenameEffectRelation(
              source, target, "", cmd.verbose, cmd.debug,
              beforeFs, preCwd, afterFs, outcome
            )
          else if cmd.overwriteMode == Schema.OverwriteSkip then
            afterFs == beforeFs &&
            outcome == MoveOutcome(SkipStdoutSpec(target, cmd.debug), [], false)
          else if cmd.updateMode == Schema.UpdateNone then
            afterFs == beforeFs &&
            outcome == MoveOutcome(SkipStdoutSpec(target, cmd.debug), [], false)
          else if cmd.updateMode == Schema.UpdateNoneFail then
            afterFs == beforeFs &&
            outcome == MoveOutcome([], NotReplacingMessageSpec(target), true)
          else
            exists decision: SameFileDecision ::
              SameFilePolicyRelation(
                cmd, beforeFs, preCwd, source, target, decision
              ) &&
              if decision == RejectSameFile then
                afterFs == beforeFs &&
                outcome == MoveOutcome(
                  [], SameFileMessageSpec(source, target), true
                )
              else if cmd.updateMode == Schema.UpdateOlder then
                exists
                  timeSourceOk: bool,
                  sourceAtimeSec: int,
                  sourceAtimeNsec: int,
                  sourceMtimeSec: int,
                  sourceMtimeNsec: int,
                  timeSourceIsDir: bool,
                  timeSourceIsSymlink: bool,
                  sourceDevice: int,
                  sourceInode: int,
                  sourceLinkCount: int,
                  timeSourceErr: int,
                  targetOk: bool,
                  targetAtimeSec: int,
                  targetAtimeNsec: int,
                  targetMtimeSec: int,
                  targetMtimeNsec: int,
                  targetIsDir: bool,
                  targetIsSymlink: bool,
                  targetDevice: int,
                  targetInode: int,
                  targetLinkCount: int,
                  targetErr: int
                  ::
                    IOContract.GetFileTimesContractFields(
                      beforeFs, source, false, timeSourceOk,
                      sourceAtimeSec, sourceAtimeNsec,
                      sourceMtimeSec, sourceMtimeNsec,
                      timeSourceIsDir, timeSourceIsSymlink,
                      sourceDevice, sourceInode, sourceLinkCount,
                      timeSourceErr
                    ) &&
                    IOContract.GetFileTimesContractFields(
                      beforeFs, target, false, targetOk,
                      targetAtimeSec, targetAtimeNsec,
                      targetMtimeSec, targetMtimeNsec,
                      targetIsDir, targetIsSymlink,
                      targetDevice, targetInode, targetLinkCount,
                      targetErr
                    ) &&
                    if !timeSourceOk || !targetOk then
                      afterFs == beforeFs &&
                      outcome == MoveOutcome(
                        [],
                        RenameFailureMessageSpec(
                          source, target,
                          if !timeSourceOk then timeSourceErr else targetErr
                        ),
                        true
                      )
                    else if !SourceNewerSpec(
                              sourceMtimeSec, sourceMtimeNsec,
                              targetMtimeSec, targetMtimeNsec
                            ) then
                      afterFs == beforeFs &&
                      outcome == MoveOutcome(
                        SkipStdoutSpec(target, cmd.debug), [], false
                      )
                    else
                      ExistingTargetRenameEffectRelation(
                        source, target, cmd, beforeFs, preCwd, afterFs, outcome
                      )
              else
                ExistingTargetRenameEffectRelation(
                  source, target, cmd, beforeFs, preCwd, afterFs, outcome
                )
  }

  ghost predicate BatchMoveWitnessRelation(
    sources: seq<string>,
    directory: string,
    cmd: Schema.MvCmd,
    beforeFs: BenchWorld.FileSystem,
    preCwd: BenchWorld.Path,
    afterFs: BenchWorld.FileSystem,
    hadError: bool,
    out: BenchWorld.Bytes,
    err: BenchWorld.Bytes,
    fsBounds: seq<BenchWorld.FileSystem>,
    outcomes: seq<MoveOutcome>,
    stdoutFragments: seq<BenchWorld.Bytes>,
    stderrFragments: seq<BenchWorld.Bytes>
  )
  {
    |fsBounds| == |sources| + 1 &&
    |outcomes| == |sources| &&
    |stdoutFragments| == |sources| &&
    |stderrFragments| == |sources| &&
    fsBounds[0] == beforeFs &&
    fsBounds[|fsBounds| - 1] == afterFs &&
    (forall i: nat | i < |sources| ::
       var normalizedSource :=
         NormalizeSourceSpec(sources[i], cmd.stripTrailingSlashes);
       MoveEffectRelation(
         normalizedSource,
         TargetInDirectorySpec(directory, normalizedSource),
         cmd,
         fsBounds[i],
         preCwd,
         fsBounds[i + 1],
         outcomes[i]
       ) &&
       stdoutFragments[i] == outcomes[i].stdoutFragment &&
       stderrFragments[i] == outcomes[i].stderrFragment) &&
    ConcatenateFragments(stdoutFragments) == out &&
    ConcatenateFragments(stderrFragments) == err &&
    (hadError <==>
     exists i: nat :: i < |outcomes| && outcomes[i].failed)
  }

  ghost predicate BatchMoveRelation(
    sources: seq<string>,
    directory: string,
    cmd: Schema.MvCmd,
    beforeFs: BenchWorld.FileSystem,
    preCwd: BenchWorld.Path,
    afterFs: BenchWorld.FileSystem,
    hadError: bool,
    out: BenchWorld.Bytes,
    err: BenchWorld.Bytes
  )
  {
    exists
      fsBounds: seq<BenchWorld.FileSystem>,
      outcomes: seq<MoveOutcome>,
      stdoutFragments: seq<BenchWorld.Bytes>,
      stderrFragments: seq<BenchWorld.Bytes>
      ::
        BatchMoveWitnessRelation(
          sources, directory, cmd, beforeFs, preCwd, afterFs,
          hadError, out, err,
          fsBounds, outcomes, stdoutFragments, stderrFragments
        )
  }

  ghost predicate TargetDirectoryCheckSpecFields(directory: string, preFs: BenchWorld.FileSystem, ok: bool, err: int)
  {
    exists statOk: bool, isDir: bool, statErr: int ::
      IOContract.IsDirectoryContractFields(
        preFs, directory, true, statOk, isDir, statErr
      ) &&
      ok == (statOk && isDir) &&
      err == TargetDirectoryErrSpec(statOk, isDir, statErr)
  }

  ghost predicate CandidateRunIntoDirectoryFields(
    sources: seq<string>,
    directory: string,
    explicitTargetDirectory: bool,
    cmd: Schema.MvCmd,
    beforeFs: BenchWorld.FileSystem,
    preCwd: BenchWorld.Path,
    afterFs: BenchWorld.FileSystem,
    preStdout: BenchWorld.Bytes,
    preStderr: BenchWorld.Bytes,
    stdout2: BenchWorld.Bytes,
    stderr2: BenchWorld.Bytes,
    exit: int
  )
  {
    (exists hadError: bool, out: BenchWorld.Bytes, err: BenchWorld.Bytes ::
       TargetDirectoryCheckSpecFields(directory, beforeFs, true, 0) &&
       BatchMoveRelation(
         sources, directory, cmd,
         beforeFs, preCwd, afterFs, hadError, out, err
       ) &&
       exit == (if hadError then 1 else 0) &&
       stdout2 == preStdout + out &&
       stderr2 == preStderr + err) ||
    (exists directoryErr: int ::
       TargetDirectoryCheckSpecFields(
         directory, beforeFs, false, directoryErr
       ) &&
       afterFs == beforeFs &&
       exit == 1 &&
       stdout2 == preStdout &&
       stderr2 == preStderr +
       TargetFailureMessageSpec(
         directory, explicitTargetDirectory, directoryErr
       ))
  }

  ghost predicate CandidateRunTwoOperandFields(
    cmd: Schema.MvCmd,
    beforeFs: BenchWorld.FileSystem,
    preCwd: BenchWorld.Path,
    afterFs: BenchWorld.FileSystem,
    preStdout: BenchWorld.Bytes,
    preStderr: BenchWorld.Bytes,
    stdout2: BenchWorld.Bytes,
    stderr2: BenchWorld.Bytes,
    exit: int
  )
    requires |cmd.operands| == 2
  {
    var source :=
      NormalizeSourceSpec(cmd.operands[0], cmd.stripTrailingSlashes);
    var destination := cmd.operands[1];
    if cmd.noTargetDirectory then
      exists outcome: MoveOutcome ::
        MoveEffectRelation(
          source, destination, cmd,
          beforeFs, preCwd, afterFs, outcome
        ) &&
        exit == (if outcome.failed then 1 else 0) &&
        stdout2 == preStdout + outcome.stdoutFragment &&
        stderr2 == preStderr + outcome.stderrFragment
    else
      (exists directoryErr: int, outcome: MoveOutcome ::
         IOContract.IsDirectoryContractFields(
           beforeFs, destination, true, true, true, directoryErr
         ) &&
         BatchMoveRelation(
           [cmd.operands[0]], destination, cmd,
           beforeFs, preCwd, afterFs, outcome.failed,
           outcome.stdoutFragment, outcome.stderrFragment
         ) &&
         exit == (if outcome.failed then 1 else 0) &&
         stdout2 == preStdout + outcome.stdoutFragment &&
         stderr2 == preStderr + outcome.stderrFragment) ||
      (exists directoryErr: int, outcome: MoveOutcome ::
         IOContract.IsDirectoryContractFields(
           beforeFs, destination, true, true, false, directoryErr
         ) &&
         MoveEffectRelation(
           source, destination, cmd,
           beforeFs, preCwd, afterFs, outcome
         ) &&
         exit == (if outcome.failed then 1 else 0) &&
         stdout2 == preStdout + outcome.stdoutFragment &&
         stderr2 == preStderr + outcome.stderrFragment) ||
      (exists directoryErr: int, outcome: MoveOutcome ::
         IOContract.IsDirectoryContractFields(
           beforeFs, destination, true, false, false, directoryErr
         ) &&
         MoveEffectRelation(
           source, destination, cmd,
           beforeFs, preCwd, afterFs, outcome
         ) &&
         exit == (if outcome.failed then 1 else 0) &&
         stdout2 == preStdout + outcome.stdoutFragment &&
         stderr2 == preStderr + outcome.stderrFragment) ||
      (exists directoryErr: int, outcome: MoveOutcome ::
         IOContract.IsDirectoryContractFields(
           beforeFs, destination, true, false, true, directoryErr
         ) &&
         MoveEffectRelation(
           source, destination, cmd,
           beforeFs, preCwd, afterFs, outcome
         ) &&
         exit == (if outcome.failed then 1 else 0) &&
         stdout2 == preStdout + outcome.stdoutFragment &&
         stderr2 == preStderr + outcome.stderrFragment)
  }

  ghost predicate CandidateSpecFields(
    raw: Schema.MvCmdRaw,
    preFs: BenchWorld.FileSystem,
    preCwd: BenchWorld.Path,
    preStdout: BenchWorld.Bytes,
    preStderr: BenchWorld.Bytes,
    io: BenchIO.IO,
    exit: int
  )
    reads io.Footprint()
  {
    var cmd := Schema.Command(raw);
    if cmd.mode == Schema.ModeInvalidBackup then
      io.fs() == preFs &&
      exit == 1 &&
      io.stdout() == preStdout &&
      io.stderr() ==
      preStderr + InvalidBackupArgumentMessageSpec(cmd.invalidBackupArg)
    else if cmd.mode == Schema.ModeInvalidUpdate then
      io.fs() == preFs &&
      exit == 1 &&
      io.stdout() == preStdout &&
      io.stderr() ==
      preStderr + InvalidUpdateArgumentMessageSpec(cmd.invalidUpdateArg)
    else if cmd.mode == Schema.ModeHelp then
      io.fs() == preFs &&
      exit == 0 &&
      io.stdout() == preStdout + HelpTextSpec() &&
      io.stderr() == preStderr
    else if cmd.mode == Schema.ModeVersion then
      io.fs() == preFs &&
      exit == 0 &&
      io.stdout() == preStdout + VersionTextSpec() &&
      io.stderr() == preStderr
    else if cmd.targetDirectory != "" && cmd.noTargetDirectory then
      io.fs() == preFs &&
      exit == 1 &&
      io.stdout() == preStdout &&
      io.stderr() == preStderr + TargetDirectoryConflictMessageSpec()
    else if |cmd.operands| == 0 then
      io.fs() == preFs &&
      exit == 1 &&
      io.stdout() == preStdout &&
      io.stderr() == preStderr + MissingFileOperandMessageSpec()
    else if cmd.targetDirectory != "" then
      CandidateRunIntoDirectoryFields(
        cmd.operands, cmd.targetDirectory, true, cmd,
        preFs, preCwd, io.fs(),
        preStdout, preStderr, io.stdout(), io.stderr(), exit
      )
    else if |cmd.operands| == 1 then
      io.fs() == preFs &&
      exit == 1 &&
      io.stdout() == preStdout &&
      io.stderr() ==
      preStderr + MissingDestinationMessageSpec(cmd.operands[0])
    else if cmd.noTargetDirectory && |cmd.operands| > 2 then
      io.fs() == preFs &&
      exit == 1 &&
      io.stdout() == preStdout &&
      io.stderr() == preStderr + ExtraOperandMessageSpec(cmd.operands[2])
    else if |cmd.operands| == 2 then
      CandidateRunTwoOperandFields(
        cmd, preFs, preCwd, io.fs(),
        preStdout, preStderr, io.stdout(), io.stderr(), exit
      )
    else
      CandidateRunIntoDirectoryFields(
        cmd.operands[..|cmd.operands| - 1],
        cmd.operands[|cmd.operands| - 1],
        false,
        cmd,
        preFs,
        preCwd,
        io.fs(),
        preStdout,
        preStderr,
        io.stdout(),
        io.stderr(),
        exit
      )
  }

  twostate predicate Spec(raw: Schema.MvCmdRaw, io: BenchIO.IO, exit: int)
    reads io.Footprint()
  {
    CandidateSpecFields(
      raw,
      old(io.fs()),
      old(io.cwd()),
      old(io.stdout()),
      old(io.stderr()),
      io,
      exit
    )
  }
}
