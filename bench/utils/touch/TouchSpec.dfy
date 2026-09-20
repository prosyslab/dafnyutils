include "../../core/World.dfy"
include "../../core/IO.dfy"
include "../../core/IOContract.dfy"
include "../../core/Utf8.dfy"
include "TouchSchema.dfy"

module TouchSpec {
  import Utf8 = Utf8Semantics
  import BenchIO
  import CliTypes
  import IOContract
  import BenchWorld
  import Schema = TouchSchema

  const EBADF: int := 9
  const ENOENT: int := 2
  const EEXIST: int := 17
  const EISDIR: int := 21
  const EINVAL: int := 22
  const ENOSYS: int := 38

  function HelpTextSpec(): BenchWorld.Bytes
  {
    "Usage: touch [OPTION]... FILE...\n"
    + "Update the access and modification times of each FILE to the current time.\n"
    + "\n"
    + "A FILE argument that does not exist is created empty, unless -c or -h\n"
    + "is supplied.\n"
    + "\n"
    + "A FILE argument string of - is handled specially and causes touch to\n"
    + "change the times of the file associated with standard output.\n"
    + "\n"
    + "Mandatory arguments to long options are mandatory for short options too.\n"
    + "  -a\n"
    + "         change only the access time\n"
    + "  -c, --no-create\n"
    + "         do not create any files\n"
    + "  -d, --date=STRING\n"
    + "         parse STRING and use it instead of current time\n"
    + "  -f\n"
    + "         (ignored)\n"
    + "  -h, --no-dereference\n"
    + "         affect each symbolic link instead of any referenced file;\n"
    + "         useful only on systems that can change the timestamps of a symlink\n"
    + "  -m\n"
    + "         change only the modification time\n"
    + "  -r, --reference=FILE\n"
    + "         use this file's times instead of current time\n"
    + "  -t [[CC]YY]MMDDhhmm[.ss]\n"
    + "         use specified time instead of current time,\n"
    + "         with a date-time format that differs from -d's\n"
    + "      --time=WORD\n"
    + "         specify which time to change:\n"
    + "         access time (-a): 'access', 'atime', 'use';\n"
    + "         modification time (-m): 'modify', 'mtime'\n"
    + "      --help\n"
    + "         display this help and exit\n"
    + "      --version\n"
    + "         output version information and exit\n"
    + "\n"
    + "Report bugs to: bug-coreutils@gnu.org\n"
    + "GNU coreutils home page: <https://www.gnu.org/software/coreutils/>\n"
    + "General help using GNU software: <https://www.gnu.org/gethelp/>\n"
    + "Report any translation bugs to <https://translationproject.org/team/>\n"
    + "Full documentation <https://www.gnu.org/software/coreutils/touch>\n"
    + "or available locally via: info '(coreutils) touch invocation'\n"
  }

  function VersionTextSpec(): BenchWorld.Bytes
  {
    "touch (GNU coreutils) 9.10.13-2cf49\n"
    + "Copyright (C) 2026 Free Software Foundation, Inc.\n"
    + "License GPLv3+: GNU GPL version 3 or later <https://gnu.org/licenses/gpl.html>.\n"
    + "This is free software: you are free to change and redistribute it.\n"
    + "There is NO WARRANTY, to the extent permitted by law.\n"
    + "\n"
    + "Written by Paul Rubin, Arnold Robbins, Jim Kingdon,\n"
    + "David MacKenzie, and Randy Smith.\n"
  }

  ghost function ErrnoTextSpec(err: int): string
  {
    BenchIO.CLocaleErrnoTextResult(err)
  }

  ghost function QuotedPathSpec(path: BenchWorld.Path): BenchWorld.Bytes
  {
    BenchIO.QuoteafPathResult(path)
  }

  ghost function TouchErrorMessageSpec(path: BenchWorld.Path, err: int): BenchWorld.Bytes
  {
    Utf8.Encode("touch: cannot touch ") + QuotedPathSpec(path)
      + Utf8.Encode(": " + ErrnoTextSpec(err) + "\n")
  }

  ghost function ReferenceErrorMessageSpec(path: BenchWorld.Path, err: int): BenchWorld.Bytes
  {
    Utf8.Encode("touch: failed to get attributes of ") + QuotedPathSpec(path)
      + Utf8.Encode(": " + ErrnoTextSpec(err) + "\n")
  }

  ghost function SetTimesErrorMessageSpec(path: BenchWorld.Path, err: int): BenchWorld.Bytes
  {
    Utf8.Encode("touch: setting times of ") + QuotedPathSpec(path)
      + Utf8.Encode(": " + ErrnoTextSpec(err) + "\n")
  }

  ghost function StdoutErrorMessageSpec(err: int): BenchWorld.Bytes
  {
    Utf8.Encode("touch: setting times of standard output: " + ErrnoTextSpec(err) + "\n")
  }

  ghost function CloseErrorMessageSpec(path: BenchWorld.Path, err: int): BenchWorld.Bytes
  {
    Utf8.Encode("touch: failed to close ") + QuotedPathSpec(path)
      + Utf8.Encode(": " + ErrnoTextSpec(err) + "\n")
  }

  function MissingOperandMessageSpec(): BenchWorld.Bytes
  {
    "touch: missing file operand\nTry 'touch --help' for more information.\n"
  }

  function MissingShortRequiredArgumentMessageSpec(option: char): BenchWorld.Bytes
  {
    Utf8.Encode("touch: option requires an argument -- '" + [option] + "'\n" +
    "Try 'touch --help' for more information.\n")
  }

  function MissingLongRequiredArgumentMessageSpec(option: string): BenchWorld.Bytes
  {
    Utf8.Encode("touch: option '--" + option + "' requires an argument\n" +
    "Try 'touch --help' for more information.\n")
  }

  function ParseErrorMessageSpec(e: CliTypes.ParseError): BenchWorld.Bytes
  {
    if Schema.IsMissingShortRequiredArgument(e) then
      MissingShortRequiredArgumentMessageSpec(e.rawToken[|e.rawToken| - 1])
    else if Schema.IsMissingLongRequiredArgument(e) then
      MissingLongRequiredArgumentMessageSpec(Schema.MissingLongRequiredOption(e))
    else
      Utf8.Encode(Schema.ParseErrorText(e))
  }

  ghost predicate ParseFailureSpec(
    e: CliTypes.ParseError,
    plan: CliTypes.CliPlan<Schema.TouchCmdRaw>
  )
  {
    plan == CliTypes.CliEarlyExit(1, [], ParseErrorMessageSpec(e))
  }

  function InvalidTimeMessageSpec(value: string): BenchWorld.Bytes
  {
    Utf8.Encode("touch: invalid argument '" + value + "' for '--time'\n" +
    "Valid arguments are:\n" +
    "  - 'atime', 'access', 'use'\n" +
    "  - 'mtime', 'modify'\n" +
    "Try 'touch --help' for more information.\n")
  }

  function AmbiguousTimeMessageSpec(value: string): BenchWorld.Bytes
  {
    Utf8.Encode("touch: ambiguous argument '" + value + "' for '--time'\n" +
    "Valid arguments are:\n" +
    "  - 'atime', 'access', 'use'\n" +
    "  - 'mtime', 'modify'\n" +
    "Try 'touch --help' for more information.\n")
  }

  function InvalidDateMessageSpec(value: string): BenchWorld.Bytes
  {
    Utf8.Encode("touch: invalid date format '" + value + "'\n")
  }

  ghost predicate SetPathTimesSpecFields(
    observations: (BenchWorld.TrustedFilesystemRequest) -> BenchWorld.TrustedFilesystemResult,
    path: BenchWorld.Path,
    followSymlink: bool,
    selection: Schema.TimeSelection,
    source: Schema.TimeSource,
    preFs: BenchWorld.FileSystem,
    preNow: int,
    fs2: BenchWorld.FileSystem,
    ok: bool,
    err: int
  )
  {
    match source
    case TimeSourceCurrent =>
      IOContract.TrustedSetFileTimesContractFields(
        observations, preFs, preNow, path, followSymlink,
        if selection == Schema.TimeModify then BenchWorld.Keep else BenchWorld.Current,
        if selection == Schema.TimeAccess then BenchWorld.Keep else BenchWorld.Current,
        ok, err, fs2
      )
    case TimeSourceFixed(sourceAtimeSec, sourceAtimeNsec, sourceMtimeSec, sourceMtimeNsec) =>
      if selection == Schema.TimeBoth then
        IOContract.TrustedSetFileTimesContractFields(
          observations, preFs, preNow, path, followSymlink,
          BenchWorld.Exact(sourceAtimeSec, sourceAtimeNsec),
          BenchWorld.Exact(sourceMtimeSec, sourceMtimeNsec),
          ok, err, fs2
        )
      else
        exists getOk: bool, oldAtimeSec: int, oldAtimeNsec: int, oldMtimeSec: int, oldMtimeNsec: int,
          isDir: bool, isSymlink: bool, device: int, inode: int, linkCount: int, getErr: int ::
          IOContract.TrustedFilesystemQueryContractFields(
            observations, preFs, path, followSymlink, getOk,
            oldAtimeSec, oldAtimeNsec, oldMtimeSec, oldMtimeNsec,
            isDir, isSymlink, device, inode, linkCount, getErr
          ) &&
          if getOk then
            IOContract.TrustedSetFileTimesContractFields(
              observations, preFs, preNow, path, followSymlink,
              BenchWorld.Exact(
                if selection == Schema.TimeAccess then sourceAtimeSec else oldAtimeSec,
                if selection == Schema.TimeAccess then sourceAtimeNsec else oldAtimeNsec
              ),
              BenchWorld.Exact(
                if selection == Schema.TimeAccess then oldMtimeSec else sourceMtimeSec,
                if selection == Schema.TimeAccess then oldMtimeNsec else sourceMtimeNsec
              ),
              ok, err, fs2
            )
          else
            fs2 == preFs &&
            ok == false &&
            err == getErr
  }

  ghost predicate SetStdoutTimesSpecFields(
    selection: Schema.TimeSelection,
    source: Schema.TimeSource,
    preNow: int,
    beforeTarget: BenchWorld.StdoutTimestampState,
    afterTarget: BenchWorld.StdoutTimestampState,
    ok: bool,
    err: int
  )
  {
    match source
    case TimeSourceCurrent =>
        IOContract.SetStdoutTimesContractFields(
          beforeTarget, afterTarget, preNow,
          if selection == Schema.TimeModify then BenchWorld.Keep else BenchWorld.Current,
          if selection == Schema.TimeAccess then BenchWorld.Keep else BenchWorld.Current,
          ok, err
        )
    case TimeSourceFixed(atimeSec, atimeNsec, mtimeSec, mtimeNsec) =>
        IOContract.SetStdoutTimesContractFields(
          beforeTarget, afterTarget, preNow,
          if selection == Schema.TimeModify then BenchWorld.Keep else BenchWorld.Exact(atimeSec, atimeNsec),
          if selection == Schema.TimeAccess then BenchWorld.Keep else BenchWorld.Exact(mtimeSec, mtimeNsec),
          ok, err
        )
  }

  predicate ProjectedTimestampUpdateFields(
    selection: Schema.TimeSelection,
    source: Schema.TimeSource,
    preNow: int,
    before: BenchWorld.FileTimes,
    after: BenchWorld.FileTimes
  )
  {
    match source
    case TimeSourceCurrent =>
      (selection != Schema.TimeModify ==> after.atimeSec == preNow) &&
      (selection != Schema.TimeAccess ==> after.mtimeSec == preNow) &&
      (selection == Schema.TimeModify ==>
         after.atimeSec == before.atimeSec &&
         after.atimeNsec == before.atimeNsec) &&
      (selection == Schema.TimeAccess ==>
         after.mtimeSec == before.mtimeSec &&
         after.mtimeNsec == before.mtimeNsec) &&
      IOContract.ValidTimestampNanoseconds(after.atimeNsec) &&
      IOContract.ValidTimestampNanoseconds(after.mtimeNsec) &&
      after.ctimeSec == preNow &&
      IOContract.ValidTimestampNanoseconds(after.ctimeNsec)
    case TimeSourceFixed(atimeSec, atimeNsec, mtimeSec, mtimeNsec) =>
      (selection != Schema.TimeModify ==>
         after.atimeSec == atimeSec && after.atimeNsec == atimeNsec) &&
      (selection != Schema.TimeAccess ==>
         after.mtimeSec == mtimeSec && after.mtimeNsec == mtimeNsec) &&
      (selection == Schema.TimeModify ==>
         after.atimeSec == before.atimeSec &&
         after.atimeNsec == before.atimeNsec) &&
      (selection == Schema.TimeAccess ==>
         after.mtimeSec == before.mtimeSec &&
         after.mtimeNsec == before.mtimeNsec) &&
      after.ctimeSec == preNow &&
      IOContract.ValidTimestampNanoseconds(after.ctimeNsec)
  }

  predicate ProjectedCreatedTimestampFields(
    selection: Schema.TimeSelection,
    source: Schema.TimeSource,
    preNow: int,
    after: BenchWorld.FileTimes
  )
  {
    match source
    case TimeSourceCurrent =>
      after.atimeSec == preNow &&
      after.mtimeSec == preNow &&
      after.ctimeSec == preNow &&
      IOContract.ValidTimestampNanoseconds(after.atimeNsec) &&
      IOContract.ValidTimestampNanoseconds(after.mtimeNsec) &&
      IOContract.ValidTimestampNanoseconds(after.ctimeNsec)
    case TimeSourceFixed(atimeSec, atimeNsec, mtimeSec, mtimeNsec) =>
      (selection != Schema.TimeModify ==>
         after.atimeSec == atimeSec && after.atimeNsec == atimeNsec) &&
      (selection != Schema.TimeAccess ==>
         after.mtimeSec == mtimeSec && after.mtimeNsec == mtimeNsec) &&
      after.ctimeSec == preNow &&
      IOContract.ValidTimestampNanoseconds(after.atimeNsec) &&
      IOContract.ValidTimestampNanoseconds(after.mtimeNsec) &&
      IOContract.ValidTimestampNanoseconds(after.ctimeNsec)
  }

  ghost predicate ProjectedDirectTargetIdFields(
    fs: BenchWorld.FileSystem,
    path: BenchWorld.Path,
    followSymlink: bool,
    id: BenchWorld.InodeId
  )
  {
    BenchWorld.FsContainsPath(fs, path) &&
    if followSymlink && BenchWorld.FsNodeAt(fs, path).Symlink? then
      var target := BenchWorld.ResolveSymlinkTarget(
        path, BenchWorld.FsNodeAt(fs, path).target
      );
      BenchWorld.FsContainsPath(fs, target) &&
      !BenchWorld.FsNodeAt(fs, target).Symlink? &&
      BenchWorld.FsIdAt(fs, target) == id
    else
      BenchWorld.FsIdAt(fs, path) == id
  }

  ghost predicate ProjectedCreationFields(
    cmd: Schema.TouchCmd,
    preFs: BenchWorld.FileSystem,
    fs2: BenchWorld.FileSystem,
    i: int,
    id: BenchWorld.InodeId
  )
  {
    0 <= i < |cmd.files| &&
    cmd.files[i] != "-" &&
    !cmd.noCreate && cmd.followSymlink &&
    !BenchWorld.FsContainsPath(preFs, cmd.files[i]) &&
    BenchWorld.FsContainsPath(fs2, cmd.files[i]) &&
    BenchWorld.FsIdAt(fs2, cmd.files[i]) == id
  }

  ghost predicate ProjectedCreationParentFields(
    cmd: Schema.TouchCmd,
    preFs: BenchWorld.FileSystem,
    fs2: BenchWorld.FileSystem,
    i: int,
    id: BenchWorld.InodeId
  )
  {
    0 <= i < |cmd.files| &&
    cmd.files[i] != "-" &&
    !cmd.noCreate && cmd.followSymlink &&
    !BenchWorld.FsContainsPath(preFs, cmd.files[i]) &&
    BenchWorld.FsContainsPath(fs2, cmd.files[i]) &&
    BenchWorld.FsContainsPath(preFs, BenchWorld.ParentPath(cmd.files[i])) &&
    BenchWorld.FsIdAt(preFs, BenchWorld.ParentPath(cmd.files[i])) == id
  }

  ghost predicate ProjectedOperandSuccessFields(
    path: BenchWorld.Path,
    noCreate: bool,
    followSymlink: bool,
    selection: Schema.TimeSelection,
    source: Schema.TimeSource,
    preFs: BenchWorld.FileSystem,
    preNow: int,
    beforeStdoutTarget: BenchWorld.StdoutTimestampState,
    afterStdoutTarget: BenchWorld.StdoutTimestampState,
    fs2: BenchWorld.FileSystem
  )
  {
    if path == "-" then
      IOContract.SetStdoutTimesContractFields(
        beforeStdoutTarget, afterStdoutTarget, preNow,
        if selection == Schema.TimeModify then BenchWorld.Keep else
          match source case TimeSourceCurrent => BenchWorld.Current
                       case TimeSourceFixed(aSec, aNsec, _, _) => BenchWorld.Exact(aSec, aNsec),
        if selection == Schema.TimeAccess then BenchWorld.Keep else
          match source case TimeSourceCurrent => BenchWorld.Current
                       case TimeSourceFixed(_, _, mSec, mNsec) => BenchWorld.Exact(mSec, mNsec),
        true, 0
      )
    else
      if exists id :: ProjectedDirectTargetIdFields(preFs, path, followSymlink, id) then
        var id :| ProjectedDirectTargetIdFields(preFs, path, followSymlink, id);
        id in fs2.inodes &&
        BenchWorld.NodeShapeUnchangedExceptTimes(
          preFs.inodes[id].node, fs2.inodes[id].node
        ) &&
        ProjectedTimestampUpdateFields(
          selection, source, preNow,
          BenchWorld.NodeTimes(preFs.inodes[id].node),
          BenchWorld.NodeTimes(fs2.inodes[id].node)
        )
      else
        if noCreate then
          !BenchWorld.FsContainsPath(fs2, path)
        else if !followSymlink then
          false
        else
          BenchWorld.FsContainsPath(fs2, path) &&
            BenchWorld.FsNodeAt(fs2, path).Regular? &&
            BenchWorld.FsNodeAt(fs2, path).data == [] &&
            ProjectedCreatedTimestampFields(
              selection, source, preNow,
              BenchWorld.NodeTimes(BenchWorld.FsNodeAt(fs2, path))
            )
  }

  ghost predicate ProjectedFilesystemFrameFields(
    cmd: Schema.TouchCmd,
    preFs: BenchWorld.FileSystem,
    fs2: BenchWorld.FileSystem
  )
  {
    preFs.inodes.Keys <= fs2.inodes.Keys &&
    (forall id :: id in preFs.inodes && id in fs2.inodes ==>
       BenchWorld.InodeNamespaceIdPaths(preFs.namespace, id) ==
         BenchWorld.InodeNamespaceIdPaths(fs2.namespace, id) &&
       BenchWorld.NodeShapeUnchangedExceptTimes(
         preFs.inodes[id].node, fs2.inodes[id].node
       ) &&
       (preFs.inodes[id].node != fs2.inodes[id].node ==>
          exists i :: 0 <= i < |cmd.files| && cmd.files[i] != "-" &&
            (ProjectedDirectTargetIdFields(
               preFs, cmd.files[i], cmd.followSymlink, id
             ) ||
             ProjectedCreationParentFields(cmd, preFs, fs2, i, id)))) &&
    (forall id :: id in fs2.inodes && id !in preFs.inodes ==>
       (exists i :: ProjectedCreationFields(cmd, preFs, fs2, i, id)) &&
       fs2.inodes[id].node.Regular? &&
       fs2.inodes[id].node.data == [])
  }

  ghost predicate ProjectedSuccessfulRunSpecFields(
    cmd: Schema.TouchCmd,
    selection: Schema.TimeSelection,
    source: Schema.TimeSource,
    preFs: BenchWorld.FileSystem,
    preNow: int,
    preStdout: BenchWorld.Bytes,
    beforeStdoutTarget: BenchWorld.StdoutTimestampState,
    fs2: BenchWorld.FileSystem,
    stdout2: BenchWorld.Bytes,
    afterStdoutTarget: BenchWorld.StdoutTimestampState
  )
  {
    |cmd.files| > 0 &&
    stdout2 == preStdout &&
    ProjectedFilesystemFrameFields(cmd, preFs, fs2) &&
    forall i :: 0 <= i < |cmd.files| ==>
      ProjectedOperandSuccessFields(
        cmd.files[i], cmd.noCreate, cmd.followSymlink,
        selection, source, preFs, preNow,
        beforeStdoutTarget, afterStdoutTarget, fs2
      )
  }

  ghost predicate RunStepSpecFields(
    observations: (BenchWorld.TrustedFilesystemRequest) -> BenchWorld.TrustedFilesystemResult,
    path: BenchWorld.Path,
    noCreate: bool,
    followSymlink: bool,
    selection: Schema.TimeSelection,
    source: Schema.TimeSource,
    preFs: BenchWorld.FileSystem,
    preNow: int,
    preStdout: BenchWorld.Bytes,
    preStdoutTarget: BenchWorld.StdoutTimestampState,
    fs2: BenchWorld.FileSystem,
    stdout2: BenchWorld.Bytes,
    stdoutTarget2: BenchWorld.StdoutTimestampState,
    hadError: bool,
    errOut: BenchWorld.Bytes
  )
  {
    if path == "-" then
      fs2 == preFs &&
      stdout2 == preStdout &&
      exists okStdout: bool, stdoutErr: int ::
        SetStdoutTimesSpecFields(
          selection, source, preNow, preStdoutTarget, stdoutTarget2,
          okStdout, stdoutErr
        ) &&
        hadError == !okStdout &&
        errOut == (if okStdout then [] else StdoutErrorMessageSpec(stdoutErr))
    else
      stdout2 == preStdout &&
      stdoutTarget2 == preStdoutTarget &&
      exists found: bool, existsErr: int ::
        IOContract.TrustedPathExistsContractFields(
          observations, preFs, path, followSymlink, found, existsErr
        ) &&
        if found then
          exists okSet: bool, setErr: int ::
            SetPathTimesSpecFields(
              observations, path, followSymlink, selection, source,
              preFs, preNow, fs2, okSet, setErr
            ) &&
            hadError == !okSet &&
            errOut == (if okSet then [] else TouchErrorMessageSpec(path, setErr))
        else if noCreate then
          fs2 == preFs &&
          hadError == (existsErr != ENOENT) &&
          errOut == (if existsErr == ENOENT then [] else TouchErrorMessageSpec(path, existsErr))
        else if !followSymlink then
          fs2 == preFs &&
          hadError == true &&
          errOut == SetTimesErrorMessageSpec(path, existsErr)
        else
          exists okCreate: bool, createErr: int, createFs: BenchWorld.FileSystem ::
            IOContract.TrustedCreateFileContractFields(
              observations, preFs, preNow, path,
              okCreate, createErr, createFs
            ) &&
            if okCreate then
              if source == Schema.TimeSourceCurrent && selection == Schema.TimeBoth then
                fs2 == createFs &&
                hadError == false &&
                errOut == []
              else
                exists okSet: bool, setErr: int ::
                  SetPathTimesSpecFields(
                    observations, path, followSymlink, selection, source,
                    createFs, preNow, fs2, okSet, setErr
                  ) &&
                  hadError == !okSet &&
                  errOut == (if okSet then [] else TouchErrorMessageSpec(path, setErr))
            else
              fs2 == createFs &&
              hadError == true &&
              errOut == TouchErrorMessageSpec(path, createErr)
  }

  datatype FileState = FileState(
    fs: BenchWorld.FileSystem,
    stdout: BenchWorld.Bytes,
    stdoutTarget: BenchWorld.StdoutTimestampState,
    hadError: bool,
    errOut: BenchWorld.Bytes
  )

  opaque ghost predicate FileTransitionRelation(
    observations: (BenchWorld.TrustedFilesystemRequest) -> BenchWorld.TrustedFilesystemResult,
    path: BenchWorld.Path,
    noCreate: bool,
    followSymlink: bool,
    selection: Schema.TimeSelection,
    source: Schema.TimeSource,
    preNow: int,
    before: FileState,
    after: FileState
  )
  {
    exists stepError: bool, stepOut: BenchWorld.Bytes ::
      RunStepSpecFields(
        observations, path, noCreate, followSymlink, selection, source,
        before.fs, preNow, before.stdout, before.stdoutTarget,
        after.fs, after.stdout, after.stdoutTarget, stepError, stepOut
      ) &&
      after.hadError == (before.hadError || stepError) &&
      after.errOut == before.errOut + stepOut
  }

  opaque ghost predicate RunFilesSpecFields(
    observations: (BenchWorld.TrustedFilesystemRequest) -> BenchWorld.TrustedFilesystemResult,
    files: seq<BenchWorld.Path>,
    noCreate: bool,
    followSymlink: bool,
    selection: Schema.TimeSelection,
    source: Schema.TimeSource,
    preFs: BenchWorld.FileSystem,
    preNow: int,
    preStdout: BenchWorld.Bytes,
    preStdoutTarget: BenchWorld.StdoutTimestampState,
    fs2: BenchWorld.FileSystem,
    stdout2: BenchWorld.Bytes,
    stdoutTarget2: BenchWorld.StdoutTimestampState,
    hadError: bool,
    errOut: BenchWorld.Bytes
  )
  {
    exists states: seq<FileState> ::
      |states| == |files| + 1 &&
      states[0] == FileState(preFs, preStdout, preStdoutTarget, false, []) &&
      states[|files|] == FileState(fs2, stdout2, stdoutTarget2, hadError, errOut) &&
      forall i {:trigger FileTransitionRelation(observations, files[i], noCreate, followSymlink, selection, source, preNow, states[i], states[i + 1])} ::
        0 <= i < |files| ==>
          FileTransitionRelation(
            observations, files[i], noCreate, followSymlink, selection, source,
            preNow, states[i], states[i + 1]
          )
  }

  lemma RunStepSpecFieldsImpliesSingletonRun(
    observations: (BenchWorld.TrustedFilesystemRequest) -> BenchWorld.TrustedFilesystemResult,
    path: BenchWorld.Path,
    noCreate: bool,
    followSymlink: bool,
    selection: Schema.TimeSelection,
    source: Schema.TimeSource,
    preFs: BenchWorld.FileSystem,
    preNow: int,
    preStdout: BenchWorld.Bytes,
    preStdoutTarget: BenchWorld.StdoutTimestampState,
    fs2: BenchWorld.FileSystem,
    stdout2: BenchWorld.Bytes,
    stdoutTarget2: BenchWorld.StdoutTimestampState,
    hadError: bool,
    errOut: BenchWorld.Bytes
  )
    requires RunStepSpecFields(
               observations, path, noCreate, followSymlink, selection, source,
               preFs, preNow, preStdout, preStdoutTarget,
               fs2, stdout2, stdoutTarget2, hadError, errOut
             )
    ensures RunFilesSpecFields(
              observations, [path], noCreate, followSymlink, selection, source,
              preFs, preNow, preStdout, preStdoutTarget,
              fs2, stdout2, stdoutTarget2, hadError, errOut
            )
  {
    var before := FileState(preFs, preStdout, preStdoutTarget, false, []);
    var after := FileState(fs2, stdout2, stdoutTarget2, hadError, errOut);
    assert FileTransitionRelation(
             observations, path, noCreate, followSymlink, selection, source,
             preNow, before, after
           ) by {
      reveal FileTransitionRelation();
      var stepError := hadError;
      var stepOut := errOut;
    }
    assert RunFilesSpecFields(
             observations, [path], noCreate, followSymlink, selection, source,
             preFs, preNow, preStdout, preStdoutTarget,
             fs2, stdout2, stdoutTarget2, hadError, errOut
           ) by {
      reveal RunFilesSpecFields();
      var states := [before, after];
    }
  }

  function RequestedSelectionValue(cmd: Schema.TouchCmd): Schema.TimeSelection
  {
    if cmd.touchAtime && !cmd.touchMtime then
      Schema.TimeAccess
    else if cmd.touchMtime && !cmd.touchAtime then
      Schema.TimeModify
    else
      Schema.TimeBoth
  }

  ghost predicate RequestedSelection(cmd: Schema.TouchCmd, selection: Schema.TimeSelection)
  {
    selection == RequestedSelectionValue(cmd)
  }

  opaque ghost predicate SuccessfulReferenceSourceFields(
    observations: (BenchWorld.TrustedFilesystemRequest) -> BenchWorld.TrustedFilesystemResult,
    preFs: BenchWorld.FileSystem,
    path: BenchWorld.Path,
    followSymlink: bool,
    source: Schema.TimeSource
  )
  {
    var observed := observations(
      BenchWorld.FilesystemQuery(preFs, path, followSymlink)
    );
    observed.postFs == preFs && observed.ok &&
      source == Schema.TimeSourceFixed(
                  observed.atimeSec, observed.atimeNsec,
                  observed.mtimeSec, observed.mtimeNsec
                )
  }

  ghost predicate DateReferenceFields(
    observations: (BenchWorld.TrustedFilesystemRequest) -> BenchWorld.TrustedFilesystemResult,
    cmd: Schema.TouchCmd,
    preFs: BenchWorld.FileSystem,
    preNow: int,
    referenceSec: int,
    referenceNsec: int
  )
  {
    if !cmd.hasReference then
      referenceSec == preNow && referenceNsec == 0
    else
      var observed := observations(
        BenchWorld.FilesystemQuery(preFs, cmd.referenceArg, cmd.followSymlink)
      );
      observed.postFs == preFs && observed.ok &&
      referenceSec == observed.mtimeSec && referenceNsec == observed.mtimeNsec
  }

  function SourceConflict(cmd: Schema.TouchCmd): bool
  {
    cmd.hasTimestamp && (cmd.hasDate || cmd.hasReference)
  }

  function SourceConflictMessageSpec(): BenchWorld.Bytes
  {
    "touch: cannot specify times from more than one source\n"
    + "Try 'touch --help' for more information.\n"
  }

  ghost predicate DateAccessReferenceFields(
    observations: (BenchWorld.TrustedFilesystemRequest) -> BenchWorld.TrustedFilesystemResult,
    cmd: Schema.TouchCmd, preFs: BenchWorld.FileSystem, preNow: int,
    referenceSec: int, referenceNsec: int
  )
  {
    if !cmd.hasReference then
      referenceSec == preNow && referenceNsec == 0
    else
      var observed := observations(
        BenchWorld.FilesystemQuery(preFs, cmd.referenceArg, cmd.followSymlink)
      );
      observed.postFs == preFs && observed.ok &&
      referenceSec == observed.atimeSec && referenceNsec == observed.atimeNsec
  }

  ghost predicate DateParseFailureFields(
    observations: (BenchWorld.TrustedFilesystemRequest) -> BenchWorld.TrustedFilesystemResult,
    cmd: Schema.TouchCmd, preFs: BenchWorld.FileSystem, preNow: int,
    parses: map<BenchWorld.TimeParseRequest, BenchWorld.ParsedTimeResult>
  )
  {
    exists aSec: int, aNsec: int, mSec: int, mNsec: int ::
      DateAccessReferenceFields(observations, cmd, preFs, preNow, aSec, aNsec) &&
      DateReferenceFields(observations, cmd, preFs, preNow, mSec, mNsec) &&
      ((RequestedSelectionValue(cmd) != Schema.TimeModify &&
        !IOContract.TrustedTimeParseResultFields(
          parses, BenchWorld.DateParseRequest(cmd.dateArg, aSec, aNsec)).ok) ||
       (RequestedSelectionValue(cmd) != Schema.TimeAccess &&
        !IOContract.TrustedTimeParseResultFields(
          parses, BenchWorld.DateParseRequest(cmd.dateArg, mSec, mNsec)).ok))
  }

  ghost predicate RequestedSourceFields(
    observations: (BenchWorld.TrustedFilesystemRequest) -> BenchWorld.TrustedFilesystemResult,
    cmd: Schema.TouchCmd,
    preFs: BenchWorld.FileSystem,
    preNow: int,
    parses: map<BenchWorld.TimeParseRequest, BenchWorld.ParsedTimeResult>,
    source: Schema.TimeSource
  )
  {
    !SourceConflict(cmd) &&
    if cmd.hasTimestamp then
      var parsed := IOContract.TrustedTimeParseResultFields(
        parses, BenchWorld.TimestampParseRequest(cmd.timestampArg, preNow, 0)
      );
      parsed.ok &&
      source == Schema.TimeSourceFixed(
                  parsed.sec, parsed.nsec, parsed.sec, parsed.nsec
                )
    else if cmd.hasDate then
      exists aSec: int, aNsec: int, mSec: int, mNsec: int ::
        DateAccessReferenceFields(observations, cmd, preFs, preNow, aSec, aNsec) &&
        DateReferenceFields(observations, cmd, preFs, preNow, mSec, mNsec) &&
        var parsedA := IOContract.TrustedTimeParseResultFields(
          parses, BenchWorld.DateParseRequest(cmd.dateArg, aSec, aNsec));
        var parsedM := IOContract.TrustedTimeParseResultFields(
          parses, BenchWorld.DateParseRequest(cmd.dateArg, mSec, mNsec));
        var selection := RequestedSelectionValue(cmd);
        (selection != Schema.TimeModify ==> parsedA.ok) &&
        (selection != Schema.TimeAccess ==> parsedM.ok) &&
        source == Schema.TimeSourceFixed(
          if selection == Schema.TimeModify then aSec else parsedA.sec,
          if selection == Schema.TimeModify then aNsec else parsedA.nsec,
          if selection == Schema.TimeAccess then mSec else parsedM.sec,
          if selection == Schema.TimeAccess then mNsec else parsedM.nsec)
    else if cmd.hasReference then
      SuccessfulReferenceSourceFields(
        observations, preFs, cmd.referenceArg, cmd.followSymlink, source
      )
    else
      source == Schema.TimeSourceCurrent
  }

  twostate predicate ResolvedRunSpecFields(
    cmd: Schema.TouchCmd,
    io: BenchIO.IO,
    exit: int
  )
    reads io.Footprint()
  {
    var selection := RequestedSelectionValue(cmd);
    exists source: Schema.TimeSource ::
      RequestedSourceFields(
        old(io.trustedFilesystem()), cmd, old(io.fs()), old(io.now()),
        old(io.trustedTimeParses()), source
      ) &&
      if |cmd.files| == 0 then
        io.fs() == old(io.fs()) &&
        io.stdout() == old(io.stdout()) &&
        io.stderr() == old(io.stderr()) + MissingOperandMessageSpec() &&
        exit == 1
      else
        (exit == 0 &&
         io.stderr() == old(io.stderr()) &&
         ProjectedSuccessfulRunSpecFields(
           cmd, selection, source,
           old(io.fs()), old(io.now()), old(io.stdout()), old(io.stdoutTimestamp()),
           io.fs(), io.stdout(), io.stdoutTimestamp()
         )) ||
        (exists hadError: bool, errOut: BenchWorld.Bytes
          {:trigger RunFilesSpecFields(old(io.trustedFilesystem()), cmd.files, cmd.noCreate, cmd.followSymlink, selection, source, old(io.fs()), old(io.now()), old(io.stdout()), old(io.stdoutTimestamp()), io.fs(), io.stdout(), io.stdoutTimestamp(), hadError, errOut)} ::
          exit == (if hadError then 1 else 0) &&
          RunFilesSpecFields(
            old(io.trustedFilesystem()), cmd.files, cmd.noCreate,
            cmd.followSymlink, selection, source,
            old(io.fs()), old(io.now()), old(io.stdout()), old(io.stdoutTimestamp()),
            io.fs(), io.stdout(), io.stdoutTimestamp(), hadError, errOut
          ) &&
          io.stderr() == old(io.stderr()) + errOut)
  }

  opaque twostate predicate Spec(raw: Schema.TouchCmdRaw, io: BenchIO.IO, exit: int)
    reads io.Footprint()
  {
    var cmd := Schema.Command(raw);
    if cmd.mode == Schema.ModeInvalidTime then
      io.fs() == old(io.fs()) &&
      exit == 1 &&
      io.stdout() == old(io.stdout()) &&
      io.stderr() == old(io.stderr()) + InvalidTimeMessageSpec(cmd.timeArg)
    else if cmd.mode == Schema.ModeAmbiguousTime then
      io.fs() == old(io.fs()) &&
      exit == 1 &&
      io.stdout() == old(io.stdout()) &&
      io.stderr() == old(io.stderr()) + AmbiguousTimeMessageSpec(cmd.timeArg)
    else if cmd.mode == Schema.ModeHelp then
      io.fs() == old(io.fs()) &&
      exit == 0 &&
      io.stdout() == old(io.stdout()) + HelpTextSpec() &&
      io.stderr() == old(io.stderr())
    else if cmd.mode == Schema.ModeVersion then
      io.fs() == old(io.fs()) &&
      exit == 0 &&
      io.stdout() == old(io.stdout()) + VersionTextSpec() &&
      io.stderr() == old(io.stderr())
    else if cmd.timeArg != "" && Schema.ClassifyTimeWord(cmd.timeArg) == Schema.TimeWordAmbiguous then
      io.fs() == old(io.fs()) &&
      exit == 1 &&
      io.stdout() == old(io.stdout()) &&
      io.stderr() == old(io.stderr()) + AmbiguousTimeMessageSpec(cmd.timeArg)
    else if cmd.timeArg != "" && Schema.ClassifyTimeWord(cmd.timeArg) == Schema.TimeWordInvalid then
      io.fs() == old(io.fs()) &&
      exit == 1 &&
      io.stdout() == old(io.stdout()) &&
      io.stderr() == old(io.stderr()) + InvalidTimeMessageSpec(cmd.timeArg)
    else if cmd.hasTimestamp then
      var parsed := IOContract.TrustedTimeParseResultFields(
        old(io.trustedTimeParses()),
        BenchWorld.TimestampParseRequest(cmd.timestampArg, old(io.now()), 0)
      );
      if !parsed.ok then
        io.fs() == old(io.fs()) &&
        io.stdout() == old(io.stdout()) &&
        io.stderr() == old(io.stderr()) + InvalidDateMessageSpec(cmd.timestampArg) &&
        exit == 1
      else if SourceConflict(cmd) then
        io.fs() == old(io.fs()) &&
        io.stdout() == old(io.stdout()) &&
        io.stderr() == old(io.stderr()) + SourceConflictMessageSpec() &&
        exit == 1
      else
        ResolvedRunSpecFields(cmd, io, exit)
    else if cmd.hasDate then
      ResolvedRunSpecFields(cmd, io, exit) ||
      (DateParseFailureFields(
         old(io.trustedFilesystem()), cmd, old(io.fs()), old(io.now()),
         old(io.trustedTimeParses())) &&
       io.fs() == old(io.fs()) &&
       io.stdout() == old(io.stdout()) &&
       io.stderr() == old(io.stderr()) + InvalidDateMessageSpec(cmd.dateArg) &&
       exit == 1) ||
      (cmd.hasReference &&
       var observed := old(io.trustedFilesystem())(
         BenchWorld.FilesystemQuery(
           old(io.fs()), cmd.referenceArg, cmd.followSymlink
         )
       );
       observed.postFs == old(io.fs()) && !observed.ok &&
         io.fs() == old(io.fs()) &&
         io.stdout() == old(io.stdout()) &&
         io.stderr() == old(io.stderr()) +
           ReferenceErrorMessageSpec(cmd.referenceArg, observed.err) &&
         exit == 1)
    else if cmd.hasReference then
      ResolvedRunSpecFields(cmd, io, exit) ||
      (var observed := old(io.trustedFilesystem())(
         BenchWorld.FilesystemQuery(
           old(io.fs()), cmd.referenceArg, cmd.followSymlink
         )
       );
       observed.postFs == old(io.fs()) && !observed.ok &&
         io.fs() == old(io.fs()) &&
         io.stdout() == old(io.stdout()) &&
         io.stderr() == old(io.stderr()) +
           ReferenceErrorMessageSpec(cmd.referenceArg, observed.err) &&
         exit == 1)
    else
      ResolvedRunSpecFields(cmd, io, exit)
  }

  twostate lemma ProjectedSuccessfulRunImpliesSpec(
    raw: Schema.TouchCmdRaw,
    io: BenchIO.IO,
    exit: int,
    source: Schema.TimeSource
  )
    requires Schema.Command(raw).mode == Schema.ModeRun
    requires !(Schema.Command(raw).timeArg != "" &&
               Schema.ClassifyTimeWord(Schema.Command(raw).timeArg) == Schema.TimeWordAmbiguous)
    requires !(Schema.Command(raw).timeArg != "" &&
               Schema.ClassifyTimeWord(Schema.Command(raw).timeArg) == Schema.TimeWordInvalid)
    requires RequestedSourceFields(
               old(io.trustedFilesystem()), Schema.Command(raw),
               old(io.fs()), old(io.now()),
               old(io.trustedTimeParses()), source
             )
    requires exit == 0
    requires io.stderr() == old(io.stderr())
    requires ProjectedSuccessfulRunSpecFields(
               Schema.Command(raw), RequestedSelectionValue(Schema.Command(raw)), source,
               old(io.fs()), old(io.now()), old(io.stdout()), old(io.stdoutTimestamp()),
               io.fs(), io.stdout(), io.stdoutTimestamp()
             )
    ensures Spec(raw, io, exit)
  {
    var cmd := Schema.Command(raw);
    assert ResolvedRunSpecFields(cmd, io, exit);
    reveal Spec();
  }

  twostate lemma ProjectedSuccessfulReferenceRunImpliesSpec(
    raw: Schema.TouchCmdRaw,
    io: BenchIO.IO,
    exit: int,
    source: Schema.TimeSource
  )
    requires Schema.Command(raw).mode == Schema.ModeRun
    requires !Schema.Command(raw).hasTimestamp
    requires !Schema.Command(raw).hasDate
    requires Schema.Command(raw).hasReference
    requires !(Schema.Command(raw).timeArg != "" &&
               Schema.ClassifyTimeWord(Schema.Command(raw).timeArg) == Schema.TimeWordAmbiguous)
    requires !(Schema.Command(raw).timeArg != "" &&
               Schema.ClassifyTimeWord(Schema.Command(raw).timeArg) == Schema.TimeWordInvalid)
    requires var observed := old(io.trustedFilesystem())(
               BenchWorld.FilesystemQuery(
                 old(io.fs()), Schema.Command(raw).referenceArg,
                 Schema.Command(raw).followSymlink
               )
             );
             observed.postFs == old(io.fs()) && observed.ok &&
             source == Schema.TimeSourceFixed(
                         observed.atimeSec, observed.atimeNsec,
                         observed.mtimeSec, observed.mtimeNsec
                       )
    requires exit == 0
    requires io.stderr() == old(io.stderr())
    requires ProjectedSuccessfulRunSpecFields(
               Schema.Command(raw), RequestedSelectionValue(Schema.Command(raw)), source,
               old(io.fs()), old(io.now()), old(io.stdout()), old(io.stdoutTimestamp()),
               io.fs(), io.stdout(), io.stdoutTimestamp()
             )
    ensures Spec(raw, io, exit)
  {
    var cmd := Schema.Command(raw);
    reveal SuccessfulReferenceSourceFields();
    assert SuccessfulReferenceSourceFields(
             old(io.trustedFilesystem()), old(io.fs()),
             cmd.referenceArg, cmd.followSymlink, source
           );
    assert RequestedSourceFields(
             old(io.trustedFilesystem()), cmd, old(io.fs()), old(io.now()),
             old(io.trustedTimeParses()), source
           );
    ProjectedSuccessfulRunImpliesSpec(raw, io, exit, source);
  }

  twostate lemma ResolvedSingletonRunImpliesSpec(
    raw: Schema.TouchCmdRaw,
    io: BenchIO.IO,
    exit: int,
    source: Schema.TimeSource,
    hadError: bool,
    errOut: BenchWorld.Bytes
  )
    requires Schema.Command(raw).mode == Schema.ModeRun
    requires !(Schema.Command(raw).timeArg != "" &&
               Schema.ClassifyTimeWord(Schema.Command(raw).timeArg) == Schema.TimeWordAmbiguous)
    requires !(Schema.Command(raw).timeArg != "" &&
               Schema.ClassifyTimeWord(Schema.Command(raw).timeArg) == Schema.TimeWordInvalid)
    requires |Schema.Command(raw).files| == 1
    requires RequestedSourceFields(
               old(io.trustedFilesystem()), Schema.Command(raw),
               old(io.fs()), old(io.now()),
               old(io.trustedTimeParses()), source
             )
    requires exit == (if hadError then 1 else 0)
    requires RunStepSpecFields(
               old(io.trustedFilesystem()), Schema.Command(raw).files[0],
               Schema.Command(raw).noCreate,
               Schema.Command(raw).followSymlink,
               RequestedSelectionValue(Schema.Command(raw)),
               source,
               old(io.fs()), old(io.now()), old(io.stdout()), old(io.stdoutTimestamp()),
               io.fs(), io.stdout(), io.stdoutTimestamp(), hadError, errOut
             )
    requires io.stderr() == old(io.stderr()) + errOut
    ensures Spec(raw, io, exit)
  {
    reveal Spec();
    var cmd := Schema.Command(raw);
    RunStepSpecFieldsImpliesSingletonRun(
      old(io.trustedFilesystem()), cmd.files[0], cmd.noCreate, cmd.followSymlink,
      RequestedSelectionValue(cmd), source,
      old(io.fs()), old(io.now()), old(io.stdout()), old(io.stdoutTimestamp()),
      io.fs(), io.stdout(), io.stdoutTimestamp(), hadError, errOut
    );
    assert exists source0: Schema.TimeSource ::
      RequestedSourceFields(
        old(io.trustedFilesystem()), cmd, old(io.fs()), old(io.now()),
        old(io.trustedTimeParses()), source0
      ) &&
      exists hadError0: bool, errOut0: BenchWorld.Bytes ::
        exit == (if hadError0 then 1 else 0) &&
        RunFilesSpecFields(
          old(io.trustedFilesystem()), cmd.files, cmd.noCreate, cmd.followSymlink,
          RequestedSelectionValue(cmd), source0,
          old(io.fs()), old(io.now()), old(io.stdout()), old(io.stdoutTimestamp()),
          io.fs(), io.stdout(), io.stdoutTimestamp(), hadError0, errOut0
        ) &&
        io.stderr() == old(io.stderr()) + errOut0 by {
      var source0 := source;
      var hadError0 := hadError;
      var errOut0 := errOut;
      assert cmd.files == [cmd.files[0]];
    }
    assert ResolvedRunSpecFields(cmd, io, exit);
  }
}
