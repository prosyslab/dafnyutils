include "../../core/World.dfy"
include "../../core/IO.dfy"
include "ReadlinkSchema.dfy"
include "ReadlinkSpec.dfy"

module ReadlinkCore {
  import BenchIO
  import Utf8 = Utf8Semantics
  import IOContract
  import BenchWorld
  import Schema = ReadlinkSchema
  import Spec = ReadlinkSpec

  function IOErrorFromErrno(errno: int): BenchWorld.IOError
  {
    if errno == 2 then
      BenchWorld.NoSuchFile
    else if errno == 13 then
      BenchWorld.PermissionDenied
    else if errno == 20 then
      BenchWorld.NotDirectory
    else
      BenchWorld.InvalidPath
  }

  function ReadlinkTrailingSlashProbeResult(
    ok: bool,
    isDir: bool,
    dirErr: int
  ): BenchWorld.Result<BenchWorld.Path>
  {
    if ok then
      if isDir then
        BenchWorld.Err(BenchWorld.InvalidPath)
      else
        BenchWorld.Err(BenchWorld.NotDirectory)
    else
      BenchWorld.Err(IOErrorFromErrno(dirErr))
  }

  ghost function ReadlinkResultFields(
    fs: BenchWorld.FileSystem,
    cwd: BenchWorld.Path,
    path: BenchWorld.Path
  ): BenchWorld.Result<BenchWorld.Path>
  {
    Spec.ReadlinkResultFieldsSpec(fs, cwd, path)
  }

  lemma ReadlinkTrailingSlashProbeMatchesResult(
    fs: BenchWorld.FileSystem,
    actualPath: BenchWorld.Path,
    ok: bool,
    isDir: bool,
    dirErr: int
  )
    requires IOContract.IsDirectoryContractFields(fs, actualPath, true, ok, isDir, dirErr)
    ensures ReadlinkTrailingSlashProbeResult(ok, isDir, dirErr) ==
            Spec.ReadlinkTrailingSlashResultFieldsSpec(fs, actualPath)
  {
    match IOContract.ResolvePathForMetadataFields(fs, actualPath, true)
    case Err(err) =>
    case Ok(resolved) =>
      if BenchWorld.FsContainsPath(fs, resolved) {
        assert ok;
        match BenchWorld.FsNodeAt(fs, resolved)
        case Regular(_, _, _, _) =>
          assert !isDir;
        case Directory(_, _, _) =>
          assert isDir;
        case Symlink(_, _, _, _) =>
          assert !isDir;
        case Inaccessible(_) =>
          assert !isDir;
      } else {
        assert !ok;
      }
  }

  method GetErrnoText(err: BenchWorld.IOError) returns (out: string)
    ensures out == Spec.ErrnoTextSpec(err)
  {
    out := Spec.ErrnoTextSpec(err);
  }

  method GetHelpText() returns (out: BenchWorld.Bytes)
    ensures out == Spec.HelpTextSpec()
  {
    out := Spec.HelpTextSpec();
  }

  method GetVersionText() returns (out: BenchWorld.Bytes)
    ensures out == Spec.VersionTextSpec()
  {
    out := Spec.VersionTextSpec();
  }

  method GetMissingOperandMessage() returns (out: BenchWorld.Bytes)
    ensures out == Spec.MissingOperandMessageSpec()
  {
    out := Spec.MissingOperandMessageSpec();
  }

  method GetUnsupportedCanonicalizeMessage() returns (out: BenchWorld.Bytes)
    ensures out == Spec.UnsupportedCanonicalizeMessageSpec()
  {
    out := Spec.UnsupportedCanonicalizeMessageSpec();
  }

  method GetNoNewlineWarning() returns (out: BenchWorld.Bytes)
    ensures out == Spec.NoNewlineWarningSpec()
  {
    out := Spec.NoNewlineWarningSpec();
  }

  method IsShellQuoteTrigger(ch: char) returns (trigger: bool)
    ensures trigger == Spec.ShellQuoteTriggerSpec(ch)
  {
    trigger := Spec.ShellQuoteTriggerSpec(ch);
  }

  method ComputeNeedsShellQuote(path: BenchWorld.Path) returns (needs: bool)
    ensures needs == Spec.NeedsShellQuoteSpec(path)
  {
    needs := |path| == 0;
    var i := 0;
    while i < |path|
      invariant 0 <= i <= |path|
      invariant needs ==> |path| == 0 || exists j :: 0 <= j < i && Spec.ShellQuoteTriggerSpec(path[j])
      invariant !needs ==> |path| != 0 && forall j :: 0 <= j < i ==> !Spec.ShellQuoteTriggerSpec(path[j])
      decreases |path| - i
    {
      var trigger := IsShellQuoteTrigger(path[i]);
      if trigger {
        assert Spec.ShellQuoteTriggerSpec(path[i]);
        needs := true;
      }
      i := i + 1;
    }
    assert i == |path|;
  }

  method ComputeQuoteFileName(path: BenchWorld.Path) returns (out: BenchWorld.Bytes)
    ensures out == Spec.QuoteFileNameSpec(path)
  {
    out := Spec.QuoteFileNameSpec(path);
  }

  method GetErrorMessage(path: BenchWorld.Path, err: BenchWorld.IOError) returns (out: BenchWorld.Bytes)
    ensures out == Spec.ErrorMessageSpec(path, err)
  {
    out := Spec.ErrorMessageSpec(path, err);
  }

  method GetOutputDelimiter(cmd: Schema.ReadlinkCmd) returns (out: BenchWorld.Bytes)
    ensures out == Spec.OutputDelimiterSpec(cmd)
  {
    if cmd.noNewline && |cmd.operands| == 1 {
      out := "";
    } else if cmd.zeroTerminated {
      out := ['\0'];
    } else {
      out := "\n";
    }
  }

  method GetInitialWarning(cmd: Schema.ReadlinkCmd) returns (out: BenchWorld.Bytes)
    ensures out == Spec.InitialWarningSpec(cmd)
  {
    if cmd.noNewline && |cmd.operands| > 1 {
      out := GetNoNewlineWarning();
    } else {
      out := "";
    }
  }

  method ComputeMakeAbsolute(cwd: BenchWorld.Path, path: BenchWorld.Path) returns (out: BenchWorld.Path)
    ensures out == Spec.MakeAbsoluteSpec(cwd, path)
  {
    if BenchWorld.IsAbsolutePath(path) {
      out := BenchWorld.NormalizePath(path);
    } else {
      out := BenchWorld.NormalizePath(BenchWorld.AppendPath(cwd, path));
    }
  }

  method ComputeEndsInSlash(path: BenchWorld.Path) returns (out: bool)
    ensures out == Spec.EndsInSlashSpec(path)
  {
    out := |path| > 0 && path[|path| - 1] == '/';
  }

  ghost predicate ReadOneSummaryFields(
    cmd: Schema.ReadlinkCmd,
    path: BenchWorld.Path,
    fs: BenchWorld.FileSystem,
    cwd: BenchWorld.Path,
    hadError: bool,
    out: BenchWorld.Bytes,
    errOut: BenchWorld.Bytes
  )
  {
    match ReadlinkResultFields(fs, cwd, path)
    case Ok(target) =>
      !hadError &&
      out == Utf8.Encode(target) + Spec.OutputDelimiterSpec(cmd) &&
      errOut == ""
    case Err(err) =>
      hadError &&
      out == "" &&
      (if cmd.verbose then Spec.ErrorMessageMatchesSpec(path, err, errOut) else errOut == "")
  }

  ghost predicate RunFilesSummaryFields(
    cmd: Schema.ReadlinkCmd,
    files: seq<BenchWorld.Path>,
    fs: BenchWorld.FileSystem,
    cwd: BenchWorld.Path,
    hadError: bool,
    out: BenchWorld.Bytes,
    errOut: BenchWorld.Bytes
  )
    decreases |files|
  {
    if |files| == 0 then
      !hadError && out == "" && errOut == ""
    else
      exists prefixError: bool, prefixOut: BenchWorld.Bytes, prefixErrOut: BenchWorld.Bytes
        {:trigger RunFilesSummaryFields(cmd, files[..|files| - 1], fs, cwd, prefixError, prefixOut, prefixErrOut)} ::
        RunFilesSummaryFields(cmd, files[..|files| - 1], fs, cwd, prefixError, prefixOut, prefixErrOut) &&
        exists stepError: bool, stepOut: BenchWorld.Bytes, stepErrOut: BenchWorld.Bytes
          {:trigger ReadOneSummaryFields(cmd, files[|files| - 1], fs, cwd, stepError, stepOut, stepErrOut)} ::
          ReadOneSummaryFields(cmd, files[|files| - 1], fs, cwd, stepError, stepOut, stepErrOut) &&
          hadError == (prefixError || stepError) &&
          out == prefixOut + stepOut &&
          errOut == prefixErrOut + stepErrOut
  }

  lemma RunFilesSummaryAppend(
    cmd: Schema.ReadlinkCmd,
    files: seq<BenchWorld.Path>,
    path: BenchWorld.Path,
    fs: BenchWorld.FileSystem,
    cwd: BenchWorld.Path,
    prefixError: bool,
    prefixOut: BenchWorld.Bytes,
    prefixErrOut: BenchWorld.Bytes,
    stepError: bool,
    stepOut: BenchWorld.Bytes,
    stepErrOut: BenchWorld.Bytes
  )
    requires RunFilesSummaryFields(cmd, files, fs, cwd, prefixError, prefixOut, prefixErrOut)
    requires ReadOneSummaryFields(cmd, path, fs, cwd, stepError, stepOut, stepErrOut)
    ensures RunFilesSummaryFields(
              cmd,
              files + [path],
              fs,
              cwd,
              prefixError || stepError,
              prefixOut + stepOut,
              prefixErrOut + stepErrOut
            )
  {
    assert |files + [path]| == |files| + 1;
    assert (files + [path])[..|files + [path]| - 1] == files;
    assert (files + [path])[|files + [path]| - 1] == path;
  }

  twostate predicate CoreSummary(raw: Schema.ReadlinkCmdRaw, io: BenchIO.IO, exit: int)
    reads io.Footprint()
  {
    var cmd := Schema.Command(raw);
    if cmd.mode == Schema.ModeHelp then
      io.stdout() == old(io.stdout()) + Spec.HelpTextSpec() &&
      io.stderr() == old(io.stderr()) &&
      exit == 0
    else if cmd.mode == Schema.ModeVersion then
      io.stdout() == old(io.stdout()) + Spec.VersionTextSpec() &&
      io.stderr() == old(io.stderr()) &&
      exit == 0
    else if |cmd.operands| == 0 then
      io.stdout() == old(io.stdout()) &&
      io.stderr() == old(io.stderr()) + Spec.MissingOperandMessageSpec() &&
      exit == 1
    else if cmd.mode == Schema.ModeUnsupportedCanonicalize then
      io.stdout() == old(io.stdout()) &&
      io.stderr() == old(io.stderr()) + Spec.UnsupportedCanonicalizeMessageSpec() &&
      exit == 1
    else
      exists hadError: bool, out: BenchWorld.Bytes, errOut: BenchWorld.Bytes ::
        RunFilesSummaryFields(
          cmd,
          cmd.operands,
          old(io.fs()),
          old(io.cwd()),
          hadError,
          out,
          errOut
        ) &&
        io.stdout() == old(io.stdout()) + out &&
        io.stderr() == old(io.stderr()) + Spec.InitialWarningSpec(cmd) + errOut &&
        exit == (if hadError then 1 else 0)
  }

  method {:vcs_split_on_every_assert} RunCore(raw: Schema.ReadlinkCmdRaw, io: BenchIO.IO) returns (exit: int)
    modifies io.stdoutRegion, io.stderrRegion
    ensures CoreSummary(raw, io, exit)
    decreases *
  {
    ghost var preFs := io.fs();
    ghost var preCwd := io.cwd();
    ghost var preStdout := io.stdout();
    ghost var preStderr := io.stderr();
    var cmd := Schema.Command(raw);
    if cmd.mode == Schema.ModeHelp {
      var out := GetHelpText();
      io.AppendStdout(out);
      exit := 0;
      assert CoreSummary(raw, io, exit);
      return;
    }

    if cmd.mode == Schema.ModeVersion {
      var out := GetVersionText();
      io.AppendStdout(out);
      exit := 0;
      assert CoreSummary(raw, io, exit);
      return;
    }

    if |cmd.operands| == 0 {
      var err := GetMissingOperandMessage();
      io.AppendStderr(err);
      exit := 1;
      assert CoreSummary(raw, io, exit);
      return;
    }

    if cmd.mode == Schema.ModeUnsupportedCanonicalize {
      var err := GetUnsupportedCanonicalizeMessage();
      io.AppendStderr(err);
      exit := 1;
      assert CoreSummary(raw, io, exit);
      return;
    }

    var hadError := false;
    var out: BenchWorld.Bytes := "";
    var errOut: BenchWorld.Bytes := "";
    var cwd := io.GetCwd();
    assert cwd == preCwd;
    var i := 0;
    while i < |cmd.operands|
      invariant 0 <= i <= |cmd.operands|
      invariant io.stdout() == preStdout
      invariant io.stderr() == preStderr
      invariant cwd == preCwd
      invariant RunFilesSummaryFields(cmd, cmd.operands[..i], preFs, preCwd, hadError, out, errOut)
      decreases *
    {
      var oldI := i;
      assert oldI < |cmd.operands|;
      var path := cmd.operands[i];
      var prefixError := hadError;
      var prefixOut := out;
      var prefixErrOut := errOut;
      var stepError := false;
      var stepOut: BenchWorld.Bytes := "";
      var stepErrOut: BenchWorld.Bytes := "";
      var actualPath := ComputeMakeAbsolute(cwd, path);
      var hasTrailingSlash := ComputeEndsInSlash(path);
      var r: BenchWorld.Result<BenchWorld.Path>;
      if path == "" {
        r := BenchWorld.Err(BenchWorld.NoSuchFile);
      } else if hasTrailingSlash {
        var rawMetadataOk1, rawMetadataStatus1, rawMetadataErr1 := io.GetFileStatus(actualPath, true);
        IOContract.FileStatusImpliesMetadata(io.fs(), actualPath, true, rawMetadataOk1, rawMetadataStatus1, rawMetadataErr1);
        var ok := rawMetadataOk1;
        var isDir := rawMetadataStatus1.kind == BenchWorld.DirectoryKind;
        var dirErr := rawMetadataErr1;
        r := ReadlinkTrailingSlashProbeResult(ok, isDir, dirErr);
        ReadlinkTrailingSlashProbeMatchesResult(preFs, actualPath, ok, isDir, dirErr);
      } else {
        r := io.ReadLink(actualPath);
        assert r == IOContract.ReadLinkResultFields(preFs, actualPath);
      }
      assert r == ReadlinkResultFields(preFs, preCwd, path);
      match r {
        case Ok(target) =>
          stepError := false;
          var delimiter := GetOutputDelimiter(cmd);
          stepOut := Utf8.Encode(target) + delimiter;
          stepErrOut := "";
        case Err(err) =>
          stepError := true;
          stepOut := "";
          if cmd.verbose {
            stepErrOut := GetErrorMessage(path, err);
          } else {
            stepErrOut := "";
          }
      }
      assert ReadOneSummaryFields(cmd, path, preFs, preCwd, stepError, stepOut, stepErrOut);
      hadError := prefixError || stepError;
      out := prefixOut + stepOut;
      errOut := prefixErrOut + stepErrOut;
      RunFilesSummaryAppend(
        cmd,
        cmd.operands[..i],
        path,
        preFs,
        preCwd,
        prefixError,
        prefixOut,
        prefixErrOut,
        stepError,
        stepOut,
        stepErrOut
      );
      i := oldI + 1;
      assert |cmd.operands| - i < |cmd.operands| - oldI;
      assert cmd.operands[..i] == cmd.operands[..i - 1] + [cmd.operands[i - 1]];
      assert RunFilesSummaryFields(cmd, cmd.operands[..i], preFs, preCwd, hadError, out, errOut);
    }
    assert cmd.operands[..i] == cmd.operands;
    io.AppendStdout(out);
    var warning := GetInitialWarning(cmd);
    io.AppendStderr(warning + errOut);
    exit := if hadError then 1 else 0;
    assert CoreSummary(raw, io, exit);
  }
}
