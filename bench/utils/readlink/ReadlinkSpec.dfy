include "../../core/World.dfy"
include "../../core/IO.dfy"
include "../../core/IOContract.dfy"
include "ReadlinkSchema.dfy"

module ReadlinkSpec {
  import BenchIO
  import Utf8 = Utf8Semantics
  import IOContract
  import BenchWorld
  import Schema = ReadlinkSchema




  function ErrnoTextSpec(err: BenchWorld.IOError): string
  {
    match err
    case NoSuchFile => "No such file or directory"
    case IsDirectory => "Is a directory"
    case NotDirectory => "Not a directory"
    case PermissionDenied => "Permission denied"
    case InvalidPath => "Invalid argument"
    case Other(msg) => msg
  }

  function IOErrorFromErrnoSpec(errno: int): BenchWorld.IOError
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

  function HelpTextSpec(): BenchWorld.Bytes
  {
    "Usage: readlink [OPTION]... FILE...\n"
    + "Print value of a symbolic link.\n"
    + "\n"
    + "  -f, --canonicalize\n"
    + "         canonicalize by following symlinks; parsed but unsupported here\n"
    + "  -e, --canonicalize-existing\n"
    + "         canonicalize existing paths; parsed but unsupported here\n"
    + "  -m, --canonicalize-missing\n"
    + "         canonicalize paths with missing components; parsed but unsupported here\n"
    + "  -n, --no-newline\n"
    + "         do not output the trailing delimiter for one FILE\n"
    + "  -q, --quiet\n"
    + "  -s, --silent\n"
    + "         suppress most error messages (on by default)\n"
    + "  -v, --verbose\n"
    + "         report error messages\n"
    + "  -z, --zero\n"
    + "         end each output line with NUL, not newline\n"
    + "      --help\n"
    + "         display this help and exit\n"
    + "      --version\n"
    + "         output version information and exit\n"
    + "\n"
    + "Report bugs to: bug-coreutils@gnu.org\n"
    + "GNU coreutils home page: <https://www.gnu.org/software/coreutils/>\n"
    + "General help using GNU software: <https://www.gnu.org/gethelp/>\n"
    + "Report any translation bugs to <https://translationproject.org/team/>\n"
    + "Full documentation <https://www.gnu.org/software/coreutils/readlink>\n"
    + "or available locally via: info '(coreutils) readlink invocation'\n"
  }

  function VersionTextSpec(): BenchWorld.Bytes
  {
    "readlink (GNU coreutils) 9.10.13-2cf49\n"
    + "Copyright (C) 2026 Free Software Foundation, Inc.\n"
    + "License GPLv3+: GNU GPL version 3 or later <https://gnu.org/licenses/gpl.html>.\n"
    + "This is free software: you are free to change and redistribute it.\n"
    + "There is NO WARRANTY, to the extent permitted by law.\n"
    + "\n"
    + "Written by Dmitry V. Levin.\n"
  }

  function MissingOperandMessageSpec(): BenchWorld.Bytes
  {
    "readlink: missing operand\nTry 'readlink --help' for more information.\n"
  }

  function UnsupportedCanonicalizeMessageSpec(): BenchWorld.Bytes
  {
    "readlink: canonicalize modes are outside this benchmark\n"
  }

  function NoNewlineWarningSpec(): BenchWorld.Bytes
  {
    "readlink: ignoring --no-newline with multiple arguments\n"
  }

  function ErrorMessageSpec(path: BenchWorld.Path, err: BenchWorld.IOError): BenchWorld.Bytes
  {
    "readlink: " + QuoteFileNameSpec(path) + ": " + ErrnoTextSpec(err) + "\n"
  }

  function QuoteFileNameSpec(path: BenchWorld.Path): BenchWorld.Bytes
  {
    if NeedsShellQuoteSpec(path) then "'" + Utf8.Encode(path) + "'" else Utf8.Encode(path)
  }

  function NeedsShellQuoteSpec(path: BenchWorld.Path): bool
  {
    |path| == 0 ||
    exists i :: 0 <= i < |path| && ShellQuoteTriggerSpec(path[i])
  }

  function ShellQuoteTriggerSpec(ch: char): bool
  {
    ch == ' ' || ch == ':' || ch == '='
  }

  ghost predicate ErrorMessageMatchesSpec(path: BenchWorld.Path, err: BenchWorld.IOError, errOut: BenchWorld.Bytes)
  {
    errOut == ErrorMessageSpec(path, err) ||
    exists prefix: string ::
      errOut == prefix + "/readlink: " + QuoteFileNameSpec(path) + ": " + ErrnoTextSpec(err) + "\n"
  }

  function OutputDelimiterSpec(cmd: Schema.ReadlinkCmd): BenchWorld.Bytes
  {
    if cmd.noNewline && |cmd.operands| == 1 then
      ""
    else if cmd.zeroTerminated then
      ['\0']
    else
      "\n"
  }

  function InitialWarningSpec(cmd: Schema.ReadlinkCmd): BenchWorld.Bytes
  {
    if cmd.noNewline && |cmd.operands| > 1 then NoNewlineWarningSpec() else ""
  }

  function MakeAbsoluteSpec(cwd: BenchWorld.Path, path: BenchWorld.Path): BenchWorld.Path
  {
    if BenchWorld.IsAbsolutePath(path) then
      BenchWorld.NormalizePath(path)
    else
      BenchWorld.NormalizePath(BenchWorld.AppendPath(cwd, path))
  }

  function EndsInSlashSpec(path: BenchWorld.Path): bool
  {
    |path| > 0 && path[|path| - 1] == '/'
  }

  function ReadlinkResultFieldsSpec(
    fs: BenchWorld.FileSystem,
    cwd: BenchWorld.Path,
    path: BenchWorld.Path
  ): BenchWorld.Result<BenchWorld.Path>
  {
    if path == "" then
      BenchWorld.Err(BenchWorld.NoSuchFile)
    else if EndsInSlashSpec(path) then
      ReadlinkTrailingSlashResultFieldsSpec(fs, MakeAbsoluteSpec(cwd, path))
    else
      IOContract.ReadLinkResultFields(fs, MakeAbsoluteSpec(cwd, path))
  }

  function ReadlinkTrailingSlashResultFieldsSpec(
    fs: BenchWorld.FileSystem,
    actualPath: BenchWorld.Path
  ): BenchWorld.Result<BenchWorld.Path>
  {
    match IOContract.ResolvePathForMetadataFields(fs, actualPath, true)
    case Ok(resolved) =>
      if BenchWorld.FsContainsPath(fs, resolved) then
        match BenchWorld.FsNodeAt(fs, resolved)
        case Regular(_, _, _, _) => BenchWorld.Err(BenchWorld.NotDirectory)
        case Directory(_, _, _) => BenchWorld.Err(BenchWorld.InvalidPath)
        case Symlink(_, _, _, _) => BenchWorld.Err(BenchWorld.NotDirectory)
        case Inaccessible(_) => BenchWorld.Err(BenchWorld.NotDirectory)
      else
        BenchWorld.Err(BenchWorld.NoSuchFile)
    case Err(err) => BenchWorld.Err(IOErrorFromErrnoSpec(IOContract.IOErrorErrno(err)))
  }

  ghost predicate ReadObservationRelation(
    fs: BenchWorld.FileSystem,
    cwd: BenchWorld.Path,
    path: BenchWorld.Path,
    result: BenchWorld.Result<BenchWorld.Path>
  )
  {
    result == ReadlinkResultFieldsSpec(fs, cwd, path)
  }

  ghost predicate ReadFragmentRelation(
    cmd: Schema.ReadlinkCmd,
    path: BenchWorld.Path,
    result: BenchWorld.Result<BenchWorld.Path>,
                              stdoutFragment: BenchWorld.Bytes,
                              stderrFragment: BenchWorld.Bytes
  )
  {
    match result
    case Ok(target) =>
      stdoutFragment == Utf8.Encode(target) + OutputDelimiterSpec(cmd) &&
      stderrFragment == ""
    case Err(err) =>
      stdoutFragment == "" &&
      (if cmd.verbose then ErrorMessageMatchesSpec(path, err, stderrFragment)
       else stderrFragment == "")
  }

  ghost predicate OutputFragmentCutsRelation(
    fragments: seq<BenchWorld.Bytes>,
    output: BenchWorld.Bytes,
    cuts: seq<nat>
  )
  {
    |cuts| == |fragments| + 1 &&
    cuts[0] == 0 &&
    cuts[|fragments|] == |output| &&
    forall i: nat {:trigger cuts[i]} | i < |fragments| ::
      cuts[i] <= cuts[i + 1] <= |output| &&
      output[cuts[i]..cuts[i + 1]] == fragments[i]
  }

  ghost predicate RunFilesWitnessRelation(
    cmd: Schema.ReadlinkCmd,
    files: seq<BenchWorld.Path>,
    fs: BenchWorld.FileSystem,
    cwd: BenchWorld.Path,
    observations: seq<BenchWorld.Result<BenchWorld.Path>>,
    stdoutFragments: seq<BenchWorld.Bytes>,
    stderrFragments: seq<BenchWorld.Bytes>,
    stdoutCuts: seq<nat>,
    stderrCuts: seq<nat>,
    hadError: bool,
    out: BenchWorld.Bytes,
    errOut: BenchWorld.Bytes
  )
  {
    |observations| == |files| &&
    |stdoutFragments| == |files| &&
    |stderrFragments| == |files| &&
    (forall i: nat | i < |files| ::
       ReadObservationRelation(fs, cwd, files[i], observations[i]) &&
       ReadFragmentRelation(
         cmd,
         files[i],
         observations[i],
         stdoutFragments[i],
         stderrFragments[i]
       )) &&
    hadError == (exists i: nat :: i < |observations| && observations[i].Err?) &&
    OutputFragmentCutsRelation(stdoutFragments, out, stdoutCuts) &&
    OutputFragmentCutsRelation(stderrFragments, errOut, stderrCuts)
  }

  ghost predicate RunFilesRelation(
    cmd: Schema.ReadlinkCmd,
    files: seq<BenchWorld.Path>,
    fs: BenchWorld.FileSystem,
    cwd: BenchWorld.Path,
    hadError: bool,
    out: BenchWorld.Bytes,
    errOut: BenchWorld.Bytes
  )
  {
    exists observations: seq<BenchWorld.Result<BenchWorld.Path>>,
      stdoutFragments: seq<BenchWorld.Bytes>,
      stderrFragments: seq<BenchWorld.Bytes>,
      stdoutCuts: seq<nat>,
      stderrCuts: seq<nat> ::
      RunFilesWitnessRelation(
        cmd,
        files,
        fs,
        cwd,
        observations,
        stdoutFragments,
        stderrFragments,
        stdoutCuts,
        stderrCuts,
        hadError,
        out,
        errOut
      )
  }

  twostate predicate Spec(raw: Schema.ReadlinkCmdRaw, io: BenchIO.IO, exit: int)
    reads io.Footprint()
  {
    var cmd := Schema.Command(raw);
    if cmd.mode == Schema.ModeHelp then
      io.stdout() == old(io.stdout()) + HelpTextSpec() &&
      io.stderr() == old(io.stderr()) &&
      exit == 0
    else if cmd.mode == Schema.ModeVersion then
      io.stdout() == old(io.stdout()) + VersionTextSpec() &&
      io.stderr() == old(io.stderr()) &&
      exit == 0
    else if |cmd.operands| == 0 then
      io.stdout() == old(io.stdout()) &&
      io.stderr() == old(io.stderr()) + MissingOperandMessageSpec() &&
      exit == 1
    else if cmd.mode == Schema.ModeUnsupportedCanonicalize then
      io.stdout() == old(io.stdout()) &&
      io.stderr() == old(io.stderr()) + UnsupportedCanonicalizeMessageSpec() &&
      exit == 1
    else
      exists hadError: bool, out: BenchWorld.Bytes, errOut: BenchWorld.Bytes ::
        RunFilesRelation(cmd, cmd.operands, old(io.fs()), old(io.cwd()), hadError, out, errOut) &&
        io.stdout() == old(io.stdout()) + out &&
        io.stderr() == old(io.stderr()) + InitialWarningSpec(cmd) + errOut &&
        exit == (if hadError then 1 else 0)
  }
}
