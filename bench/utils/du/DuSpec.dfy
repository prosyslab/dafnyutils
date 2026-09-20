include "../../core/World.dfy"
include "../../core/IO.dfy"
include "../../core/IOContract.dfy"
include "DuSchema.dfy"

module DuSpec {
  import BenchIO
  import BenchWorld
  import IOContract
  import Schema = DuSchema

  function HelpTextSpec(): BenchWorld.Bytes
  {
    "Usage: du [OPTION]... [FILE]...\n"
    + "Estimate file space usage.\n"
    + "\n"
    + "  -A, --apparent-size   print apparent sizes rather than disk usage\n"
    + "  -B, --block-size=SIZE scale sizes by SIZE before printing them\n"
    + "  -b, --bytes           equivalent to --apparent-size --block-size=1\n"
    + "  -s, --summarize       display only a total for each argument\n"
    + "      --help            display this help and exit\n"
    + "      --version         output version information and exit\n"
    + "\n"
    + "This benchmark supports apparent byte counts for named regular files.\n"
    + "Default block usage, recursive directories, hard links, symlinks, excludes,\n"
    + "device boundaries, inode mode, max-depth, thresholds, timestamps, totals,\n"
    + "and files0-from are outside this slice.\n"
    + "\n"
    + "Report bugs to: bug-coreutils@gnu.org\n"
    + "GNU coreutils home page: <https://www.gnu.org/software/coreutils/>\n"
    + "Full documentation <https://www.gnu.org/software/coreutils/du>\n"
    + "or available locally via: info '(coreutils) du invocation'\n"
  }

  function VersionTextSpec(): BenchWorld.Bytes
  {
    "du (GNU coreutils) 9.10.13-2cf49\n"
    + "Copyright (C) 2026 Free Software Foundation, Inc.\n"
    + "License GPLv3+: GNU GPL version 3 or later <https://gnu.org/licenses/gpl.html>.\n"
    + "This is free software: you are free to change and redistribute it.\n"
    + "There is NO WARRANTY, to the extent permitted by law.\n"
    + "\n"
    + "Written by Torbjorn Granlund, David MacKenzie, Paul Eggert, and Jim Meyering.\n"
  }

  function UnsupportedAccountingMessageSpec(): BenchWorld.Bytes
  {
    "du: this benchmark supports apparent byte counts only; use -b or --bytes\n"
  }



  function ErrnoText(err: BenchWorld.IOError): string
  {
    match err
    case NoSuchFile => "No such file or directory"
    case IsDirectory => "Is a directory"
    case NotDirectory => "Not a directory"
    case PermissionDenied => "Permission denied"
    case InvalidPath => "Too many levels of symbolic links"
    case Other(msg) => msg
  }

  function ErrorMessageSpec(path: BenchWorld.Path, err: BenchWorld.IOError): BenchWorld.Bytes
  {
    "du: cannot access '" + path + "': " + ErrnoText(err) + "\n"
  }

  function DigitChar(d: nat): char
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

  function NatText(n: nat): string
    decreases n
  {
    if n < 10 then
      [DigitChar(n)]
    else
      NatText(n / 10) + [DigitChar(n % 10)]
  }

  function CountLineSpec(size: nat, path: BenchWorld.Path): BenchWorld.Bytes
  {
    NatText(size) + "\t" + path + "\n"
  }

  ghost predicate FileObservationRelation(
    cmd: Schema.DuCmd,
    preFs: BenchWorld.FileSystem,
    observations: map<nat, BenchWorld.Result<BenchWorld.Bytes>>
  )
  {
    (forall i: nat :: i in observations.Keys <==> i < |cmd.operands|) &&
    forall i: nat | i < |cmd.operands| ::
      observations[i] == IOContract.ReadFileResultFields(preFs, cmd.operands[i])
  }

  function OutputPieceSpec(path: BenchWorld.Path, result: BenchWorld.Result<BenchWorld.Bytes>): BenchWorld.Bytes
  {
    match result
    case Ok(data) => CountLineSpec(|data|, path)
    case Err(_) => []
  }

  function ErrorPieceSpec(path: BenchWorld.Path, result: BenchWorld.Result<BenchWorld.Bytes>): BenchWorld.Bytes
  {
    match result
    case Ok(_) => []
    case Err(err) => ErrorMessageSpec(path, err)
  }

  ghost predicate PieceSequencesRelation(
    cmd: Schema.DuCmd,
    observations: map<nat, BenchWorld.Result<BenchWorld.Bytes>>,
    outputPieces: seq<BenchWorld.Bytes>,
    errorPieces: seq<BenchWorld.Bytes>
  )
  {
    |outputPieces| == |cmd.operands| &&
    |errorPieces| == |cmd.operands| &&
    forall i: nat | i < |cmd.operands| ::
      i in observations.Keys &&
      outputPieces[i] == OutputPieceSpec(cmd.operands[i], observations[i]) &&
      errorPieces[i] == ErrorPieceSpec(cmd.operands[i], observations[i])
  }

  ghost predicate FragmentsConcatenate(
    fragments: seq<BenchWorld.Bytes>,
    combined: BenchWorld.Bytes,
    cuts: seq<nat>
  )
  {
    |cuts| == |fragments| + 1 &&
    cuts[0] == 0 &&
    cuts[|fragments|] == |combined| &&
    forall i: nat {:trigger cuts[i + 1], fragments[i]} | i < |fragments| ::
      cuts[i] <= cuts[i + 1] &&
      cuts[i + 1] <= |combined| &&
      cuts[i + 1] == cuts[i] + |fragments[i]| &&
      combined[cuts[i]..cuts[i + 1]] == fragments[i]
  }

  ghost predicate RunRelation(
    cmd: Schema.DuCmd,
    preFs: BenchWorld.FileSystem,
    output: BenchWorld.Bytes,
    errors: BenchWorld.Bytes,
    exit: int
  )
  {
    exists observations: map<nat, BenchWorld.Result<BenchWorld.Bytes>>,
      outputPieces: seq<BenchWorld.Bytes>,
      outputCuts: seq<nat>,
      errorPieces: seq<BenchWorld.Bytes>,
      errorCuts: seq<nat> ::
      FileObservationRelation(cmd, preFs, observations) &&
      PieceSequencesRelation(cmd, observations, outputPieces, errorPieces) &&
      FragmentsConcatenate(outputPieces, output, outputCuts) &&
      FragmentsConcatenate(errorPieces, errors, errorCuts) &&
      exit ==
      (if exists i: nat ::
            i < |cmd.operands| && observations[i].Err?
       then 1
       else 0)
  }

  twostate predicate Spec(raw: Schema.DuCmdRaw, io: BenchIO.IO, exit: int)
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
    else if cmd.mode == Schema.ModeUnsupportedAccounting then
      io.stdout() == old(io.stdout()) &&
      io.stderr() == old(io.stderr()) + UnsupportedAccountingMessageSpec() &&
      exit == 1
    else
      exists output: BenchWorld.Bytes, errors: BenchWorld.Bytes ::
        RunRelation(cmd, old(io.fs()), output, errors, exit) &&
        io.stdout() == old(io.stdout()) + output &&
        io.stderr() == old(io.stderr()) + errors
  }
}
