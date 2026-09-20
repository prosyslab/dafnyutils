include "../../core/World.dfy"
include "../../core/IO.dfy"
include "../../core/IOContract.dfy"
include "StatSchema.dfy"

module StatSpec {
  import BenchWorld
  import BenchIO
  import Utf8 = Utf8Semantics
  import IOContract
  import Schema = StatSchema

  function HelpTextSpec(): BenchWorld.Bytes
  {
    "Usage: stat [OPTION]... FILE...\n"
    + "Display numeric file status using a required format.\n"
    + "\n"
    + "  -L, --dereference     follow links\n"
    + "  -c, --format=FORMAT   use FORMAT; append a newline after each result\n"
    + "      --help            display this help and exit\n"
    + "      --version         output version information and exit\n"
    + "\n"
    + "Supported directives: %a %b %B %d %D %f %g %h %i %o %s %u %X %Y %Z %%\n"
  }

  function VersionTextSpec(): BenchWorld.Bytes
  {
    "stat (GNU coreutils) 9.10.13-2cf49\n"
    + "Copyright (C) 2026 Free Software Foundation, Inc.\n"
    + "License GPLv3+: GNU GPL version 3 or later <https://gnu.org/licenses/gpl.html>.\n"
    + "This is free software: you are free to change and redistribute it.\n"
    + "There is NO WARRANTY, to the extent permitted by law.\n"
    + "\n"
    + "Written by Michael Meskes.\n"
  }

  function MissingFormatMessageSpec(): BenchWorld.Bytes
  {
    "stat: a format is required in this benchmark\nTry 'stat --help' for more information.\n"
  }

  function MissingOperandMessageSpec(): BenchWorld.Bytes
  {
    "stat: missing operand\nTry 'stat --help' for more information.\n"
  }

  function ErrnoTextSpec(errno: int): string
  {
    if errno == 2 then "No such file or directory"
    else if errno == 13 then "Permission denied"
    else if errno == 20 then "Not a directory"
    else if errno == 40 then "Too many levels of symbolic links"
    else "unknown error"
  }

  function ErrorMessageSpec(path: BenchWorld.Path, errno: int): BenchWorld.Bytes
  {
    "stat: cannot statx '" + path + "': " + ErrnoTextSpec(errno) + "\n"
  }

  function DigitForBaseSpec(digit: nat): char
    requires digit < 16
  {
    if digit < 10 then
      (('0' as int) + digit) as char
    else
      (('a' as int) + digit - 10) as char
  }

  function BaseNatTextSpec(value: nat, base: nat): string
    requires 2 <= base <= 16
    decreases value
  {
    if value < base then
      [DigitForBaseSpec(value)]
    else
      BaseNatTextSpec(value / base, base) + [DigitForBaseSpec(value % base)]
  }

  function IntTextSpec(value: int): string
  {
    if value < 0 then "-" + BaseNatTextSpec((-value) as nat, 10)
    else BaseNatTextSpec(value as nat, 10)
  }

  function IntHexTextSpec(value: int): string
  {
    if value < 0 then "-" + BaseNatTextSpec((-value) as nat, 16)
    else BaseNatTextSpec(value as nat, 16)
  }

  function RawModeValueSpec(status: BenchWorld.FileStatus): nat
  {
    var kindBits :=
      if status.kind == BenchWorld.RegularKind then 32768
      else if status.kind == BenchWorld.DirectoryKind then 16384
      else if status.kind == BenchWorld.SymlinkKind then 40960
      else if status.kind == BenchWorld.BlockDeviceKind then 24576
      else if status.kind == BenchWorld.CharacterDeviceKind then 8192
      else if status.kind == BenchWorld.FifoKind then 4096
      else 49152;
    kindBits + (status.mode as int) as nat
  }

  function SupportedDirectiveSpec(directive: char): bool
  {
    directive == '%' || directive == 'a' || directive == 'b' || directive == 'B' ||
    directive == 'd' || directive == 'D' || directive == 'f' || directive == 'g' ||
    directive == 'h' || directive == 'i' || directive == 'o' || directive == 's' ||
    directive == 'u' || directive == 'X' || directive == 'Y' || directive == 'Z'
  }

  function DirectiveTextSpec(
    directive: char,
    status: BenchWorld.FileStatus
  ): BenchWorld.Bytes
  {
    Utf8.Encode(if directive == '%' then "%"
    else if directive == 'a' then BaseNatTextSpec((status.mode as int) as nat, 8)
    else if directive == 'b' then BaseNatTextSpec(status.storage.allocatedBlocks, 10)
    else if directive == 'B' then BaseNatTextSpec(BenchWorld.STAT_BLOCK_BYTES, 10)
    else if directive == 'd' then IntTextSpec(status.hostKey.device)
    else if directive == 'D' then IntHexTextSpec(status.hostKey.device)
    else if directive == 'f' then BaseNatTextSpec(RawModeValueSpec(status), 16)
    else if directive == 'g' then BaseNatTextSpec(status.ownership.gid, 10)
    else if directive == 'h' then BaseNatTextSpec(status.linkCount, 10)
    else if directive == 'i' then IntTextSpec(status.hostKey.inode)
    else if directive == 'o' then BaseNatTextSpec(status.storage.preferredIoBlockBytes, 10)
    else if directive == 's' then BaseNatTextSpec(status.storage.size, 10)
    else if directive == 'u' then BaseNatTextSpec(status.ownership.uid, 10)
    else if directive == 'X' then IntTextSpec(status.times.atimeSec)
    else if directive == 'Y' then IntTextSpec(status.times.mtimeSec)
    else if directive == 'Z' then IntTextSpec(status.times.ctimeSec)
    else "?")
  }

  ghost predicate FormatStepRelation(
    format: string,
    status: BenchWorld.FileStatus,
    lo: nat,
    hi: nat,
    piece: BenchWorld.Bytes
  )
  {
    lo < |format| &&
    if format[lo] != '%' then
      hi == lo + 1 && piece == Utf8.EncodeChar(format[lo])
    else if lo + 1 == |format| then
      hi == lo + 1 && piece == "%"
    else
      lo + 1 < |format| && hi == lo + 2 &&
      piece == DirectiveTextSpec(format[lo + 1], status)
  }

  function ConcatPiecesSpec(pieces: seq<BenchWorld.Bytes>): BenchWorld.Bytes
    decreases |pieces|
  {
    if |pieces| == 0 then []
    else pieces[0] + ConcatPiecesSpec(pieces[1..])
  }

  ghost predicate PrefixRenderingWitnessRelation(
    format: string,
    status: BenchWorld.FileStatus,
    end: nat,
    rendered: BenchWorld.Bytes,
    cuts: seq<nat>,
    pieces: seq<BenchWorld.Bytes>
  )
  {
    end <= |format| &&
    |cuts| == |pieces| + 1 &&
    |cuts| > 0 &&
    cuts[0] == 0 &&
    cuts[|pieces|] == end &&
    (forall i: nat {:trigger cuts[i]} | i < |pieces| ::
       FormatStepRelation(format, status, cuts[i], cuts[i + 1], pieces[i])) &&
    rendered == ConcatPiecesSpec(pieces)
  }

  ghost predicate RenderingWitnessRelation(
    format: string,
    status: BenchWorld.FileStatus,
    rendered: BenchWorld.Bytes,
    cuts: seq<nat>,
    pieces: seq<BenchWorld.Bytes>
  )
  {
    PrefixRenderingWitnessRelation(format, status, |format|, rendered, cuts, pieces)
  }

  ghost predicate FormatRenderingRelation(
    format: string,
    status: BenchWorld.FileStatus,
    rendered: BenchWorld.Bytes
  )
  {
    exists cuts: seq<nat>, pieces: seq<BenchWorld.Bytes> ::
      RenderingWitnessRelation(format, status, rendered, cuts, pieces)
  }

  ghost predicate FormatValidSpec(format: string)
  {
    exists status: BenchWorld.FileStatus, rendered: BenchWorld.Bytes ::
      FormatRenderingRelation(format, status, rendered)
  }

  ghost predicate StatusObservationRelation(
    fs: BenchWorld.FileSystem,
    path: BenchWorld.Path,
    followSymlink: bool,
    result: BenchWorld.Result<BenchWorld.FileStatus>
  )
  {
    result == IOContract.GetFileStatusResultFields(fs, path, followSymlink)
  }

  ghost predicate FileFragmentRelation(
    format: string,
    path: BenchWorld.Path,
    result: BenchWorld.Result<BenchWorld.FileStatus>,
                              stdoutFragment: BenchWorld.Bytes,
                              stderrFragment: BenchWorld.Bytes
  )
  {
    match result
    case Ok(status) =>
      exists rendered: BenchWorld.Bytes ::
        FormatRenderingRelation(format, status, rendered) &&
        stdoutFragment == rendered + "\n" && stderrFragment == ""
    case Err(error) =>
      stdoutFragment == "" && stderrFragment == ErrorMessageSpec(path, IOContract.IOErrorErrno(error))
  }

  ghost predicate OutputFragmentCutsRelation(
    fragments: seq<BenchWorld.Bytes>,
    output: BenchWorld.Bytes,
    cuts: seq<nat>
  )
  {
    |cuts| == |fragments| + 1 && cuts[0] == 0 && cuts[|fragments|] == |output| &&
    forall i: nat {:trigger cuts[i]} | i < |fragments| ::
      cuts[i] <= cuts[i + 1] <= |output| &&
      output[cuts[i]..cuts[i + 1]] == fragments[i]
  }

  ghost predicate RunFilesRelation(
    cmd: Schema.StatCmd,
    files: seq<BenchWorld.Path>,
    fs: BenchWorld.FileSystem,
    hadError: bool,
    out: BenchWorld.Bytes,
    errOut: BenchWorld.Bytes
  )
  {
    exists stdoutFragments: seq<BenchWorld.Bytes>,
      stderrFragments: seq<BenchWorld.Bytes> ::
      |stdoutFragments| == |files| &&
      |stderrFragments| == |files| &&
      (forall i: nat | i < |files| ::
         FileFragmentRelation(
           cmd.format,
           files[i],
           IOContract.GetFileStatusResultFields(fs, files[i], cmd.followSymlink),
           stdoutFragments[i],
           stderrFragments[i]
         )) &&
      hadError == (exists i: nat ::
                     i < |files| &&
                     IOContract.GetFileStatusResultFields(fs, files[i], cmd.followSymlink).Err?) &&
      out == ConcatPiecesSpec(stdoutFragments) &&
      errOut == ConcatPiecesSpec(stderrFragments)
  }

  twostate predicate Spec(raw: Schema.StatCmdRaw, io: BenchIO.IO, exit: int)
    reads io.fsRegion, io.stdoutRegion, io.stderrRegion
  {
    var cmd := Schema.Command(raw);
    if cmd.mode == Schema.ModeHelp then
      io.stdout() == old(io.stdout()) + HelpTextSpec() && io.stderr() == old(io.stderr()) && exit == 0
    else if cmd.mode == Schema.ModeVersion then
      io.stdout() == old(io.stdout()) + VersionTextSpec() && io.stderr() == old(io.stderr()) && exit == 0
    else if cmd.mode == Schema.ModeMissingFormat then
      io.stdout() == old(io.stdout()) &&
      io.stderr() == old(io.stderr()) + MissingFormatMessageSpec() && exit == 1
    else if cmd.mode == Schema.ModeMissingOperand then
      io.stdout() == old(io.stdout()) &&
      io.stderr() == old(io.stderr()) + MissingOperandMessageSpec() && exit == 1
    else
      FormatValidSpec(cmd.format) &&
      exists hadError: bool, out: BenchWorld.Bytes, errOut: BenchWorld.Bytes ::
        RunFilesRelation(cmd, cmd.files, old(io.fs()), hadError, out, errOut) &&
        io.stdout() == old(io.stdout()) + out &&
        io.stderr() == old(io.stderr()) + errOut &&
        exit == (if hadError then 1 else 0)
  }
}
