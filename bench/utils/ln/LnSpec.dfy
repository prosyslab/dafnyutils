include "../../core/World.dfy"
include "../../core/IO.dfy"
include "../../core/IOContract.dfy"
include "LnSchema.dfy"

module LnSpec {
  import BenchIO
  import IOContract
  import BenchWorld
  import Schema = LnSchema




  function ErrnoTextSpec(err: int): string
  {
    if err == 2 then
      "No such file or directory"
    else if err == 13 then
      "Permission denied"
    else if err == 17 then
      "File exists"
    else if err == 20 then
      "Not a directory"
    else if err == 21 then
      "Is a directory"
    else if err == 22 then
      "Invalid argument"
    else if err == 36 then
      "File name too long"
    else if err == 40 then
      "Too many levels of symbolic links"
    else
      "unknown error"
  }

  function HelpTextSpec(): BenchWorld.Bytes
  {
    "Usage: ln [OPTION]... TARGET LINK_NAME\n"
    + "Create a link named LINK_NAME to TARGET.\n"
    + "\n"
    + "This benchmark slice supports symbolic links only.\n"
    + "\n"
    + "  -s, --symbolic\n"
    + "         make symbolic links instead of hard links\n"
    + "      --help\n"
    + "         display this help and exit\n"
    + "      --version\n"
    + "         output version information and exit\n"
    + "\n"
    + "Report bugs to: bug-coreutils@gnu.org\n"
    + "GNU coreutils home page: <https://www.gnu.org/software/coreutils/>\n"
    + "General help using GNU software: <https://www.gnu.org/gethelp/>\n"
    + "Report any translation bugs to <https://translationproject.org/team/>\n"
    + "Full documentation <https://www.gnu.org/software/coreutils/ln>\n"
    + "or available locally via: info '(coreutils) ln invocation'\n"
  }

  function VersionTextSpec(): BenchWorld.Bytes
  {
    "ln (GNU coreutils) 9.10.13-2cf49\n"
    + "Copyright (C) 2026 Free Software Foundation, Inc.\n"
    + "License GPLv3+: GNU GPL version 3 or later <https://gnu.org/licenses/gpl.html>.\n"
    + "This is free software: you are free to change and redistribute it.\n"
    + "There is NO WARRANTY, to the extent permitted by law.\n"
    + "\n"
    + "Written by Mike Parker and David MacKenzie.\n"
  }

  function MissingOperandMessageSpec(): BenchWorld.Bytes
  {
    "ln: missing file operand\nTry 'ln --help' for more information.\n"
  }

  function UnsupportedHardLinkMessageSpec(): BenchWorld.Bytes
  {
    "ln: hard links are outside this benchmark; use -s/--symbolic\n"
  }

  function UnsupportedTargetDirectoryMessageSpec(): BenchWorld.Bytes
  {
    "ln: target-directory link modes are outside this benchmark; use explicit SOURCE LINK_NAME\n"
  }

  function CreateSymlinkErrorMessageSpec(linkName: BenchWorld.Path, err: int): BenchWorld.Bytes
  {
    "ln: failed to create symbolic link '" + linkName + "': " + ErrnoTextSpec(err) + "\n"
  }

  function LinkNameIsDirectoryFs(fs: BenchWorld.FileSystem, linkName: BenchWorld.Path): bool
  {
    match IOContract.ResolvePathForMetadataFields(fs, linkName, true)
    case Ok(resolved) =>
      BenchWorld.FsContainsPath(fs, resolved) &&
      (match BenchWorld.FsNodeAt(fs, resolved)
       case Directory(_, _, _) => true
       case _ => false)
    case Err(_) => false
  }

  twostate predicate Spec(raw: Schema.LnCmdRaw, io: BenchIO.IO, exit: int)
    reads io.Footprint()
  {
    var cmd := Schema.Command(raw);
    if cmd.mode == Schema.ModeHelp then
      io.fs() == old(io.fs()) &&
      io.stdout() == old(io.stdout()) + HelpTextSpec() &&
      io.stderr() == old(io.stderr()) &&
      exit == 0
    else if cmd.mode == Schema.ModeVersion then
      io.fs() == old(io.fs()) &&
      io.stdout() == old(io.stdout()) + VersionTextSpec() &&
      io.stderr() == old(io.stderr()) &&
      exit == 0
    else if |cmd.operands| == 0 then
      io.fs() == old(io.fs()) &&
      io.stdout() == old(io.stdout()) &&
      io.stderr() == old(io.stderr()) + MissingOperandMessageSpec() &&
      exit == 1
    else if !cmd.symbolic then
      io.fs() == old(io.fs()) &&
      io.stdout() == old(io.stdout()) &&
      io.stderr() == old(io.stderr()) + UnsupportedHardLinkMessageSpec() &&
      exit == 1
    else if |cmd.operands| != 2 then
      io.fs() == old(io.fs()) &&
      io.stdout() == old(io.stdout()) &&
      io.stderr() == old(io.stderr()) + UnsupportedTargetDirectoryMessageSpec() &&
      exit == 1
    else if LinkNameIsDirectoryFs(old(io.fs()), cmd.operands[1]) then
      io.fs() == old(io.fs()) &&
      io.stdout() == old(io.stdout()) &&
      io.stderr() == old(io.stderr()) + UnsupportedTargetDirectoryMessageSpec() &&
      exit == 1
    else
      exists ok: bool, err: int ::
        IOContract.CreateSymlinkContractFields(
          old(io.fs()),
          old(io.now()),
          cmd.operands[1],
          cmd.operands[0],
          ok,
          err,
          io.fs()
        ) &&
        io.stdout() == old(io.stdout()) &&
        io.stderr() ==
        (if ok then old(io.stderr()) else old(io.stderr()) + CreateSymlinkErrorMessageSpec(cmd.operands[1], err)) &&
        exit == (if ok then 0 else 1)
  }
}
