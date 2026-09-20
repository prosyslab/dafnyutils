include "../../core/World.dfy"
include "../../core/IO.dfy"
include "FalseSchema.dfy"

module FalseSpec {
  import BenchIO
  import BenchWorld
  import Schema = FalseSchema


  function HelpTextSpec(): BenchWorld.Bytes
  {
    "Usage: false [ignored command line arguments]\n"
    + "  or:  false OPTION\n"
    + "Exit with a status code indicating failure.\n"
    + "\n"
    + "      --help\n"
    + "         display this help and exit\n"
    + "      --version\n"
    + "         output version information and exit\n"
    + "\n"
    + "Your shell may have its own version of false, which usually supersedes\n"
    + "the version described here.  Please refer to your shell's documentation\n"
    + "for details about the options it supports.\n"
    + "\n"
    + "Report bugs to: bug-coreutils@gnu.org\n"
    + "GNU coreutils home page: <https://www.gnu.org/software/coreutils/>\n"
    + "General help using GNU software: <https://www.gnu.org/gethelp/>\n"
    + "Report any translation bugs to <https://translationproject.org/team/>\n"
    + "Full documentation <https://www.gnu.org/software/coreutils/false>\n"
    + "or available locally via: info '(coreutils) false invocation'\n"
  }

  function VersionTextSpec(): BenchWorld.Bytes
  {
    "false (GNU coreutils) 9.10.13-2cf49\n"
    + "Copyright (C) 2026 Free Software Foundation, Inc.\n"
    + "License GPLv3+: GNU GPL version 3 or later <https://gnu.org/licenses/gpl.html>.\n"
    + "This is free software: you are free to change and redistribute it.\n"
    + "There is NO WARRANTY, to the extent permitted by law.\n"
    + "\n"
    + "Written by Jim Meyering.\n"
  }

  twostate predicate Spec(raw: Schema.FalseCmdRaw, io: BenchIO.IO, exit: int)
    reads io.Footprint()
  {
    var cmd := Schema.Command(raw);
    if cmd.mode == Schema.ModeHelp then
      io.stdout() == old(io.stdout()) + HelpTextSpec() &&
      io.stderr() == old(io.stderr()) &&
      exit == 1
    else if cmd.mode == Schema.ModeVersion then
      io.stdout() == old(io.stdout()) + VersionTextSpec() &&
      io.stderr() == old(io.stderr()) &&
      exit == 1
    else
      io.stdout() == old(io.stdout()) &&
      io.stderr() == old(io.stderr()) &&
      exit == 1
  }
}
