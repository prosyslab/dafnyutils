include "../../core/IO.dfy"
include "LognameSchema.dfy"

module LognameSpec {
  import BenchIO
  import Utf8 = Utf8Semantics
  import BenchWorld
  import Schema = LognameSchema




  function HelpTextSpec(): BenchWorld.Bytes
  {
    "Usage: logname [OPTION]\n"
    + "Print the user's login name.\n"
    + "\n"
    + "      --help\n"
    + "         display this help and exit\n"
    + "      --version\n"
    + "         output version information and exit\n"
    + "\n"
    + "Report bugs to: bug-coreutils@gnu.org\n"
    + "GNU coreutils home page: <https://www.gnu.org/software/coreutils/>\n"
    + "General help using GNU software: <https://www.gnu.org/gethelp/>\n"
    + "Report any translation bugs to <https://translationproject.org/team/>\n"
    + "Full documentation <https://www.gnu.org/software/coreutils/logname>\n"
    + "or available locally via: info '(coreutils) logname invocation'\n"
  }

  function VersionTextSpec(): BenchWorld.Bytes
  {
    "logname (GNU coreutils) 9.10.13-2cf49\n"
    + "Copyright (C) 2026 Free Software Foundation, Inc.\n"
    + "License GPLv3+: GNU GPL version 3 or later <https://gnu.org/licenses/gpl.html>.\n"
    + "This is free software: you are free to change and redistribute it.\n"
    + "There is NO WARRANTY, to the extent permitted by law.\n"
    + "\n"
    + "Written by David MacKenzie.\n"
  }

  function ExtraOperandMessageSpec(op: string): BenchWorld.Bytes
  {
    "logname: extra operand '" + op + "'\n"
    + "Try 'logname --help' for more information.\n"
  }

  function NoLoginNameMessageSpec(): BenchWorld.Bytes
  {
    "logname: no login name\n"
  }

  function HasLoginNameProps(props: map<string, string>): bool
  {
    "loginName" in props
  }

  function LoginNameOutput(name: string): BenchWorld.Bytes
  {
    Utf8.Encode(name) + "\n"
  }

  twostate predicate Spec(raw: Schema.LognameCmdRaw, io: BenchIO.IO, exit: int)
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
    else if |cmd.operands| > 0 then
      io.stdout() == old(io.stdout()) &&
      io.stderr() == old(io.stderr()) + ExtraOperandMessageSpec(cmd.operands[0]) &&
      exit == 1
    else if HasLoginNameProps(old(io.props())) then
      io.stdout() == old(io.stdout()) + LoginNameOutput(old(io.props())["loginName"]) &&
      io.stderr() == old(io.stderr()) &&
      exit == 0
    else
      io.stdout() == old(io.stdout()) &&
      io.stderr() == old(io.stderr()) + NoLoginNameMessageSpec() &&
      exit == 1
  }
}
