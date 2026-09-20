include "../../core/World.dfy"
include "../../core/IO.dfy"
include "../../core/IOContract.dfy"
include "PrintenvSchema.dfy"

module PrintenvSpec {
  import BenchIO
  import Schema = PrintenvSchema
  import BenchWorld
  import IOContract




  function HelpTextSpec(): BenchWorld.Bytes
  {
    "Usage: printenv [OPTION]... [VARIABLE]...\n"
    + "Print the values of the specified environment VARIABLE(s).\n"
    + "If no VARIABLE is specified, print name and value pairs for them all.\n"
    + "\n"
    + "  -0, --null     end each output line with NUL, not newline\n"
    + "      --help     display this help and exit\n"
    + "      --version  output version information and exit\n"
    + "\n"
    + "Report bugs to: bug-coreutils@gnu.org\n"
    + "GNU coreutils home page: <https://www.gnu.org/software/coreutils/>\n"
    + "General help using GNU software: <https://www.gnu.org/gethelp/>\n"
    + "Report any translation bugs to <https://translationproject.org/team/>\n"
    + "Full documentation <https://www.gnu.org/software/coreutils/printenv>\n"
    + "or available locally via: info '(coreutils) printenv invocation'\n"
  }

  function VersionTextSpec(): BenchWorld.Bytes
  {
    "printenv (GNU coreutils) 9.10.13-2cf49\n"
    + "Copyright (C) 2026 Free Software Foundation, Inc.\n"
    + "License GPLv3+: GNU GPL version 3 or later <https://gnu.org/licenses/gpl.html>.\n"
    + "This is free software: you are free to change and redistribute it.\n"
    + "There is NO WARRANTY, to the extent permitted by law.\n"
    + "\n"
    + "Written by David MacKenzie and Richard Mlynarik.\n"
  }

  function Terminator(nullTerminated: bool): BenchWorld.Bytes
  {
    if nullTerminated then [(0 as char)] else "\n"
  }

  ghost predicate EnvironmentOutputRelation(
    entries: seq<string>,
    terminator: BenchWorld.Bytes,
    out: BenchWorld.Bytes
  )
    decreases |entries|
  {
    if |entries| == 0 then
      out == []
    else
      exists rest: BenchWorld.Bytes ::
        EnvironmentOutputRelation(entries[1..], terminator, rest) &&
        out == entries[0] + terminator + rest
  }

  ghost predicate OperandResultRelation(
    env: map<string, string>,
    operands: seq<string>,
    terminator: BenchWorld.Bytes,
    out: BenchWorld.Bytes,
    exit: int
  )
    decreases |operands|
  {
    if |operands| == 0 then
      out == [] && exit == 0
    else
      exists rest: BenchWorld.Bytes, restExit: int ::
        OperandResultRelation(
          env, operands[1..], terminator, rest, restExit
        ) &&
        if operands[0] in env then
          out == env[operands[0]] + terminator + rest &&
          exit == restExit
        else
          out == rest &&
          exit == 1
  }

  twostate predicate Spec(raw: Schema.PrintenvCmdRaw, io: BenchIO.IO, exit: int)
    reads io.envRegion, io.stdoutRegion, io.stderrRegion
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
      exists entries: seq<string>, out: BenchWorld.Bytes ::
        IOContract.GetEnvironmentContractFields(old(io.env()), entries) &&
        EnvironmentOutputRelation(
          entries, Terminator(cmd.nullTerminated), out) &&
        io.stdout() == old(io.stdout()) + out &&
        io.stderr() == old(io.stderr()) &&
        exit == 0
    else
      exists out: BenchWorld.Bytes ::
        OperandResultRelation(
          old(io.env()),
          cmd.operands,
          Terminator(cmd.nullTerminated),
          out,
          exit
        ) &&
        io.stdout() == old(io.stdout()) + out &&
        io.stderr() == old(io.stderr())
  }
}
