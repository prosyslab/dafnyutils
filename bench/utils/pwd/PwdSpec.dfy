include "../../core/World.dfy"
include "../../core/IO.dfy"
include "PwdSchema.dfy"

module PwdSpec {
  import BenchIO
  import Utf8 = Utf8Semantics
  import BenchWorld
  import Schema = PwdSchema




  function HelpTextSpec(): BenchWorld.Bytes
  {
    "Usage: pwd [OPTION]...\n"
    + "Print the name of the current working directory.\n"
    + "\n"
    + "  -L, --logical    use PWD from the environment when it is valid\n"
    + "  -P, --physical   print the physical directory, ignoring PWD\n"
    + "      --help       display this help and exit\n"
    + "      --version    output version information and exit\n"
  }

  function VersionTextSpec(): BenchWorld.Bytes
  {
    "pwd (GNU coreutils) 9.10.13-2cf49\n"
    + "Copyright (C) 2026 Free Software Foundation, Inc.\n"
    + "License GPLv3+: GNU GPL version 3 or later <https://gnu.org/licenses/gpl.html>.\n"
    + "This is free software: you are free to change and redistribute it.\n"
    + "There is NO WARRANTY, to the extent permitted by law.\n"
  }

  function IgnoredOperandsWarningSpec(): BenchWorld.Bytes
  {
    "pwd: ignoring non-option arguments\n"
  }

  function CurrentDirectoryTextSpec(dir: string): BenchWorld.Bytes
  {
    Utf8.Encode(dir) + "\n"
  }

  function HelpSelected(raw: Schema.PwdCmdRaw): bool
  {
    raw.seenHelp &&
    (!raw.seenVersion || raw.helpOccurrenceIndex > raw.versionOccurrenceIndex)
  }

  function VersionSelected(raw: Schema.PwdCmdRaw): bool
  {
    raw.seenVersion &&
    (!raw.seenHelp || raw.versionOccurrenceIndex > raw.helpOccurrenceIndex)
  }

  function UseLogicalFields(raw: Schema.PwdCmdRaw, env: map<string, string>): bool
  {
    if raw.seenLogical && raw.seenPhysical then
      raw.logicalOccurrenceIndex > raw.physicalOccurrenceIndex
    else if raw.seenLogical then
      true
    else if raw.seenPhysical then
      false
    else
      "POSIXLY_CORRECT" in env
  }

  ghost predicate SelectedDirectoryRelation(
    raw: Schema.PwdCmdRaw,
    cwd: string,
    env: map<string, string>,
    dir: string
  )
  {
    if UseLogicalFields(raw, env) && "PWD" in env then
      var pwd := env["PWD"];
      var components :=
        BenchWorld.SplitSegments(BenchWorld.StripLeadingSlash(pwd), 0, 0);
      if BenchWorld.IsAbsolutePath(pwd) &&
         "." !in components &&
         ".." !in components &&
         BenchWorld.NormalizePath(pwd) == cwd
      then
        dir == pwd
      else
        dir == cwd
    else
      dir == cwd
  }

  twostate predicate Spec(raw: Schema.PwdCmdRaw, io: BenchIO.IO, exit: int)
    reads io.Footprint()
  {
    if HelpSelected(raw) then
      io.stdout() == old(io.stdout()) + HelpTextSpec() &&
      io.stderr() == old(io.stderr()) &&
      exit == 0
    else if VersionSelected(raw) then
      io.stdout() == old(io.stdout()) + VersionTextSpec() &&
      io.stderr() == old(io.stderr()) &&
      exit == 0
    else
      exists dir: string ::
        SelectedDirectoryRelation(
          raw, old(io.cwd()), old(io.env()), dir
        ) &&
        io.stdout() ==
        old(io.stdout()) + CurrentDirectoryTextSpec(dir) &&
        io.stderr() ==
        old(io.stderr()) +
        (if |raw.operands| > 0
         then IgnoredOperandsWarningSpec()
         else "") &&
        exit == 0
  }
}
