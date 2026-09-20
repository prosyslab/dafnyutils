include "../../core/World.dfy"
include "../../core/IO.dfy"
include "../../core/Utf8.dfy"
include "BasenameSchema.dfy"

module BasenameSpec {
  import Utf8 = Utf8Semantics
  import BenchIO
  import BenchWorld
  import Schema = BasenameSchema




  function IsSlash(ch: char): bool
  {
    ch == '/'
  }

  function OutputSeparator(cmd: Schema.BasenameCmd): string
  {
    if cmd.zeroTerminated then ['\0'] else "\n"
  }

  ghost predicate SlashFree(text: string)
  {
    '/' !in text
  }

  ghost predicate SlashesOnly(text: string)
  {
    forall i :: 0 <= i < |text| ==> IsSlash(text[i])
  }

  ghost predicate MaximalSlashFreeSuffix(text: string, suffix: string)
  {
    0 < |suffix| <= |text| &&
    text[|text| - |suffix|..] == suffix &&
    SlashFree(suffix) &&
    (|suffix| == |text| || IsSlash(text[|text| - |suffix| - 1]))
  }

  ghost predicate BasenameRelation(path: string, base: string)
  {
    if |path| == 0 then
      base == ""
    else if SlashesOnly(path) then
      base == "/"
    else
      exists trimmed: string, trailing: string ::
        path == trimmed + trailing &&
        SlashesOnly(trailing) &&
        0 < |trimmed| &&
        !IsSlash(trimmed[|trimmed| - 1]) &&
        MaximalSlashFreeSuffix(trimmed, base)
  }

  ghost predicate SuffixRemovalRelation(
    base: string, suffixText: string, hasSuffix: bool, value: string
  )
  {
    if hasSuffix &&
       0 < |suffixText| < |base| &&
       base[|base| - |suffixText|..] == suffixText then
      value == base[..|base| - |suffixText|]
    else
      value == base
  }

  ghost predicate BasenamePieceRelation(
    path: string, suffixText: string, hasSuffix: bool, value: string
  )
  {
    exists base: string ::
      BasenameRelation(path, base) &&
      SuffixRemovalRelation(base, suffixText, hasSuffix, value)
  }

  ghost predicate OperandOutputPartition(
    paths: seq<string>,
    suffixText: string,
    hasSuffix: bool,
    sep: string,
    out: string,
    pieces: seq<string>,
    cuts: seq<nat>
  )
  {
    |pieces| == |paths| &&
    |cuts| == |paths| + 1 &&
    cuts[0] == 0 &&
    cuts[|paths|] == |out| &&
    (forall i {:trigger cuts[i + 1]} :: 0 <= i < |paths| ==>
                                                   cuts[i] <= cuts[i + 1] <= |out|) &&
    (forall i {:trigger out[cuts[i]..cuts[i + 1]]} ::
       0 <= i < |paths| &&
       cuts[i] <= cuts[i + 1] <= |out| ==>
         BasenamePieceRelation(paths[i], suffixText, hasSuffix, pieces[i]) &&
         out[cuts[i]..cuts[i + 1]] == pieces[i] + sep)
  }

  ghost predicate OperandOutputRelation(
    paths: seq<string>,
    suffixText: string,
    hasSuffix: bool,
    sep: string,
    out: string
  )
  {
    exists pieces: seq<string>, cuts: seq<nat> ::
      OperandOutputPartition(
        paths, suffixText, hasSuffix, sep, out, pieces, cuts
      )
  }

  ghost predicate CommandOutputRelation(cmd: Schema.BasenameCmd, out: string)
  {
    var sep := OutputSeparator(cmd);
    if |cmd.operands| == 0 then
      out == ""
    else if cmd.multiple then
      match cmd.suffix
      case Some(s) =>
        OperandOutputRelation(cmd.operands, s, true, sep, out)
      case None =>
        OperandOutputRelation(cmd.operands, "", false, sep, out)
    else if |cmd.operands| == 2 then
      exists piece: string ::
        BasenamePieceRelation(cmd.operands[0], cmd.operands[1], true, piece) &&
        out == piece + sep
    else
      exists piece: string ::
        BasenamePieceRelation(cmd.operands[0], "", false, piece) &&
        out == piece + sep
  }

  function HelpTextSpec(): BenchWorld.Bytes
  {
    "Usage: _build/coreutils/src/basename NAME [SUFFIX]\n"
    + "  or:  _build/coreutils/src/basename OPTION... NAME...\n"
    + "Print NAME with any leading directory components removed.\n"
    + "If specified, also remove a trailing SUFFIX.\n"
    + "\n"
    + "Mandatory arguments to long options are mandatory for short options too.\n"
    + "  -a, --multiple\n"
    + "         support multiple arguments and treat each as a NAME\n"
    + "  -s, --suffix=SUFFIX\n"
    + "         remove a trailing SUFFIX; implies -a\n"
    + "  -z, --zero\n"
    + "         end each output line with NUL, not newline\n"
    + "      --help\n"
    + "         display this help and exit\n"
    + "      --version\n"
    + "         output version information and exit\n"
    + "\n"
    + "Examples:\n"
    + "  _build/coreutils/src/basename /usr/bin/sort          -> \"sort\"\n"
    + "  _build/coreutils/src/basename include/stdio.h .h     -> \"stdio\"\n"
    + "  _build/coreutils/src/basename -s .h include/stdio.h  -> \"stdio\"\n"
    + "  _build/coreutils/src/basename -a any/str1 any/str2   -> \"str1\" followed by \"str2\"\n"
    + "\n"
    + "Report bugs to: bug-coreutils@gnu.org\n"
    + "GNU coreutils home page: <https://www.gnu.org/software/coreutils/>\n"
    + "General help using GNU software: <https://www.gnu.org/gethelp/>\n"
    + "Report any translation bugs to <https://translationproject.org/team/>\n"
    + "Full documentation <https://www.gnu.org/software/coreutils/basename>\n"
    + "or available locally via: info '(coreutils) basename invocation'\n"
  }

  function VersionTextSpec(): BenchWorld.Bytes
  {
    "basename (GNU coreutils) 9.10.13-2cf49\n"
    + "Copyright (C) 2026 Free Software Foundation, Inc.\n"
    + "License GPLv3+: GNU GPL version 3 or later <https://gnu.org/licenses/gpl.html>.\n"
    + "This is free software: you are free to change and redistribute it.\n"
    + "There is NO WARRANTY, to the extent permitted by law.\n"
    + "\n"
    + "Written by David MacKenzie.\n"
  }

  function MissingOperandMessageSpec(): BenchWorld.Bytes
  {
    "basename: missing operand\nTry 'basename --help' for more information.\n"
  }

  function ExtraOperandMessageSpec(op: string): BenchWorld.Bytes
  {
    Utf8.Encode("basename: extra operand '" + op + "'\n" +
    "Try 'basename --help' for more information.\n")
  }

  twostate predicate Spec(raw: Schema.BasenameCmdRaw, io: BenchIO.IO, exit: int)
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
    else if !cmd.multiple && |cmd.operands| > 2 then
      io.stdout() == old(io.stdout()) &&
      io.stderr() == old(io.stderr()) + ExtraOperandMessageSpec(cmd.operands[2]) &&
      exit == 1
    else
      io.stderr() == old(io.stderr()) &&
      exit == 0 &&
      exists out: string ::
        CommandOutputRelation(cmd, out) &&
        io.stdout() == old(io.stdout()) + Utf8.Encode(out)
  }
}
