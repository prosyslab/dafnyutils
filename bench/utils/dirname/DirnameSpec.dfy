include "../../core/World.dfy"
include "../../core/IO.dfy"
include "../../core/Utf8.dfy"
include "DirnameSchema.dfy"

module DirnameSpec {
  import Utf8 = Utf8Semantics
  import BenchIO
  import BenchWorld
  import Schema = DirnameSchema



  function IsSlash(ch: char): bool
  {
    ch == '/'
  }

  function HelpRequested(raw: Schema.DirnameCmdRaw): bool
  {
    raw.seenHelp &&
    (!raw.seenVersion || raw.helpTokenIndex <= raw.versionTokenIndex)
  }

  function VersionRequested(raw: Schema.DirnameCmdRaw): bool
  {
    !HelpRequested(raw) && raw.seenVersion
  }

  function OutputSeparator(zeroTerminated: bool): string
  {
    if zeroTerminated then ['\0'] else "\n"
  }

  ghost predicate SlashFree(text: string)
  {
    '/' !in text
  }

  ghost predicate SlashesOnly(text: string)
  {
    forall i :: 0 <= i < |text| ==> IsSlash(text[i])
  }

  ghost predicate PathWithoutTrailingSlashes(
    path: string, trimmed: string, trailing: string
  )
  {
    path == trimmed + trailing &&
    SlashesOnly(trailing) &&
    0 < |trimmed| &&
    !IsSlash(trimmed[|trimmed| - 1])
  }

  ghost predicate MaximalDirnamePrefix(
    trimmed: string, prefix: string, component: string
  )
  {
    trimmed == prefix + "/" + component &&
    0 < |component| &&
    SlashFree(component)
  }

  ghost predicate NormalizedDirnamePrefix(prefix: string, value: string)
  {
    if |prefix| == 0 then
      value == "/"
    else if SlashesOnly(prefix) then
      value == "/"
    else
      exists trailing: string ::
        prefix == value + trailing &&
        SlashesOnly(trailing) &&
        0 < |value| &&
        !IsSlash(value[|value| - 1])
  }

  opaque ghost predicate DirnameRelation(path: string, value: string)
  {
    if |path| == 0 then
      value == "."
    else if SlashesOnly(path) then
      value == "/"
    else
      exists trimmed: string, trailing: string ::
        PathWithoutTrailingSlashes(path, trimmed, trailing) &&
        (if SlashFree(trimmed) then
           value == "."
         else
           exists prefix: string, component: string ::
             MaximalDirnamePrefix(trimmed, prefix, component) &&
             NormalizedDirnamePrefix(prefix, value))
  }

  ghost predicate OperandOutputPartition(
    paths: seq<string>,
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
         DirnameRelation(paths[i], pieces[i]) &&
         out[cuts[i]..cuts[i + 1]] == pieces[i] + sep)
  }

  ghost predicate OperandOutputRelation(
    paths: seq<string>, sep: string, out: string
  )
  {
    exists pieces: seq<string>, cuts: seq<nat> ::
      OperandOutputPartition(paths, sep, out, pieces, cuts)
  }

  ghost predicate CommandOutputRelation(
    zeroTerminated: bool,
    operands: seq<string>,
    out: string
  )
  {
    OperandOutputRelation(operands, OutputSeparator(zeroTerminated), out)
  }

  function HelpTextSpec(): BenchWorld.Bytes
  {
    "Usage: dirname [OPTION] NAME...\n"
    + "Output each NAME with its last non-slash component and trailing slashes\n"
    + "removed; if NAME contains no /'s, output '.' (meaning the current directory).\n"
    + "\n"
    + "  -z, --zero\n"
    + "         end each output line with NUL, not newline\n"
    + "      --help\n"
    + "         display this help and exit\n"
    + "      --version\n"
    + "         output version information and exit\n"
    + "\n"
    + "Examples:\n"
    + "  dirname /usr/bin/          -> \"/usr\"\n"
    + "  dirname dir1/str dir2/str  -> \"dir1\" followed by \"dir2\"\n"
    + "  dirname stdio.h            -> \".\"\n"
    + "\n"
    + "Report bugs to: bug-coreutils@gnu.org\n"
    + "GNU coreutils home page: <https://www.gnu.org/software/coreutils/>\n"
    + "General help using GNU software: <https://www.gnu.org/gethelp/>\n"
    + "Report any translation bugs to <https://translationproject.org/team/>\n"
    + "Full documentation <https://www.gnu.org/software/coreutils/dirname>\n"
    + "or available locally via: info '(coreutils) dirname invocation'\n"
  }

  function VersionTextSpec(): BenchWorld.Bytes
  {
    "dirname (GNU coreutils) 9.10.13-2cf49\n"
    + "Copyright (C) 2026 Free Software Foundation, Inc.\n"
    + "License GPLv3+: GNU GPL version 3 or later <https://gnu.org/licenses/gpl.html>.\n"
    + "This is free software: you are free to change and redistribute it.\n"
    + "There is NO WARRANTY, to the extent permitted by law.\n"
    + "\n"
    + "Written by David MacKenzie and Jim Meyering.\n"
  }

  function MissingOperandMessageSpec(): BenchWorld.Bytes
  {
    "dirname: missing operand\nTry 'dirname --help' for more information.\n"
  }

  twostate predicate Spec(raw: Schema.DirnameCmdRaw, io: BenchIO.IO, exit: int)
    reads io.Footprint()
  {
    if HelpRequested(raw) then
      io.stdout() == old(io.stdout()) + HelpTextSpec() &&
      io.stderr() == old(io.stderr()) &&
      exit == 0
    else if VersionRequested(raw) then
      io.stdout() == old(io.stdout()) + VersionTextSpec() &&
      io.stderr() == old(io.stderr()) &&
      exit == 0
    else if |raw.operands| == 0 then
      io.stdout() == old(io.stdout()) &&
      io.stderr() == old(io.stderr()) + MissingOperandMessageSpec() &&
      exit == 1
    else
      io.stderr() == old(io.stderr()) &&
      exit == 0 &&
      exists out: string ::
        CommandOutputRelation(raw.seenZero, raw.operands, out) &&
        io.stdout() == old(io.stdout()) + Utf8.Encode(out)
  }
}
