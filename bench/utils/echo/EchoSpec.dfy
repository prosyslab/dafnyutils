include "../../core/World.dfy"
include "../../core/IO.dfy"
include "EchoSchema.dfy"

module EchoSpec {
  import BenchIO
  import Utf8 = Utf8Semantics
  import BenchWorld
  import EchoSchema



  datatype EchoMode = ModeRun | ModeHelp | ModeVersion

  function PosixlyCorrect(env: map<string, string>): bool
  {
    "POSIXLY_CORRECT" in env
  }

  function HelpText(): BenchWorld.Bytes
  {
    "Usage: echo [SHORT-OPTION]... [STRING]...\n"
    + "  or:  echo LONG-OPTION\n"
    + "Echo the STRING(s) to standard output.\n"
    + "\n"
    + "  -n             do not output the trailing newline\n"
    + "  -e             enable interpretation of backslash escapes\n"
    + "  -E             disable interpretation of backslash escapes (default)\n"
    + "      --help     display this help and exit\n"
    + "      --version  output version information and exit\n"
    + "\n"
    + "If -e is in effect, the following sequences are recognized:\n"
    + "\n"
    + "  \\\\      backslash\n"
    + "  \\a      alert (BEL)\n"
    + "  \\b      backspace\n"
    + "  \\c      produce no further output\n"
    + "  \\e      escape\n"
    + "  \\f      form feed\n"
    + "  \\n      new line\n"
    + "  \\r      carriage return\n"
    + "  \\t      horizontal tab\n"
    + "  \\v      vertical tab\n"
    + "  \\0NNN   byte with octal value NNN (1 to 3 digits)\n"
    + "  \\xHH    byte with hexadecimal value HH (1 to 2 digits)\n"
    + "\n"
    + "Report bugs to: bug-coreutils@gnu.org\n"
    + "GNU coreutils home page: <https://www.gnu.org/software/coreutils/>\n"
    + "General help using GNU software: <https://www.gnu.org/gethelp/>\n"
    + "Report any translation bugs to <https://translationproject.org/team/>\n"
    + "Full documentation <https://www.gnu.org/software/coreutils/echo>\n"
    + "or available locally via: info '(coreutils) echo invocation'\n"
  }

  function VersionText(): BenchWorld.Bytes
  {
    "echo (GNU coreutils) 9.10.13-2cf49\n"
    + "Copyright (C) 2026 Free Software Foundation, Inc.\n"
    + "License GPLv3+: GNU GPL version 3 or later <https://gnu.org/licenses/gpl.html>.\n"
    + "This is free software: you are free to change and redistribute it.\n"
    + "There is NO WARRANTY, to the extent permitted by law.\n"
    + "\n"
    + "Written by Brian Fox and Chet Ramey.\n"
  }

  function ValidEchoOptionChar(c: char): bool
  {
    c == 'n' || c == 'e' || c == 'E'
  }

  function IsHexDigit(c: char): bool
  {
    ('0' <= c <= '9') || ('a' <= c <= 'f') || ('A' <= c <= 'F')
  }

  function HexValue(c: char): int
    requires IsHexDigit(c)
  {
    if '0' <= c <= '9' then
      (c as int) - ('0' as int)
    else if 'a' <= c <= 'f' then
      10 + (c as int) - ('a' as int)
    else
      10 + (c as int) - ('A' as int)
  }

  ghost predicate OptionToken(token: string)
  {
    |token| > 1 &&
    token[0] == '-' &&
    forall i :: 1 <= i < |token| ==> ValidEchoOptionChar(token[i])
  }

  ghost predicate MaximalOptionPrefix(args: seq<string>, next: nat)
  {
    next <= |args| &&
    (forall i :: 0 <= i < next ==> OptionToken(args[i])) &&
    (next == |args| || !OptionToken(args[next]))
  }

  ghost predicate NoNewlineInPrefix(args: seq<string>, next: nat, noNewline: bool)
    requires next <= |args|
  {
    noNewline ==
    (exists i ::
       0 <= i < next &&
       0 < |args[i]| &&
       'n' in args[i][1..])
  }

  ghost predicate LastEscapeOptionEnables(args: seq<string>, next: nat, enabled: bool)
    requires next <= |args|
  {
    enabled ==
    (exists i ::
       0 <= i < next &&
       exists j ::
         1 <= j < |args[i]| &&
         args[i][j] == 'e' &&
         forall k ::
           0 <= k < next ==>
             forall l ::
               1 <= l < |args[k]| &&
               (i < k || (i == k && j < l)) ==>
                 args[k][l] != 'e' && args[k][l] != 'E')
  }

  ghost predicate CommandRelation(
    raw: EchoSchema.EchoCmdRaw,
    posixlyCorrect: bool,
    mode: EchoMode,
    noNewline: bool,
    escapes: bool,
    operands: seq<string>
  )
  {
    var args := raw.args;
    var allowOptions := !posixlyCorrect || (|args| > 0 && args[0] == "-n");
    if allowOptions && |args| == 1 && args[0] == "--help" then
      mode == ModeHelp &&
      !noNewline &&
      !escapes &&
      operands == []
    else if allowOptions && |args| == 1 && args[0] == "--version" then
      mode == ModeVersion &&
      !noNewline &&
      !escapes &&
      operands == []
    else if allowOptions then
      mode == ModeRun &&
      exists next: nat, doV9: bool ::
        MaximalOptionPrefix(args, next) &&
        NoNewlineInPrefix(args, next, noNewline) &&
        LastEscapeOptionEnables(args, next, doV9) &&
        escapes == (doV9 || posixlyCorrect) &&
        operands == args[next..]
    else
      mode == ModeRun &&
      !noNewline &&
      escapes == posixlyCorrect &&
      operands == args
  }

  ghost predicate OctalSpan(text: string, start: nat, count: nat, limit: nat)
  {
    start <= |text| &&
    count <= limit &&
    start + count <= |text| &&
    (forall i :: start <= i < start + count ==> BenchWorld.IsOctalDigit(text[i])) &&
    (count >= 1 ==> BenchWorld.IsOctalDigit(text[start])) &&
    (count >= 2 ==> BenchWorld.IsOctalDigit(text[start + 1])) &&
    (count >= 3 ==> BenchWorld.IsOctalDigit(text[start + 2])) &&
    (count == limit ||
     start + count == |text| ||
     !BenchWorld.IsOctalDigit(text[start + count]))
  }

  function OctalSpanValue(text: string, start: nat, count: nat): int
    requires start + count <= |text|
    requires count <= 3
    requires count >= 1 ==> BenchWorld.IsOctalDigit(text[start])
    requires count >= 2 ==> BenchWorld.IsOctalDigit(text[start + 1])
    requires count >= 3 ==> BenchWorld.IsOctalDigit(text[start + 2])
  {
    if count == 0 then
      0
    else if count == 1 then
      BenchWorld.CharToDigit(text[start])
    else if count == 2 then
      BenchWorld.CharToDigit(text[start]) * 8 +
      BenchWorld.CharToDigit(text[start + 1])
    else
      BenchWorld.CharToDigit(text[start]) * 64 +
      BenchWorld.CharToDigit(text[start + 1]) * 8 +
      BenchWorld.CharToDigit(text[start + 2])
  }

  ghost predicate EscapeUnitRelation(
    text: string,
    lo: nat,
    hi: nat,
    piece: BenchWorld.Bytes,
    stopped: bool
  )
  {
    lo < |text| &&
    if text[lo] != '\\' || lo + 1 >= |text| then
      hi == lo + 1 && piece == Utf8.EncodeChar(text[lo]) && !stopped
    else
      var e := text[lo + 1];
      if e == 'c' then
        hi == lo + 2 && piece == [] && stopped
      else if e == 'a' then
        hi == lo + 2 && piece == [(7 as char)] && !stopped
      else if e == 'b' then
        hi == lo + 2 && piece == [(8 as char)] && !stopped
      else if e == 'e' then
        hi == lo + 2 && piece == [(27 as char)] && !stopped
      else if e == 'f' then
        hi == lo + 2 && piece == [(12 as char)] && !stopped
      else if e == 'n' then
        hi == lo + 2 && piece == [(10 as char)] && !stopped
      else if e == 'r' then
        hi == lo + 2 && piece == [(13 as char)] && !stopped
      else if e == 't' then
        hi == lo + 2 && piece == [(9 as char)] && !stopped
      else if e == 'v' then
        hi == lo + 2 && piece == [(11 as char)] && !stopped
      else if e == '\\' then
        hi == lo + 2 && piece == ['\\'] && !stopped
      else if e == 'x' && lo + 2 < |text| && IsHexDigit(text[lo + 2]) then
        var count := if lo + 3 < |text| && IsHexDigit(text[lo + 3]) then 2 else 1;
        hi == lo + 2 + count &&
        piece == [
          (if count == 2 then
             HexValue(text[lo + 2]) * 16 + HexValue(text[lo + 3])
           else
             HexValue(text[lo + 2])) as char
        ] &&
        !stopped
      else if e == 'x' then
        hi == lo + 2 && piece == ['\\', 'x'] && !stopped
      else if e == '0' then
        exists count: nat {:trigger OctalSpan(text, lo + 2, count, 3)} ::
          OctalSpan(text, lo + 2, count, 3) &&
          hi == lo + 2 + count &&
          piece == [(OctalSpanValue(text, lo + 2, count) % 256) as char] &&
          !stopped
      else if BenchWorld.IsOctalDigit(e) then
        exists count: nat {:trigger OctalSpan(text, lo + 1, count, 3)} ::
          1 <= count <= 3 &&
          OctalSpan(text, lo + 1, count, 3) &&
          hi == lo + 1 + count &&
          piece == [(OctalSpanValue(text, lo + 1, count) % 256) as char] &&
          !stopped
      else
        hi == lo + 2 && piece == ['\\'] + Utf8.EncodeChar(e) && !stopped
  }

  ghost predicate EscapedPartition(
    text: string,
    start: nat,
    out: BenchWorld.Bytes,
    stopped: bool,
    inputCuts: seq<nat>,
    outputCuts: seq<nat>
  )
  {
    |inputCuts| == |outputCuts| &&
    0 < |inputCuts| &&
    start <= |text| &&
    inputCuts[0] == start &&
    outputCuts[0] == 0 &&
    inputCuts[|inputCuts| - 1] <= |text| &&
    outputCuts[|outputCuts| - 1] == |out| &&
    (!stopped ==> inputCuts[|inputCuts| - 1] == |text|) &&
    (stopped ==> 1 < |inputCuts|) &&
    (forall i
       {:trigger inputCuts[i], inputCuts[i + 1]}
       {:trigger out[outputCuts[i]..outputCuts[i + 1]]} ::
       0 <= i && i + 1 < |inputCuts| ==>
         inputCuts[i] < inputCuts[i + 1] <= |text| &&
         outputCuts[i] <= outputCuts[i + 1] <= |out| &&
         EscapeUnitRelation(
           text,
           inputCuts[i],
           inputCuts[i + 1],
           out[outputCuts[i]..outputCuts[i + 1]],
           stopped && i + 2 == |inputCuts|
         ))
  }

  ghost predicate EscapedStringRelation(
    text: string, out: BenchWorld.Bytes, stopped: bool
  )
  {
    exists inputCuts: seq<nat>, outputCuts: seq<nat> ::
      EscapedPartition(text, 0, out, stopped, inputCuts, outputCuts)
  }

  ghost predicate ArgumentRelation(
    text: string, escapes: bool, out: BenchWorld.Bytes, stopped: bool
  )
  {
    if escapes then
      EscapedStringRelation(text, out, stopped)
    else
      out == Utf8.Encode(text) && !stopped
  }

  ghost predicate OperandPartition(
    args: seq<string>,
    escapes: bool,
    out: BenchWorld.Bytes,
    stopped: bool,
    count: nat,
    pieces: seq<BenchWorld.Bytes>,
    cuts: seq<nat>
  )
  {
    count <= |args| &&
    |pieces| == count &&
    |cuts| == count + 1 &&
    cuts[0] == 0 &&
    cuts[count] == |out| &&
    (!stopped ==> count == |args|) &&
    (stopped ==> 0 < count) &&
    (forall i {:trigger cuts[i], cuts[i + 1]} ::
       0 <= i < count ==>
         cuts[i] <= cuts[i + 1] <= |out| &&
         ArgumentRelation(args[i], escapes, pieces[i], stopped && i + 1 == count) &&
         out[cuts[i]..cuts[i + 1]] ==
         pieces[i] + (if i + 1 < count then [' '] else []))
  }

  ghost predicate OperandRelation(
    args: seq<string>, escapes: bool, out: BenchWorld.Bytes, stopped: bool
  )
  {
    exists count: nat, pieces: seq<BenchWorld.Bytes>, cuts: seq<nat> ::
      OperandPartition(args, escapes, out, stopped, count, pieces, cuts)
  }

  ghost predicate OutputRelation(
    raw: EchoSchema.EchoCmdRaw,
    posixlyCorrect: bool,
    out: BenchWorld.Bytes
  )
  {
    exists mode: EchoMode, noNewline: bool, escapes: bool, operands: seq<string> ::
      CommandRelation(raw, posixlyCorrect, mode, noNewline, escapes, operands) &&
      if mode == ModeHelp then
        out == HelpText()
      else if mode == ModeVersion then
        out == VersionText()
      else
        exists rendered: BenchWorld.Bytes, stopped: bool ::
          OperandRelation(operands, escapes, rendered, stopped) &&
          out == rendered + (if stopped || noNewline then [] else "\n")
  }

  twostate predicate Spec(raw: EchoSchema.EchoCmdRaw, io: BenchIO.IO, exit: int)
    reads io.Footprint()
  {
    exit == 0 &&
    exists out: BenchWorld.Bytes ::
      OutputRelation(raw, PosixlyCorrect(old(io.env())), out) &&
      io.stdout() == old(io.stdout()) + out
  }
}
