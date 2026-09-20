include "../../core/World.dfy"
include "../../core/Utf8.dfy"
include "../../core/IO.dfy"
include "../../core/IOContract.dfy"
include "UniqSchema.dfy"

module UniqSpec {
  import BenchIO
  import BenchWorld
  import IOContract
  import BW = BenchWorld
  import Utf8 = Utf8Semantics
  import UniqSchema




  function SpecCPrintableByte(byte: char): bool
  {
    0x20 <= byte as int <= 0x7e
  }

  function SpecOctDigit(value: int): char
  {
    if value == 0 then '0'
    else if value == 1 then '1'
    else if value == 2 then '2'
    else if value == 3 then '3'
    else if value == 4 then '4'
    else if value == 5 then '5'
    else if value == 6 then '6'
    else '7'
  }

  function SpecOctalEscape(byte: char): BW.Bytes
  {
    var value := byte as int;
    ['\\', SpecOctDigit((value / 64) % 8), SpecOctDigit((value / 8) % 8), SpecOctDigit(value % 8)]
  }

  function SpecNamedEscape(byte: char): BW.Bytes
  {
    if byte == 7 as char then "\\a"
    else if byte == 8 as char then "\\b"
    else if byte == 12 as char then "\\f"
    else if byte == '\n' then "\\n"
    else if byte == '\r' then "\\r"
    else if byte == '\t' then "\\t"
    else if byte == 11 as char then "\\v"
    else []
  }

  function SpecAnsiEscape(byte: char): BW.Bytes
  {
    var named := SpecNamedEscape(byte);
    if named != [] then named else SpecOctalEscape(byte)
  }

  function SpecNeedsAnsiEscape(byte: char): bool
  {
    !SpecCPrintableByte(byte)
  }

  function SpecCQuoteByte(byte: char): BW.Bytes
  {
    var named := SpecNamedEscape(byte);
    if named != [] then named
    else if byte == '\\' then "\\\\"
    else if byte == '"' then "\\\""
    else if SpecCPrintableByte(byte) then [byte]
    else SpecOctalEscape(byte)
  }

  function SpecCQuoteBytes(bytes: BW.Bytes): BW.Bytes
    decreases |bytes|
  {
    if |bytes| == 0 then
      []
    else
      SpecCQuoteByte(bytes[0]) + SpecCQuoteBytes(bytes[1..])
  }

  function SpecDoubleQuote(bytes: BW.Bytes): BW.Bytes
  {
    "\"" + SpecCQuoteBytes(bytes) + "\""
  }

  // `atStart` and `singleton` carry the only positional facts the byte test
  // needs; both are supplied once at the entry point.
  function SpecShellCompatibleByte(byte: char, atStart: bool, singleton: bool): bool
  {
    if byte == '?' || byte == '\\' then
      false
    else if byte == '{' || byte == '}' then
      singleton
    else if byte == '#' || byte == '~' then
      atStart
    else if byte == ' ' || byte == '\'' then
      true
    else if byte == '!' || byte == '"' || byte == '$' || byte == '&' ||
            byte == '(' || byte == ')' || byte == '*' || byte == ';' ||
            byte == '<' || byte == '=' || byte == '>' || byte == '[' ||
            byte == '^' || byte == '`' || byte == '|' then
      false
    else
      SpecCPrintableByte(byte)
  }

  function SpecShellCompatibleTail(bytes: BW.Bytes): bool
    decreases |bytes|
  {
    |bytes| == 0 ||
    (SpecShellCompatibleByte(bytes[0], false, false) &&
     SpecShellCompatibleTail(bytes[1..]))
  }

  function SpecAllShellCompatible(bytes: BW.Bytes): bool
  {
    |bytes| == 0 ||
    (SpecShellCompatibleByte(bytes[0], true, |bytes| == 1) &&
     SpecShellCompatibleTail(bytes[1..]))
  }

  function SpecContainsApostrophe(bytes: BW.Bytes): bool
  {
    '\'' in bytes
  }

  function SpecShellEscapeTail(bytes: BW.Bytes, ansi: bool): BW.Bytes
    decreases |bytes|
  {
    if |bytes| == 0 then
      "'"
    else
      var byte := bytes[0];
      if byte == '\'' then
        "'\\''" + SpecShellEscapeTail(bytes[1..], false)
      else if SpecNeedsAnsiEscape(byte) then
        (if ansi then [] else "'$'") + SpecAnsiEscape(byte) +
        SpecShellEscapeTail(bytes[1..], true)
      else
        (if ansi then "''" else []) + [byte] +
        SpecShellEscapeTail(bytes[1..], false)
  }

  function SpecQuoteAfBytes(bytes: BW.Bytes): BW.Bytes
  {
    if SpecContainsApostrophe(bytes) && SpecAllShellCompatible(bytes) then
      SpecDoubleQuote(bytes)
    else
      "'" + SpecShellEscapeTail(bytes, false)
  }

  function SpecShellQuoteTriggerByte(byte: char, atStart: bool, singleton: bool): bool
  {
    !SpecCPrintableByte(byte) ||
    byte == '\\' || byte == '\'' || byte == '?' || byte == ':' ||
    byte == ' ' || byte == '!' || byte == '"' || byte == '$' ||
    byte == '&' || byte == '(' || byte == ')' || byte == '*' ||
    byte == ';' || byte == '<' || byte == '=' || byte == '>' ||
    byte == '[' || byte == '^' || byte == '`' || byte == '|' ||
    ((byte == '#' || byte == '~') && atStart) ||
    ((byte == '{' || byte == '}') && singleton)
  }

  function SpecHasShellQuoteTriggerTail(bytes: BW.Bytes): bool
    decreases |bytes|
  {
    |bytes| != 0 &&
    (SpecShellQuoteTriggerByte(bytes[0], false, false) ||
     SpecHasShellQuoteTriggerTail(bytes[1..]))
  }

  function SpecHasShellQuoteTrigger(bytes: BW.Bytes): bool
  {
    |bytes| != 0 &&
    (SpecShellQuoteTriggerByte(bytes[0], true, |bytes| == 1) ||
     SpecHasShellQuoteTriggerTail(bytes[1..]))
  }

  function SpecQuoteFBytes(bytes: BW.Bytes): BW.Bytes
  {
    if |bytes| == 0 || SpecHasShellQuoteTrigger(bytes) then
      SpecQuoteAfBytes(bytes)
    else
      bytes
  }

  datatype Group = Group(line: BenchWorld.Bytes, count: nat)

  function HelpTextSpec(): BenchWorld.Bytes
  {
    "Usage: uniq [OPTION]... [INPUT [OUTPUT]]\n"
    + "Filter adjacent matching lines from INPUT (or standard input),\n"
    + "writing to OUTPUT (or standard output).\n"
    + "\n"
    + "With no options, matching lines are merged to the first occurrence.\n"
    + "\n"
    + "  -c, --count           prefix lines by the number of occurrences\n"
    + "  -d, --repeated        only print duplicate lines, one for each group\n"
    + "  -i, --ignore-case     ignore differences in case when comparing\n"
    + "  -u, --unique          only print unique lines\n"
    + "      --help        display this help and exit\n"
    + "      --version     output version information and exit\n"
    + "\n"
    + "Note: 'uniq' does not detect repeated lines unless they are adjacent.\n"
    + "You may want to sort the input first, or use 'sort -u' without 'uniq'.\n"
    + "\n"
    + "Benchmark note: non-'-' OUTPUT operands and GNU field, character,\n"
    + "grouping, and zero-terminated modes are not implemented here.\n"
    + "\n"
    + "Report bugs to: bug-coreutils@gnu.org\n"
    + "GNU coreutils home page: <https://www.gnu.org/software/coreutils/>\n"
    + "General help using GNU software: <https://www.gnu.org/gethelp/>\n"
    + "Full documentation <https://www.gnu.org/software/coreutils/uniq>\n"
    + "or available locally via: info '(coreutils) uniq invocation'\n"
  }

  function VersionTextSpec(): BenchWorld.Bytes
  {
    "uniq (GNU coreutils) 9.10.13-2cf49\n"
    + "Copyright (C) 2026 Free Software Foundation, Inc.\n"
    + "License GPLv3+: GNU GPL version 3 or later <https://gnu.org/licenses/gpl.html>.\n"
    + "This is free software: you are free to change and redistribute it.\n"
    + "There is NO WARRANTY, to the extent permitted by law.\n"
    + "\n"
    + "Written by Richard M. Stallman and David MacKenzie.\n"
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

  function QuoteIfNeeded(path: string): BenchWorld.Bytes
  {
    SpecQuoteFBytes(Utf8.Encode(path))
  }

  function QuoteAlways(path: string): string
  {
    "'" + path + "'"
  }

  function ReadErrorMessageSpec(path: BenchWorld.Path, err: BenchWorld.IOError): BenchWorld.Bytes
  {
    if err == BenchWorld.IsDirectory then
      Utf8.Encode("uniq: error reading " + QuoteAlways(path) + ": " + ErrnoText(err) + "\n")
    else
      "uniq: " + QuoteIfNeeded(path) + ": " + Utf8.Encode(ErrnoText(err)) + "\n"
  }

  // Formal specification gap: non-"-" OUTPUT operands are intentionally
  // rejected in this benchmark relation until World/IO can model file-content
  // writes and truncation.
  function UnsupportedOutputMessageSpec(path: BenchWorld.Path): BenchWorld.Bytes
  {
    Utf8.Encode("uniq: output file " + QuoteAlways(path) +
    " is not supported by this benchmark\n")
  }

  function UnsupportedSkipCharsMessageSpec(operand: string): BenchWorld.Bytes
  {
    Utf8.Encode("uniq: traditional skip-character operand '" + operand +
    "' is not supported by this benchmark\n")
  }

  function ExtraOperandMessageSpec(operand: string): BenchWorld.Bytes
  {
    Utf8.Encode("uniq: extra operand '" + operand + "'\n" +
    "Try 'uniq --help' for more information.\n")
  }

  function InputFromOperands(operands: seq<string>): UniqSchema.Input
  {
    if |operands| > 0 && operands[0] != "-" then
      UniqSchema.File(operands[0])
    else
      UniqSchema.Stdin
  }

  function Command(raw: UniqSchema.UniqCmdRaw): UniqSchema.UniqCmd
  {
    var mode :=
      if raw.seenHelp && (!raw.seenVersion || raw.helpTokenIndex <= raw.versionTokenIndex) then
        UniqSchema.ModeHelp
      else if raw.seenVersion then
        UniqSchema.ModeVersion
      else if UniqSchema.UnsupportedSkipOperand(raw.operands) != "" then
        UniqSchema.ModeUnsupportedSkipChars(UniqSchema.UnsupportedSkipOperand(raw.operands))
      else if |raw.operands| > 2 then
        UniqSchema.ModeExtraOperand(raw.operands[2])
      else if |raw.operands| == 2 && raw.operands[1] != "-" then
        UniqSchema.ModeUnsupportedOutput(raw.operands[1])
      else
        UniqSchema.ModeRun;
    UniqSchema.UniqCmd(
      mode,
      raw.seenCount,
      !raw.seenRepeated,
      !raw.seenUnique,
      raw.seenIgnoreCase,
      InputFromOperands(raw.operands)
    )
  }

  function LowerAscii(ch: BenchWorld.RawByte): BenchWorld.RawByte
  {
    var code := ch as int;
    if ('A' as int) <= code <= ('Z' as int) then
      (code + (('a' as int) - ('A' as int))) as char
    else
      ch
  }

  function EqualFoldAscii(a: BenchWorld.Bytes, b: BenchWorld.Bytes): bool
    decreases |a|
  {
    if |a| != |b| then
      false
    else if |a| == 0 then
      true
    else
      LowerAscii(a[0]) == LowerAscii(b[0]) && EqualFoldAscii(a[1..], b[1..])
  }

  function LinesEqual(cmd: UniqSchema.UniqCmd, a: BenchWorld.Bytes, b: BenchWorld.Bytes): bool
  {
    if cmd.ignoreCase then EqualFoldAscii(a, b) else a == b
  }

  ghost predicate FragmentsConcatenate(
    fragments: seq<BenchWorld.Bytes>,
    combined: BenchWorld.Bytes,
    cuts: seq<nat>
  )
  {
    |cuts| == |fragments| + 1 &&
    cuts[0] == 0 &&
    cuts[|cuts| - 1] == |combined| &&
    forall i {:trigger cuts[i]} :: 0 <= i < |fragments| ==>
                                     cuts[i] <= cuts[i + 1] &&
                                     cuts[i + 1] <= |combined| &&
                                     cuts[i + 1] == cuts[i] + |fragments[i]| &&
                                     combined[cuts[i]..cuts[i + 1]] == fragments[i]
  }

  ghost predicate RecordPartitionWitnessRelation(
    data: BenchWorld.Bytes,
    records: seq<BenchWorld.Bytes>,
    terminated: seq<bool>,
    fragments: seq<BenchWorld.Bytes>,
    cuts: seq<nat>
  )
  {
    |records| == |terminated| == |fragments| &&
    (|data| == 0) == (|records| == 0) &&
    (forall i :: 0 <= i < |records| ==>
                   |fragments[i]| > 0 &&
                   fragments[i] ==
                   records[i] + (if terminated[i] then ['\n'] else []) &&
                   '\n' !in records[i] &&
                   (i + 1 < |records| ==> terminated[i])) &&
    FragmentsConcatenate(fragments, data, cuts)
  }

  ghost predicate RecordsConcatenate(
    runs: seq<seq<BenchWorld.Bytes>>,
    records: seq<BenchWorld.Bytes>,
    cuts: seq<nat>
  )
  {
    |cuts| == |runs| + 1 &&
    cuts[0] == 0 &&
    cuts[|cuts| - 1] == |records| &&
    forall i {:trigger cuts[i]} :: 0 <= i < |runs| ==>
                                     cuts[i] <= cuts[i + 1] &&
                                     cuts[i + 1] <= |records| &&
                                     cuts[i + 1] == cuts[i] + |runs[i]| &&
                                     records[cuts[i]..cuts[i + 1]] == runs[i]
  }

  ghost predicate RecordPartitionRelation(
    data: BenchWorld.Bytes,
    records: seq<BenchWorld.Bytes>,
    terminated: seq<bool>
  )
  {
    exists fragments: seq<BenchWorld.Bytes>, cuts: seq<nat> ::
      RecordPartitionWitnessRelation(
        data, records, terminated, fragments, cuts
      )
  }

  ghost predicate RunPartitionWitnessRelation(
    command: UniqSchema.UniqCmd,
    records: seq<BenchWorld.Bytes>,
    groups: seq<Group>,
    runs: seq<seq<BenchWorld.Bytes>>,
    cuts: seq<nat>
  )
  {
    |groups| == |runs| &&
    (|records| == 0) == (|groups| == 0) &&
    (forall i :: 0 <= i < |groups| ==>
                   |runs[i]| > 0 &&
                   groups[i].count == |runs[i]| &&
                   groups[i].line == runs[i][0] &&
                   (forall j :: 0 <= j < |runs[i]| ==>
                                  LinesEqual(command, groups[i].line, runs[i][j])) &&
                   (i + 1 < |groups| ==>
                      !LinesEqual(command, groups[i].line, groups[i + 1].line))) &&
    RecordsConcatenate(runs, records, cuts)
  }

  ghost predicate RunPartitionRelation(
    command: UniqSchema.UniqCmd,
    records: seq<BenchWorld.Bytes>,
    groups: seq<Group>
  )
  {
    exists runs: seq<seq<BenchWorld.Bytes>>, cuts: seq<nat> ::
      RunPartitionWitnessRelation(
        command, records, groups, runs, cuts
      )
  }

  function DigitChar(d: int): BenchWorld.RawByte
  {
    if 0 <= d < 10 then
      (d + ('0' as int)) as char
    else
      '0'
  }

  function Digits(n: nat): BenchWorld.Bytes
    decreases n
  {
    if n < 10 then
      [DigitChar(n as int)]
    else
      Digits(n / 10) + [DigitChar((n % 10) as int)]
  }

  function PadLeft(text: BenchWorld.Bytes, width: int): BenchWorld.Bytes
    decreases width - |text|
  {
    if |text| >= width then
      text
    else
      PadLeft([' '] + text, width)
  }

  function CountPrefix(count: nat): BenchWorld.Bytes
  {
    PadLeft(Digits(count), 7) + [' ']
  }

  function ShouldOutputGroup(cmd: UniqSchema.UniqCmd, group: Group): bool
  {
    (group.count == 1 && cmd.outputUnique) ||
    (group.count > 1 && cmd.outputRepeated)
  }

  ghost predicate GroupRenderRelation(
    command: UniqSchema.UniqCmd,
    group: Group,
    outputRecord: BenchWorld.Bytes
  )
  {
    outputRecord ==
    if ShouldOutputGroup(command, group) then
      (if command.countOccurrences then CountPrefix(group.count) else []) +
      group.line + ['\n']
    else
      []
  }

  ghost predicate OutputWitnessRelation(
    command: UniqSchema.UniqCmd,
    data: BenchWorld.Bytes,
    output: BenchWorld.Bytes,
    records: seq<BenchWorld.Bytes>,
    terminated: seq<bool>,
    groups: seq<Group>,
    outputFragments: seq<BenchWorld.Bytes>,
    outputCuts: seq<nat>
  )
  {
    RecordPartitionRelation(data, records, terminated) &&
    RunPartitionRelation(command, records, groups) &&
    |outputFragments| == |groups| &&
    (forall i :: 0 <= i < |groups| ==>
                   GroupRenderRelation(command, groups[i], outputFragments[i])) &&
    FragmentsConcatenate(outputFragments, output, outputCuts)
  }

  ghost predicate OutputRelation(
    command: UniqSchema.UniqCmd,
    data: BenchWorld.Bytes,
    output: BenchWorld.Bytes
  )
  {
    exists records: seq<BenchWorld.Bytes>,
      terminated: seq<bool>,
      groups: seq<Group>,
      outputFragments: seq<BenchWorld.Bytes>,
      outputCuts: seq<nat> ::
      OutputWitnessRelation(
        command, data, output, records, terminated, groups,
        outputFragments, outputCuts
      )
  }

  twostate predicate InputTraceRelation(
    command: UniqSchema.UniqCmd,
    io: BenchIO.IO,
    new readResults: seq<BenchWorld.Result<BenchWorld.Bytes>>,
    new stdoutPart: BenchWorld.Bytes,
    new stderrPart: BenchWorld.Bytes,
    hadError: bool
  )
    reads io.Footprint()
  {
    |readResults| == 1 &&
    match command.input
    case Stdin =>
      readResults[0] == BenchWorld.Ok(old(io.stdin())) &&
      OutputRelation(command, old(io.stdin()), stdoutPart) &&
      stderrPart == [] &&
      !hadError
    case File(path) =>
      readResults[0] == IOContract.ReadFileResultFields(old(io.fs()), path) &&
      match readResults[0]
      case Ok(data) =>
        OutputRelation(command, data, stdoutPart) &&
        stderrPart == [] &&
        !hadError
      case Err(err) =>
        stdoutPart == [] &&
        stderrPart == ReadErrorMessageSpec(path, err) &&
        hadError
  }

  twostate predicate Spec(raw: UniqSchema.UniqCmdRaw, io: BenchIO.IO, exit: int)
    reads io.Footprint()
  {
    var cmd := Command(raw);
    match cmd.mode
    case ModeHelp =>
      io.stdin() == old(io.stdin()) &&
      io.stdout() == old(io.stdout()) + HelpTextSpec() &&
      io.stderr() == old(io.stderr()) &&
      exit == 0
    case ModeVersion =>
      io.stdin() == old(io.stdin()) &&
      io.stdout() == old(io.stdout()) + VersionTextSpec() &&
      io.stderr() == old(io.stderr()) &&
      exit == 0
    case ModeUnsupportedOutput(path) =>
      io.stdin() == old(io.stdin()) &&
      io.stdout() == old(io.stdout()) &&
      io.stderr() == old(io.stderr()) + UnsupportedOutputMessageSpec(path) &&
      exit == 1
    case ModeUnsupportedSkipChars(operand) =>
      io.stdin() == old(io.stdin()) &&
      io.stdout() == old(io.stdout()) &&
      io.stderr() == old(io.stderr()) + UnsupportedSkipCharsMessageSpec(operand) &&
      exit == 1
    case ModeExtraOperand(operand) =>
      io.stdin() == old(io.stdin()) &&
      io.stdout() == old(io.stdout()) &&
      io.stderr() == old(io.stderr()) + ExtraOperandMessageSpec(operand) &&
      exit == 1
    case ModeRun =>
      exists readResults: seq<BenchWorld.Result<BenchWorld.Bytes>>,
        stdoutPart: BenchWorld.Bytes,
        stderrPart: BenchWorld.Bytes,
        hadError: bool ::
        InputTraceRelation(
          cmd, io, readResults, stdoutPart, stderrPart, hadError
        ) &&
        io.stdin() ==
        (match cmd.input
         case Stdin => IOContract.AfterReadStdinFields(old(io.stdin()))
         case File(_) => old(io.stdin())) &&
        io.stdout() == old(io.stdout()) + stdoutPart &&
        io.stderr() == old(io.stderr()) + stderrPart &&
        exit == (if hadError then 1 else 0)
  }
}
