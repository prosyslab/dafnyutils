include "../../core/World.dfy"
include "../../core/Utf8.dfy"
include "../../core/IO.dfy"
include "../../core/IOContract.dfy"
include "NlSchema.dfy"

module NlSpec {
  import BenchIO
  import BenchWorld
  import IOContract
  import BW = BenchWorld
  import Utf8 = Utf8Semantics
  import NlSchema




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

  function HelpText(): BenchWorld.Bytes
  {
    "Usage: nl [OPTION]... [FILE]...\n"
    + "Write each FILE to standard output, with line numbers added.\n"
    + "\n"
    + "With no FILE, or when FILE is -, read standard input.\n"
    + "  -b, --body-numbering=STYLE      use STYLE for numbering body lines\n"
    + "  -n, --number-format=FORMAT      insert line numbers according to FORMAT\n"
    + "  -s, --number-separator=STRING   add STRING after line numbers\n"
    + "      --help                      display this help and exit\n"
    + "      --version                   output version information and exit\n"
    + "\n"
    + "Supported benchmark STYLE values are a, t, and n.\n"
    + "Supported benchmark FORMAT values are ln, rn, and rz.\n"
  }

  function VersionText(): BenchWorld.Bytes
  {
    "nl (GNU coreutils) 9.10.13-2cf49\n"
    + "Copyright (C) 2026 Free Software Foundation, Inc.\n"
    + "License GPLv3+: GNU GPL version 3 or later <https://gnu.org/licenses/gpl.html>.\n"
    + "This is free software: you are free to change and redistribute it.\n"
    + "There is NO WARRANTY, to the extent permitted by law.\n"
    + "\n"
    + "Written by Scott Bartram and David MacKenzie.\n"
  }


  function InvalidBodyStyleMessage(value: string): BenchWorld.Bytes
  {
    "nl: invalid body numbering style: '" + Utf8.Encode(value) + "'\n" + NlSchema.TryHelp()
  }

  // Formal specification gap: pBRE body numbering is part of GNU nl, but this
  // relation intentionally excludes regex-based line selection until the
  // benchmark has a regex model.
  function UnsupportedRegexBodyStyleMessage(value: string): BenchWorld.Bytes
  {
    "nl: unsupported body numbering style in benchmark: '" + Utf8.Encode(value) + "'\n" + NlSchema.TryHelp()
  }

  function UnsupportedLogicalPageDelimiterMessage(): BenchWorld.Bytes
  {
    "nl: unsupported logical page delimiter in benchmark input\n" + NlSchema.TryHelp()
  }

  function InvalidNumberFormatMessage(value: string): BenchWorld.Bytes
  {
    "nl: invalid line numbering format: '" + Utf8.Encode(value) + "'\n" + NlSchema.TryHelp()
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

  function ErrorMessage(path: BenchWorld.Path, err: BenchWorld.IOError): BenchWorld.Bytes
  {
    "nl: " + SpecQuoteFBytes(Utf8.Encode(path)) +
    ": " + ErrnoText(err) + "\n"
  }

  ghost predicate NormalizedInputRelation(
    data: BenchWorld.Bytes,
    normalized: BenchWorld.Bytes
  )
  {
    normalized ==
    if |data| > 0 && data[|data| - 1] != '\n'
    then data + ['\n']
    else data
  }

  function IsLogicalPageDelimiterLine(line: BenchWorld.Bytes): bool
  {
    line == [(92 as char), ':'] ||
    line == [(92 as char), ':', (92 as char), ':'] ||
    line == [(92 as char), ':', (92 as char), ':', (92 as char), ':']
  }

  function ErrorPiece(input: NlSchema.Input, result: BenchWorld.Result<BenchWorld.Bytes>): BenchWorld.Bytes
  {
    match input
    case Stdin => []
    case File(path) =>
      match result
      case Ok(_) => []
      case Err(err) => ErrorMessage(path, err)
  }

  function HadErrorPiece(input: NlSchema.Input, result: BenchWorld.Result<BenchWorld.Bytes>): bool
  {
    match input
    case Stdin => false
    case File(_) =>
      match result
      case Ok(_) => false
      case Err(_) => true
  }

  function RepeatChar(ch: BenchWorld.RawByte, count: int): BenchWorld.Bytes
    decreases count
  {
    if count <= 0 then [] else [ch] + RepeatChar(ch, count - 1)
  }

  function DigitChar(d: int): char
  {
    if 0 <= d < 10 then
      (d + ('0' as int)) as char
    else
      '0'
  }

  function Digits(n: int): BenchWorld.Bytes
    requires 0 <= n
    decreases n
  {
    if n < 10 then
      [DigitChar(n)]
    else
      Digits(n / 10) + [DigitChar(n % 10)]
  }

  function RenderNumber(format: NlSchema.NumberFormat, n: int, width: int): BenchWorld.Bytes
    requires 0 <= n
  {
    var digits := Digits(n);
    if format == NlSchema.FormatLeft then
      digits + RepeatChar(' ', width - |digits|)
    else if format == NlSchema.FormatRightZero then
      RepeatChar('0', width - |digits|) + digits
    else
      RepeatChar(' ', width - |digits|) + digits
  }

  function ShouldNumber(style: NlSchema.BodyStyle, nonempty: bool): bool
  {
    style == NlSchema.NumberAll || (style == NlSchema.NumberNonEmpty && nonempty)
  }

  function LineNumberText(cmd: NlSchema.NlCmd, n: int): BenchWorld.Bytes
    requires 0 <= n
  {
    RenderNumber(cmd.numberFormat, n, 6) + cmd.separator
  }

  function BlankPrefix(cmd: NlSchema.NlCmd): BenchWorld.Bytes
  {
    RepeatChar(' ', 6 + |cmd.separator|)
  }

  function LinePrefix(cmd: NlSchema.NlCmd, nonempty: bool, n: int): BenchWorld.Bytes
    requires 0 <= n
  {
    if ShouldNumber(cmd.bodyStyle, nonempty) then
      LineNumberText(cmd, n)
    else
      BlankPrefix(cmd)
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

  ghost predicate LinePartitionRelation(
    data: BenchWorld.Bytes,
    lines: seq<BenchWorld.Bytes>,
    terminated: seq<bool>,
    fragments: seq<BenchWorld.Bytes>,
    cuts: seq<nat>
  )
  {
    |lines| == |terminated| == |fragments| &&
    (|data| == 0) == (|lines| == 0) &&
    (forall i :: 0 <= i < |lines| ==>
                   |fragments[i]| > 0 &&
                   fragments[i] == lines[i] + (if terminated[i] then ['\n'] else []) &&
                   '\n' !in lines[i] &&
                   (i + 1 < |lines| ==> terminated[i])) &&
    FragmentsConcatenate(fragments, data, cuts)
  }

  ghost predicate LineNumberFromRelation(
    cmd: NlSchema.NlCmd,
    lines: seq<BenchWorld.Bytes>,
    start: nat,
    numbers: seq<nat>
  )
  {
    |numbers| == |lines| + 1 &&
    numbers[0] == start &&
    forall i {:trigger numbers[i]} :: 0 <= i < |lines| ==>
                                        numbers[i + 1] == numbers[i] +
                                        (if ShouldNumber(cmd.bodyStyle, |lines[i]| > 0) then 1 else 0)
  }

  ghost predicate LineNumberRelation(
    cmd: NlSchema.NlCmd,
    lines: seq<BenchWorld.Bytes>,
    numbers: seq<nat>
  )
  {
    LineNumberFromRelation(cmd, lines, 1, numbers)
  }

  ghost predicate LineRenderRelation(
    cmd: NlSchema.NlCmd,
    line: BenchWorld.Bytes,
    terminated: bool,
    number: nat,
    outputFragment: BenchWorld.Bytes
  )
  {
    outputFragment ==
    LinePrefix(cmd, |line| > 0, number as int) + line +
    (if terminated then ['\n'] else [])
  }

  ghost predicate OutputWitnessRelation(
    cmd: NlSchema.NlCmd,
    data: BenchWorld.Bytes,
    output: BenchWorld.Bytes,
    lines: seq<BenchWorld.Bytes>,
    terminated: seq<bool>,
    lineFragments: seq<BenchWorld.Bytes>,
    lineCuts: seq<nat>,
    numbers: seq<nat>,
    outputFragments: seq<BenchWorld.Bytes>,
    outputCuts: seq<nat>
  )
  {
    LinePartitionRelation(data, lines, terminated, lineFragments, lineCuts) &&
    LineNumberRelation(cmd, lines, numbers) &&
    |outputFragments| == |lines| &&
    (forall i :: 0 <= i < |lines| ==>
                   LineRenderRelation(
                     cmd, lines[i], terminated[i], numbers[i], outputFragments[i]
                   )) &&
    FragmentsConcatenate(outputFragments, output, outputCuts)
  }

  ghost predicate OutputRelation(
    cmd: NlSchema.NlCmd,
    data: BenchWorld.Bytes,
    output: BenchWorld.Bytes
  )
  {
    exists lines: seq<BenchWorld.Bytes>,
      terminated: seq<bool>,
      lineFragments: seq<BenchWorld.Bytes>,
      lineCuts: seq<nat>,
      numbers: seq<nat>,
      outputFragments: seq<BenchWorld.Bytes>,
      outputCuts: seq<nat> ::
      OutputWitnessRelation(
        cmd, data, output, lines, terminated, lineFragments, lineCuts, numbers,
        outputFragments, outputCuts
      )
  }

  ghost predicate ReadResultRelation(
    cmd: NlSchema.NlCmd,
    preFs: BenchWorld.FileSystem,
    preStdin: BenchWorld.Bytes,
    i: nat,
    result: BenchWorld.Result<BenchWorld.Bytes>
  )
    requires i < |cmd.inputs|
  {
    match cmd.inputs[i]
    case Stdin =>
      result == BenchWorld.Ok(
        if exists j :: 0 <= j < i && cmd.inputs[j] == NlSchema.Stdin
        then []
        else preStdin
      )
    case File(path) =>
      result == IOContract.ReadFileResultFields(preFs, path)
  }

  ghost predicate InputTraceRelation(
    cmd: NlSchema.NlCmd,
    preFs: BenchWorld.FileSystem,
    preStdin: BenchWorld.Bytes,
    readResults: seq<BenchWorld.Result<BenchWorld.Bytes>>,
    inputFragments: seq<BenchWorld.Bytes>,
    combined: BenchWorld.Bytes,
    inputCuts: seq<nat>,
    errorFragments: seq<BenchWorld.Bytes>,
    errorOutput: BenchWorld.Bytes,
    errorCuts: seq<nat>,
    hadError: bool,
    hasDelimiter: bool
  )
  {
    |readResults| == |cmd.inputs| &&
    |inputFragments| == |cmd.inputs| &&
    |errorFragments| == |cmd.inputs| &&
    (forall i :: 0 <= i < |cmd.inputs| ==>
                   ReadResultRelation(cmd, preFs, preStdin, i, readResults[i]) &&
                   (match readResults[i]
                    case Ok(data) =>
                      NormalizedInputRelation(data, inputFragments[i])
                    case Err(_) =>
                      inputFragments[i] == []) &&
                   errorFragments[i] == ErrorPiece(cmd.inputs[i], readResults[i])) &&
    FragmentsConcatenate(inputFragments, combined, inputCuts) &&
    FragmentsConcatenate(errorFragments, errorOutput, errorCuts) &&
    hadError ==
    (exists i :: 0 <= i < |cmd.inputs| &&
                 HadErrorPiece(cmd.inputs[i], readResults[i])) &&
    (exists lines: seq<BenchWorld.Bytes>,
       terminated: seq<bool>,
       fragments: seq<BenchWorld.Bytes>,
       cuts: seq<nat> ::
       LinePartitionRelation(combined, lines, terminated, fragments, cuts) &&
       hasDelimiter ==
       (exists i :: 0 <= i < |lines| &&
                    IsLogicalPageDelimiterLine(lines[i])))
  }

  function ModeErrorMessage(mode: NlSchema.NlMode): BenchWorld.Bytes
  {
    match mode
    case ModeInvalidBodyStyle(value) => InvalidBodyStyleMessage(value)
    case ModeUnsupportedRegexBodyStyle(value) => UnsupportedRegexBodyStyleMessage(value)
    case ModeInvalidNumberFormat(value) => InvalidNumberFormatMessage(value)
    case _ => []
  }

  twostate predicate Spec(raw: NlSchema.NlCmdRaw, io: BenchIO.IO, exit: int)
    reads io.fsRegion, io.stdinRegion, io.stdoutRegion, io.stderrRegion
  {
    var cmd := NlSchema.Command(raw);
    if cmd.mode == NlSchema.ModeHelp then
      io.stdin() == old(io.stdin()) &&
      io.stdout() == old(io.stdout()) + HelpText() &&
      io.stderr() == old(io.stderr()) &&
      exit == 0
    else if cmd.mode == NlSchema.ModeVersion then
      io.stdin() == old(io.stdin()) &&
      io.stdout() == old(io.stdout()) + VersionText() &&
      io.stderr() == old(io.stderr()) &&
      exit == 0
    else if cmd.mode != NlSchema.ModeRun then
      io.stdin() == old(io.stdin()) &&
      io.stdout() == old(io.stdout()) &&
      io.stderr() == old(io.stderr()) + ModeErrorMessage(cmd.mode) &&
      exit == 1
    else
      exists readResults: seq<BenchWorld.Result<BenchWorld.Bytes>>,
        inputFragments: seq<BenchWorld.Bytes>,
        combined: BenchWorld.Bytes,
        inputCuts: seq<nat>,
        errorFragments: seq<BenchWorld.Bytes>,
        errorOutput: BenchWorld.Bytes,
        errorCuts: seq<nat>,
        hadError: bool,
        hasDelimiter: bool,
        outputPart: BenchWorld.Bytes ::
        InputTraceRelation(
          cmd, old(io.fs()), old(io.stdin()), readResults, inputFragments,
          combined, inputCuts, errorFragments, errorOutput, errorCuts,
          hadError, hasDelimiter
        ) &&
        io.stdin() ==
        (if exists i ::
              (0 <= i < |cmd.inputs| &&
               cmd.inputs[i] == NlSchema.Stdin)
         then []
         else old(io.stdin())) &&
        (if hasDelimiter then
           outputPart == []
         else
           OutputRelation(cmd, combined, outputPart)) &&
        io.stdout() == old(io.stdout()) + outputPart &&
        io.stderr() == old(io.stderr()) + errorOutput +
        (if hasDelimiter then
           UnsupportedLogicalPageDelimiterMessage()
         else
           []) &&
        exit == (if hasDelimiter || hadError then 1 else 0)
  }
}
