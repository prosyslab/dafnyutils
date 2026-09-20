include "../../core/World.dfy"
include "../../core/Utf8.dfy"
include "../../core/IO.dfy"
include "../../core/IOContract.dfy"
include "FoldSchema.dfy"

module FoldSpec {
  import BenchIO
  import BenchWorld
  import IOContract
  import BW = BenchWorld
  import Utf8 = Utf8Semantics
  import Schema = FoldSchema

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
    "Usage: fold [OPTION]... [FILE]...\n"
    + "Wrap input lines in each FILE, writing to standard output.\n"
    + "\n"
    + "With no FILE, or when FILE is -, read standard input.\n"
    + "  -b, --bytes         count bytes rather than columns\n"
    + "  -s, --spaces        break at spaces\n"
    + "  -w, --width=WIDTH   use WIDTH columns instead of 80\n"
    + "      --help          display this help and exit\n"
    + "      --version       output version information and exit\n"
    + "\n"
    + "Benchmark note: this slice models LC_ALL=C column wrapping.\n"
    + "Locale-sensitive multibyte display widths and combining characters are deferred.\n"
    + "\n"
    + "Full documentation <https://www.gnu.org/software/coreutils/fold>\n"
    + "or available locally via: info '(coreutils) fold invocation'\n"
  }

  function VersionText(): BenchWorld.Bytes
  {
    "fold (GNU coreutils) 9.10.13-2cf49\n"
    + "Copyright (C) 2026 Free Software Foundation, Inc.\n"
    + "License GPLv3+: GNU GPL version 3 or later <https://gnu.org/licenses/gpl.html>.\n"
    + "This is free software: you are free to change and redistribute it.\n"
    + "There is NO WARRANTY, to the extent permitted by law.\n"
    + "\n"
    + "Written by David MacKenzie.\n"
  }

  function InvalidWidthMessage(value: string): BenchWorld.Bytes
  {
    if AllDigits(value) then
      Utf8.Encode("fold: invalid number of columns: '" + value + "': Numerical result out of range\n")
    else
      Utf8.Encode("fold: invalid number of columns: '" + value + "'\n")
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
    "fold: " + SpecQuoteFBytes(Utf8.Encode(path)) +
    ": " + ErrnoText(err) + "\n"
  }

  function AllDigits(text: string): bool
    decreases |text|
  {
    |text| > 0 &&
    '0' <= text[0] <= '9' &&
    (|text| == 1 || AllDigits(text[1..]))
  }

  function IsDigit(ch: char): bool
  {
    '0' <= ch <= '9'
  }

  function DigitValue(ch: char): nat
    requires IsDigit(ch)
  {
    ((ch as int) - ('0' as int)) as nat
  }

  // Ghost counterpart of `AllDigits` above. `AllDigits` stays compilable and
  // non-empty because `InvalidWidthMessage` executes it; this one is the form a
  // recursion over prefixes can carry.
  ghost predicate EveryDigit(text: string)
  {
    forall k :: 0 <= k < |text| ==> IsDigit(text[k])
  }

  ghost function DecimalValue(digits: string): nat
    requires EveryDigit(digits)
    decreases |digits|
  {
    if |digits| == 0 then
      0
    else
      DecimalValue(digits[..|digits| - 1]) * 10 +
      DigitValue(digits[|digits| - 1])
  }

  ghost predicate PositiveNatRelation(
    text: string,
    result: Schema.NatParse
  )
  {
    if EveryDigit(text) && |text| > 0 && DecimalValue(text) != 0 then
      result == Schema.NatOk(DecimalValue(text))
    else
      result == Schema.NatErr
  }

  ghost predicate WidthArgsRelation(
    args: seq<Schema.WidthArg>,
    width: nat,
    result: Schema.WidthParse
  )
    requires width > 0
    decreases |args|
  {
    if |args| == 0 then
      result == Schema.WidthParse(false, "", -1, width)
    else
      exists parsed: Schema.NatParse ::
        PositiveNatRelation(args[0].text, parsed) &&
        match parsed
        case NatErr =>
          result == Schema.WidthParse(
            true, args[0].text, args[0].tokenIndex, width
          )
        case NatOk(nextWidth) =>
          if nextWidth == 0 then
            result == Schema.WidthParse(
              true, args[0].text, args[0].tokenIndex, width
            )
          else
            WidthArgsRelation(args[1..], nextWidth, result)
  }

  ghost predicate InputsRelation(
    operands: seq<string>,
    inputs: seq<Schema.Input>
  )
  {
    if |operands| == 0 then
      inputs == [Schema.Stdin]
    else
      |inputs| == |operands| &&
      forall i: nat :: i < |operands| ==>
                         inputs[i] ==
                         (if operands[i] == "-"
                          then Schema.Stdin
                          else Schema.File(operands[i]))
  }

  ghost predicate CommandRelation(
    raw: Schema.FoldCmdRaw,
    cmd: Schema.FoldCmd
  )
  {
    exists widthPlan: Schema.WidthParse ::
      WidthArgsRelation(raw.widthArgs, 80, widthPlan) &&
      if raw.seenHelp &&
         (!raw.seenVersion ||
          raw.helpTokenIndex <= raw.versionTokenIndex) &&
         (!widthPlan.hasInvalid ||
          raw.helpTokenIndex <= widthPlan.invalidTokenIndex) then
        cmd == Schema.FoldCmd(
          Schema.ModeHelp, 80, "", raw.byteMode, raw.spaceMode, []
        )
      else if raw.seenVersion &&
              (!widthPlan.hasInvalid ||
               raw.versionTokenIndex <= widthPlan.invalidTokenIndex) then
        cmd == Schema.FoldCmd(
          Schema.ModeVersion, 80, "", raw.byteMode, raw.spaceMode, []
        )
      else if widthPlan.hasInvalid then
        cmd == Schema.FoldCmd(
          Schema.ModeInvalidWidth,
          80,
          widthPlan.invalidText,
          raw.byteMode,
          raw.spaceMode,
          []
        )
      else
        exists inputs: seq<Schema.Input> ::
          InputsRelation(raw.operands, inputs) &&
          cmd == Schema.FoldCmd(
            Schema.ModeRun,
            widthPlan.width,
            "",
            raw.byteMode,
            raw.spaceMode,
            inputs
          )
  }

  function StepColumn(byteMode: bool, ch: char, column: nat): nat
  {
    if byteMode then
      column + 1
    else if ch == '\U{0}' then
      column
    else if ch == '\U{8}' then
      if column == 0 then 0 else column - 1
    else if ch == '\r' then
      0
    else if ch == '\t' then
      column + (8 - column % 8)
    else
      column + 1
  }

  // Formal specification gap: this relation intentionally models LC_ALL=C
  // column widths. Multibyte display widths and zero-width combining characters
  // are excluded; -b/--bytes switches to byte counts. The vendored GNU fold
  // scanner treats byte 0xff as end-of-input, so bytes after it are ignored.
  function JoinFragments(fragments: seq<BenchWorld.Bytes>): BenchWorld.Bytes
    decreases |fragments|
  {
    if |fragments| == 0 then [] else fragments[0] + JoinFragments(fragments[1..])
  }

  function RenderSegments(segments: seq<BenchWorld.Bytes>): BenchWorld.Bytes
    decreases |segments|
  {
    if |segments| == 0 then
      []
    else
      segments[0] +
      (if |segments| == 1 then [] else ['\n'] + RenderSegments(segments[1..]))
  }

  function RenderRecords(
    lineOutputs: seq<BenchWorld.Bytes>,
    terminated: seq<bool>
  ): BenchWorld.Bytes
    requires |lineOutputs| == |terminated|
    decreases |lineOutputs|
  {
    if |lineOutputs| == 0 then
      []
    else
      lineOutputs[0] + (if terminated[0] then ['\n'] else []) +
      RenderRecords(lineOutputs[1..], terminated[1..])
  }

  ghost predicate EffectivePrefixRelation(
    data: BenchWorld.Bytes,
    effective: BenchWorld.Bytes,
    end: nat
  )
  {
    end <= |data| &&
    effective == data[..end] &&
    '\U{FF}' !in data[..end] &&
    (end == |data| || data[end] == '\U{FF}')
  }

  ghost predicate RecordPartitionWitnessRelation(
    data: BenchWorld.Bytes,
    records: seq<BenchWorld.Bytes>,
    terminated: seq<bool>,
    fragments: seq<BenchWorld.Bytes>
  )
  {
    |records| == |terminated| == |fragments| &&
    (|data| == 0) == (|records| == 0) &&
    (forall i :: 0 <= i < |records| ==>
                   fragments[i] ==
                   records[i] + (if terminated[i] then ['\n'] else []) &&
                   '\n' !in records[i] &&
                   (i + 1 < |records| ==> terminated[i])) &&
    data == JoinFragments(fragments)
  }

  ghost predicate RecordPartitionRelation(
    data: BenchWorld.Bytes,
    records: seq<BenchWorld.Bytes>,
    terminated: seq<bool>
  )
  {
    exists fragments: seq<BenchWorld.Bytes> ::
      RecordPartitionWitnessRelation(data, records, terminated, fragments)
  }

  ghost predicate ColumnTraceRelation(
    byteMode: bool,
    data: BenchWorld.Bytes,
    initialColumn: nat,
    columns: seq<nat>
  )
  {
    |columns| == |data| + 1 &&
    columns[0] == initialColumn &&
    forall i :: 0 <= i < |data| ==>
                  columns[i + 1] == StepColumn(byteMode, data[i], columns[i])
  }

  ghost predicate FittingEndRelation(
    width: nat,
    byteMode: bool,
    line: BenchWorld.Bytes,
    start: nat,
    fitEnd: nat
  )
  {
    width > 0 &&
    start < fitEnd <= |line| &&
    exists columns: seq<nat> ::
      ColumnTraceRelation(byteMode, line[start..fitEnd], 0, columns) &&
      (forall i {:trigger columns[i + 1]} ::
         1 <= i < |line[start..fitEnd]| ==> columns[i + 1] <= width) &&
      (fitEnd == |line| ||
       StepColumn(byteMode, line[fitEnd], columns[|columns| - 1]) > width)
  }

  ghost predicate BreakPointRelation(
    width: nat,
    byteMode: bool,
    spaceMode: bool,
    line: BenchWorld.Bytes,
    start: nat,
    end: nat
  )
  {
    start < end <= |line| &&
    exists fitEnd: nat ::
      end <= fitEnd <= |line| &&
      FittingEndRelation(width, byteMode, line, start, fitEnd) &&
      if spaceMode && fitEnd < |line| &&
         exists j :: start <= j < fitEnd && IsBlank(line[j])
      then
        IsBlank(line[end - 1]) &&
        forall j :: start <= j < fitEnd && IsBlank(line[j]) ==> j < end
      else
        end == fitEnd
  }

  ghost predicate LinePartitionRelation(
    width: nat,
    byteMode: bool,
    spaceMode: bool,
    line: BenchWorld.Bytes,
    segments: seq<BenchWorld.Bytes>
  )
  {
    (|line| == 0) == (|segments| == 0) &&
    line == JoinFragments(segments) &&
    forall i :: 0 <= i < |segments| ==>
                  |segments[i]| > 0 &&
                  BreakPointRelation(
                    width,
                    byteMode,
                    spaceMode,
                    JoinFragments(segments[i..]),
                    0,
                    |segments[i]|
                  )
  }

  ghost predicate LineOutputRelation(
    width: nat,
    byteMode: bool,
    spaceMode: bool,
    line: BenchWorld.Bytes,
    output: BenchWorld.Bytes
  )
  {
    exists segments: seq<BenchWorld.Bytes> ::
      LinePartitionRelation(width, byteMode, spaceMode, line, segments) &&
      output == RenderSegments(segments)
  }

  ghost predicate DataFoldRelation(
    width: nat,
    byteMode: bool,
    spaceMode: bool,
    data: BenchWorld.Bytes,
    output: BenchWorld.Bytes
  )
  {
    exists effectiveEnd: nat,
      records: seq<BenchWorld.Bytes>, terminated: seq<bool>,
      lineOutputs: seq<BenchWorld.Bytes> ::
      effectiveEnd <= |data| &&
      EffectivePrefixRelation(data, data[..effectiveEnd], effectiveEnd) &&
      RecordPartitionRelation(data[..effectiveEnd], records, terminated) &&
      |lineOutputs| == |records| &&
      (forall i :: 0 <= i < |records| ==>
                     LineOutputRelation(width, byteMode, spaceMode, records[i], lineOutputs[i])) &&
      output == RenderRecords(lineOutputs, terminated)
  }

  ghost predicate HasEarlierStdin(cmd: Schema.FoldCmd, i: nat)
    requires i <= |cmd.inputs|
  {
    Schema.Stdin in cmd.inputs[..i]
  }

  ghost function ReadResultAt(
    cmd: Schema.FoldCmd,
    preFs: BenchWorld.FileSystem,
    preStdin: BenchWorld.Bytes,
    i: nat
  ): BenchWorld.Result<BenchWorld.Bytes>
    requires i < |cmd.inputs|
  {
    match cmd.inputs[i]
    case Stdin =>
      BenchWorld.Ok(if HasEarlierStdin(cmd, i) then [] else preStdin)
    case File(path) =>
      IOContract.ReadFileResultFields(preFs, path)
  }

  ghost predicate InputTraceRelation(
    cmd: Schema.FoldCmd,
    preFs: BenchWorld.FileSystem,
    preStdin: BenchWorld.Bytes,
    postStdin: BenchWorld.Bytes,
    stdoutPart: BenchWorld.Bytes,
    stderrPart: BenchWorld.Bytes,
    hadError: bool
  )
  {
    exists results: seq<BenchWorld.Result<BenchWorld.Bytes>>,
      stdoutFragments: seq<BenchWorld.Bytes>,
      stderrFragments: seq<BenchWorld.Bytes> ::
      InputPrefixTraceRelation(
        cmd,
        preFs,
        preStdin,
        |cmd.inputs|,
        postStdin,
        results,
        stdoutFragments,
        stderrFragments,
        hadError
      ) &&
      stdoutPart == JoinFragments(stdoutFragments) &&
      stderrPart == JoinFragments(stderrFragments)
  }

  ghost predicate InputPrefixTraceRelation(
    cmd: Schema.FoldCmd,
    preFs: BenchWorld.FileSystem,
    preStdin: BenchWorld.Bytes,
    count: nat,
    postStdin: BenchWorld.Bytes,
    results: seq<BenchWorld.Result<BenchWorld.Bytes>>,
    stdoutFragments: seq<BenchWorld.Bytes>,
    stderrFragments: seq<BenchWorld.Bytes>,
    hadError: bool
  )
  {
    count <= |cmd.inputs| &&
    |results| == |stdoutFragments| == |stderrFragments| == count &&
    (forall i :: 0 <= i < |results| ==>
                   results[i] == ReadResultAt(cmd, preFs, preStdin, i)) &&
    (forall i :: 0 <= i < |results| ==>
                   match results[i]
                   case Ok(data) =>
                     DataFoldRelation(
                       cmd.width, cmd.byteMode, cmd.spaceMode, data, stdoutFragments[i]
                     ) &&
                     stderrFragments[i] == []
                   case Err(err) =>
                     stdoutFragments[i] == [] &&
                     match cmd.inputs[i]
                     case Stdin => false
                     case File(path) => stderrFragments[i] == ErrorMessage(path, err)) &&
    postStdin == (if HasEarlierStdin(cmd, count) then [] else preStdin) &&
    hadError ==
    (exists i :: 0 <= i < |results| &&
                 match results[i]
                 case Ok(_) => false
                 case Err(_) => cmd.inputs[i].File?)
  }

  function IsBlank(ch: char): bool
  {
    ch == ' ' || ch == '\t'
  }

  twostate predicate Spec(raw: Schema.FoldCmdRaw, io: BenchIO.IO, exit: int)
    reads io.Footprint()
  {
    exists cmd: Schema.FoldCmd ::
      CommandRelation(raw, cmd) &&
      if cmd.mode == Schema.ModeHelp then
        io.stdin() == old(io.stdin()) &&
        io.stdout() == old(io.stdout()) + HelpText() &&
        io.stderr() == old(io.stderr()) &&
        exit == 0
      else if cmd.mode == Schema.ModeVersion then
        io.stdin() == old(io.stdin()) &&
        io.stdout() == old(io.stdout()) + VersionText() &&
        io.stderr() == old(io.stderr()) &&
        exit == 0
      else if cmd.mode == Schema.ModeInvalidWidth then
        io.stdin() == old(io.stdin()) &&
        io.stdout() == old(io.stdout()) &&
        io.stderr() ==
        old(io.stderr()) + InvalidWidthMessage(cmd.invalidWidthValue) &&
        exit == 1
      else
        exists stdoutPart: BenchWorld.Bytes,
          stderrPart: BenchWorld.Bytes,
          hadError: bool ::
          InputTraceRelation(
            cmd,
            old(io.fs()),
            old(io.stdin()),
            io.stdin(),
            stdoutPart,
            stderrPart,
            hadError
          ) &&
          io.stdout() == old(io.stdout()) + stdoutPart &&
          io.stderr() == old(io.stderr()) + stderrPart &&
          exit == (if hadError then 1 else 0)
  }
}
