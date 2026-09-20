include "../../core/World.dfy"
include "../../core/IO.dfy"
include "../../core/IOContract.dfy"
include "ExpandSchema.dfy"

module ExpandSpec {
  import BenchIO
  import BenchWorld
  import IOContract
  import Schema = ExpandSchema

  function HelpText(): BenchWorld.Bytes
  {
    "Usage: expand [OPTION]... [FILE]...\n"
    + "Convert tabs in each FILE to spaces, writing to standard output.\n"
    + "\n"
    + "With no FILE, or when FILE is -, read standard input.\n"
    + "  -i, --initial         convert only leading tabs on each line\n"
    + "  -t, --tabs=LIST       use tab positions, +N increments, or /N repeats\n"
    + "      --help            display this help and exit\n"
    + "      --version         output version information and exit\n"
    + "\n"
    + "Benchmark note: columns are byte columns in LC_ALL=C. Locale-sensitive\n"
    + "multibyte display width is outside this benchmark slice.\n"
    + "\n"
    + "Full documentation <https://www.gnu.org/software/coreutils/expand>\n"
    + "or available locally via: info '(coreutils) expand invocation'\n"
  }

  function VersionText(): BenchWorld.Bytes
  {
    "expand (GNU coreutils) 9.10.13-2cf49\n"
    + "Copyright (C) 2026 Free Software Foundation, Inc.\n"
    + "License GPLv3+: GNU GPL version 3 or later <https://gnu.org/licenses/gpl.html>.\n"
    + "This is free software: you are free to change and redistribute it.\n"
    + "There is NO WARRANTY, to the extent permitted by law.\n"
    + "\n"
    + "Written by David MacKenzie.\n"
  }




  function InvalidTabsMessage(value: string): BenchWorld.Bytes
  {
    "expand: " + value + "\n"
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

  function NeedsQuoting(path: BenchWorld.Path): bool
    decreases |path|
  {
    |path| > 0 && (path[0] == ' ' || path[0] == ':' || path[0] == '=' || NeedsQuoting(path[1..]))
  }

  function DisplayPath(path: BenchWorld.Path): string
  {
    if NeedsQuoting(path) then "'" + path + "'" else path
  }

  function ErrorMessage(path: BenchWorld.Path, err: BenchWorld.IOError): BenchWorld.Bytes
  {
    "expand: " + DisplayPath(path) + ": " + ErrnoText(err) + "\n"
  }

  function IsDigit(ch: char): bool
  {
    '0' <= ch <= '9'
  }

  function MaxColumn(): nat
  {
    9223372036854775807
  }

  function DigitValue(ch: char): nat
    requires IsDigit(ch)
  {
    ((ch as int) - ('0' as int)) as nat
  }

  function FindDigitsEnd(text: string, start: nat): nat
    requires start <= |text|
    ensures start <= FindDigitsEnd(text, start) <= |text|
    decreases |text| - start
  {
    if start == |text| || !IsDigit(text[start]) then
      start
    else
      FindDigitsEnd(text, start + 1)
  }

  function IsSeparator(ch: char): bool
  {
    ch == ',' || ch == ' ' || ch == '\t'
  }

  function IsMarker(ch: char): bool
  {
    ch == '+' || ch == '/'
  }

  function MarkerText(marker: Schema.MarkerKind): string
  {
    if marker == Schema.MarkerPlus then "+" else "/"
  }

  function OctalDigit(value: int): char
    requires 0 <= value < 8
  {
    (('0' as int) + value) as char
  }

  function OctalEscape(ch: char): string
  {
    var value := ch as int;
    ['\\', OctalDigit((value / 64) % 8),
     OctalDigit((value / 8) % 8), OctalDigit(value % 8)]
  }

  function QuoteChar(ch: char): string
  {
    if ch == 7 as char then "\\a"
    else if ch == 8 as char then "\\b"
    else if ch == 12 as char then "\\f"
    else if ch == '\n' then "\\n"
    else if ch == '\r' then "\\r"
    else if ch == '\t' then "\\t"
    else if ch == 11 as char then "\\v"
    else if ch == '\\' then "\\\\"
    else if ch == '\'' then "\\'"
    else if 32 <= ch as int < 127 then [ch]
    else OctalEscape(ch)
  }

  function QuoteBody(value: string): string
    decreases |value|
  {
    if |value| == 0 then ""
    else QuoteChar(value[0]) + QuoteBody(value[1..])
  }

  function Quote(value: string): string
  {
    "'" + QuoteBody(value) + "'"
  }

  function InvalidCharacterMessage(suffix: string): string
  {
    "tab size contains invalid character(s): " + Quote(suffix)
  }

  function MarkerNotAtStartMessage(
    marker: Schema.MarkerKind, suffix: string
  ): string
  {
    Quote(MarkerText(marker)) +
    " specifier not at start of number: " + Quote(suffix)
  }

  function TooLargeMessage(digits: string): string
  {
    "tab stop is too large " + Quote(digits)
  }

  function CombineDiagnostics(first: string, rest: string): string
  {
    if rest == "" then first else first + "\nexpand: " + rest
  }

  function SyntaxDiagnosticsFrom(
    text: string,
    i: nat,
    haveValue: bool,
    numberStart: nat,
    value: nat
  ): string
    requires i <= |text|
    requires !haveValue || numberStart <= i
    decreases |text| - i
  {
    if i == |text| then
      ""
    else if IsSeparator(text[i]) then
      SyntaxDiagnosticsFrom(text, i + 1, false, 0, 0)
    else if IsMarker(text[i]) then
      var rest := SyntaxDiagnosticsFrom(
                    text, i + 1, haveValue, numberStart, value
                  );
      if haveValue then
        CombineDiagnostics(
          MarkerNotAtStartMessage(MarkerOf(text[i]), text[i..]),
          rest
        )
      else
        rest
    else if IsDigit(text[i]) then
      var start := if haveValue then numberStart else i;
      var accumulated := if haveValue then value else 0;
      var digit := DigitValue(text[i]);
      if accumulated > (MaxColumn() - digit) / 10 then
        var end := FindDigitsEnd(text, i);
        CombineDiagnostics(
          TooLargeMessage(text[start..end]),
          SyntaxDiagnosticsFrom(
            text, end, true, start, accumulated
          )
        )
      else
        SyntaxDiagnosticsFrom(
          text, i + 1, true, start,
          accumulated * 10 + digit
        )
    else
      InvalidCharacterMessage(text[i..])
  }

  function SyntaxDiagnostics(text: string): string
  {
    SyntaxDiagnosticsFrom(text, 0, false, 0, 0)
  }

  function RepeatOnlyLastMessage(marker: Schema.MarkerKind): string
  {
    Quote(MarkerText(marker)) +
    " specifier only allowed with the last value"
  }

  function AscendingTabsMessage(): string
  {
    "tab sizes must be ascending"
  }

  function ZeroTabMessage(): string
  {
    "tab size cannot be 0"
  }

  function MixedRepeatMessage(): string
  {
    "'/' specifier is mutually exclusive with '+'"
  }

  function MarkerOf(ch: char): Schema.MarkerKind
    requires IsMarker(ch)
  {
    if ch == '+' then Schema.MarkerPlus else Schema.MarkerSlash
  }

  function LastStop(stops: seq<nat>): nat
    requires |stops| > 0
  {
    stops[|stops| - 1]
  }

  function HelpBeforeOther(raw: Schema.ExpandCmdRaw): bool
  {
    raw.seenHelp &&
    (!raw.seenVersion || raw.helpTokenIndex <= raw.versionTokenIndex)
  }

  function VersionBeforeInvalid(raw: Schema.ExpandCmdRaw): bool
  {
    raw.seenVersion &&
    (!raw.seenHelp || raw.versionTokenIndex < raw.helpTokenIndex)
  }

  function RequestTokenIndex(raw: Schema.ExpandCmdRaw): int
  {
    if HelpBeforeOther(raw) then raw.helpTokenIndex
    else if VersionBeforeInvalid(raw) then raw.versionTokenIndex
    else -1
  }

  ghost predicate NatParseRelation(
    text: string,
    i: nat,
    acc: nat,
    result: Schema.NatParse
  )
    requires i <= |text|
    decreases |text| - i
  {
    if i == |text| then
      result == Schema.NatOk(acc)
    else if !IsDigit(text[i]) then
      result == Schema.NatErr
    else if acc > (MaxColumn() - DigitValue(text[i])) / 10 then
      result == Schema.NatErr
    else
      NatParseRelation(
        text,
        i + 1,
        acc * 10 + DigitValue(text[i]),
        result
      )
  }

  ghost predicate PositiveNatRelation(
    text: string, result: Schema.NatParse
  )
  {
    if |text| == 0 then
      result == Schema.NatErr
    else
      NatParseRelation(text, 0, 0, result)
  }

  ghost predicate TokenEndRelation(
    text: string, start: nat, end: nat
  )
    requires start <= |text|
    decreases |text| - start
  {
    if start == |text| || IsSeparator(text[start]) then
      end == start
    else
      TokenEndRelation(text, start + 1, end)
  }

  ghost predicate DigitsEndRelation(
    text: string, start: nat, end: nat
  )
    requires start <= |text|
    decreases |text| - start
  {
    if start == |text| || !IsDigit(text[start]) then
      end == start
    else
      DigitsEndRelation(text, start + 1, end)
  }

  ghost predicate MarkerScanRelation(
    part: string,
    i: nat,
    marker: Schema.MarkerKind,
    hasMarker: bool,
    result: Schema.MarkerScan
  )
    requires i <= |part|
    decreases |part| - i
  {
    if i == |part| || !IsMarker(part[i]) then
      result == Schema.MarkerScan(i, marker, hasMarker)
    else
      MarkerScanRelation(
        part, i + 1, MarkerOf(part[i]), true, result
      )
  }

  ghost predicate CommitTabValueRelation(
    acc: Schema.TabAccum,
    marker: Schema.MarkerKind,
    value: nat,
    result: Schema.TabAccumParse
  )
  {
    if marker == Schema.MarkerSlash then
      if acc.extendSize != 0 then
        result == Schema.TabAccumErr(
          RepeatOnlyLastMessage(Schema.MarkerSlash)
        )
      else
        result == Schema.TabAccumOk(Schema.TabAccum(
                                      acc.stops, value, acc.incrementSize, marker
                                    ))
    else if marker == Schema.MarkerPlus then
      if acc.incrementSize != 0 then
        result == Schema.TabAccumErr(
          RepeatOnlyLastMessage(Schema.MarkerPlus)
        )
      else
        result == Schema.TabAccumOk(Schema.TabAccum(
                                      acc.stops, acc.extendSize, value, marker
                                    ))
    else
      result == Schema.TabAccumOk(Schema.TabAccum(
                                    acc.stops + [value], acc.extendSize,
                                    acc.incrementSize, marker
                                  ))
  }

  ghost predicate TabPartRelation(
    part: string,
    acc: Schema.TabAccum,
    result: Schema.TabAccumParse
  )
  {
    if |part| == 0 then
      result == Schema.TabAccumOk(acc)
    else
      exists scan: Schema.MarkerScan ::
        scan.index <= |part| &&
        MarkerScanRelation(
          part, 0, Schema.MarkerNone, false, scan
        ) &&
        var marker := if scan.hasMarker then scan.marker else acc.activeMarker;
        if scan.index == |part| then
          result == Schema.TabAccumOk(Schema.TabAccum(
                                        acc.stops, acc.extendSize, acc.incrementSize, marker
                                      ))
        else
          exists end: nat ::
            scan.index <= end <= |part| &&
            DigitsEndRelation(part, scan.index, end) &&
            if end < |part| then
              result == Schema.TabAccumErr(
                if IsMarker(part[end]) then
                  MarkerNotAtStartMessage(
                    MarkerOf(part[end]), part[end..]
                  )
                else
                  InvalidCharacterMessage(part[end..])
              )
            else
              var digits := part[scan.index..end];
              exists parsed: Schema.NatParse ::
                PositiveNatRelation(digits, parsed) &&
                match parsed
                case NatErr =>
                  result == Schema.TabAccumErr(
                    TooLargeMessage(digits)
                  )
                case NatOk(value) =>
                  CommitTabValueRelation(acc, marker, value, result)
  }

  ghost predicate TabTextRelation(
    text: string,
    start: nat,
    acc: Schema.TabAccum,
    result: Schema.TabAccumParse
  )
    requires start <= |text|
    decreases |text| - start
  {
    if start == |text| then
      result == Schema.TabAccumOk(acc)
    else if IsSeparator(text[start]) then
      TabTextRelation(text, start + 1, acc, result)
    else
      exists end: nat, partResult: Schema.TabAccumParse ::
        start < end <= |text| &&
        TokenEndRelation(text, start, end) &&
        TabPartRelation(text[start..end], acc, partResult) &&
        match partResult
        case TabAccumErr(value) =>
          result == Schema.TabAccumErr(value)
        case TabAccumOk(next) =>
          TabTextRelation(text, end, next, result)
  }

  ghost predicate TabArgsFromRelation(
    args: seq<Schema.TabArg>,
    i: nat,
    limit: int,
    acc: Schema.TabAccum,
    result: Schema.TabAccumParse
  )
    requires i <= |args|
    decreases |args| - i
  {
    if i == |args| ||
       (limit >= 0 && args[i].tokenIndex >= limit) then
      result == Schema.TabAccumOk(acc)
    else
      var argAcc := Schema.TabAccum(
                      acc.stops,
                      acc.extendSize,
                      acc.incrementSize,
                      Schema.MarkerNone
                    );
      var diagnostics := SyntaxDiagnostics(args[i].text);
      if diagnostics != "" then
        result == Schema.TabAccumErr(diagnostics)
      else
        exists parsed: Schema.TabAccumParse ::
          TabTextRelation(args[i].text, 0, argAcc, parsed) &&
          match parsed
          case TabAccumErr(value) =>
            result == Schema.TabAccumErr(value)
          case TabAccumOk(next) =>
            TabArgsFromRelation(args, i + 1, limit, next, result)
  }

  ghost predicate FinalizedTabsRelation(
    acc: Schema.TabAccum, result: Schema.TabParse
  )
  {
    var validationError := StopsValidationError(acc.stops, 0, 0);
    if validationError != "" then
      result == Schema.TabErr(validationError)
    else if acc.incrementSize != 0 && acc.extendSize != 0 then
      result == Schema.TabErr(MixedRepeatMessage())
    else if |acc.stops| == 0 then
      result == Schema.TabOk(Schema.TabStops(
                               [],
                               Schema.RepeatFixed(
                                 if acc.extendSize != 0 then acc.extendSize
                                 else if acc.incrementSize != 0 then acc.incrementSize
                                 else 8
                               )
                             ))
    else if |acc.stops| == 1 &&
            acc.extendSize == 0 && acc.incrementSize == 0 then
      result == Schema.TabOk(Schema.TabStops(
                               [], Schema.RepeatFixed(acc.stops[0])
                             ))
    else
      result == Schema.TabOk(Schema.TabStops(
                               acc.stops,
                               if acc.extendSize != 0 then
                                 Schema.RepeatFixed(acc.extendSize)
                               else if acc.incrementSize != 0 then
                                 Schema.RepeatIncremental(acc.incrementSize)
                               else
                                 Schema.RepeatNone
                             ))
  }

  function StopsValidationError(
    stops: seq<nat>, i: nat, previous: nat
  ): string
    requires i <= |stops|
    decreases |stops| - i
  {
    if i == |stops| then ""
    else if stops[i] == 0 then ZeroTabMessage()
    else if stops[i] <= previous then AscendingTabsMessage()
    else StopsValidationError(stops, i + 1, stops[i])
  }

  ghost predicate OptionScanRelation(
    raw: Schema.ExpandCmdRaw, scan: Schema.OptionScan
  )
  {
    var initial := Schema.TabAccum([], 0, 0, Schema.MarkerNone);
    exists parsed: Schema.TabAccumParse ::
      TabArgsFromRelation(
        raw.tabArgs, 0, RequestTokenIndex(raw), initial, parsed
      ) &&
      match parsed
      case TabAccumErr(value) =>
        scan == Schema.ScanInvalidTabs(value)
      case TabAccumOk(acc) =>
        if HelpBeforeOther(raw) then
          scan == Schema.ScanHelp
        else if VersionBeforeInvalid(raw) then
          scan == Schema.ScanVersion
        else
          scan == Schema.ScanContinue(acc)
  }

  ghost predicate InputsRelation(
    operands: seq<string>, inputs: seq<Schema.Input>
  )
  {
    if |operands| == 0 then
      inputs == [Schema.Stdin]
    else
      inputs == seq(|operands|, i requires 0 <= i < |operands| =>
        if operands[i] == "-" then Schema.Stdin else Schema.File(operands[i]))
  }

  ghost predicate CommandRelation(
    raw: Schema.ExpandCmdRaw, cmd: Schema.ExpandCmd
  )
  {
    exists scan: Schema.OptionScan ::
      OptionScanRelation(raw, scan) &&
      match scan
      case ScanInvalidTabs(value) =>
        cmd == Schema.ExpandCmd(
          Schema.ModeInvalidTabs,
          Schema.TabStops([], Schema.RepeatFixed(8)),
          false,
          value,
          []
        )
      case ScanHelp =>
        cmd == Schema.ExpandCmd(
          Schema.ModeHelp,
          Schema.TabStops([], Schema.RepeatFixed(8)),
          false,
          "",
          []
        )
      case ScanVersion =>
        cmd == Schema.ExpandCmd(
          Schema.ModeVersion,
          Schema.TabStops([], Schema.RepeatFixed(8)),
          false,
          "",
          []
        )
      case ScanContinue(acc) =>
        exists parsed: Schema.TabParse ::
          FinalizedTabsRelation(acc, parsed) &&
          match parsed
          case TabErr(value) =>
            cmd == Schema.ExpandCmd(
              Schema.ModeInvalidTabs,
              Schema.TabStops([], Schema.RepeatFixed(8)),
              false,
              value,
              []
            )
          case TabOk(tabs) =>
            exists inputs: seq<Schema.Input> ::
              InputsRelation(raw.operands, inputs) &&
              cmd == Schema.ExpandCmd(
                Schema.ModeRun,
                tabs,
                raw.seenInitial,
                "",
                inputs
              )
  }

  function JoinPieces(pieces: seq<BenchWorld.Bytes>): BenchWorld.Bytes
    decreases |pieces|
  {
    if |pieces| == 0 then [] else pieces[0] + JoinPieces(pieces[1..])
  }

  ghost predicate FixedWidthRelation(width: nat, column: nat, spaces: nat)
  {
    if width == 0 then
      spaces == 1
    else
      spaces == (if column % width == 0 then width else width - column % width)
  }

  ghost predicate IncrementalWidthRelation(base: nat, width: nat, column: nat, spaces: nat)
  {
    if width == 0 then
      spaces == 1
    else if column < base then
      spaces == base - column
    else
      spaces ==
      (if (column - base) % width == 0
       then width
       else width - (column - base) % width)
  }

  ghost predicate TabStopRelation(tabs: Schema.TabStops, column: nat, spaces: nat)
  {
    match tabs
    case TabStops(stops, repeat) =>
      (exists j: nat ::
         j < |stops| &&
         (forall k: nat :: k < j ==> stops[k] <= column) &&
         column < stops[j] &&
         spaces == stops[j] - column) ||
      ((forall j: nat :: j < |stops| ==> stops[j] <= column) &&
       match repeat
       case RepeatNone => spaces == 1
       case RepeatFixed(width) => FixedWidthRelation(width, column, spaces)
       case RepeatIncremental(width) =>
         if |stops| == 0 then
           FixedWidthRelation(width, column, spaces)
         else
           IncrementalWidthRelation(LastStop(stops), width, column, spaces))
  }

  ghost predicate SpacePiece(piece: BenchWorld.Bytes, count: nat)
  {
    piece == seq(count, _ => ' ')
  }

  // Formal specification gap: columns are LC_ALL=C byte columns.
  // Locale-sensitive multibyte display widths remain outside this slice.
  ghost predicate ByteExpansionRelation(
    tabs: Schema.TabStops,
    initialOnly: bool,
    b: BenchWorld.RawByte,
    column: nat,
    leading: bool,
    piece: BenchWorld.Bytes,
    nextColumn: nat,
    nextLeading: bool
  )
  {
    if initialOnly && !leading then
      piece == [b] &&
      (if b == '\n' then
         nextColumn == 0 && nextLeading
       else
         nextColumn == column && !nextLeading)
    else if b == '\t' then
      exists spaces: nat ::
        TabStopRelation(tabs, column, spaces) &&
        nextColumn == column + spaces &&
        nextLeading == leading &&
        SpacePiece(piece, spaces)
    else if b == '\n' then
      piece == ['\n'] && nextColumn == 0 && nextLeading
    else if b == (8 as char) then
      piece == [(8 as char)] &&
      nextColumn == (if column == 0 then 0 else column - 1) &&
      !nextLeading
    else
      piece == [b] &&
      nextColumn == column + 1 &&
      nextLeading == (leading && b == ' ')
  }

  ghost predicate DataExpansionWitnessRelation(
    tabs: Schema.TabStops,
    initialOnly: bool,
    data: BenchWorld.Bytes,
    column: nat,
    leading: bool,
    output: BenchWorld.Bytes,
    nextColumn: nat,
    nextLeading: bool,
    pieces: seq<BenchWorld.Bytes>,
    columns: seq<nat>,
    leadings: seq<bool>
  )
  {
    |pieces| == |data| &&
    |columns| == |data| + 1 &&
    |leadings| == |data| + 1 &&
    columns[0] == column &&
    leadings[0] == leading &&
    columns[|data|] == nextColumn &&
    leadings[|data|] == nextLeading &&
    (forall i: nat :: i < |data| ==>
                        ByteExpansionRelation(
                          tabs, initialOnly, data[i], columns[i], leadings[i],
                          pieces[i], columns[i + 1], leadings[i + 1]
                        )) &&
    output == JoinPieces(pieces)
  }

  ghost predicate DataExpansionRelation(
    tabs: Schema.TabStops,
    initialOnly: bool,
    data: BenchWorld.Bytes,
    column: nat,
    leading: bool,
    output: BenchWorld.Bytes,
    nextColumn: nat,
    nextLeading: bool
  )
  {
    exists pieces: seq<BenchWorld.Bytes>, columns: seq<nat>, leadings: seq<bool> ::
      DataExpansionWitnessRelation(
        tabs, initialOnly, data, column, leading, output,
        nextColumn, nextLeading, pieces, columns, leadings
      )
  }

  ghost predicate ReadStepRelation(
    input: Schema.Input,
    preFs: BenchWorld.FileSystem,
    stdinBefore: BenchWorld.Bytes,
    stdinAfter: BenchWorld.Bytes,
    result: BenchWorld.Result<BenchWorld.Bytes>
  )
  {
    match input
    case Stdin =>
      result == BenchWorld.Ok(stdinBefore) && stdinAfter == []
    case File(path) =>
      result == IOContract.ReadFileResultFields(preFs, path) &&
      stdinAfter == stdinBefore
  }

  ghost predicate InputPieceRelation(
    cmd: Schema.ExpandCmd,
    result: BenchWorld.Result<BenchWorld.Bytes>,
                              column: nat,
                              leading: bool,
                              output: BenchWorld.Bytes,
                              nextColumn: nat,
                              nextLeading: bool
  )
  {
    match result
    case Ok(data) =>
      DataExpansionRelation(
        cmd.tabs, cmd.initialOnly, data, column, leading,
        output, nextColumn, nextLeading
      )
    case Err(_) =>
      output == [] && nextColumn == column && nextLeading == leading
  }

  ghost predicate ErrorPieceRelation(
    input: Schema.Input,
    result: BenchWorld.Result<BenchWorld.Bytes>,
                              output: BenchWorld.Bytes,
                              hadError: bool
  )
  {
    match input
    case Stdin =>
      output == [] && !hadError
    case File(path) =>
      match result
      case Ok(_) => output == [] && !hadError
      case Err(err) => output == ErrorMessage(path, err) && hadError
  }

  ghost predicate InputTracePrefixWitnessRelation(
    cmd: Schema.ExpandCmd,
    preFs: BenchWorld.FileSystem,
    preStdin: BenchWorld.Bytes,
    count: nat,
    currentStdin: BenchWorld.Bytes,
    output: BenchWorld.Bytes,
    errorOutput: BenchWorld.Bytes,
    hadError: bool,
    results: seq<BenchWorld.Result<BenchWorld.Bytes>>,
    outputPieces: seq<BenchWorld.Bytes>,
    errorPieces: seq<BenchWorld.Bytes>,
    errorFlags: seq<bool>,
    columns: seq<nat>,
    leadings: seq<bool>,
    stdinStates: seq<BenchWorld.Bytes>
  )
  {
    count <= |cmd.inputs| &&
    |results| == count &&
    |outputPieces| == count &&
    |errorPieces| == count &&
    |errorFlags| == count &&
    |columns| == count + 1 &&
    |leadings| == count + 1 &&
    |stdinStates| == count + 1 &&
    columns[0] == 0 &&
    leadings[0] &&
    stdinStates[0] == preStdin &&
    stdinStates[count] == currentStdin &&
    (forall i: nat :: i < count ==>
                        ReadStepRelation(
                          cmd.inputs[i], preFs, stdinStates[i], stdinStates[i + 1],
                          results[i]
                        ) &&
                        InputPieceRelation(
                          cmd, results[i], columns[i], leadings[i],
                          outputPieces[i], columns[i + 1], leadings[i + 1]
                        ) &&
                        ErrorPieceRelation(
                          cmd.inputs[i], results[i], errorPieces[i], errorFlags[i]
                        )) &&
    output == JoinPieces(outputPieces) &&
    errorOutput == JoinPieces(errorPieces) &&
    hadError == (true in errorFlags)
  }

  ghost predicate InputTraceWitnessRelation(
    cmd: Schema.ExpandCmd,
    preFs: BenchWorld.FileSystem,
    preStdin: BenchWorld.Bytes,
    postStdin: BenchWorld.Bytes,
    output: BenchWorld.Bytes,
    errorOutput: BenchWorld.Bytes,
    hadError: bool,
    results: seq<BenchWorld.Result<BenchWorld.Bytes>>,
    outputPieces: seq<BenchWorld.Bytes>,
    errorPieces: seq<BenchWorld.Bytes>,
    errorFlags: seq<bool>,
    columns: seq<nat>,
    leadings: seq<bool>,
    stdinStates: seq<BenchWorld.Bytes>
  )
  {
    InputTracePrefixWitnessRelation(
      cmd, preFs, preStdin, |cmd.inputs|, postStdin,
      output, errorOutput, hadError, results, outputPieces,
      errorPieces, errorFlags, columns, leadings, stdinStates
    )
  }

  ghost predicate InputTraceRelation(
    cmd: Schema.ExpandCmd,
    preFs: BenchWorld.FileSystem,
    preStdin: BenchWorld.Bytes,
    postStdin: BenchWorld.Bytes,
    output: BenchWorld.Bytes,
    errorOutput: BenchWorld.Bytes,
    hadError: bool
  )
  {
    exists
      results: seq<BenchWorld.Result<BenchWorld.Bytes>>,
      outputPieces: seq<BenchWorld.Bytes>,
      errorPieces: seq<BenchWorld.Bytes>,
      errorFlags: seq<bool>,
      columns: seq<nat>,
      leadings: seq<bool>,
      stdinStates: seq<BenchWorld.Bytes> ::
      InputTraceWitnessRelation(
        cmd, preFs, preStdin, postStdin, output, errorOutput, hadError,
        results, outputPieces, errorPieces, errorFlags,
        columns, leadings, stdinStates
      )
  }

  twostate predicate Spec(raw: Schema.ExpandCmdRaw, io: BenchIO.IO, exit: int)
    reads io.Footprint()
  {
    exists cmd: Schema.ExpandCmd ::
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
      else if cmd.mode == Schema.ModeInvalidTabs then
        io.stdin() == old(io.stdin()) &&
        io.stdout() == old(io.stdout()) &&
        io.stderr() == old(io.stderr()) +
        InvalidTabsMessage(cmd.invalidTabsValue) &&
        exit == 1
      else
        exists output: BenchWorld.Bytes,
          errorOutput: BenchWorld.Bytes, hadError: bool ::
          InputTraceRelation(
            cmd, old(io.fs()), old(io.stdin()), io.stdin(),
            output, errorOutput, hadError
          ) &&
          io.stdout() == old(io.stdout()) + output &&
          io.stderr() == old(io.stderr()) + errorOutput &&
          exit == (if hadError then 1 else 0)
  }
}
