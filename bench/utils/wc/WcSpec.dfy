include "../../core/World.dfy"
include "../../core/IO.dfy"
include "../../core/IOContract.dfy"
include "WcSchema.dfy"

module WcSpec {
  import BenchIO
  import BenchWorld
  import IOContract
  import WcSchema




  datatype Counts = Counts(lines: int, words: int, chars: int, bytes: int, maxLine: int)
  datatype Entry = Entry(name: string, counts: Counts, wide: bool)
  datatype InputObservation = InputObservation(
    result: BenchWorld.Result<BenchWorld.Bytes>,
    entries: seq<Entry>,
    errorOutput: BenchWorld.Bytes,
    failed: bool
  )

  function HelpText(): BenchWorld.Bytes
  {
    "Usage: wc [OPTION]... [FILE]...\n"
    + "  or:  wc [OPTION]... --files0-from=F\n"
    + "Print newline, word, and byte counts for each FILE, and a total line if\n"
    + "more than one FILE is specified.  With no FILE, or when FILE is -, read\n"
    + "standard input.\n"
    + "\n"
    + "  -c, --bytes            print the byte counts\n"
    + "  -m, --chars            print the character counts\n"
    + "  -l, --lines            print the newline counts\n"
    + "  -L, --max-line-length  print the maximum display width\n"
    + "  -w, --words            print the word counts\n"
    + "      --help     display this help and exit\n"
    + "      --version  output version information and exit\n"
    + "\n"
    + "Report bugs to: bug-coreutils@gnu.org\n"
    + "GNU coreutils home page: <https://www.gnu.org/software/coreutils/>\n"
    + "General help using GNU software: <https://www.gnu.org/gethelp/>\n"
    + "Full documentation <https://www.gnu.org/software/coreutils/wc>\n"
    + "or available locally via: info '(coreutils) wc invocation'\n"
  }

  function VersionText(): BenchWorld.Bytes
  {
    "wc (GNU coreutils) 9.10.13-2cf49\n"
    + "Copyright (C) 2026 Free Software Foundation, Inc.\n"
    + "License GPLv3+: GNU GPL version 3 or later <https://gnu.org/licenses/gpl.html>.\n"
    + "This is free software: you are free to change and redistribute it.\n"
    + "There is NO WARRANTY, to the extent permitted by law.\n"
    + "\n"
    + "Written by Paul Rubin and David MacKenzie.\n"
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
    var displayPath :=
      if ' ' in path then "'" + path + "'"
      else path;
    "wc: " + displayPath + ": " + ErrnoText(err) + "\n"
  }

  function InputsFromOperands(operands: seq<string>): seq<WcSchema.Input>
    decreases |operands|
  {
    if |operands| == 0 then
      []
    else
      [(if operands[0] == "-" then WcSchema.Stdin("-") else WcSchema.File(operands[0]))] +
      InputsFromOperands(operands[1..])
  }

  function Command(raw: WcSchema.WcCmdRaw): WcSchema.WcCmd
  {
    var mode :=
      if raw.seenHelp && (!raw.seenVersion || raw.helpTokenIndex <= raw.versionTokenIndex) then
        WcSchema.ModeHelp
      else if raw.seenVersion then
        WcSchema.ModeVersion
      else
        WcSchema.ModeRun;
    var selected :=
      raw.seenLines || raw.seenWords || raw.seenChars || raw.seenBytes || raw.seenMaxLineLength;
    var inputs := InputsFromOperands(raw.operands);
    var runInputs := if mode == WcSchema.ModeRun && |inputs| == 0 then [WcSchema.Stdin("")] else inputs;
    WcSchema.WcCmd(
      mode,
      if selected then raw.seenLines else true,
      if selected then raw.seenWords else true,
      if selected then raw.seenChars else false,
      if selected then raw.seenBytes else true,
      if selected then raw.seenMaxLineLength else false,
      runInputs
    )
  }

  function IsStdinInput(input: WcSchema.Input): bool
  {
    match input
    case Stdin(_) => true
    case File(_) => false
  }

  function ZeroCounts(): Counts
  {
    Counts(0, 0, 0, 0, 0)
  }

  function AddCounts(a: Counts, b: Counts): Counts
  {
    Counts(a.lines + b.lines, a.words + b.words, a.chars + b.chars, a.bytes + b.bytes, Max(a.maxLine, b.maxLine))
  }

  function Max(a: int, b: int): int
  {
    if a < b then b else a
  }

  function IsWordSpace(ch: char): bool
  {
    ch == ' ' || ch == '\n' || ch == '\t' || ch == '\r' ||
    ch == (11 as char) || ch == (12 as char) || ch == (160 as char)
  }

  function NextLineLen(ch: char, current: int): int
    requires 0 <= current
  {
    if ch == '\t' then
      current + (8 - current % 8)
    else if ch == '\r' || ch == (12 as char) then
      0
    else if 32 <= ch as int < 127 then
      current + 1
    else
      current
  }

  function NewlineIndices(data: BenchWorld.Bytes): set<nat>
  {
    set i: nat | i < |data| && data[i] == '\n'
  }

  function WordStartIndices(data: BenchWorld.Bytes): set<nat>
  {
    set i: nat {:trigger data[i]} |
    i < |data| &&
    !IsWordSpace(data[i]) &&
    (i == 0 || IsWordSpace(data[i - 1]))
  }

  ghost predicate LineColumnTraceRelation(data: BenchWorld.Bytes, columns: seq<nat>)
  {
    |columns| == |data| + 1 &&
    columns[0] == 0 &&
    forall i: nat | i < |data| ::
      columns[i + 1] ==
      if data[i] == '\n' then 0
      else NextLineLen(data[i], columns[i])
  }

  ghost predicate MaximumRelation(values: seq<nat>, maximum: int)
  {
    0 <= maximum &&
    (forall i: nat | i < |values| :: values[i] <= maximum) &&
    (maximum == 0 || maximum in values)
  }

  ghost predicate CountRelation(data: BenchWorld.Bytes, counts: Counts)
  {
    counts.bytes == |data| &&
    counts.chars == |data| &&
    counts.lines == |NewlineIndices(data)| &&
    counts.words == |WordStartIndices(data)| &&
    exists columns: seq<nat> ::
      LineColumnTraceRelation(data, columns) &&
      MaximumRelation(columns, counts.maxLine)
  }

  ghost predicate ReadResultRelation(
    cmd: WcSchema.WcCmd,
    preFs: BenchWorld.FileSystem,
    preStdin: BenchWorld.Bytes,
    i: nat,
    result: BenchWorld.Result<BenchWorld.Bytes>
  )
    requires i < |cmd.inputs|
  {
    match cmd.inputs[i]
    case File(path) =>
      result == IOContract.ReadFileResultFields(preFs, path)
    case Stdin(_) =>
      result == BenchWorld.Ok(
        if exists j: nat :: j < i && IsStdinInput(cmd.inputs[j])
        then []
        else preStdin
      )
  }

  ghost predicate InputStepRelation(
    input: WcSchema.Input,
    result: BenchWorld.Result<BenchWorld.Bytes>,
                              entries: seq<Entry>,
                              errorOutput: BenchWorld.Bytes,
                              hadError: bool
  )
  {
    match input
    case Stdin(displayName) =>
      (match result
       case Ok(data) =>
         exists counts: Counts ::
           CountRelation(data, counts) &&
           entries == [Entry(displayName, counts, true)] &&
           errorOutput == [] &&
           !hadError
       case Err(_) => false)
    case File(path) =>
      (match result
       case Ok(data) =>
         exists counts: Counts ::
           CountRelation(data, counts) &&
           entries == [Entry(path, counts, false)] &&
           errorOutput == [] &&
           !hadError
       case Err(err) =>
         entries ==
         (if err == BenchWorld.IsDirectory
          then [Entry(path, ZeroCounts(), true)]
          else []) &&
         errorOutput == ErrorMessage(path, err) &&
         hadError)
  }

  ghost predicate FragmentsConcatenate<T>(
    fragments: seq<seq<T>>,
    combined: seq<T>,
    cuts: seq<nat>
  )
  {
    |cuts| == |fragments| + 1 &&
    cuts[0] == 0 &&
    cuts[|cuts| - 1] == |combined| &&
    forall i: nat {:trigger cuts[i]} | i < |fragments| ::
      cuts[i] <= cuts[i + 1] &&
      cuts[i + 1] <= |combined| &&
      cuts[i + 1] == cuts[i] + |fragments[i]| &&
      combined[cuts[i]..cuts[i + 1]] == fragments[i]
  }

  ghost predicate InputObservationRelation(
    cmd: WcSchema.WcCmd,
    preFs: BenchWorld.FileSystem,
    preStdin: BenchWorld.Bytes,
    i: nat,
    observation: InputObservation
  )
    requires i < |cmd.inputs|
  {
    ReadResultRelation(cmd, preFs, preStdin, i, observation.result) &&
    InputStepRelation(
      cmd.inputs[i],
      observation.result,
      observation.entries,
      observation.errorOutput,
      observation.failed
    )
  }

  ghost function ObservationEntryFragments(
    observations: seq<InputObservation>
  ): seq<seq<Entry>>
  {
    seq(
    |observations|,
    i requires 0 <= i < |observations| => observations[i].entries
      )
  }

  ghost function ObservationErrorFragments(
    observations: seq<InputObservation>
  ): seq<BenchWorld.Bytes>
  {
    seq(
    |observations|,
    i requires 0 <= i < |observations| => observations[i].errorOutput
      )
  }

  ghost predicate HasFailedObservation(observations: seq<InputObservation>)
  {
    exists i: nat :: i < |observations| && observations[i].failed
  }

  ghost predicate OrderedTraceWitnessRelation(
    cmd: WcSchema.WcCmd,
    preFs: BenchWorld.FileSystem,
    preStdin: BenchWorld.Bytes,
    postStdin: BenchWorld.Bytes,
    entries: seq<Entry>,
    errorOutput: BenchWorld.Bytes,
    hadError: bool,
    observations: seq<InputObservation>,
    entryCuts: seq<nat>,
    errorCuts: seq<nat>
  )
  {
    |observations| == |cmd.inputs| &&
    (forall i: nat | i < |observations| ::
       InputObservationRelation(
         cmd,
         preFs,
         preStdin,
         i,
         observations[i]
       )) &&
    FragmentsConcatenate(
      ObservationEntryFragments(observations),
      entries,
      entryCuts
    ) &&
    FragmentsConcatenate(
      ObservationErrorFragments(observations),
      errorOutput,
      errorCuts
    ) &&
    hadError == HasFailedObservation(observations) &&
    postStdin ==
    (if exists i: nat ::
          i < |cmd.inputs| && IsStdinInput(cmd.inputs[i])
     then []
     else preStdin)
  }

  ghost predicate InputTraceRelation(
    cmd: WcSchema.WcCmd,
    preFs: BenchWorld.FileSystem,
    preStdin: BenchWorld.Bytes,
    postStdin: BenchWorld.Bytes,
    entries: seq<Entry>,
    errorOutput: BenchWorld.Bytes,
    hadError: bool
  )
  {
    exists observations: seq<InputObservation>,
      entryCuts: seq<nat>,
      errorCuts: seq<nat> ::
      OrderedTraceWitnessRelation(
        cmd,
        preFs,
        preStdin,
        postStdin,
        entries,
        errorOutput,
        hadError,
        observations,
        entryCuts,
        errorCuts
      )
  }

  function SelectedFieldCount(cmd: WcSchema.WcCmd): int
  {
    (if cmd.showLines then 1 else 0) +
    (if cmd.showWords then 1 else 0) +
    (if cmd.showChars then 1 else 0) +
    (if cmd.showBytes then 1 else 0) +
    (if cmd.showMaxLineLength then 1 else 0)
  }

  function SelectedValues(cmd: WcSchema.WcCmd, counts: Counts): seq<int>
  {
    (if cmd.showLines then [counts.lines] else []) +
    (if cmd.showWords then [counts.words] else []) +
    (if cmd.showChars then [counts.chars] else []) +
    (if cmd.showBytes then [counts.bytes] else []) +
    (if cmd.showMaxLineLength then [counts.maxLine] else [])
  }

  function MaxSelectedValue(cmd: WcSchema.WcCmd, counts: Counts): int
  {
    Max(
      Max(
        if cmd.showLines then counts.lines else 0,
        if cmd.showWords then counts.words else 0
      ),
      Max(
        Max(
          if cmd.showChars then counts.chars else 0,
          if cmd.showBytes then counts.bytes else 0
        ),
        if cmd.showMaxLineLength then counts.maxLine else 0
      )
    )
  }

  function ShouldPrintTotal(cmd: WcSchema.WcCmd): bool
  {
    |cmd.inputs| > 1
  }

  function TotalName(): string
  {
    "total"
  }

  ghost predicate TotalCountsWitnessRelation(
    entries: seq<Entry>,
    total: Counts,
    prefixes: seq<Counts>
  )
  {
    |prefixes| == |entries| + 1 &&
    prefixes[0] == total &&
    prefixes[|entries|] == ZeroCounts() &&
    forall i: nat | i < |entries| ::
      prefixes[i] == AddCounts(entries[i].counts, prefixes[i + 1])
  }

  ghost predicate DecimalTextWitness(
    n: nat,
    text: BenchWorld.Bytes,
    digits: seq<nat>,
    values: seq<nat>
  )
  {
    |digits| > 0 &&
    |text| == |digits| &&
    |values| == |digits| + 1 &&
    values[0] == 0 &&
    values[|digits|] == n &&
    (|digits| == 1 || digits[0] != 0) &&
    forall i: nat | i < |digits| ::
      digits[i] < 10 &&
      text[i] == (('0' as int) + digits[i]) as char &&
      values[i + 1] == values[i] * 10 + digits[i]
  }

  ghost predicate DecimalText(n: nat, text: BenchWorld.Bytes)
  {
    exists digits: seq<nat>, values: seq<nat> ::
      DecimalTextWitness(n, text, digits, values)
  }

  ghost predicate PaddedDecimalText(
    n: nat,
    width: int,
    padded: BenchWorld.Bytes
  )
  {
    exists text: BenchWorld.Bytes,
      digits: seq<nat>,
      values: seq<nat> ::
      DecimalTextWitness(n, text, digits, values) &&
      |text| <= |padded| &&
      |padded| == (if |text| >= width then |text| else width) &&
      padded[|padded| - |text|..] == text &&
      forall i: nat | i < |padded| - |text| :: padded[i] == ' '
  }

  ghost predicate ValueFragmentRelation(
    value: int,
    width: int,
    first: bool,
    fragment: BenchWorld.Bytes
  )
  {
    0 <= value &&
    exists padded: BenchWorld.Bytes
      {:trigger PaddedDecimalText(value as nat, width, padded)} ::
      PaddedDecimalText(value as nat, width, padded) &&
      fragment == (if first then [] else [' ']) + padded
  }

  ghost predicate ValuesRenderWitnessRelation(
    values: seq<int>,
    width: int,
    first: bool,
    output: BenchWorld.Bytes,
    fragments: seq<BenchWorld.Bytes>,
    cuts: seq<nat>
  )
  {
    |fragments| == |values| &&
    (forall i: nat | i < |values| ::
       ValueFragmentRelation(
         values[i], width, first && i == 0, fragments[i]
       )) &&
    FragmentsConcatenate(fragments, output, cuts)
  }

  ghost predicate ValuesRenderRelation(
    values: seq<int>,
    width: int,
    first: bool,
    output: BenchWorld.Bytes
  )
  {
    exists fragments: seq<BenchWorld.Bytes>, cuts: seq<nat> ::
      ValuesRenderWitnessRelation(
        values, width, first, output, fragments, cuts
      )
  }

  ghost predicate CountsLineRelation(
    cmd: WcSchema.WcCmd,
    counts: Counts,
    name: string,
    width: int,
    line: BenchWorld.Bytes
  )
  {
    exists valuesOutput: BenchWorld.Bytes ::
      ValuesRenderRelation(
        SelectedValues(cmd, counts), width, true, valuesOutput
      ) &&
      line ==
      valuesOutput +
      (if name == "" then [] else [' '] + name) +
      ['\n']
  }

  ghost predicate EntryMaximumWitnessRelation(
    cmd: WcSchema.WcCmd,
    entries: seq<Entry>,
    selectedSuffixes: seq<int>,
    byteSuffixes: seq<int>
  )
  {
    |selectedSuffixes| == |entries| + 1 &&
    |byteSuffixes| == |entries| + 1 &&
    selectedSuffixes[|entries|] == 0 &&
    byteSuffixes[|entries|] == 0 &&
    forall i: nat | i < |entries| ::
      selectedSuffixes[i] ==
      Max(MaxSelectedValue(cmd, entries[i].counts), selectedSuffixes[i + 1]) &&
      byteSuffixes[i] ==
      Max(entries[i].counts.bytes, byteSuffixes[i + 1])
  }

  ghost predicate FieldWidthRelation(
    cmd: WcSchema.WcCmd,
    entries: seq<Entry>,
    total: Counts,
    width: int
  )
  {
    exists selectedSuffixes: seq<int>,
      byteSuffixes: seq<int>,
      maximum: int,
      maximumText: BenchWorld.Bytes
      {:trigger EntryMaximumWitnessRelation(
        cmd, entries, selectedSuffixes, byteSuffixes
      ), DecimalText(maximum as nat, maximumText)} ::
      EntryMaximumWitnessRelation(
        cmd, entries, selectedSuffixes, byteSuffixes
      ) &&
      maximum ==
      Max(
        Max(MaxSelectedValue(cmd, total), selectedSuffixes[0]),
        Max(total.bytes, byteSuffixes[0])
      ) &&
      0 <= maximum &&
      DecimalText(maximum as nat, maximumText) &&
      width ==
      if SelectedFieldCount(cmd) <= 1 && !ShouldPrintTotal(cmd) then
        1
      else if exists i: nat :: i < |entries| && entries[i].wide then
        Max(7, |maximumText|)
      else
        Max(1, |maximumText|)
  }

  ghost predicate OutputWitnessRelation(
    cmd: WcSchema.WcCmd,
    entries: seq<Entry>,
    output: BenchWorld.Bytes,
    total: Counts,
    totalPrefixes: seq<Counts>,
    width: int,
    entryLines: seq<BenchWorld.Bytes>,
    entryOutput: BenchWorld.Bytes,
    entryCuts: seq<nat>,
    totalLine: BenchWorld.Bytes
  )
  {
    TotalCountsWitnessRelation(entries, total, totalPrefixes) &&
    FieldWidthRelation(cmd, entries, total, width) &&
    |entryLines| == |entries| &&
    (forall i: nat | i < |entries| ::
       CountsLineRelation(
         cmd, entries[i].counts, entries[i].name, width, entryLines[i]
       )) &&
    FragmentsConcatenate(entryLines, entryOutput, entryCuts) &&
    (if ShouldPrintTotal(cmd) then
       CountsLineRelation(cmd, total, TotalName(), width, totalLine) &&
       output == entryOutput + totalLine
     else
       totalLine == [] &&
       output == entryOutput)
  }

  ghost predicate OutputRelation(
    cmd: WcSchema.WcCmd,
    entries: seq<Entry>,
    output: BenchWorld.Bytes
  )
  {
    exists total: Counts,
      totalPrefixes: seq<Counts>,
      width: int,
      entryLines: seq<BenchWorld.Bytes>,
      entryOutput: BenchWorld.Bytes,
      entryCuts: seq<nat>,
      totalLine: BenchWorld.Bytes ::
      OutputWitnessRelation(
        cmd, entries, output, total, totalPrefixes, width,
        entryLines, entryOutput, entryCuts, totalLine
      )
  }

  twostate predicate Spec(raw: WcSchema.WcCmdRaw, io: BenchIO.IO, exit: int)
    reads io.Footprint()
  {
    var cmd := Command(raw);
    if cmd.mode == WcSchema.ModeHelp then
      io.stdin() == old(io.stdin()) &&
      io.stdout() == old(io.stdout()) + HelpText() &&
      io.stderr() == old(io.stderr()) &&
      exit == 0
    else if cmd.mode == WcSchema.ModeVersion then
      io.stdin() == old(io.stdin()) &&
      io.stdout() == old(io.stdout()) + VersionText() &&
      io.stderr() == old(io.stderr()) &&
      exit == 0
    else
      exists entries: seq<Entry>,
        outputPart: BenchWorld.Bytes,
        errorOutput: BenchWorld.Bytes,
        hadError: bool ::
        InputTraceRelation(
          cmd,
          old(io.fs()),
          old(io.stdin()),
          io.stdin(),
          entries,
          errorOutput,
          hadError
        ) &&
        OutputRelation(cmd, entries, outputPart) &&
        io.stdout() == old(io.stdout()) + outputPart &&
        io.stderr() == old(io.stderr()) + errorOutput &&
        exit == (if hadError then 1 else 0)
  }
}
