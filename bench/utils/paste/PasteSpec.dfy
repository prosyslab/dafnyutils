include "../../core/World.dfy"
include "../../core/IO.dfy"
include "../../core/IOContract.dfy"
include "PasteSchema.dfy"

module PasteSpec {
  import BenchIO
  import Utf8 = Utf8Semantics
  import BenchWorld
  import IOContract
  import PasteSchema

  datatype Entry = Entry(lines: seq<BenchWorld.Bytes>, readOk: bool)
  datatype DelimPlan = DelimsOk(delims: seq<BenchWorld.Bytes>) | DelimsErr(stderr: BenchWorld.Bytes)
  datatype InputObservation = InputObservation(
    result: BenchWorld.Result<BenchWorld.Bytes>,
    entry: Entry,
    errorPiece: BenchWorld.Bytes,
    failed: bool,
    blocking: bool
  )




  function HelpText(): BenchWorld.Bytes
  {
    "Usage: paste [OPTION]... [FILE]...\n"
    + "Write lines consisting of the sequentially corresponding lines from\n"
    + "each FILE, separated by TABs, to standard output.\n"
    + "With no FILE, or when FILE is -, read standard input.\n"
    + "\n"
    + "  -d, --delimiters=LIST   reuse characters from LIST instead of TABs\n"
    + "  -s, --serial            paste one file at a time instead of in parallel\n"
    + "  -z, --zero-terminated    line delimiter is NUL, not newline\n"
    + "      --help              display this help and exit\n"
    + "      --version           output version information and exit\n"
    + "\n"
    + "Report bugs to: bug-coreutils@gnu.org\n"
    + "GNU coreutils home page: <https://www.gnu.org/software/coreutils/>\n"
    + "General help using GNU software: <https://www.gnu.org/gethelp/>\n"
    + "Full documentation <https://www.gnu.org/software/coreutils/paste>\n"
    + "or available locally via: info '(coreutils) paste invocation'\n"
  }

  function VersionText(): BenchWorld.Bytes
  {
    "paste (GNU coreutils) 9.10.13-2cf49\n"
    + "Copyright (C) 2026 Free Software Foundation, Inc.\n"
    + "License GPLv3+: GNU GPL version 3 or later <https://gnu.org/licenses/gpl.html>.\n"
    + "This is free software: you are free to change and redistribute it.\n"
    + "There is NO WARRANTY, to the extent permitted by law.\n"
    + "\n"
    + "Written by David M. Ihnat and David MacKenzie.\n"
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

  function NeedsErrorQuoting(path: string): bool
    decreases |path|
  {
    if |path| == 0 then
      false
    else
      path[0] == ' ' || path[0] == '=' || path[0] == ':' || NeedsErrorQuoting(path[1..])
  }

  function ErrorMessage(path: BenchWorld.Path, err: BenchWorld.IOError): BenchWorld.Bytes
  {
    var displayPath :=
      if NeedsErrorQuoting(path) then "'" + path + "'"
      else path;
    Utf8.Encode("paste: " + displayPath + ": " + ErrnoText(err) + "\n")
  }

  function DelimiterBackslashError(text: BenchWorld.Bytes): BenchWorld.Bytes
  {
    "paste: delimiter list ends with an unescaped backslash: " + text + "\n"
  }

  function RecordDelimiter(zeroTerminated: bool): BenchWorld.RawByte
  {
    if zeroTerminated then '\0' else '\n'
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
      cuts[i] <= cuts[i + 1] <= |combined| &&
      cuts[i + 1] == cuts[i] + |fragments[i]| &&
      combined[cuts[i]..cuts[i + 1]] == fragments[i]
  }

  ghost predicate LinePartitionRelation(
    data: BenchWorld.Bytes,
    recordDelimiter: BenchWorld.RawByte,
    lines: seq<BenchWorld.Bytes>,
    terminated: seq<bool>,
    fragments: seq<BenchWorld.Bytes>,
    cuts: seq<nat>
  )
  {
    |lines| == |terminated| == |fragments| &&
    FragmentsConcatenate(fragments, data, cuts) &&
    (forall i: nat | i < |lines| ::
       |fragments[i]| > 0 &&
       fragments[i] ==
       lines[i] + (if terminated[i] then [recordDelimiter] else []) &&
       recordDelimiter !in lines[i] &&
       (i + 1 < |lines| ==> terminated[i]))
  }

  ghost predicate ReadResultRelation(
    cmd: PasteSchema.PasteCmd,
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
        if PasteSchema.Stdin in cmd.inputs[..i]
        then []
        else preStdin)
    case File(path) =>
      result == IOContract.ReadFileResultFields(preFs, path)
  }

  ghost predicate EntryRelation(
    result: BenchWorld.Result<BenchWorld.Bytes>,
                              recordDelimiter: BenchWorld.RawByte,
                              entry: Entry
  )
  {
    match result
    case Ok(data) =>
      exists terminated: seq<bool>,
        fragments: seq<BenchWorld.Bytes>,
        cuts: seq<nat> ::
        entry.readOk &&
        LinePartitionRelation(
          data, recordDelimiter, entry.lines, terminated, fragments, cuts)
    case Err(err) =>
      entry == Entry([], err == BenchWorld.IsDirectory)
  }

  ghost predicate InputObservationRelation(
    cmd: PasteSchema.PasteCmd,
    preFs: BenchWorld.FileSystem,
    preStdin: BenchWorld.Bytes,
    i: nat,
    observation: InputObservation
  )
    requires i < |cmd.inputs|
  {
    ReadResultRelation(
      cmd, preFs, preStdin, i, observation.result) &&
    EntryRelation(
      observation.result,
      RecordDelimiter(cmd.zeroTerminated),
      observation.entry) &&
    match cmd.inputs[i]
    case Stdin =>
      observation.errorPiece == [] &&
      !observation.failed &&
      !observation.blocking
    case File(path) =>
      match observation.result
      case Ok(_) =>
        observation.errorPiece == [] &&
        !observation.failed &&
        !observation.blocking
      case Err(err) =>
        observation.errorPiece == ErrorMessage(path, err) &&
        observation.failed &&
        observation.blocking == (err != BenchWorld.IsDirectory)
  }

  ghost function ObservationEntries(
    observations: seq<InputObservation>
  ): seq<Entry>
  {
    seq(
    |observations|,
    i requires 0 <= i < |observations| => observations[i].entry)
  }

  ghost predicate SelectedLinesRelation(
    stdinLines: seq<BenchWorld.Bytes>,
    stdinIndex: nat,
    stdinCount: nat,
    selected: seq<BenchWorld.Bytes>
  )
  {
    stdinCount > 0 &&
    (forall k: nat | k < |selected| ::
       stdinIndex + k * stdinCount < |stdinLines| &&
       selected[k] == stdinLines[stdinIndex + k * stdinCount]) &&
    (|selected| == 0 ==> stdinIndex >= |stdinLines|) &&
    (|selected| > 0 ==>
       stdinIndex + (|selected| - 1) * stdinCount < |stdinLines| &&
       stdinIndex + |selected| * stdinCount >= |stdinLines|)
  }

  ghost predicate HasStdinInput(inputs: seq<PasteSchema.Input>)
  {
    PasteSchema.Stdin in inputs
  }

  ghost predicate StdinPositionsRelation(
    inputs: seq<PasteSchema.Input>,
    positions: seq<nat>
  )
  {
    (forall k: nat | k < |positions| ::
       positions[k] < |inputs| &&
       inputs[positions[k]] == PasteSchema.Stdin &&
       (k > 0 ==> positions[k - 1] < positions[k])) &&
    (forall i: nat | i < |inputs| ::
       inputs[i] == PasteSchema.Stdin ==> i in positions)
  }

  datatype EntriesForOutputWitness = EntriesForOutputWitness(
    positions: seq<nat>,
    stdinLines: seq<BenchWorld.Bytes>,
    terminated: seq<bool>,
    fragments: seq<BenchWorld.Bytes>,
    cuts: seq<nat>
  )

  ghost predicate ParallelEntriesForOutputRelation(
    cmd: PasteSchema.PasteCmd,
    preStdin: BenchWorld.Bytes,
    rawEntries: seq<Entry>,
    entries: seq<Entry>,
    trace: EntriesForOutputWitness
  )
  {
    |rawEntries| == |cmd.inputs| &&
    |entries| == |cmd.inputs| &&
    StdinPositionsRelation(cmd.inputs, trace.positions) &&
    LinePartitionRelation(
      if HasStdinInput(cmd.inputs) then preStdin else [],
      RecordDelimiter(cmd.zeroTerminated),
      trace.stdinLines,
      trace.terminated,
      trace.fragments,
      trace.cuts) &&
    forall i: nat | i < |cmd.inputs| ::
      match cmd.inputs[i]
      case File(_) =>
        entries[i] == rawEntries[i]
      case Stdin =>
        exists rank: nat, selected: seq<BenchWorld.Bytes> ::
          rank < |trace.positions| &&
          trace.positions[rank] == i &&
          SelectedLinesRelation(
            trace.stdinLines,
            rank,
            |trace.positions|,
            selected) &&
          entries[i] == Entry(selected, true)
  }

  ghost predicate EntriesForOutputRelation(
    cmd: PasteSchema.PasteCmd,
    preStdin: BenchWorld.Bytes,
    rawEntries: seq<Entry>,
    entries: seq<Entry>
  )
  {
    if cmd.serial then
      entries == rawEntries
    else
      exists trace: EntriesForOutputWitness ::
        ParallelEntriesForOutputRelation(
          cmd, preStdin, rawEntries, entries, trace)
  }

  datatype VisibleErrorAssembly =
    VisibleErrorsDone |
    VisibleErrorStep(
      previous: BenchWorld.Bytes,
      rest: VisibleErrorAssembly)

  ghost predicate VisibleErrorPrefixRelation(
    serial: bool,
    observations: seq<InputObservation>,
    i: nat,
    output: BenchWorld.Bytes,
    assembly: VisibleErrorAssembly
  )
    decreases assembly
  {
    i <= |observations| &&
    match assembly
    case VisibleErrorsDone =>
      i == 0 && output == []
    case VisibleErrorStep(previous, rest) =>
      i > 0 &&
      VisibleErrorPrefixRelation(
        serial, observations, i - 1, previous, rest) &&
      output ==
      if serial then
        previous + observations[i - 1].errorPiece
      else if exists j: nat ::
                j < i - 1 && observations[j].blocking then
        previous
      else if observations[i - 1].blocking then
        observations[i - 1].errorPiece
      else
        previous + observations[i - 1].errorPiece
  }

  ghost predicate VisibleErrorRelation(
    serial: bool,
    observations: seq<InputObservation>,
    output: BenchWorld.Bytes
  )
  {
    exists assembly: VisibleErrorAssembly ::
      VisibleErrorPrefixRelation(
        serial, observations, |observations|, output, assembly)
  }

  ghost predicate InputTraceRelation(
    cmd: PasteSchema.PasteCmd,
    preFs: BenchWorld.FileSystem,
    preStdin: BenchWorld.Bytes,
    postStdin: BenchWorld.Bytes,
    entries: seq<Entry>,
    errorOutput: BenchWorld.Bytes,
    hadError: bool,
    hadBlockingError: bool
  )
  {
    exists observations: seq<InputObservation> ::
      |observations| == |cmd.inputs| &&
      (forall i: nat | i < |observations| ::
         InputObservationRelation(
           cmd, preFs, preStdin, i, observations[i])) &&
      EntriesForOutputRelation(
        cmd, preStdin, ObservationEntries(observations), entries) &&
      VisibleErrorRelation(cmd.serial, observations, errorOutput) &&
      hadError ==
      (exists i: nat ::
         i < |observations| && observations[i].failed) &&
      hadBlockingError ==
      (exists i: nat ::
         i < |observations| && observations[i].blocking) &&
      postStdin ==
      (if HasStdinInput(cmd.inputs) then [] else preStdin)
  }

  ghost predicate EscapedDelimiterRelation(
    ch: BenchWorld.RawByte,
    delimiter: BenchWorld.Bytes
  )
  {
    delimiter ==
    if ch == '0' then []
    else if ch == 'n' then ['\n']
    else if ch == 't' then ['\t']
    else if ch == '\\' then ['\\']
    else if ch == 'b' then [(8 as char)]
    else if ch == 'f' then [(12 as char)]
    else if ch == 'r' then ['\r']
    else if ch == 'v' then [(11 as char)]
    else [ch]
  }

  datatype DelimiterAssembly =
    DelimiterDone |
    DelimiterFailure |
    DelimiterStep(
      index: nat,
      nextIndex: nat,
      delimiter: BenchWorld.Bytes,
      rest: DelimiterAssembly)

  ghost predicate DelimiterParseRelation(
    text: BenchWorld.Bytes,
    i: nat,
    plan: DelimPlan,
    assembly: DelimiterAssembly
  )
    decreases assembly
  {
    i <= |text| &&
    match assembly
    case DelimiterDone =>
      i == |text| && plan == DelimsOk([])
    case DelimiterFailure =>
      i < |text| &&
      text[i] == '\\' &&
      i + 1 == |text| &&
      plan == DelimsErr(DelimiterBackslashError(text))
    case DelimiterStep(index, nextIndex, delimiter, rest) =>
      index == i &&
      i < |text| &&
      (if text[i] == '\\' then
         nextIndex == i + 2 &&
         i + 1 < |text| &&
         EscapedDelimiterRelation(text[i + 1], delimiter)
       else
         nextIndex == i + 1 &&
         delimiter == [text[i]]) &&
      exists restPlan: DelimPlan ::
        DelimiterParseRelation(text, nextIndex, restPlan, rest) &&
        plan ==
        match restPlan
        case DelimsErr(stderr) => DelimsErr(stderr)
        case DelimsOk(delims) => DelimsOk([delimiter] + delims)
  }

  ghost predicate DelimiterPlanRelation(
    text: string,
    plan: DelimPlan
  )
  {
    if |text| == 0 then
      plan == DelimsOk([[]])
    else
      exists assembly: DelimiterAssembly ::
        DelimiterParseRelation(Utf8.Encode(text), 0, plan, assembly)
  }

  function Max(a: nat, b: nat): nat
  {
    if a < b then b else a
  }

  function MaxLineCount(entries: seq<Entry>): nat
    decreases |entries|
  {
    if |entries| == 0 then
      0
    else
      Max(|entries[0].lines|, MaxLineCount(entries[1..]))
  }

  function DelimAt(delims: seq<BenchWorld.Bytes>, i: nat): BenchWorld.Bytes
    requires |delims| > 0
  {
    delims[i % |delims|]
  }

  datatype ColumnAssembly =
    ColumnsDone |
    ColumnStep(cut: nat, nextCut: nat, after: BenchWorld.Bytes, rest: ColumnAssembly)

  datatype RecordAssembly =
    RecordsDone |
    RecordStep(cut: nat, nextCut: nat, record: BenchWorld.Bytes,
               after: BenchWorld.Bytes, columns: ColumnAssembly, rest: RecordAssembly)

  ghost predicate ParallelColumnsRelation(
    entries: seq<Entry>,
    delims: seq<BenchWorld.Bytes>,
    row: nat,
    i: nat,
    before: BenchWorld.Bytes,
    output: BenchWorld.Bytes,
    assembly: ColumnAssembly
  )
    decreases assembly
  {
    |delims| > 0 &&
    match assembly
    case ColumnsDone =>
      i == |entries| && output == before
    case ColumnStep(cut, nextCut, after, rest) =>
      i < |entries| &&
      var fragment :=
        (if row < |entries[i].lines| then entries[i].lines[row] else []) +
        (if i + 1 < |entries| then DelimAt(delims, i) else []);
      cut == |before| &&
      nextCut == cut + |fragment| &&
      after == before + fragment &&
      ParallelColumnsRelation(entries, delims, row, i + 1, after, output, rest)
  }

  ghost predicate ParallelRowRelation(
    entries: seq<Entry>,
    delims: seq<BenchWorld.Bytes>,
    row: nat,
    output: BenchWorld.Bytes
  )
  {
    |delims| > 0 &&
    exists columns: ColumnAssembly ::
      ParallelColumnsRelation(entries, delims, row, 0, [], output, columns)
  }

  ghost predicate ParallelRecordsRelation(
    entries: seq<Entry>,
    delims: seq<BenchWorld.Bytes>,
    recordDelimiter: BenchWorld.RawByte,
    row: nat,
    limit: nat,
    before: BenchWorld.Bytes,
    output: BenchWorld.Bytes,
    assembly: RecordAssembly
  )
    decreases assembly
  {
    |delims| > 0 &&
    match assembly
    case RecordsDone =>
      row == limit && output == before
    case RecordStep(cut, nextCut, record, after, columns, rest) =>
      row < limit &&
      ParallelColumnsRelation(entries, delims, row, 0, [], record, columns) &&
      cut == |before| &&
      nextCut == cut + |record| + 1 &&
      after == before + record + [recordDelimiter] &&
      ParallelRecordsRelation(
        entries, delims, recordDelimiter, row + 1, limit, after, output, rest)
  }

  ghost predicate ParallelOutputRelation(
    entries: seq<Entry>,
    delims: seq<BenchWorld.Bytes>,
    recordDelimiter: BenchWorld.RawByte,
    output: BenchWorld.Bytes
  )
  {
    |delims| > 0 &&
    exists records: RecordAssembly ::
      ParallelRecordsRelation(
        entries, delims, recordDelimiter, 0, MaxLineCount(entries), [], output, records)
  }

  ghost predicate SerialColumnsRelation(
    lines: seq<BenchWorld.Bytes>,
    delims: seq<BenchWorld.Bytes>,
    i: nat,
    before: BenchWorld.Bytes,
    output: BenchWorld.Bytes,
    assembly: ColumnAssembly
  )
    decreases assembly
  {
    |delims| > 0 &&
    match assembly
    case ColumnsDone =>
      i == |lines| && output == before
    case ColumnStep(cut, nextCut, after, rest) =>
      i < |lines| &&
      var fragment := lines[i] +
                      (if i + 1 < |lines| then DelimAt(delims, i) else []);
      cut == |before| &&
      nextCut == cut + |fragment| &&
      after == before + fragment &&
      SerialColumnsRelation(lines, delims, i + 1, after, output, rest)
  }

  ghost predicate SerialRecordsRelation(
    entries: seq<Entry>,
    delims: seq<BenchWorld.Bytes>,
    recordDelimiter: BenchWorld.RawByte,
    i: nat,
    before: BenchWorld.Bytes,
    output: BenchWorld.Bytes,
    assembly: RecordAssembly
  )
    decreases assembly
  {
    |delims| > 0 &&
    match assembly
    case RecordsDone =>
      i == |entries| && output == before
    case RecordStep(cut, nextCut, record, after, columns, rest) =>
      i < |entries| &&
      (if entries[i].readOk then
         SerialColumnsRelation(entries[i].lines, delims, 0, [], record, columns) &&
         cut == |before| &&
         nextCut == cut + |record| + 1 &&
         after == before + record + [recordDelimiter]
       else
         columns == ColumnsDone &&
         record == [] &&
         cut == |before| &&
         nextCut == cut &&
         after == before) &&
      SerialRecordsRelation(
        entries, delims, recordDelimiter, i + 1, after, output, rest)
  }

  ghost predicate SerialOutputRelation(
    entries: seq<Entry>,
    delims: seq<BenchWorld.Bytes>,
    recordDelimiter: BenchWorld.RawByte,
    output: BenchWorld.Bytes
  )
  {
    |delims| > 0 &&
    exists records: RecordAssembly ::
      SerialRecordsRelation(entries, delims, recordDelimiter, 0, [], output, records)
  }

  ghost predicate OutputRelation(
    serial: bool,
    delims: seq<BenchWorld.Bytes>,
    recordDelimiter: BenchWorld.RawByte,
    entries: seq<Entry>,
    output: BenchWorld.Bytes
  )
  {
    if serial then
      SerialOutputRelation(entries, delims, recordDelimiter, output)
    else
      ParallelOutputRelation(entries, delims, recordDelimiter, output)
  }

  twostate predicate SpecCmd(cmd: PasteSchema.PasteCmd, io: BenchIO.IO, exit: int)
    reads io.fsRegion, io.stdinRegion, io.stdoutRegion, io.stderrRegion
  {
    if cmd.mode == PasteSchema.ModeHelp then
      io.stdin() == old(io.stdin()) &&
      io.stdout() == old(io.stdout()) + HelpText() &&
      io.stderr() == old(io.stderr()) &&
      exit == 0
    else if cmd.mode == PasteSchema.ModeVersion then
      io.stdin() == old(io.stdin()) &&
      io.stdout() == old(io.stdout()) + VersionText() &&
      io.stderr() == old(io.stderr()) &&
      exit == 0
    else
      exists plan: DelimPlan ::
        DelimiterPlanRelation(cmd.delimiterText, plan) &&
        match plan
        case DelimsErr(stderr) =>
          io.stdin() == old(io.stdin()) &&
          io.stdout() == old(io.stdout()) &&
          io.stderr() == old(io.stderr()) + stderr &&
          exit == 1
        case DelimsOk(delims) =>
          exists entries: seq<Entry>,
            errorOutput: BenchWorld.Bytes,
            hadError: bool,
            hadBlockingError: bool,
            output: BenchWorld.Bytes ::
            InputTraceRelation(
              cmd, old(io.fs()), old(io.stdin()), io.stdin(), entries,
              errorOutput, hadError, hadBlockingError) &&
            OutputRelation(
              cmd.serial, delims, RecordDelimiter(cmd.zeroTerminated),
              entries, output) &&
            io.stdout() == old(io.stdout()) +
            (if hadBlockingError && !cmd.serial then [] else output) &&
            io.stderr() == old(io.stderr()) + errorOutput &&
            exit == (if hadError then 1 else 0)
  }

  twostate predicate Spec(raw: PasteSchema.PasteCmdRaw, io: BenchIO.IO, exit: int)
    reads io.fsRegion, io.stdinRegion, io.stdoutRegion, io.stderrRegion
  {
    SpecCmd(PasteSchema.Command(raw), io, exit)
  }
}
