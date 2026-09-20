include "../../core/World.dfy"
include "../../core/IO.dfy"
include "../../core/IOContract.dfy"
include "PasteSchema.dfy"
include "PasteSpec.dfy"

module PasteCore {
  import BenchIO
  import Utf8 = Utf8Semantics
  import BenchWorld
  import IOContract
  import PasteSchema
  import Spec = PasteSpec

  datatype LineRead = NoLine | SomeLine(line: BenchWorld.Bytes, rest: BenchWorld.Bytes)
  datatype Entry = Entry(lines: seq<BenchWorld.Bytes>, readOk: bool)
  datatype DelimPlan = DelimsOk(delims: seq<BenchWorld.Bytes>) | DelimsErr(stderr: BenchWorld.Bytes)

  function Command(raw: PasteSchema.PasteCmdRaw): PasteSchema.PasteCmd
  {
    PasteSchema.Command(raw)
  } by method {
    return PasteSchema.Command(raw);
  }

  function RecordDelimiter(zeroTerminated: bool): BenchWorld.RawByte
  {
    if zeroTerminated then '\0' else '\n'
  } by method {
    return if zeroTerminated then '\0' else '\n';
  }

  ghost function PrefixStdinCore(cmd: PasteSchema.PasteCmd, preStdin: BenchWorld.Bytes, i: nat): BenchWorld.Bytes
    requires i <= |cmd.inputs|
    decreases i
  {
    if i == 0 then
      preStdin
    else
      match cmd.inputs[i - 1]
      case Stdin => []
      case File(_) => PrefixStdinCore(cmd, preStdin, i - 1)
  }

  ghost function ReadResultCore(
    cmd: PasteSchema.PasteCmd,
    preFs: BenchWorld.FileSystem,
    preStdin: BenchWorld.Bytes,
    i: nat
  ): BenchWorld.Result<BenchWorld.Bytes>
    requires i < |cmd.inputs|
  {
    match cmd.inputs[i]
    case Stdin => BenchWorld.Ok(PrefixStdinCore(cmd, preStdin, i))
    case File(path) => IOContract.ReadFileResultFields(preFs, path)
  }

  function ReadLine(data: BenchWorld.Bytes, recordDelimiter: BenchWorld.RawByte): LineRead
    ensures ReadLine(data, recordDelimiter).SomeLine? ==> |ReadLine(data, recordDelimiter).rest| < |data|
    decreases |data|
  {
    if |data| == 0 then
      NoLine
    else if data[0] == recordDelimiter then
      SomeLine([], data[1..])
    else
      match ReadLine(data[1..], recordDelimiter)
      case NoLine => SomeLine([data[0]], [])
      case SomeLine(line, rest) => SomeLine([data[0]] + line, rest)
  } by method {
    if |data| == 0 {
      return NoLine;
    } else if data[0] == recordDelimiter {
      return SomeLine([], data[1..]);
    } else {
      var tail := ReadLine(data[1..], recordDelimiter);
      return
        match tail
        case NoLine => SomeLine([data[0]], [])
        case SomeLine(line, rest) => SomeLine([data[0]] + line, rest);
    }
  }

  function Lines(data: BenchWorld.Bytes, recordDelimiter: BenchWorld.RawByte): seq<BenchWorld.Bytes>
    decreases |data|
  {
    match ReadLine(data, recordDelimiter)
    case NoLine => []
    case SomeLine(line, rest) => [line] + Lines(rest, recordDelimiter)
  } by method {
    var lineRead := ReadLine(data, recordDelimiter);
    match lineRead
    case NoLine =>
      return [];
    case SomeLine(line, rest) =>
      var tail := Lines(rest, recordDelimiter);
      return [line] + tail;
  }

  function EntryForRead(result: BenchWorld.Result<BenchWorld.Bytes>, recordDelimiter: BenchWorld.RawByte): Entry
  {
    match result
    case Ok(data) => Entry(Lines(data, recordDelimiter), true)
    case Err(err) =>
      match err
      case IsDirectory => Entry([], true)
      case _ => Entry([], false)
  } by method {
    match result
    case Ok(data) =>
      return Entry(Lines(data, recordDelimiter), true);
    case Err(err) =>
      return
        match err
        case IsDirectory => Entry([], true)
        case _ => Entry([], false);
  }

  function IsStdinInput(input: PasteSchema.Input): bool
  {
    match input
    case Stdin => true
    case File(_) => false
  } by method {
    return
      match input
      case Stdin => true
      case File(_) => false;
  }

  function PrefixHadStdinCore(inputs: seq<PasteSchema.Input>, i: nat): bool
    requires i <= |inputs|
    decreases i
  {
    if i == 0 then
      false
    else
      PrefixHadStdinCore(inputs, i - 1) || IsStdinInput(inputs[i - 1])
  } by method {
    if i == 0 {
      return false;
    } else {
      return PrefixHadStdinCore(inputs, i - 1) || IsStdinInput(inputs[i - 1]);
    }
  }

  function CountStdinInputs(inputs: seq<PasteSchema.Input>): nat
  {
    CountStdinPrefix(inputs, |inputs|)
  } by method {
    return CountStdinPrefix(inputs, |inputs|);
  }

  function CountStdinPrefix(inputs: seq<PasteSchema.Input>, i: nat): nat
    requires i <= |inputs|
    decreases i
  {
    if i == 0 then
      0
    else
      CountStdinPrefix(inputs, i - 1) + (if IsStdinInput(inputs[i - 1]) then 1 else 0)
  } by method {
    if i == 0 {
      return 0;
    } else {
      return CountStdinPrefix(inputs, i - 1) +
        (if IsStdinInput(inputs[i - 1]) then 1 else 0);
    }
  }

  function SelectStdinLines(lines: seq<BenchWorld.Bytes>, stdinIndex: nat, stdinCount: nat): seq<BenchWorld.Bytes>
    decreases if stdinIndex <= |lines| then |lines| - stdinIndex else 0
  {
    if stdinCount == 0 || |lines| <= stdinIndex then
      []
    else
      [lines[stdinIndex]] +
      SelectStdinLines(lines, stdinIndex + stdinCount, stdinCount)
  } by method {
    if stdinCount == 0 || |lines| <= stdinIndex {
      return [];
    } else {
      return [lines[stdinIndex]] +
        SelectStdinLines(lines, stdinIndex + stdinCount, stdinCount);
    }
  }

  function ParallelEntriesFrom(
    inputs: seq<PasteSchema.Input>,
    entries: seq<Entry>,
    stdinLines: seq<BenchWorld.Bytes>,
    stdinCount: nat,
    i: nat
  ): seq<Entry>
    requires |entries| == |inputs|
    requires i <= |inputs|
    ensures |ParallelEntriesFrom(
              inputs, entries, stdinLines, stdinCount, i)| == |inputs| - i
    decreases |inputs| - i
  {
    if i == |inputs| then
      []
    else
      var head :=
        match inputs[i]
        case Stdin => Entry(SelectStdinLines(stdinLines, CountStdinPrefix(inputs, i), stdinCount), true)
        case File(_) => entries[i];
      [head] + ParallelEntriesFrom(inputs, entries, stdinLines, stdinCount, i + 1)
  } by method {
    if i == |inputs| {
      return [];
    } else {
      var head :=
        match inputs[i]
        case Stdin =>
          Entry(
            SelectStdinLines(stdinLines, CountStdinPrefix(inputs, i), stdinCount),
            true)
        case File(_) =>
          entries[i];
      return [head] +
        ParallelEntriesFrom(inputs, entries, stdinLines, stdinCount, i + 1);
    }
  }

  function EntriesForOutputFromEntries(cmd: PasteSchema.PasteCmd, entries: seq<Entry>, stdinData: BenchWorld.Bytes): seq<Entry>
    requires |entries| == |cmd.inputs|
  {
    if cmd.serial then
      entries
    else
      var recordDelimiter := RecordDelimiter(cmd.zeroTerminated);
      var stdinLines := Lines(stdinData, recordDelimiter);
      ParallelEntriesFrom(cmd.inputs, entries, stdinLines, CountStdinInputs(cmd.inputs), 0)
  } by method {
    if cmd.serial {
      return entries;
    } else {
      var recordDelimiter := RecordDelimiter(cmd.zeroTerminated);
      var stdinLines := Lines(stdinData, recordDelimiter);
      return ParallelEntriesFrom(
          cmd.inputs, entries, stdinLines, CountStdinInputs(cmd.inputs), 0);
    }
  }

  ghost function StdinDataForOutputCore(cmd: PasteSchema.PasteCmd, preStdin: BenchWorld.Bytes): BenchWorld.Bytes
  {
    if PrefixHadStdinCore(cmd.inputs, |cmd.inputs|) then preStdin else []
  }

  function ErrorPiece(input: PasteSchema.Input, result: BenchWorld.Result<BenchWorld.Bytes>): BenchWorld.Bytes
  {
    match input
    case Stdin => []
    case File(path) =>
      match result
      case Ok(_) => []
      case Err(err) => Spec.ErrorMessage(path, err)
  } by method {
    return
      match input
      case Stdin => []
      case File(path) =>
        match result
        case Ok(_) => []
        case Err(err) => Spec.ErrorMessage(path, err);
  }

  function HadErrorPiece(input: PasteSchema.Input, result: BenchWorld.Result<BenchWorld.Bytes>): bool
  {
    match input
    case Stdin => false
    case File(_) =>
      match result
      case Ok(_) => false
      case Err(_) => true
  } by method {
    return
      match input
      case Stdin => false
      case File(_) =>
        match result
        case Ok(_) => false
        case Err(_) => true;
  }

  function HadBlockingErrorPiece(input: PasteSchema.Input, result: BenchWorld.Result<BenchWorld.Bytes>): bool
  {
    match input
    case Stdin => false
    case File(_) =>
      match result
      case Ok(_) => false
      case Err(err) =>
        match err
        case IsDirectory => false
        case _ => true
  } by method {
    return
      match input
      case Stdin => false
      case File(_) =>
        match result
        case Ok(_) => false
        case Err(err) =>
          match err
          case IsDirectory => false
          case _ => true;
  }

  ghost function PrefixEntriesCore(
    cmd: PasteSchema.PasteCmd,
    preFs: BenchWorld.FileSystem,
    preStdin: BenchWorld.Bytes,
    i: nat
  ): seq<Entry>
    requires i <= |cmd.inputs|
    ensures |PrefixEntriesCore(cmd, preFs, preStdin, i)| == i
    decreases i
  {
    if i == 0 then
      []
    else
      PrefixEntriesCore(cmd, preFs, preStdin, i - 1) +
      [EntryForRead(ReadResultCore(cmd, preFs, preStdin, i - 1), RecordDelimiter(cmd.zeroTerminated))]
  }

  ghost function EntriesCore(
    cmd: PasteSchema.PasteCmd,
    preFs: BenchWorld.FileSystem,
    preStdin: BenchWorld.Bytes
  ): seq<Entry>
  {
    PrefixEntriesCore(cmd, preFs, preStdin, |cmd.inputs|)
  }

  ghost function PrefixVisibleErrorOutputCore(
    cmd: PasteSchema.PasteCmd,
    preFs: BenchWorld.FileSystem,
    preStdin: BenchWorld.Bytes,
    i: nat
  ): BenchWorld.Bytes
    requires i <= |cmd.inputs|
    decreases i
  {
    if i == 0 then
      []
    else
      var previous := PrefixVisibleErrorOutputCore(cmd, preFs, preStdin, i - 1);
      if cmd.serial then
        previous + ErrorPiece(cmd.inputs[i - 1], ReadResultCore(cmd, preFs, preStdin, i - 1))
      else if PrefixHadBlockingErrorCore(cmd, preFs, preStdin, i - 1) then
        previous
      else if HadBlockingErrorPiece(cmd.inputs[i - 1], ReadResultCore(cmd, preFs, preStdin, i - 1)) then
        ErrorPiece(cmd.inputs[i - 1], ReadResultCore(cmd, preFs, preStdin, i - 1))
      else
        previous + ErrorPiece(cmd.inputs[i - 1], ReadResultCore(cmd, preFs, preStdin, i - 1))
  }

  ghost function PrefixHadErrorCore(
    cmd: PasteSchema.PasteCmd,
    preFs: BenchWorld.FileSystem,
    preStdin: BenchWorld.Bytes,
    i: nat
  ): bool
    requires i <= |cmd.inputs|
    decreases i
  {
    if i == 0 then
      false
    else
      PrefixHadErrorCore(cmd, preFs, preStdin, i - 1) ||
      HadErrorPiece(cmd.inputs[i - 1], ReadResultCore(cmd, preFs, preStdin, i - 1))
  }

  ghost function PrefixHadBlockingErrorCore(
    cmd: PasteSchema.PasteCmd,
    preFs: BenchWorld.FileSystem,
    preStdin: BenchWorld.Bytes,
    i: nat
  ): bool
    requires i <= |cmd.inputs|
    decreases i
  {
    if i == 0 then
      false
    else
      PrefixHadBlockingErrorCore(cmd, preFs, preStdin, i - 1) ||
      HadBlockingErrorPiece(cmd.inputs[i - 1], ReadResultCore(cmd, preFs, preStdin, i - 1))
  }

  function EscapeDelimiter(ch: BenchWorld.RawByte): BenchWorld.Bytes
  {
    if ch == '0' then
      []
    else if ch == 'n' then
      ['\n']
    else if ch == 't' then
      ['\t']
    else if ch == '\\' then
      ['\\']
    else if ch == 'b' then
      [(8 as char)]
    else if ch == 'f' then
      [(12 as char)]
    else if ch == 'r' then
      ['\r']
    else if ch == 'v' then
      [(11 as char)]
    else
      [ch]
  } by method {
    return
      if ch == '0' then []
      else if ch == 'n' then ['\n']
      else if ch == 't' then ['\t']
      else if ch == '\\' then ['\\']
      else if ch == 'b' then [(8 as char)]
      else if ch == 'f' then [(12 as char)]
      else if ch == 'r' then ['\r']
      else if ch == 'v' then [(11 as char)]
      else [ch];
  }

  function CollapseDelimitersFrom(text: BenchWorld.Bytes, i: nat): DelimPlan
    requires i <= |text|
    decreases |text| - i
  {
    if i >= |text| then
      DelimsOk([])
    else if text[i] == '\\' then
      if i + 1 >= |text| then
        DelimsErr(Spec.DelimiterBackslashError(text))
      else
        match CollapseDelimitersFrom(text, i + 2)
        case DelimsErr(stderr) => DelimsErr(stderr)
        case DelimsOk(rest) => DelimsOk([EscapeDelimiter(text[i + 1])] + rest)
    else
      match CollapseDelimitersFrom(text, i + 1)
      case DelimsErr(stderr) => DelimsErr(stderr)
      case DelimsOk(rest) => DelimsOk([[text[i]]] + rest)
  } by method {
    if i >= |text| {
      return DelimsOk([]);
    } else if text[i] == '\\' {
      if i + 1 >= |text| {
        return DelimsErr(Spec.DelimiterBackslashError(text));
      } else {
        match CollapseDelimitersFrom(text, i + 2)
        case DelimsErr(stderr) =>
          return DelimsErr(stderr);
        case DelimsOk(delims) =>
          return DelimsOk([EscapeDelimiter(text[i + 1])] + delims);
      }
    } else {
      match CollapseDelimitersFrom(text, i + 1)
      case DelimsErr(stderr) =>
        return DelimsErr(stderr);
      case DelimsOk(delims) =>
        return DelimsOk([[text[i]]] + delims);
    }
  }

  function CollapseDelimiters(text: string): DelimPlan
  {
    if |text| == 0 then
      DelimsOk([[]])
    else
      CollapseDelimitersFrom(Utf8.Encode(text), 0)
  } by method {
    return
      if |text| == 0 then DelimsOk([[]])
      else CollapseDelimitersFrom(Utf8.Encode(text), 0);
  }

  function Max(a: nat, b: nat): nat
  {
    if a < b then b else a
  } by method {
    return if a < b then b else a;
  }

  function MaxLineCount(entries: seq<Entry>): nat
    decreases |entries|
  {
    if |entries| == 0 then
      0
    else
      Max(|entries[0].lines|, MaxLineCount(entries[1..]))
  } by method {
    if |entries| == 0 {
      return 0;
    } else {
      return Max(|entries[0].lines|, MaxLineCount(entries[1..]));
    }
  }

  function DelimAt(delims: seq<BenchWorld.Bytes>, i: nat): BenchWorld.Bytes
    requires |delims| > 0
  {
    delims[i % |delims|]
  } by method {
    return delims[i % |delims|];
  }

  function RenderParallelRow(entries: seq<Entry>, delims: seq<BenchWorld.Bytes>, row: nat, i: nat, last: nat): BenchWorld.Bytes
    requires |delims| > 0
    requires last < |entries|
    requires i <= last + 1
    decreases last + 1 - i
  {
    if i > last then
      []
    else
      var field := if row < |entries[i].lines| then entries[i].lines[row] else [];
      field +
      (if i < last then DelimAt(delims, i) else []) +
      RenderParallelRow(entries, delims, row, i + 1, last)
  } by method {
    if i > last {
      return [];
    } else {
      var field := if row < |entries[i].lines| then entries[i].lines[row] else [];
      var delimiter := if i < last then DelimAt(delims, i) else [];
      return field + delimiter +
        RenderParallelRow(entries, delims, row, i + 1, last);
    }
  }

  function RenderParallelRows(entries: seq<Entry>, delims: seq<BenchWorld.Bytes>, recordDelimiter: BenchWorld.RawByte, row: nat, limit: nat): BenchWorld.Bytes
    requires |delims| > 0
    requires row <= limit
    requires limit == MaxLineCount(entries)
    decreases limit - row
  {
    if row >= limit then
      []
    else if |entries| == 0 then
      []
    else
      var last: nat := |entries| - 1;
      RenderParallelRow(entries, delims, row, 0, last) + [recordDelimiter] +
      RenderParallelRows(entries, delims, recordDelimiter, row + 1, limit)
  } by method {
    if row >= limit || |entries| == 0 {
      return [];
    } else {
      var last: nat := |entries| - 1;
      return RenderParallelRow(entries, delims, row, 0, last) +
        [recordDelimiter] +
        RenderParallelRows(entries, delims, recordDelimiter, row + 1, limit);
    }
  }

  function RenderParallel(entries: seq<Entry>, delims: seq<BenchWorld.Bytes>, recordDelimiter: BenchWorld.RawByte): BenchWorld.Bytes
    requires |delims| > 0
  {
    RenderParallelRows(entries, delims, recordDelimiter, 0, MaxLineCount(entries))
  } by method {
    return RenderParallelRows(
        entries, delims, recordDelimiter, 0, MaxLineCount(entries));
  }

  function JoinLines(lines: seq<BenchWorld.Bytes>, delims: seq<BenchWorld.Bytes>, i: nat): BenchWorld.Bytes
    requires |delims| > 0
    requires i <= |lines|
    decreases |lines| - i
  {
    if i >= |lines| then
      []
    else
      lines[i] +
      (if i + 1 < |lines| then DelimAt(delims, i) else []) +
      JoinLines(lines, delims, i + 1)
  } by method {
    if i >= |lines| {
      return [];
    } else {
      var delimiter := if i + 1 < |lines| then DelimAt(delims, i) else [];
      return lines[i] + delimiter + JoinLines(lines, delims, i + 1);
    }
  }

  function RenderSerial(entries: seq<Entry>, delims: seq<BenchWorld.Bytes>, recordDelimiter: BenchWorld.RawByte): BenchWorld.Bytes
    requires |delims| > 0
    decreases |entries|
  {
    if |entries| == 0 then
      []
    else if !entries[0].readOk then
      RenderSerial(entries[1..], delims, recordDelimiter)
    else
      JoinLines(entries[0].lines, delims, 0) + [recordDelimiter] +
      RenderSerial(entries[1..], delims, recordDelimiter)
  } by method {
    if |entries| == 0 {
      return [];
    } else if !entries[0].readOk {
      return RenderSerial(entries[1..], delims, recordDelimiter);
    } else {
      return JoinLines(entries[0].lines, delims, 0) +
        [recordDelimiter] +
        RenderSerial(entries[1..], delims, recordDelimiter);
    }
  }

  function RenderOutput(serial: bool, delims: seq<BenchWorld.Bytes>, recordDelimiter: BenchWorld.RawByte, entries: seq<Entry>): BenchWorld.Bytes
    requires |delims| > 0
  {
    if serial then RenderSerial(entries, delims, recordDelimiter) else RenderParallel(entries, delims, recordDelimiter)
  } by method {
    return
      if serial then RenderSerial(entries, delims, recordDelimiter)
      else RenderParallel(entries, delims, recordDelimiter);
  }

  ghost function EntriesForOutputCore(
    cmd: PasteSchema.PasteCmd,
    preFs: BenchWorld.FileSystem,
    preStdin: BenchWorld.Bytes
  ): seq<Entry>
  {
    EntriesForOutputFromEntries(cmd, EntriesCore(cmd, preFs, preStdin), StdinDataForOutputCore(cmd, preStdin))
  }

  ghost function RunOutputCore(
    cmd: PasteSchema.PasteCmd,
    preFs: BenchWorld.FileSystem,
    preStdin: BenchWorld.Bytes,
    delims: seq<BenchWorld.Bytes>
  ): BenchWorld.Bytes
    requires |delims| > 0
  {
    RenderOutput(cmd.serial, delims, RecordDelimiter(cmd.zeroTerminated), EntriesForOutputCore(cmd, preFs, preStdin))
  }

  twostate predicate CoreSummaryCmd(cmd: PasteSchema.PasteCmd, io: BenchIO.IO, exit: int)
    reads io.fsRegion, io.stdinRegion, io.stdoutRegion, io.stderrRegion
  {
    if cmd.mode == PasteSchema.ModeHelp then
      io.stdin() == old(io.stdin()) &&
      io.stdout() == old(io.stdout()) + Spec.HelpText() &&
      io.stderr() == old(io.stderr()) &&
      exit == 0
    else if cmd.mode == PasteSchema.ModeVersion then
      io.stdin() == old(io.stdin()) &&
      io.stdout() == old(io.stdout()) + Spec.VersionText() &&
      io.stderr() == old(io.stderr()) &&
      exit == 0
    else
      match CollapseDelimiters(cmd.delimiterText)
      case DelimsErr(stderr) =>
        io.stdin() == old(io.stdin()) &&
        io.stdout() == old(io.stdout()) &&
        io.stderr() == old(io.stderr()) + stderr &&
        exit == 1
      case DelimsOk(delims) =>
        io.stdin() == PrefixStdinCore(cmd, old(io.stdin()), |cmd.inputs|) &&
        io.stdout() == old(io.stdout()) +
        (if PrefixHadBlockingErrorCore(cmd, old(io.fs()), old(io.stdin()), |cmd.inputs|) && !cmd.serial then
           []
         else
           RunOutputCore(cmd, old(io.fs()), old(io.stdin()), delims)) &&
        io.stderr() == old(io.stderr()) + PrefixVisibleErrorOutputCore(cmd, old(io.fs()), old(io.stdin()), |cmd.inputs|) &&
        exit == (if PrefixHadErrorCore(cmd, old(io.fs()), old(io.stdin()), |cmd.inputs|) then 1 else 0)
  }

  twostate predicate CoreSummary(raw: PasteSchema.PasteCmdRaw, io: BenchIO.IO, exit: int)
    reads io.fsRegion, io.stdinRegion, io.stdoutRegion, io.stderrRegion
  {
    CoreSummaryCmd(Command(raw), io, exit)
  }

  lemma PrefixStdinCoreStep(cmd: PasteSchema.PasteCmd, preStdin: BenchWorld.Bytes, i: nat)
    requires i < |cmd.inputs|
    ensures PrefixStdinCore(cmd, preStdin, i + 1) ==
            match cmd.inputs[i]
            case Stdin => IOContract.AfterReadStdinFields(PrefixStdinCore(cmd, preStdin, i))
            case File(_) => PrefixStdinCore(cmd, preStdin, i)
  {
  }

  lemma PrefixStdinCoreNoStdinPrefix(cmd: PasteSchema.PasteCmd, preStdin: BenchWorld.Bytes, i: nat)
    requires i <= |cmd.inputs|
    requires !PrefixHadStdinCore(cmd.inputs, i)
    ensures PrefixStdinCore(cmd, preStdin, i) == preStdin
    decreases i
  {
    if i > 0 {
      PrefixStdinCoreNoStdinPrefix(cmd, preStdin, i - 1);
    }
  }

  lemma PrefixEntriesCoreStep(
    cmd: PasteSchema.PasteCmd,
    preFs: BenchWorld.FileSystem,
    preStdin: BenchWorld.Bytes,
    i: nat
  )
    requires i < |cmd.inputs|
    ensures PrefixEntriesCore(cmd, preFs, preStdin, i + 1) ==
            PrefixEntriesCore(cmd, preFs, preStdin, i) +
            [EntryForRead(ReadResultCore(cmd, preFs, preStdin, i), RecordDelimiter(cmd.zeroTerminated))]
  {
  }

  lemma PrefixVisibleErrorOutputCoreStep(
    cmd: PasteSchema.PasteCmd,
    preFs: BenchWorld.FileSystem,
    preStdin: BenchWorld.Bytes,
    i: nat
  )
    requires i < |cmd.inputs|
    ensures PrefixVisibleErrorOutputCore(cmd, preFs, preStdin, i + 1) ==
            if cmd.serial then
              PrefixVisibleErrorOutputCore(cmd, preFs, preStdin, i) + ErrorPiece(cmd.inputs[i], ReadResultCore(cmd, preFs, preStdin, i))
            else if PrefixHadBlockingErrorCore(cmd, preFs, preStdin, i) then
              PrefixVisibleErrorOutputCore(cmd, preFs, preStdin, i)
            else if HadBlockingErrorPiece(cmd.inputs[i], ReadResultCore(cmd, preFs, preStdin, i)) then
              ErrorPiece(cmd.inputs[i], ReadResultCore(cmd, preFs, preStdin, i))
            else
              PrefixVisibleErrorOutputCore(cmd, preFs, preStdin, i) + ErrorPiece(cmd.inputs[i], ReadResultCore(cmd, preFs, preStdin, i))
  {
  }

  lemma PrefixHadErrorCoreStep(
    cmd: PasteSchema.PasteCmd,
    preFs: BenchWorld.FileSystem,
    preStdin: BenchWorld.Bytes,
    i: nat
  )
    requires i < |cmd.inputs|
    ensures PrefixHadErrorCore(cmd, preFs, preStdin, i + 1) ==
            (PrefixHadErrorCore(cmd, preFs, preStdin, i) || HadErrorPiece(cmd.inputs[i], ReadResultCore(cmd, preFs, preStdin, i)))
  {
  }

  lemma PrefixHadBlockingErrorCoreStep(
    cmd: PasteSchema.PasteCmd,
    preFs: BenchWorld.FileSystem,
    preStdin: BenchWorld.Bytes,
    i: nat
  )
    requires i < |cmd.inputs|
    ensures PrefixHadBlockingErrorCore(cmd, preFs, preStdin, i + 1) ==
            (PrefixHadBlockingErrorCore(cmd, preFs, preStdin, i) ||
             HadBlockingErrorPiece(cmd.inputs[i], ReadResultCore(cmd, preFs, preStdin, i)))
  {
  }

  method RunOutputFromEntriesMethod(
    cmd: PasteSchema.PasteCmd,
    delims: seq<BenchWorld.Bytes>,
    entries: seq<Entry>,
    stdinData: BenchWorld.Bytes
  )
    returns (out: BenchWorld.Bytes)
    requires |delims| > 0
    requires |entries| == |cmd.inputs|
    ensures out == RenderOutput(cmd.serial, delims, RecordDelimiter(cmd.zeroTerminated), EntriesForOutputFromEntries(cmd, entries, stdinData))
  {
    var recordDelimiter := RecordDelimiter(cmd.zeroTerminated);
    var outputEntries := EntriesForOutputFromEntries(cmd, entries, stdinData);
    out := RenderOutput(cmd.serial, delims, recordDelimiter, outputEntries);
  }

  method RunCore(raw: PasteSchema.PasteCmdRaw, io: BenchIO.IO) returns (exit: int)
    modifies io.stdinRegion, io.stdoutRegion, io.stderrRegion
    ensures CoreSummary(raw, io, exit)
    decreases *
  {
    ghost var preFs := io.fs();
    ghost var preStdin := io.stdin();
    ghost var preStdout := io.stdout();
    ghost var preStderr := io.stderr();
    var cmd := Command(raw);

    if cmd.mode == PasteSchema.ModeHelp {
      var help := Spec.HelpText();
      io.AppendStdout(help);
      exit := 0;
      assert io.stdin() == preStdin;
      assert io.stderr() == preStderr;
      assert io.stdout() == preStdout + Spec.HelpText();
      return;
    }

    if cmd.mode == PasteSchema.ModeVersion {
      var version := Spec.VersionText();
      io.AppendStdout(version);
      exit := 0;
      assert io.stdin() == preStdin;
      assert io.stderr() == preStderr;
      assert io.stdout() == preStdout + Spec.VersionText();
      return;
    }

    var delimPlan := CollapseDelimiters(cmd.delimiterText);
    match delimPlan
    case DelimsErr(stderr) =>
      io.AppendStderr(stderr);
      exit := 1;
      assert io.stdin() == preStdin;
      assert io.stdout() == preStdout;
      assert io.stderr() == preStderr + stderr;
      return;
    case DelimsOk(delims) =>
      var entries: seq<Entry> := [];
      var err: BenchWorld.Bytes := [];
      var hadError := false;
      var hadBlockingError := false;
      var recordDelimiter := RecordDelimiter(cmd.zeroTerminated);
      var stdinRead := false;
      var stdinData: BenchWorld.Bytes := [];

      var i: nat := 0;
      while i < |cmd.inputs|
        invariant 0 <= i <= |cmd.inputs|
        invariant io.stdin() == PrefixStdinCore(cmd, preStdin, i)
        invariant io.stdout() == preStdout
        invariant io.stderr() == preStderr
        invariant entries == PrefixEntriesCore(cmd, preFs, preStdin, i)
        invariant err == PrefixVisibleErrorOutputCore(cmd, preFs, preStdin, i)
        invariant hadError == PrefixHadErrorCore(cmd, preFs, preStdin, i)
        invariant hadBlockingError == PrefixHadBlockingErrorCore(cmd, preFs, preStdin, i)
        invariant stdinRead == PrefixHadStdinCore(cmd.inputs, i)
        invariant stdinData == (if stdinRead then preStdin else [])
        decreases |cmd.inputs| - i
      {
        var input := cmd.inputs[i];
        var readResult: BenchWorld.Result<BenchWorld.Bytes>;
        match input {
          case Stdin =>
            var wasStdinRead := stdinRead;
            if !wasStdinRead {
              PrefixStdinCoreNoStdinPrefix(cmd, preStdin, i);
              assert io.stdin() == preStdin;
            }
            ghost var beforeStdin := io.stdin();
            var data := io.ReadStdinAll();
            readResult := BenchWorld.Ok(data);
            PrefixStdinCoreStep(cmd, preStdin, i);
            assert beforeStdin == PrefixStdinCore(cmd, preStdin, i);
            assert IOContract.ReadStdinAllFields(beforeStdin, io.stdin(), data);
            assert data == beforeStdin;
            assert readResult == ReadResultCore(cmd, preFs, preStdin, i);
            if !wasStdinRead {
              stdinData := data;
            }
          case File(path) =>
            readResult := io.ReadFile(path);
            assert readResult == IOContract.ReadFileResultFields(preFs, path);
            assert readResult == ReadResultCore(cmd, preFs, preStdin, i);
        }

        PrefixEntriesCoreStep(cmd, preFs, preStdin, i);
        PrefixVisibleErrorOutputCoreStep(cmd, preFs, preStdin, i);
        PrefixHadErrorCoreStep(cmd, preFs, preStdin, i);
        PrefixHadBlockingErrorCoreStep(cmd, preFs, preStdin, i);
        assert readResult == ReadResultCore(cmd, preFs, preStdin, i);

        var entry := EntryForRead(readResult, recordDelimiter);
        var errorPiece := ErrorPiece(input, readResult);
        var inputHadError := HadErrorPiece(input, readResult);
        var inputHadBlockingError := HadBlockingErrorPiece(input, readResult);
        entries := entries + [entry];
        if cmd.serial {
          err := err + errorPiece;
        } else if hadBlockingError {
        } else if inputHadBlockingError {
          err := errorPiece;
        } else {
          err := err + errorPiece;
        }
        hadError := hadError || inputHadError;
        hadBlockingError := hadBlockingError || inputHadBlockingError;
        var inputIsStdin := IsStdinInput(input);
        stdinRead := stdinRead || inputIsStdin;
        i := i + 1;
      }

      var out := RunOutputFromEntriesMethod(cmd, delims, entries, stdinData);
      if (cmd.serial || !hadBlockingError) && |out| > 0 {
        io.AppendStdout(out);
      } else {
        if hadBlockingError && !cmd.serial {
          assert io.stdout() == preStdout;
          assert (if PrefixHadBlockingErrorCore(cmd, preFs, preStdin, |cmd.inputs|) && !cmd.serial then
                    []
                  else
                    RunOutputCore(cmd, preFs, preStdin, delims)) == [];
        } else {
          assert out == [];
          assert io.stdout() == preStdout + out;
        }
      }
      if |err| > 0 {
        io.AppendStderr(err);
      } else {
        assert err == [];
        assert io.stderr() == preStderr + err;
      }
      exit := if hadError then 1 else 0;
      assert entries == EntriesCore(cmd, preFs, preStdin);
      assert stdinData == StdinDataForOutputCore(cmd, preStdin);
      assert EntriesForOutputFromEntries(cmd, entries, stdinData) == EntriesForOutputCore(cmd, preFs, preStdin);
      assert out == RunOutputCore(cmd, preFs, preStdin, delims);
      assert err == PrefixVisibleErrorOutputCore(cmd, preFs, preStdin, |cmd.inputs|);
      assert hadError == PrefixHadErrorCore(cmd, preFs, preStdin, |cmd.inputs|);
      assert hadBlockingError == PrefixHadBlockingErrorCore(cmd, preFs, preStdin, |cmd.inputs|);
      assert io.stdin() == PrefixStdinCore(cmd, preStdin, |cmd.inputs|);
      assert io.stdout() == preStdout +
                          (if PrefixHadBlockingErrorCore(cmd, preFs, preStdin, |cmd.inputs|) && !cmd.serial then
                             []
                           else
                             RunOutputCore(cmd, preFs, preStdin, delims));
      assert io.stderr() == preStderr + PrefixVisibleErrorOutputCore(cmd, preFs, preStdin, |cmd.inputs|);
  }
}
