include "../../../core/Utf8.dfy"
include "../Spec/PasteSpec.dfy"
include "../../../core/World.dfy"
include "../../../core/IO.dfy"
include "../../../core/IOContract.dfy"
include "../Spec/PasteSchema.dfy"

module PasteCore {
  import StreamContract = IOContract

  import Result = Results
  import BenchIO
  import Utf8 = Utf8Semantics
  import BenchWorld
  import IOContract
  import PasteSchema
  import Spec = PasteSpec

  datatype LineRead = NoLine | SomeLine(line: BenchWorld.Bytes, rest: BenchWorld.Bytes)
  type DelimiterResult = Result.Result<seq<BenchWorld.Bytes>, BenchWorld.Bytes>

  ghost function PrefixStdinCore(cmd: PasteSchema.PasteCmd, preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult, preStdin: BenchWorld.Bytes, i: nat): BenchWorld.Bytes
    requires i <= |cmd.inputs|
    decreases i
  {
    if i == 0 then
      preStdin
    else
      match cmd.inputs[i - 1]
      case Stdin => IOContract.ObservedReadStdinRemainingFields(
        PrefixStdinCore(cmd, preStreams, preStdin, i - 1), preStreams)
      case File(_) => PrefixStdinCore(cmd, preStreams, preStdin, i - 1)
  }

  ghost function ReadResultCore(
    cmd: PasteSchema.PasteCmd,
    preFs: BenchWorld.FileSystem, preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult,
    preStdin: BenchWorld.Bytes,
    i: nat
  ): BenchWorld.IOResult<BenchWorld.Bytes>
    requires i < |cmd.inputs|
  {
    match cmd.inputs[i]
    case Stdin => IOContract.ObservedReadStdinResultFields(
      PrefixStdinCore(cmd, preStreams, preStdin, i), preStreams)
    case File(path) => IOContract.ObservedReadFileResultFields(preFs, preStreams, path)
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

  function EntryForRead(result: BenchWorld.IOResult<BenchWorld.Bytes>, recordDelimiter: BenchWorld.RawByte): Spec.Entry
  {
    Spec.Entry(Lines(IOContract.ReadResultData(result), recordDelimiter),
               result.Ok? || !Spec.BlockingReadFailure(result.e))
  } by method {
    return Spec.Entry(Lines(IOContract.ReadResultData(result), recordDelimiter),
                      result.Ok? || !Spec.BlockingReadFailure(result.e));
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
    entries: seq<Spec.Entry>,
    stdinLines: seq<BenchWorld.Bytes>,
    stdinCount: nat,
    i: nat
  ): seq<Spec.Entry>
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
        case Stdin => Spec.Entry(SelectStdinLines(stdinLines, CountStdinPrefix(inputs, i), stdinCount), true)
        case File(_) => entries[i];
      [head] + ParallelEntriesFrom(inputs, entries, stdinLines, stdinCount, i + 1)
  } by method {
    if i == |inputs| {
      return [];
    } else {
      var head :=
        match inputs[i]
        case Stdin =>
          Spec.Entry(
            SelectStdinLines(stdinLines, CountStdinPrefix(inputs, i), stdinCount),
            true)
        case File(_) =>
          entries[i];
      return [head] +
        ParallelEntriesFrom(inputs, entries, stdinLines, stdinCount, i + 1);
    }
  }

  function EntriesForOutputFromEntries(cmd: PasteSchema.PasteCmd, entries: seq<Spec.Entry>, stdinData: BenchWorld.Bytes): seq<Spec.Entry>
    requires |entries| == |cmd.inputs|
  {
    if cmd.serial then
      entries
    else
      var recordDelimiter := Spec.RecordDelimiter(cmd.zeroTerminated);
      var stdinLines := Lines(stdinData, recordDelimiter);
      ParallelEntriesFrom(cmd.inputs, entries, stdinLines, CountStdinInputs(cmd.inputs), 0)
  } by method {
    if cmd.serial {
      return entries;
    } else {
      var recordDelimiter := Spec.RecordDelimiter(cmd.zeroTerminated);
      var stdinLines := Lines(stdinData, recordDelimiter);
      return ParallelEntriesFrom(
          cmd.inputs, entries, stdinLines, CountStdinInputs(cmd.inputs), 0);
    }
  }

  ghost function StdinDataPrefixCore(cmd: PasteSchema.PasteCmd,
                                     preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult,
                                     preStdin: BenchWorld.Bytes, i: nat): BenchWorld.Bytes
    requires i <= |cmd.inputs|
    decreases i
  {
    if i == 0 then [] else
    StdinDataPrefixCore(cmd, preStreams, preStdin, i - 1) +
    (if cmd.inputs[i - 1].Stdin? then IOContract.ReadResultData(
                                        IOContract.ObservedReadStdinResultFields(
                                          PrefixStdinCore(cmd, preStreams, preStdin, i - 1), preStreams)) else [])
  }

  ghost function StdinDataForOutputCore(cmd: PasteSchema.PasteCmd,
                                        preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult,
                                        preStdin: BenchWorld.Bytes): BenchWorld.Bytes
  {
    StdinDataPrefixCore(cmd, preStreams, preStdin, |cmd.inputs|)
  }

  function ErrorPiece(input: PasteSchema.Input, result: BenchWorld.IOResult<BenchWorld.Bytes>): BenchWorld.Bytes
  {
    match input
    case Stdin => if result.Ok? then [] else Spec.ErrorMessage("-", result.e)
    case File(path) =>
      match result
      case Ok(_) => []
      case Err(err) => Spec.ErrorMessage(path, err)
  } by method {
    return
      match input
      case Stdin => if result.Ok? then [] else Spec.ErrorMessage("-", result.e)
      case File(path) =>
        match result
        case Ok(_) => []
        case Err(err) => Spec.ErrorMessage(path, err);
  }

  function HadErrorPiece(input: PasteSchema.Input, result: BenchWorld.IOResult<BenchWorld.Bytes>): bool
  {
    result.Err?
  } by method {
    return result.Err?;
  }

  function HadBlockingErrorPiece(input: PasteSchema.Input, result: BenchWorld.IOResult<BenchWorld.Bytes>): bool
  {
    match input
    case Stdin => false
    case File(_) =>
      match result
      case Ok(_) => false
      case Err(err) =>
        Spec.BlockingReadFailure(err)
  } by method {
    return
      match input
      case Stdin => false
      case File(_) =>
        match result
        case Ok(_) => false
        case Err(err) =>
          Spec.BlockingReadFailure(err);
  }

  ghost function PrefixEntriesCore(
    cmd: PasteSchema.PasteCmd,
    preFs: BenchWorld.FileSystem, preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult,
    preStdin: BenchWorld.Bytes,
    i: nat
  ): seq<Spec.Entry>
    requires i <= |cmd.inputs|
    ensures |PrefixEntriesCore(cmd, preFs, preStreams, preStdin, i)| == i
    decreases i
  {
    if i == 0 then
      []
    else
      PrefixEntriesCore(cmd, preFs, preStreams, preStdin, i - 1) +
      [EntryForRead(ReadResultCore(cmd, preFs, preStreams, preStdin, i - 1), Spec.RecordDelimiter(cmd.zeroTerminated))]
  }

  ghost function EntriesCore(
    cmd: PasteSchema.PasteCmd,
    preFs: BenchWorld.FileSystem, preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult,
    preStdin: BenchWorld.Bytes
  ): seq<Spec.Entry>
  {
    PrefixEntriesCore(cmd, preFs, preStreams, preStdin, |cmd.inputs|)
  }

  ghost function PrefixVisibleErrorOutputCore(
    cmd: PasteSchema.PasteCmd,
    preFs: BenchWorld.FileSystem, preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult,
    preStdin: BenchWorld.Bytes,
    i: nat
  ): BenchWorld.Bytes
    requires i <= |cmd.inputs|
    decreases i
  {
    if i == 0 then
      []
    else
      var previous := PrefixVisibleErrorOutputCore(cmd, preFs, preStreams, preStdin, i - 1);
      if cmd.serial then
        previous + ErrorPiece(cmd.inputs[i - 1], ReadResultCore(cmd, preFs, preStreams, preStdin, i - 1))
      else if PrefixHadBlockingErrorCore(cmd, preFs, preStreams, preStdin, i - 1) then
        previous
      else if HadBlockingErrorPiece(cmd.inputs[i - 1], ReadResultCore(cmd, preFs, preStreams, preStdin, i - 1)) then
        ErrorPiece(cmd.inputs[i - 1], ReadResultCore(cmd, preFs, preStreams, preStdin, i - 1))
      else
        previous + ErrorPiece(cmd.inputs[i - 1], ReadResultCore(cmd, preFs, preStreams, preStdin, i - 1))
  }

  ghost function PrefixHadErrorCore(
    cmd: PasteSchema.PasteCmd,
    preFs: BenchWorld.FileSystem, preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult,
    preStdin: BenchWorld.Bytes,
    i: nat
  ): bool
    requires i <= |cmd.inputs|
    decreases i
  {
    if i == 0 then
      false
    else
      PrefixHadErrorCore(cmd, preFs, preStreams, preStdin, i - 1) ||
      HadErrorPiece(cmd.inputs[i - 1], ReadResultCore(cmd, preFs, preStreams, preStdin, i - 1))
  }

  ghost function PrefixHadBlockingErrorCore(
    cmd: PasteSchema.PasteCmd,
    preFs: BenchWorld.FileSystem, preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult,
    preStdin: BenchWorld.Bytes,
    i: nat
  ): bool
    requires i <= |cmd.inputs|
    decreases i
  {
    if i == 0 then
      false
    else
      PrefixHadBlockingErrorCore(cmd, preFs, preStreams, preStdin, i - 1) ||
      HadBlockingErrorPiece(cmd.inputs[i - 1], ReadResultCore(cmd, preFs, preStreams, preStdin, i - 1))
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

  function CollapseDelimitersFrom(text: BenchWorld.Bytes, i: nat): DelimiterResult
    requires i <= |text|
    decreases |text| - i
  {
    if i >= |text| then
      Result.Ok([])
    else if text[i] == '\\' then
      if i + 1 >= |text| then
        Result.Err(Spec.DelimiterBackslashError(text))
      else
        match CollapseDelimitersFrom(text, i + 2)
        case Err(stderr) => Result.Err(stderr)
        case Ok(rest) => Result.Ok([EscapeDelimiter(text[i + 1])] + rest)
    else
      match CollapseDelimitersFrom(text, i + 1)
      case Err(stderr) => Result.Err(stderr)
      case Ok(rest) => Result.Ok([[text[i]]] + rest)
  } by method {
    if i >= |text| {
      return Result.Ok([]);
    } else if text[i] == '\\' {
      if i + 1 >= |text| {
        return Result.Err(Spec.DelimiterBackslashError(text));
      } else {
        match CollapseDelimitersFrom(text, i + 2)
        case Err(stderr) =>
          return Result.Err(stderr);
        case Ok(delims) =>
          return Result.Ok([EscapeDelimiter(text[i + 1])] + delims);
      }
    } else {
      match CollapseDelimitersFrom(text, i + 1)
      case Err(stderr) =>
        return Result.Err(stderr);
      case Ok(delims) =>
        return Result.Ok([[text[i]]] + delims);
    }
  }

  function CollapseDelimiters(text: string): DelimiterResult
  {
    if |text| == 0 then
      Result.Ok([[]])
    else
      CollapseDelimitersFrom(Utf8.Encode(text), 0)
  } by method {
    return
      if |text| == 0 then Result.Ok([[]])
      else CollapseDelimitersFrom(Utf8.Encode(text), 0);
  }

  function RenderParallelRow(entries: seq<Spec.Entry>, delims: seq<BenchWorld.Bytes>, row: nat, i: nat, last: nat): BenchWorld.Bytes
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
      (if i < last then Spec.DelimAt(delims, i) else []) +
      RenderParallelRow(entries, delims, row, i + 1, last)
  } by method {
    if i > last {
      return [];
    } else {
      var field := if row < |entries[i].lines| then entries[i].lines[row] else [];
      var delimiter := if i < last then Spec.DelimAt(delims, i) else [];
      return field + delimiter +
        RenderParallelRow(entries, delims, row, i + 1, last);
    }
  }

  function RenderParallelRows(entries: seq<Spec.Entry>, delims: seq<BenchWorld.Bytes>, recordDelimiter: BenchWorld.RawByte, row: nat, limit: nat): BenchWorld.Bytes
    requires |delims| > 0
    requires row <= limit
    requires limit == Spec.MaxLineCount(entries)
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

  function RenderParallel(entries: seq<Spec.Entry>, delims: seq<BenchWorld.Bytes>, recordDelimiter: BenchWorld.RawByte): BenchWorld.Bytes
    requires |delims| > 0
  {
    RenderParallelRows(entries, delims, recordDelimiter, 0, Spec.MaxLineCount(entries))
  } by method {
    return RenderParallelRows(
        entries, delims, recordDelimiter, 0, Spec.MaxLineCount(entries));
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
      (if i + 1 < |lines| then Spec.DelimAt(delims, i) else []) +
      JoinLines(lines, delims, i + 1)
  } by method {
    if i >= |lines| {
      return [];
    } else {
      var delimiter := if i + 1 < |lines| then Spec.DelimAt(delims, i) else [];
      return lines[i] + delimiter + JoinLines(lines, delims, i + 1);
    }
  }

  function RenderSerial(entries: seq<Spec.Entry>, delims: seq<BenchWorld.Bytes>, recordDelimiter: BenchWorld.RawByte): BenchWorld.Bytes
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

  function RenderOutput(serial: bool, delims: seq<BenchWorld.Bytes>, recordDelimiter: BenchWorld.RawByte, entries: seq<Spec.Entry>): BenchWorld.Bytes
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
    preFs: BenchWorld.FileSystem, preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult,
    preStdin: BenchWorld.Bytes
  ): seq<Spec.Entry>
  {
    EntriesForOutputFromEntries(cmd, EntriesCore(cmd, preFs, preStreams, preStdin), StdinDataForOutputCore(cmd, preStreams, preStdin))
  }

  ghost function RunOutputCore(
    cmd: PasteSchema.PasteCmd,
    preFs: BenchWorld.FileSystem, preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult,
    preStdin: BenchWorld.Bytes,
    delims: seq<BenchWorld.Bytes>
  ): BenchWorld.Bytes
    requires |delims| > 0
  {
    RenderOutput(cmd.serial, delims, Spec.RecordDelimiter(cmd.zeroTerminated), EntriesForOutputCore(cmd, preFs, preStreams, preStdin))
  }

  twostate predicate CoreSummaryCmd(cmd: PasteSchema.PasteCmd, io: BenchIO.IO, exit: int, resultStdout: BenchWorld.Bytes, resultStderr: BenchWorld.Bytes)
    reads io.Footprint() - {io.stdoutRegion, io.stderrRegion}
  {
    if cmd.mode == PasteSchema.ModeHelp then
      io.stdin() == old(io.stdin()) &&
      resultStdout == old(io.stdout()) + Spec.HelpText() &&
      resultStderr == old(io.stderr()) &&
      exit == 0
    else if cmd.mode == PasteSchema.ModeVersion then
      io.stdin() == old(io.stdin()) &&
      resultStdout == old(io.stdout()) + Spec.VersionText() &&
      resultStderr == old(io.stderr()) &&
      exit == 0
    else
      match CollapseDelimiters(cmd.delimiterText)
      case Err(stderr) =>
        io.stdin() == old(io.stdin()) &&
        resultStdout == old(io.stdout()) &&
        resultStderr == old(io.stderr()) + stderr &&
        exit == 1
      case Ok(delims) =>
        io.stdin() == PrefixStdinCore(cmd, old(io.trustedStreams()), old(io.stdin()), |cmd.inputs|) &&
        resultStdout == old(io.stdout()) +
        (if PrefixHadBlockingErrorCore(cmd, old(io.fs()), old(io.trustedStreams()), old(io.stdin()), |cmd.inputs|) && !cmd.serial then
           []
         else
           RunOutputCore(cmd, old(io.fs()), old(io.trustedStreams()), old(io.stdin()), delims)) &&
        resultStderr == old(io.stderr()) + PrefixVisibleErrorOutputCore(cmd, old(io.fs()), old(io.trustedStreams()), old(io.stdin()), |cmd.inputs|) &&
        exit == (if PrefixHadErrorCore(cmd, old(io.fs()), old(io.trustedStreams()), old(io.stdin()), |cmd.inputs|) then 1 else 0)
  }

  twostate predicate PreparedSummary(raw: PasteSchema.PasteCmdRaw, io: BenchIO.IO, exit: int, resultStdout: BenchWorld.Bytes, resultStderr: BenchWorld.Bytes)
    reads io.Footprint() - {
            io.stdoutRegion, io.stderrRegion}
  {
    CoreSummaryCmd(PasteSchema.Command(raw), io, exit, resultStdout, resultStderr)
  }

  lemma StdinDataPrefixCoreStep(cmd: PasteSchema.PasteCmd,
                                preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult,
                                preStdin: BenchWorld.Bytes, i: nat)
    requires i < |cmd.inputs|
    ensures StdinDataPrefixCore(cmd, preStreams, preStdin, i + 1) ==
            StdinDataPrefixCore(cmd, preStreams, preStdin, i) +
            (if cmd.inputs[i].Stdin? then IOContract.ReadResultData(
                                            IOContract.ObservedReadStdinResultFields(
                                              PrefixStdinCore(cmd, preStreams, preStdin, i), preStreams)) else [])
  {
  }

  lemma PrefixStdinCoreStep(cmd: PasteSchema.PasteCmd, preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult, preStdin: BenchWorld.Bytes, i: nat)
    requires i < |cmd.inputs|
    ensures PrefixStdinCore(cmd, preStreams, preStdin, i + 1) ==
            match cmd.inputs[i]
            case Stdin => IOContract.ObservedReadStdinRemainingFields(PrefixStdinCore(cmd, preStreams, preStdin, i), preStreams)
            case File(_) => PrefixStdinCore(cmd, preStreams, preStdin, i)
  {
  }

  lemma PrefixStdinCoreNoStdinPrefix(cmd: PasteSchema.PasteCmd, preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult, preStdin: BenchWorld.Bytes, i: nat)
    requires i <= |cmd.inputs|
    requires !PrefixHadStdinCore(cmd.inputs, i)
    ensures PrefixStdinCore(cmd, preStreams, preStdin, i) == preStdin
    decreases i
  {
    if i > 0 {
      PrefixStdinCoreNoStdinPrefix(cmd, preStreams, preStdin, i - 1);
    }
  }

  lemma PrefixEntriesCoreStep(
    cmd: PasteSchema.PasteCmd,
    preFs: BenchWorld.FileSystem, preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult,
    preStdin: BenchWorld.Bytes,
    i: nat
  )
    requires i < |cmd.inputs|
    ensures PrefixEntriesCore(cmd, preFs, preStreams, preStdin, i + 1) ==
            PrefixEntriesCore(cmd, preFs, preStreams, preStdin, i) +
            [EntryForRead(ReadResultCore(cmd, preFs, preStreams, preStdin, i), Spec.RecordDelimiter(cmd.zeroTerminated))]
  {
  }

  lemma PrefixVisibleErrorOutputCoreStep(
    cmd: PasteSchema.PasteCmd,
    preFs: BenchWorld.FileSystem, preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult,
    preStdin: BenchWorld.Bytes,
    i: nat
  )
    requires i < |cmd.inputs|
    ensures PrefixVisibleErrorOutputCore(cmd, preFs, preStreams, preStdin, i + 1) ==
            if cmd.serial then
              PrefixVisibleErrorOutputCore(cmd, preFs, preStreams, preStdin, i) + ErrorPiece(cmd.inputs[i], ReadResultCore(cmd, preFs, preStreams, preStdin, i))
            else if PrefixHadBlockingErrorCore(cmd, preFs, preStreams, preStdin, i) then
              PrefixVisibleErrorOutputCore(cmd, preFs, preStreams, preStdin, i)
            else if HadBlockingErrorPiece(cmd.inputs[i], ReadResultCore(cmd, preFs, preStreams, preStdin, i)) then
              ErrorPiece(cmd.inputs[i], ReadResultCore(cmd, preFs, preStreams, preStdin, i))
            else
              PrefixVisibleErrorOutputCore(cmd, preFs, preStreams, preStdin, i) + ErrorPiece(cmd.inputs[i], ReadResultCore(cmd, preFs, preStreams, preStdin, i))
  {
  }

  lemma PrefixHadErrorCoreStep(
    cmd: PasteSchema.PasteCmd,
    preFs: BenchWorld.FileSystem, preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult,
    preStdin: BenchWorld.Bytes,
    i: nat
  )
    requires i < |cmd.inputs|
    ensures PrefixHadErrorCore(cmd, preFs, preStreams, preStdin, i + 1) ==
            (PrefixHadErrorCore(cmd, preFs, preStreams, preStdin, i) || HadErrorPiece(cmd.inputs[i], ReadResultCore(cmd, preFs, preStreams, preStdin, i)))
  {
  }

  lemma PrefixHadBlockingErrorCoreStep(
    cmd: PasteSchema.PasteCmd,
    preFs: BenchWorld.FileSystem, preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult,
    preStdin: BenchWorld.Bytes,
    i: nat
  )
    requires i < |cmd.inputs|
    ensures PrefixHadBlockingErrorCore(cmd, preFs, preStreams, preStdin, i + 1) ==
            (PrefixHadBlockingErrorCore(cmd, preFs, preStreams, preStdin, i) ||
             HadBlockingErrorPiece(cmd.inputs[i], ReadResultCore(cmd, preFs, preStreams, preStdin, i)))
  {
  }

  method RunOutputFromEntriesMethod(
    cmd: PasteSchema.PasteCmd,
    delims: seq<BenchWorld.Bytes>,
    entries: seq<Spec.Entry>,
    stdinData: BenchWorld.Bytes
  )
    returns (out: BenchWorld.Bytes)
    requires |delims| > 0
    requires |entries| == |cmd.inputs|
    ensures out == RenderOutput(cmd.serial, delims, Spec.RecordDelimiter(cmd.zeroTerminated), EntriesForOutputFromEntries(cmd, entries, stdinData))
  {
    var recordDelimiter := Spec.RecordDelimiter(cmd.zeroTerminated);
    var outputEntries := EntriesForOutputFromEntries(cmd, entries, stdinData);
    out := RenderOutput(cmd.serial, delims, recordDelimiter, outputEntries);
  }

  method Prepare(raw: PasteSchema.PasteCmdRaw, io: BenchIO.IO) returns (exit: int, resultOut: BenchWorld.Bytes, resultErr: BenchWorld.Bytes)
    modifies io.stdinRegion
    ensures PreparedSummary(raw, io, exit, old(io.stdout()) + resultOut, old(io.stderr()) + resultErr)
    decreases *
  {
    resultOut := [];
    resultErr := [];
    ghost var initialStdout := io.stdout();
    ghost var initialStderr := io.stderr();

    ghost var preFs := io.fs();
    ghost var preStreams := io.trustedStreams();
    ghost var preStdin := io.stdin();
    ghost var preStdout := (initialStdout + resultOut);
    ghost var preStderr := (initialStderr + resultErr);
    var cmd := PasteSchema.Command(raw);
    hide PasteSchema.Command();
    hide PrefixStdinCore();

    if cmd.mode == PasteSchema.ModeHelp {
      var help := Spec.HelpText();
      resultOut := resultOut + help;
      exit := 0;
      assert io.stdin() == preStdin;
      assert (initialStderr + resultErr) == preStderr;
      assert (initialStdout + resultOut) == preStdout + Spec.HelpText();
      assert PreparedSummary(raw, io, exit, old(io.stdout()) + resultOut, old(io.stderr()) + resultErr) by {
        hide *;
        reveal PreparedSummary(), CoreSummaryCmd();
      }
      return;
    }

    if cmd.mode == PasteSchema.ModeVersion {
      var version := Spec.VersionText();
      resultOut := resultOut + version;
      exit := 0;
      assert io.stdin() == preStdin;
      assert (initialStderr + resultErr) == preStderr;
      assert (initialStdout + resultOut) == preStdout + Spec.VersionText();
      assert PreparedSummary(raw, io, exit, old(io.stdout()) + resultOut, old(io.stderr()) + resultErr) by {
        hide *;
        reveal PreparedSummary(), CoreSummaryCmd();
      }
      return;
    }

    var delimiterResult := CollapseDelimiters(cmd.delimiterText);
    match delimiterResult
    case Err(stderr) =>
      resultErr := resultErr + stderr;
      exit := 1;
      assert io.stdin() == preStdin;
      assert (initialStdout + resultOut) == preStdout;
      assert (initialStderr + resultErr) == preStderr + stderr;
      return;
    case Ok(delims) =>
      var entries: seq<Spec.Entry> := [];
      var err: BenchWorld.Bytes := [];
      var hadError := false;
      var hadBlockingError := false;
      var recordDelimiter := Spec.RecordDelimiter(cmd.zeroTerminated);
      var stdinData: BenchWorld.Bytes := [];

      var i: nat := 0;
      assert io.stdin() == PrefixStdinCore(cmd, preStreams, preStdin, i) by {
        hide *;
        reveal PrefixStdinCore();
      }
      assert stdinData == StdinDataPrefixCore(cmd, preStreams, preStdin, i) by {
        hide *;
        reveal StdinDataPrefixCore();
      }
      while i < |cmd.inputs|
        invariant 0 <= i <= |cmd.inputs|
        invariant io.stdin() == PrefixStdinCore(cmd, preStreams, preStdin, i)
        invariant (initialStdout + resultOut) == preStdout
        invariant (initialStderr + resultErr) == preStderr
        invariant |entries| == i
        invariant entries == PrefixEntriesCore(cmd, preFs, preStreams, preStdin, i)
        invariant err == PrefixVisibleErrorOutputCore(cmd, preFs, preStreams, preStdin, i)
        invariant hadError == PrefixHadErrorCore(cmd, preFs, preStreams, preStdin, i)
        invariant hadBlockingError == PrefixHadBlockingErrorCore(cmd, preFs, preStreams, preStdin, i)
        invariant stdinData == StdinDataPrefixCore(cmd, preStreams, preStdin, i)
        decreases |cmd.inputs| - i
      {
        var input := cmd.inputs[i];
        var readResult: BenchWorld.IOResult<BenchWorld.Bytes>;
        PrefixStdinCoreStep(cmd, preStreams, preStdin, i);
        StdinDataPrefixCoreStep(cmd, preStreams, preStdin, i);
        match input {
          case Stdin =>
            ghost var beforeStdin := io.stdin();
            readResult := io.ReadStdin();
            assert readResult == ReadResultCore(cmd, preFs, preStreams, preStdin, i);
            stdinData := stdinData + IOContract.ReadResultData(readResult);
          case File(path) =>
            readResult := io.ReadFile(path);
            assert readResult == IOContract.ObservedReadFileResultFields(preFs, preStreams, path);
            assert readResult == ReadResultCore(cmd, preFs, preStreams, preStdin, i);
        }
        assert io.stdin() == PrefixStdinCore(cmd, preStreams, preStdin, i + 1) by {
          hide *;
        }
        assert stdinData == StdinDataPrefixCore(cmd, preStreams, preStdin, i + 1) by {
          hide *;
          reveal ReadResultCore();
        }

        PrefixEntriesCoreStep(cmd, preFs, preStreams, preStdin, i);
        PrefixVisibleErrorOutputCoreStep(cmd, preFs, preStreams, preStdin, i);
        PrefixHadErrorCoreStep(cmd, preFs, preStreams, preStdin, i);
        PrefixHadBlockingErrorCoreStep(cmd, preFs, preStreams, preStdin, i);
        assert readResult == ReadResultCore(cmd, preFs, preStreams, preStdin, i);

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
        i := i + 1;
        assert io.stdin() == PrefixStdinCore(cmd, preStreams, preStdin, i) by {
          hide *;
        }
      }

      var out := RunOutputFromEntriesMethod(cmd, delims, entries, stdinData);
      if (cmd.serial || !hadBlockingError) && |out| > 0 {
        resultOut := resultOut + out;
      } else {
        if hadBlockingError && !cmd.serial {
          assert (initialStdout + resultOut) == preStdout;
          assert (if PrefixHadBlockingErrorCore(cmd, preFs, preStreams, preStdin, |cmd.inputs|) && !cmd.serial then
                    []
                  else
                    RunOutputCore(cmd, preFs, preStreams, preStdin, delims)) == [];
        } else {
          assert out == [];
          assert (initialStdout + resultOut) == preStdout + out;
        }
      }
      if |err| > 0 {
        resultErr := resultErr + err;
      } else {
        assert err == [];
        assert (initialStderr + resultErr) == preStderr + err;
      }
      exit := if hadError then 1 else 0;
      assert entries == EntriesCore(cmd, preFs, preStreams, preStdin);
      assert stdinData == StdinDataForOutputCore(cmd, preStreams, preStdin);
      assert EntriesForOutputFromEntries(cmd, entries, stdinData) == EntriesForOutputCore(cmd, preFs, preStreams, preStdin);
      assert out == RunOutputCore(cmd, preFs, preStreams, preStdin, delims);
      assert err == PrefixVisibleErrorOutputCore(cmd, preFs, preStreams, preStdin, |cmd.inputs|);
      assert hadError == PrefixHadErrorCore(cmd, preFs, preStreams, preStdin, |cmd.inputs|);
      assert hadBlockingError == PrefixHadBlockingErrorCore(cmd, preFs, preStreams, preStdin, |cmd.inputs|);
      assert io.stdin() == PrefixStdinCore(cmd, preStreams, preStdin, |cmd.inputs|);
      assert (initialStdout + resultOut) == preStdout +
                                            (if PrefixHadBlockingErrorCore(cmd, preFs, preStreams, preStdin, |cmd.inputs|) && !cmd.serial then
                                               []
                                             else
                                               RunOutputCore(cmd, preFs, preStreams, preStdin, delims)) by {
        hide *;
      }
      assert (initialStderr + resultErr) == preStderr + PrefixVisibleErrorOutputCore(cmd, preFs, preStreams, preStdin, |cmd.inputs|) by {
        hide *;
      }
      assert PreparedSummary(raw, io, exit, old(io.stdout()) + resultOut, old(io.stderr()) + resultErr) by {
        hide *;
        reveal PreparedSummary(), CoreSummaryCmd();
      }
  }

  twostate predicate CoreSummary(raw: PasteSchema.PasteCmdRaw, io: BenchIO.IO, exit: int)
    reads io.Footprint()
  {
    exists out: BenchWorld.Bytes, diagnostics: BenchWorld.Bytes, normalExit: int ::
      PreparedSummary(raw, io, normalExit,
                      old(io.stdout()) + out, old(io.stderr()) + diagnostics) &&
      Spec.Emission(io, out, diagnostics, normalExit, exit)
  }

  method Flush(io: BenchIO.IO, out: BenchWorld.Bytes,
               diagnostics: BenchWorld.Bytes, normalExit: int) returns (exit: int)
    modifies io.stdoutRegion, io.stderrRegion
    ensures Spec.EmitFields(old(io.trustedStreams()), old(io.stdout()), old(io.stderr()),
                            io.stdout(), io.stderr(), out, diagnostics, normalExit, exit)
  {
    var written := io.WriteStdout(out);
    var outErr := StreamContract.ResultErrno(written);
    var errors := diagnostics;
    if outErr != 0 {
      var message := io.GetCLocaleErrnoText(outErr);
      errors := errors + Spec.StreamWriteErrorMessage(message);
    }
    assert errors == diagnostics + (if outErr == 0 then [] else
                                    Spec.StreamWriteErrorMessage(StreamContract.CLocaleErrnoTextResult(outErr)));
    var diagnosed := io.WriteStderr(errors);
    assert StreamContract.WriteStderrSpec(old(io.stderr()), io.trustedStreams(), io.stderr(),
                                          errors, StreamContract.WriteResultCommitted(diagnosed), StreamContract.ResultErrno(diagnosed));
    exit := if outErr != 0 || StreamContract.ResultErrno(diagnosed) != 0 then 1 else normalExit;
  }

  method RunCore(raw: PasteSchema.PasteCmdRaw, io: BenchIO.IO) returns (exit: int)
    modifies io.stdinRegion, io.stdoutRegion, io.stderrRegion
    ensures CoreSummary(raw, io, exit)
    decreases *
  {
    var normalExit, out, diagnostics := Prepare(raw, io);

    assert PreparedSummary(raw, io, normalExit, old(io.stdout()) + out, old(io.stderr()) + diagnostics);
    exit := Flush(io, out, diagnostics, normalExit);
    assert PreparedSummary(raw, io, normalExit, old(io.stdout()) + out, old(io.stderr()) + diagnostics);
    assert Spec.Emission(io, out, diagnostics, normalExit, exit);
  }
}
