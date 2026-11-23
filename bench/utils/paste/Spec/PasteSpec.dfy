include "../../../core/World.dfy"
include "../../../core/IO.dfy"
include "../../../core/IOContract.dfy"
include "PasteSchema.dfy"
include "../../../core/StringEscaping.dfy"

module PasteSpec {

  import StreamContract = IOContract
  import StreamUtf8 = Utf8Semantics

  import Result = Results
  import BenchIO
  import Utf8 = Utf8Semantics
  import BenchWorld
  import IOContract
  import PasteSchema
  import SE = StringEscaping

  datatype Entry = Entry(lines: seq<BenchWorld.Bytes>, readOk: bool)
  type DelimiterResult = Result.Result<seq<BenchWorld.Bytes>, BenchWorld.Bytes>

  const HelpText: BenchWorld.Bytes :=
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

  const VersionText: BenchWorld.Bytes :=
    "paste (GNU coreutils) 9.10.13-2cf49\n"
    + "Copyright (C) 2026 Free Software Foundation, Inc.\n"
    + "License GPLv3+: GNU GPL version 3 or later <https://gnu.org/licenses/gpl.html>.\n"
    + "This is free software: you are free to change and redistribute it.\n"
    + "There is NO WARRANTY, to the extent permitted by law.\n"
    + "\n"
    + "Written by David M. Ihnat and David MacKenzie.\n"

  function ErrnoText(err: BenchWorld.IOError): string
  {
    match err
    case NoSuchFile => "No such file or directory"
    case IsDirectory => "Is a directory"
    case NotDirectory => "Not a directory"
    case PermissionDenied => "Permission denied"
    case InvalidPath => "Too many levels of symbolic links"
    case Other(msg) => msg
    case ReadFailure(_, message, _, _) => message
    case NativeFailure(_, message) => message
    case WriteFailure(_, message, _, _) => message
    case StreamFailure(_, message, _, _) => message
    case TimeParseFailure(message, _, _) => message
  }

  function ErrorMessage(path: BenchWorld.Path, err: BenchWorld.IOError): BenchWorld.Bytes
  {
    "paste: " + SE.SpecQuoteFBytes(Utf8.Encode(path)) +
    ": " + Utf8.Encode(ErrnoText(err)) + "\n"
  }

  function DelimiterBackslashError(text: BenchWorld.Bytes): BenchWorld.Bytes
  {
    var rendered :=
      if exists i: nat :: i < |text| &&
                          (text[i] == ':' || text[i] == '"' || !SE.SpecCPrintableByte(text[i]))
      then SE.SpecDoubleQuote(text)
      else text;
    "paste: delimiter list ends with an unescaped backslash: " + rendered + "\n"
  }

  function RecordDelimiter(zeroTerminated: bool): BenchWorld.RawByte
  {
    if zeroTerminated then '\0' else '\n'
  }

  ghost predicate LinesRelation(data: BenchWorld.Bytes, recordDelimiter: BenchWorld.RawByte,
                                lines: seq<BenchWorld.Bytes>)
  {
    if |data| == 0 then lines == []
    else
      |lines| > 0 &&
      (forall i: nat | i < |lines| :: recordDelimiter !in lines[i]) &&
      data == Join(lines, [[recordDelimiter]]) +
      (if data[|data| - 1] == recordDelimiter then [recordDelimiter] else [])
  }

  ghost function ReadInput(
    input: PasteSchema.Input,
    fs: BenchWorld.FileSystem,
    streams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult,
    stdin: BenchWorld.Bytes
  ): BenchWorld.IOResult<BenchWorld.Bytes>
  {
    match input
    case Stdin => IOContract.ObservedReadStdinResultFields(stdin, streams)
    case File(path) => IOContract.ObservedReadFileResultFields(fs, streams, path)
  }

  function BlockingReadFailure(err: BenchWorld.IOError): bool
  {
    !IOContract.IOErrorIsDirectory(err) && !err.StreamFailure? &&
    !(err.ReadFailure? && err.readStage != BenchWorld.OpenFailed)
  }

  ghost predicate EntryRelation(
    result: BenchWorld.IOResult<BenchWorld.Bytes>,
                                recordDelimiter: BenchWorld.RawByte,
                                entry: Entry
  )
  {
    entry.readOk == (result.Ok? || !BlockingReadFailure(result.e)) &&
    LinesRelation(IOContract.ReadResultData(result), recordDelimiter, entry.lines)
  }

  function InputDiagnostic(
    input: PasteSchema.Input, result: BenchWorld.IOResult<BenchWorld.Bytes>
  ): BenchWorld.Bytes
  {
    if result.Ok? then []
    else ErrorMessage(if input.Stdin? then "-" else input.path, result.e)
  }

  predicate IsBlockingInput(input: PasteSchema.Input, result: BenchWorld.IOResult<BenchWorld.Bytes>)
  {
    input.File? && result.Err? && BlockingReadFailure(result.e)
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

  predicate HasStdinInput(inputs: seq<PasteSchema.Input>)
  {
    PasteSchema.Stdin in inputs
  }

  ghost predicate EntriesForOutputRelation(
    cmd: PasteSchema.PasteCmd,
    preStdin: BenchWorld.Bytes,
    rawEntries: seq<Entry>,
    entries: seq<Entry>
  )
  {
    if cmd.serial then entries == rawEntries
    else
      |rawEntries| == |cmd.inputs| && |entries| == |cmd.inputs| &&
      exists stdinLines: seq<BenchWorld.Bytes>
        {:trigger LinesRelation(if HasStdinInput(cmd.inputs) then preStdin else [],
                                RecordDelimiter(cmd.zeroTerminated), stdinLines)} ::
        LinesRelation(if HasStdinInput(cmd.inputs) then preStdin else [],
                      RecordDelimiter(cmd.zeroTerminated), stdinLines) &&
        forall i: nat | i < |cmd.inputs| ::
          if cmd.inputs[i].Stdin? then
            entries[i].readOk && SelectedLinesRelation(stdinLines,
                                                       StdinCount(cmd.inputs[..i]), StdinCount(cmd.inputs), entries[i].lines)
          else entries[i] == rawEntries[i]
  }

  lemma FirstBlockingExists(
    inputs: seq<PasteSchema.Input>, results: seq<BenchWorld.IOResult<BenchWorld.Bytes>>
  )
    requires |inputs| == |results|
    requires exists i: nat :: i < |inputs| && IsBlockingInput(inputs[i], results[i])
    ensures exists i: nat ::
              i < |inputs| && IsBlockingInput(inputs[i], results[i]) &&
              (forall j: nat | j < i :: !IsBlockingInput(inputs[j], results[j]))
    decreases |inputs|
  {
    var n := |inputs| - 1;
    if exists i: nat :: i < n && IsBlockingInput(inputs[i], results[i]) {
      var i: nat :| i < n && IsBlockingInput(inputs[i], results[i]);
      assert IsBlockingInput(inputs[..n][i], results[..n][i]);
      FirstBlockingExists(inputs[..n], results[..n]);
    }
  }

  ghost function FirstBlocking(
    inputs: seq<PasteSchema.Input>, results: seq<BenchWorld.IOResult<BenchWorld.Bytes>>
  ): (i: nat)
    requires |inputs| == |results|
    requires exists i: nat :: i < |inputs| && IsBlockingInput(inputs[i], results[i])
    ensures i < |inputs| && IsBlockingInput(inputs[i], results[i])
    ensures forall j: nat | j < i :: !IsBlockingInput(inputs[j], results[j])
  {
    FirstBlockingExists(inputs, results);
    var i: nat :| i < |inputs| && IsBlockingInput(inputs[i], results[i]) &&
                  (forall j: nat | j < i :: !IsBlockingInput(inputs[j], results[j]));
    i
  }

  ghost function VisibleErrors(
    serial: bool, inputs: seq<PasteSchema.Input>, results: seq<BenchWorld.IOResult<BenchWorld.Bytes>>
  ): BenchWorld.Bytes
    requires |inputs| == |results|
  {
    if !serial && (exists i: nat :: i < |inputs| && IsBlockingInput(inputs[i], results[i])) then
      var i := FirstBlocking(inputs, results);
      InputDiagnostic(inputs[i], results[i])
    else
      Concat<BenchWorld.RawByte>(InputDiagnostics(inputs, results))
  }

  ghost function InputDiagnostics(
    inputs: seq<PasteSchema.Input>, results: seq<BenchWorld.IOResult<BenchWorld.Bytes>>
  ): (pieces: seq<BenchWorld.Bytes>)
    requires |inputs| == |results|
    ensures |pieces| == |inputs|
  {
    seq(|inputs|, i requires 0 <= i < |inputs| => InputDiagnostic(inputs[i], results[i]))
  }

  twostate predicate InputRelation(
    cmd: PasteSchema.PasteCmd,
    io: BenchIO.IO,
    entries: seq<Entry>,
    errorOutput: BenchWorld.Bytes,
    hadError: bool,
    hadBlockingError: bool
  )
    reads io.stdinRegion
  {
    var inputs := cmd.inputs;
    var streams := old(io.trustedStreams());
    var stdin := old(io.stdin());
    var results := ReadResults(inputs, old(io.fs()), streams, stdin);
    io.stdin() == StdinAfterReads(stdin, streams, StdinCount(inputs)) &&
    errorOutput == VisibleErrors(cmd.serial, inputs, results) &&
    hadError == (exists i: nat :: i < |inputs| && results[i].Err?) &&
    hadBlockingError == (exists i: nat :: i < |inputs| && IsBlockingInput(inputs[i], results[i])) &&
    exists rawEntries: seq<Entry> ::
      |rawEntries| == |inputs| &&
      (forall i: nat | i < |inputs| ::
         EntryRelation(results[i], RecordDelimiter(cmd.zeroTerminated), rawEntries[i])) &&
      EntriesForOutputRelation(cmd, StdinData(inputs, results), rawEntries, entries)
  }

  function StdinCount(inputs: seq<PasteSchema.Input>): nat
  {
    multiset(inputs)[PasteSchema.Stdin]
  }

  // Repeated consumption is observable when '-' occurs more than once. The
  // count is semantic input; no per-operand execution trace is required.
  ghost function StdinAfterReads(before: BenchWorld.Bytes,
                                 observations: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult,
                                 count: nat): BenchWorld.Bytes
    decreases count
  {
    if count == 0 then before
    else IOContract.ObservedReadStdinRemainingFields(
           StdinAfterReads(before, observations, count - 1), observations)
  }

  ghost function ReadResults(
    inputs: seq<PasteSchema.Input>, fs: BenchWorld.FileSystem,
    streams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult,
    stdin: BenchWorld.Bytes
  ): (results: seq<BenchWorld.IOResult<BenchWorld.Bytes>>)
    ensures |results| == |inputs|
  {
    seq(|inputs|, i requires 0 <= i < |inputs| =>
      ReadInput(inputs[i], fs, streams, StdinAfterReads(stdin, streams, StdinCount(inputs[..i]))))
  }

  ghost function StdinData(
    inputs: seq<PasteSchema.Input>, results: seq<BenchWorld.IOResult<BenchWorld.Bytes>>
  ): BenchWorld.Bytes
    requires |inputs| == |results|
  {
    Concat<BenchWorld.RawByte>(StdinPieces(inputs, results))
  }

  ghost function StdinPieces(
    inputs: seq<PasteSchema.Input>, results: seq<BenchWorld.IOResult<BenchWorld.Bytes>>
  ): (pieces: seq<BenchWorld.Bytes>)
    requires |inputs| == |results|
    ensures |pieces| == |inputs|
  {
    seq(|inputs|, i requires 0 <= i < |inputs| =>
      if inputs[i].Stdin? then IOContract.ReadResultData(results[i]) else [])
  }

  function EscapedDelimiter(ch: BenchWorld.RawByte): BenchWorld.Bytes
  {
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

  ghost predicate DelimiterCuts(text: BenchWorld.Bytes, start: nat, cuts: seq<nat>)
  {
    start <= |text| && |cuts| > 0 && cuts[0] == start &&
    cuts[|cuts| - 1] == |text| &&
    forall k {:trigger cuts[k]} | 0 <= k < |cuts| - 1 ::
      cuts[k] < cuts[k + 1] <= |text| &&
      cuts[k + 1] == cuts[k] +
      (if text[cuts[k]] == '\\' && cuts[k] + 1 < |text| then 2 else 1)
  }

  ghost function DelimiterValue(text: BenchWorld.Bytes, cuts: seq<nat>): DelimiterResult
    requires |cuts| > 0 && DelimiterCuts(text, cuts[0], cuts)
  {
    if exists k | 0 <= k < |cuts| - 1 ::
         text[cuts[k]] == '\\' && cuts[k] + 1 == |text| then
      Result.Err(DelimiterBackslashError(text))
    else
      var delimiters: seq<BenchWorld.Bytes> := seq(|cuts| - 1, k requires 0 <= k < |cuts| - 1 =>
                                                 if text[cuts[k]] == '\\' then EscapedDelimiter(text[cuts[k] + 1])
                                                 else [text[cuts[k]]]);
      Result.Ok(delimiters)
  }

  ghost predicate DelimiterResultRelation(
    text: string,
    result: DelimiterResult
  )
  {
    if |text| == 0 then
      result == Result.Ok([[]])
    else
      exists cuts: seq<nat> ::
        DelimiterCuts(Utf8.Encode(text), 0, cuts) &&
        result == DelimiterValue(Utf8.Encode(text), cuts)
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

  // Canonical sequence concatenation, independent of a renderer's traversal.
  ghost function Concat<T>(parts: seq<seq<T>>): seq<T>
    decreases |parts|
  {
    if |parts| == 0 then [] else parts[0] + Concat(parts[1..])
  }

  ghost function Join(fields: seq<BenchWorld.Bytes>,
                      delims: seq<BenchWorld.Bytes>): BenchWorld.Bytes
    requires |delims| > 0
  {
    Concat<BenchWorld.RawByte>(seq(|fields|, i requires 0 <= i < |fields| =>
                                 fields[i] + (if i + 1 < |fields| then DelimAt(delims, i) else [])))
  }

  ghost function ParallelRow(entries: seq<Entry>, delims: seq<BenchWorld.Bytes>,
                             row: nat): BenchWorld.Bytes
    requires |delims| > 0
  {
    Join(seq(|entries|, i requires 0 <= i < |entries| =>
           if row < |entries[i].lines| then entries[i].lines[row] else []), delims)
  }

  ghost function ParallelRecords(entries: seq<Entry>, delims: seq<BenchWorld.Bytes>,
                                 recordDelimiter: BenchWorld.RawByte): seq<BenchWorld.Bytes>
    requires |delims| > 0
  {
    seq(MaxLineCount(entries), row requires 0 <= row < MaxLineCount(entries) =>
      ParallelRow(entries, delims, row) + [recordDelimiter])
  }

  ghost function SerialRecords(entries: seq<Entry>, delims: seq<BenchWorld.Bytes>,
                               recordDelimiter: BenchWorld.RawByte): seq<BenchWorld.Bytes>
    requires |delims| > 0
  {
    seq(|entries|, i requires 0 <= i < |entries| =>
      if entries[i].readOk then
        Join(entries[i].lines, delims) + [recordDelimiter]
      else [])
  }

  ghost function Output(serial: bool, delims: seq<BenchWorld.Bytes>,
                        recordDelimiter: BenchWorld.RawByte,
                        entries: seq<Entry>): BenchWorld.Bytes
    requires |delims| > 0
  {
    Concat<BenchWorld.RawByte>(if serial then SerialRecords(entries, delims, recordDelimiter)
                               else ParallelRecords(entries, delims, recordDelimiter))
  }

  twostate predicate SpecCmd(cmd: PasteSchema.PasteCmd, io: BenchIO.IO, exit: int, resultStdout: BenchWorld.Bytes, resultStderr: BenchWorld.Bytes)
    reads io.stdinRegion
  {
    if cmd.mode == PasteSchema.ModeHelp then
      io.stdin() == old(io.stdin()) &&
      resultStdout == old(io.stdout()) + HelpText &&
      resultStderr == old(io.stderr()) &&
      exit == 0
    else if cmd.mode == PasteSchema.ModeVersion then
      io.stdin() == old(io.stdin()) &&
      resultStdout == old(io.stdout()) + VersionText &&
      resultStderr == old(io.stderr()) &&
      exit == 0
    else
      exists result: DelimiterResult ::
        DelimiterResultRelation(cmd.delimiterText, result) &&
        match result
        case Err(stderr) =>
          io.stdin() == old(io.stdin()) &&
          resultStdout == old(io.stdout()) &&
          resultStderr == old(io.stderr()) + stderr &&
          exit == 1
        case Ok(delims) =>
          |delims| > 0 &&
          exists entries: seq<Entry>,
            errorOutput: BenchWorld.Bytes,
            hadError: bool,
            hadBlockingError: bool ::
            InputRelation(cmd, io, entries, errorOutput, hadError, hadBlockingError) &&
            resultStdout == old(io.stdout()) +
            (if hadBlockingError && !cmd.serial then [] else
             Output(cmd.serial, delims, RecordDelimiter(cmd.zeroTerminated), entries)) &&
            resultStderr == old(io.stderr()) + errorOutput &&
            exit == (if hadError then 1 else 0)
  }

  twostate predicate PreparedSpec(raw: PasteSchema.PasteCmdRaw, io: BenchIO.IO, exit: int, resultStdout: BenchWorld.Bytes, resultStderr: BenchWorld.Bytes)
    reads io.stdinRegion
  {
    SpecCmd(PasteSchema.Command(raw), io, exit, resultStdout, resultStderr)
  }

  function StreamWriteErrorMessage(message: string): BenchWorld.Bytes
  {
    StreamUtf8.Encode("paste: write error: " + message + "\n")
  }

  twostate predicate Emission(
    io: BenchIO.IO,
    out: BenchWorld.Bytes, diagnostics: BenchWorld.Bytes,
    normalExit: int, exit: int
  )
    reads io.stdoutRegion, io.stderrRegion
  {
    var observations := old(io.trustedStreams());
    var stdoutResult := observations(BenchWorld.StreamWriteStdout(old(io.stdout()), out));
    stdoutResult.StreamWriteResult? &&
    var errors := diagnostics + (if stdoutResult.err == 0 then [] else
                                 StreamWriteErrorMessage(StreamContract.CLocaleErrnoTextResult(stdoutResult.err)));
    var stderrResult := observations(BenchWorld.StreamWriteStderr(old(io.stderr()), errors));
    stderrResult.StreamWriteResult? &&
    StreamContract.WriteStdoutSpec(
      old(io.stdout()), observations, io.stdout(), out, stdoutResult.committed, stdoutResult.err) &&
    StreamContract.WriteStderrSpec(
      old(io.stderr()), observations, io.stderr(), errors, stderrResult.committed, stderrResult.err) &&
    exit == (if stdoutResult.err != 0 || stderrResult.err != 0 then 1 else normalExit)
  }

  twostate predicate Spec(raw: PasteSchema.PasteCmdRaw, io: BenchIO.IO, exit: int)
    reads io.stdinRegion, io.stdoutRegion, io.stderrRegion
  {
    exists out: BenchWorld.Bytes, diagnostics: BenchWorld.Bytes, normalExit: int ::
      PreparedSpec(raw, io, normalExit,
                   old(io.stdout()) + out, old(io.stderr()) + diagnostics) &&
      Emission(io, out, diagnostics, normalExit, exit)
  }
}
