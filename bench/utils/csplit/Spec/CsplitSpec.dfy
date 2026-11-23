include "../../../core/Errno.dfy"
include "../../../core/World.dfy"
include "../../../core/IO.dfy"
include "../../../core/IOContract.dfy"
include "../../../core/StringEscaping.dfy"
include "CsplitSchema.dfy"

module CsplitSpec {
  import StreamContract = IOContract
  import StreamUtf8 = Utf8Semantics

  import Errno = Errnos
  import Result = Results
  import BenchIO
  import Utf8 = Utf8Semantics
  import BenchWorld
  import IOContract
  import Schema = CsplitSchema
  import SE = StringEscaping

  datatype NumberStatus = NumbersOk | NumberZero | NumberBackwards(current: nat, previous: nat)
  datatype SplitPlan = SplitComplete(pieces: seq<BenchWorld.Bytes>) |
                       SplitOutOfRange(pieces: seq<BenchWorld.Bytes>, line: nat)

  datatype ObservationContext = ObservationContext(
    props: map<string, string>,
    now: int,
    credentials: BenchWorld.ProcessCredentials,
    filesystem: (BenchWorld.TrustedFilesystemRequest) -> BenchWorld.TrustedFilesystemResult,
    failures: (BenchWorld.NativeFailureRequest) -> int)

  /** Captures the environment and trusted observations used by filesystem operations. */
  ghost function Context(io: BenchIO.IO): (observations: ObservationContext)
    reads io.propsRegion, io.nowRegion, io.credentialsRegion,
          io.trustedFilesystemRegion, io.trustedNativeFailuresRegion
    ensures observations == ObservationContext(io.props(), io.now(), io.credentials(),
                                               io.trustedFilesystem(), io.trustedNativeFailures())
  {
    ObservationContext(io.props(), io.now(), io.credentials(),
                       io.trustedFilesystem(), io.trustedNativeFailures())
  }

  /** Returns the help text for the supported numeric-pattern csplit commands. */
  function HelpText(): BenchWorld.Bytes
  {
    "Usage: csplit [OPTION]... FILE PATTERN...\n"
    + "Output pieces of FILE separated by PATTERN(s) to files 'xx00', 'xx01', ...\n"
    + "\n"
    + "This benchmark slice supports positive numeric line-number patterns only.\n"
    + "With FILE as -, read standard input.  Each numeric pattern N starts the\n"
    + "next output file at line N.  Byte counts are printed after successful\n"
    + "output file creation.\n"
    + "\n"
    + "      --help     display this help and exit\n"
    + "      --version  output version information and exit\n"
  }

  /** Returns the csplit version and copyright text. */
  function VersionText(): BenchWorld.Bytes
  {
    "csplit (GNU coreutils) 9.10.13-2cf49\n"
    + "Copyright (C) 2026 Free Software Foundation, Inc.\n"
    + "License GPLv3+: GNU GPL version 3 or later <https://gnu.org/licenses/gpl.html>.\n"
    + "This is free software: you are free to change and redistribute it.\n"
    + "There is NO WARRANTY, to the extent permitted by law.\n"
    + "\n"
    + "Written by Stuart Kemp and David MacKenzie.\n"
  }

  /** Returns the diagnostic text for an input error. */
  function ReadErrnoText(err: BenchWorld.IOError): string
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

  /** Returns the diagnostic text for a supported write errno. */
  function WriteErrnoText(err: int): string
  {
    if err == Errno.ENOENT then "No such file or directory"
    else if err == Errno.EACCES then "Permission denied"
    else if err == Errno.ENOTDIR then "Not a directory"
    else if err == Errno.EISDIR then "Is a directory"
    else if err == Errno.EFBIG then "File too large"
    else if err == Errno.ENOSPC then "No space left on device"
    else if err == Errno.ELOOP then "Too many levels of symbolic links"
    else "unknown error"
  }

  /** Formats a stdin read error or a named input file open error. */
  function ReadErrorMessage(input: Schema.Input, err: BenchWorld.IOError): BenchWorld.Bytes
  {
    match input
    case Stdin => "csplit: read error: " + Utf8.Encode(ReadErrnoText(err)) + "\n"
    case File(path) =>
      "csplit: cannot open " + SE.SpecQuoteAfBytes(Utf8.Encode(path)) +
      " for reading: " + Utf8.Encode(ReadErrnoText(err)) + "\n"
  }

  /** Formats an output file error with its path and errno text. */
  function WriteErrorMessage(path: BenchWorld.Path, err: int): BenchWorld.Bytes
  {
    "csplit: " + SE.SpecQuoteFBytes(Utf8.Encode(path)) +
    ": " + Utf8.Encode(WriteErrnoText(err)) + "\n"
  }

  /** Formats the error for a zero line-number pattern. */
  function ZeroLineMessage(line: nat): BenchWorld.Bytes
  {
    "csplit: " + Schema.DigitsNat(line) + ": line number must be greater than zero\n"
  }

  /** Formats the error for a line number smaller than its predecessor. */
  function BackwardLineMessage(current: nat, previous: nat): BenchWorld.Bytes
  {
    "csplit: line number '" + Schema.DigitsNat(current) + "' is smaller than preceding line number, " +
    Schema.DigitsNat(previous) + "\n"
  }

  /** Formats the error for a line-number pattern beyond the input. */
  function OutOfRangeMessage(line: nat): BenchWorld.Bytes
  {
    "csplit: '" + Schema.DigitsNat(line) + "': line number out of range\n"
  }

  /** Formats the warning for consecutive equal line-number patterns. */
  function DuplicateWarning(line: nat): BenchWorld.Bytes
  {
    "csplit: warning: line number '" + Schema.DigitsNat(line) + "' is the same as preceding line number\n"
  }

  /** Formats an output piece's byte count followed by a newline. */
  function CountLine(n: nat): BenchWorld.Bytes
  {
    Schema.DigitsNat(n) + "\n"
  }

  /** Returns the xx-prefixed output name with at least two decimal digits. */
  function OutputName(index: nat): BenchWorld.Path
  {
    if index < 10 then
      "xx0" + Schema.DigitsNat(index)
    else
      "xx" + Schema.DigitsNat(index)
  }

  /** Requires the first count line-number patterns to be positive and nondecreasing. */
  ghost predicate ValidNumberPrefix(lines: seq<nat>, count: nat)
  {
    count <= |lines| &&
    forall i :: 0 <= i < count ==>
                  lines[i] > 0 &&
                  (i == 0 || lines[i - 1] <= lines[i])
  }

  /** Relates the valid numeric prefix to success or the first invalid line number. */
  ghost predicate NumberStatusAtRelation(
    lines: seq<nat>,
    status: NumberStatus,
    processed: nat
  )
  {
    processed <= |lines| &&
    ValidNumberPrefix(lines, processed) &&
    match status
    case NumbersOk =>
      processed == |lines|
    case NumberZero =>
      processed < |lines| &&
      lines[processed] == 0
    case NumberBackwards(current, previous) =>
      0 < processed < |lines| &&
      lines[processed] > 0 &&
      current == lines[processed] &&
      previous == lines[processed - 1] &&
      current < previous
  }

  /** Relates a line number to its starting byte offset, capped at the input length. */
  ghost predicate LineCutRelation(data: BenchWorld.Bytes, line: nat, cut: nat)
  {
    if line <= 1 then
      cut == 0
    else if multiset(data)['\n'] < line - 1 then
      cut == |data|
    else
      0 < cut <= |data| &&
      data[cut - 1] == '\n' &&
      multiset(data[..cut])['\n'] == line - 1
  }

  /** Requires the pieces to partition the input at consecutive byte offsets. */
  ghost predicate PiecePartitionRelation(
    data: BenchWorld.Bytes,
    pieces: seq<BenchWorld.Bytes>,
    cuts: seq<nat>
  )
  {
    |cuts| == |pieces| + 1 &&
    cuts[0] == 0 &&
    cuts[|cuts| - 1] == |data| &&
    forall i {:trigger cuts[i]} :: 0 <= i < |pieces| ==>
                                     cuts[i] <= cuts[i + 1] <= |data| &&
                                     pieces[i] == data[cuts[i]..cuts[i + 1]]
  }

  // Deferred GNU behavior: regular-expression contexts, repeat counts, custom
  // prefixes/suffixes, suppress-matched, quiet mode, and eliding empty files are
  // outside this benchmark slice.  The formal relation intentionally covers
  // decoded numeric line patterns and their write/cleanup transitions.
  /** Partitions the input at the cuts before the first out-of-range pattern. */
  ghost predicate SplitPlanRelation(
    data: BenchWorld.Bytes,
    lines: seq<nat>,
    plan: SplitPlan
  )
  {
    var pieces := plan.pieces;
    0 < |pieces| <= |lines| + 1 &&
    var accepted := |pieces| - 1;
    (exists cuts: seq<nat> ::
      PiecePartitionRelation(data, pieces, cuts) &&
      (forall i :: 0 <= i < accepted ==>
                     LineCutRelation(data, lines[i], cuts[i + 1]) &&
                     cuts[i + 1] < |data|)) &&
    match plan
    case SplitComplete(_) => accepted == |lines|
    case SplitOutOfRange(_, line) =>
      accepted < |lines| &&
      line == lines[accepted] &&
      LineCutRelation(data, line, |data|)
  }

  /** Relates ordered byte fragments to their concatenation and boundary offsets. */
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
                                     cuts[i] <= cuts[i + 1] <= |combined| &&
                                     cuts[i + 1] == cuts[i] + |fragments[i]| &&
                                     combined[cuts[i]..cuts[i + 1]] == fragments[i]
  }

  /** Relates line-number patterns to warnings for consecutive duplicates. */
  ghost predicate DuplicateWarningsRelation(
    lines: seq<nat>,
    warnings: BenchWorld.Bytes
  )
  {
    exists fragments: seq<BenchWorld.Bytes>, cuts: seq<nat> ::
      |fragments| == |lines| &&
      (forall i :: 0 <= i < |lines| ==>
                     fragments[i] ==
                     if i > 0 && lines[i] == lines[i - 1]
                     then DuplicateWarning(lines[i])
                     else []) &&
      FragmentsConcatenate(fragments, warnings, cuts)
  }

  /** Combines numeric-pattern validation with warnings from the valid prefix. */
  ghost predicate NumberAnalysisRelation(
    lines: seq<nat>,
    status: NumberStatus,
    processed: nat,
    warnings: BenchWorld.Bytes
  )
  {
    NumberStatusAtRelation(lines, status, processed) &&
    DuplicateWarningsRelation(lines[..processed], warnings)
  }

  /** Returns the observed remaining stdin, preserving it for file input. */
  ghost function ReadStdinAfterFields(input: Schema.Input, preStdin: BenchWorld.Bytes, preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult): BenchWorld.Bytes
  {
    match input
    case Stdin => IOContract.ObservedReadStdinRemainingFields(preStdin, preStreams)
    case File(_) => preStdin
  }

  /** Returns the observed read result for stdin or the named input file. */
  ghost function ReadResultFields(
    input: Schema.Input,
    preFs: BenchWorld.FileSystem,
    preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult,
    preStdin: BenchWorld.Bytes
  ): BenchWorld.IOResult<BenchWorld.Bytes>
  {
    match input
    case Stdin => IOContract.ObservedReadStdinResultFields(preStdin, preStreams)
    case File(path) => IOContract.ObservedReadFileResultFields(preFs, preStreams, path)
  }

  /** Returns the read result, deferring stdin reads for invalid numeric patterns. */
  ghost function DeferredReadResultFields(raw: Schema.CsplitCmdRaw,
                                          preFs: BenchWorld.FileSystem,
                                          preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult,
                                          preStdin: BenchWorld.Bytes): BenchWorld.IOResult<BenchWorld.Bytes>
  {
    if raw.input.Stdin? && !ValidNumberPrefix(raw.lineNumbers, |raw.lineNumbers|) then
      Result.Ok(preStdin)
    else ReadResultFields(raw.input, preFs, preStreams, preStdin)
  }

  // A failed open preserves its entry; a failed write/close attempts to remove the output.
  datatype FileStep = FileStep(state: BenchWorld.FileSystem, ok: bool, err: int)
  datatype FileTrace = FileTrace(start: BenchWorld.FileSystem, steps: seq<FileStep>)
  datatype WriteRun = WriteRun(writes: FileTrace, cleanup: FileTrace)

  // A trace has one more state than operation results, including its initial state.
  /** Returns the filesystem state at a trace position, including the initial state. */
  ghost function StateAt(trace: FileTrace, position: nat): BenchWorld.FileSystem
    requires position <= |trace.steps|
  {
    if position == 0 then trace.start else trace.steps[position - 1].state
  }

  /** Returns the filesystem state after the final traced operation. */
  ghost function EndState(trace: FileTrace): BenchWorld.FileSystem
  {
    StateAt(trace, |trace.steps|)
  }

  /** Relates each attempted piece write to its filesystem state and write result. */
  twostate predicate WriteAttemptsRelation(io: BenchIO.IO,
                                           pieces: seq<BenchWorld.Bytes>, index: nat,
                                           new writes: FileTrace)
  {
    |writes.steps| <= |pieces| &&
    forall i: nat | i < |writes.steps| ::
      exists committed: nat, stage: BenchWorld.FileWriteStage
        {:trigger IOContract.WriteFileSpec(StateAt(writes, i), old(io.props()), old(io.now()),
                                           old(io.credentials()), old(io.trustedFilesystem()), writes.steps[i].state,
                                           OutputName(index + i), pieces[i], writes.steps[i].ok, writes.steps[i].err, committed, stage)} ::
        IOContract.WriteFileSpec(StateAt(writes, i), old(io.props()), old(io.now()),
                                 old(io.credentials()), old(io.trustedFilesystem()), writes.steps[i].state,
                                 OutputName(index + i), pieces[i], writes.steps[i].ok, writes.steps[i].err,
                                 committed, stage)
  }

  // Outputs are removed in reverse order. Failed deletions remain visible in the trace.
  /** Relates reverse-order output deletions to their filesystem states and results. */
  twostate predicate CleanupRelation(io: BenchIO.IO, index: nat, new cleanup: FileTrace)
  {
    forall i: nat | i < |cleanup.steps| ::
      IOContract.DeletePathSpec(StateAt(cleanup, i), old(io.now()), old(io.trustedNativeFailures()),
                                cleanup.steps[i].state, OutputName(index + |cleanup.steps| - 1 - i),
                                cleanup.steps[i].ok, cleanup.steps[i].err)
  }

  // A failed open leaves its entry; a failed write or close attempts to remove it.
  /** Relates a failed write to cleanup, preserving the entry after an open failure. */
  twostate predicate FailedWriteCleanupRelation(io: BenchIO.IO,
                                                pieces: seq<BenchWorld.Bytes>, index: nat,
                                                new history: WriteRun)
    requires 0 < |history.writes.steps| <= |pieces|
  {
    var last := |history.writes.steps| - 1;
    var writes := history.writes;
    exists committed: nat, stage: BenchWorld.FileWriteStage
      {:trigger IOContract.WriteFileSpec(StateAt(writes, last), old(io.props()), old(io.now()),
                                         old(io.credentials()), old(io.trustedFilesystem()), writes.steps[last].state,
                                         OutputName(index + last), pieces[last], false, writes.steps[last].err, committed, stage)} ::
      IOContract.WriteFileSpec(StateAt(writes, last), old(io.props()), old(io.now()),
                               old(io.credentials()), old(io.trustedFilesystem()), writes.steps[last].state,
                               OutputName(index + last), pieces[last], false, writes.steps[last].err, committed, stage) &&
      (if stage == BenchWorld.WriteOpenFailed then history.cleanup.start == EndState(writes)
       else exists ok: bool, err: int
              {:trigger IOContract.DeletePathSpec(EndState(writes), old(io.now()), old(io.trustedNativeFailures()),
                                                  history.cleanup.start, OutputName(index + last), ok, err)} ::
              IOContract.DeletePathSpec(EndState(writes), old(io.now()), old(io.trustedNativeFailures()),
                                        history.cleanup.start, OutputName(index + last), ok, err))
  }

  /** Relates the first count pieces to their newline-separated byte counts. */
  ghost predicate CountOutputRelation(pieces: seq<BenchWorld.Bytes>, count: nat,
                                      output: BenchWorld.Bytes)
  {
    count <= |pieces| &&
    exists fragments: seq<BenchWorld.Bytes>, cuts: seq<nat> ::
      |fragments| == count &&
      (forall i :: 0 <= i < count ==> fragments[i] == CountLine(|pieces[i]|)) &&
      FragmentsConcatenate(fragments, output, cuts)
  }

  /** Relates a write and cleanup trace to file effects, output, diagnostics, and exit status. */
  twostate predicate WriteTraceWitnessRelation(io: BenchIO.IO,
                                               pieces: seq<BenchWorld.Bytes>, index: nat,
                                               terminalError: BenchWorld.Bytes,
                                               hasTerminalError: bool,
                                               new history: WriteRun,
                                               stdout: BenchWorld.Bytes,
                                               stderr: BenchWorld.Bytes, exit: int)
    reads io.fsRegion
  {
    var writes := history.writes;
    var cleanup := history.cleanup;
    var attempted := |writes.steps|;
    writes.start == old(io.fs()) &&
    WriteAttemptsRelation(io, pieces, index, writes) &&
    (forall i: nat | i + 1 < attempted :: writes.steps[i].ok) &&
    if attempted > 0 && !writes.steps[attempted - 1].ok then
      CountOutputRelation(pieces, attempted - 1, stdout) &&
      FailedWriteCleanupRelation(io, pieces, index, history) &&
      |cleanup.steps| == attempted - 1 && CleanupRelation(io, index, cleanup) &&
      EndState(cleanup) == io.fs() &&
      stderr == WriteErrorMessage(OutputName(index + attempted - 1), writes.steps[attempted - 1].err) &&
      exit == 1
    else
      attempted == |pieces| &&
      (forall i: nat | i < attempted :: writes.steps[i].ok) &&
      CountOutputRelation(pieces, attempted, stdout) &&
      if hasTerminalError then
        cleanup.start == EndState(writes) && |cleanup.steps| == attempted &&
        CleanupRelation(io, index, cleanup) && EndState(cleanup) == io.fs() &&
        stderr == terminalError && exit == 1
      else
        EndState(writes) == io.fs() && stderr == [] && exit == 0
  }

  /** Requires a write and cleanup trace explaining the specified observable result. */
  twostate predicate WriteTraceRelation(io: BenchIO.IO,
                                        pieces: seq<BenchWorld.Bytes>, index: nat,
                                        terminalError: BenchWorld.Bytes, hasTerminalError: bool,
                                        stdout: BenchWorld.Bytes, stderr: BenchWorld.Bytes, exit: int)
    reads io.fsRegion
  {
    exists history: WriteRun ::
      WriteTraceWitnessRelation(io, pieces, index, terminalError, hasTerminalError,
                                history, stdout, stderr, exit)
  }

  /** Specifies writing all pieces, including cleanup if an output write fails. */
  twostate predicate WritePiecesSummary(io: BenchIO.IO,
                                        pieces: seq<BenchWorld.Bytes>, index: nat,
                                        stdout: BenchWorld.Bytes, stderr: BenchWorld.Bytes, exit: int)
    reads io.fsRegion
  {
    WriteTraceRelation(io, pieces, index, [], false, stdout, stderr, exit)
  }

  /** Specifies writing pieces before reporting an out-of-range pattern and cleaning up. */
  twostate predicate WritePiecesThenErrorSummary(io: BenchIO.IO,
                                                 pieces: seq<BenchWorld.Bytes>, index: nat, line: nat,
                                                 stdout: BenchWorld.Bytes, stderr: BenchWorld.Bytes, exit: int)
    reads io.fsRegion
  {
    WriteTraceRelation(io, pieces, index, OutOfRangeMessage(line), true, stdout, stderr, exit)
  }

  /** Relates command input and file effects to planned output, diagnostics, and exit status. */
  twostate predicate PreparedSpec(raw: Schema.CsplitCmdRaw, io: BenchIO.IO, exit: int, plannedStdout: BenchWorld.Bytes, plannedStderr: BenchWorld.Bytes)
    reads io.fsRegion, io.stdinRegion
  {
    if raw.mode == Schema.ModeHelp then
      io.fs() == old(io.fs()) &&
      io.stdin() == old(io.stdin()) &&
      plannedStdout == HelpText() &&
      plannedStderr == [] &&
      exit == 0
    else if raw.mode == Schema.ModeVersion then
      io.fs() == old(io.fs()) &&
      io.stdin() == old(io.stdin()) &&
      plannedStdout == VersionText() &&
      plannedStderr == [] &&
      exit == 0
    else
      match DeferredReadResultFields(raw, old(io.fs()), old(io.trustedStreams()), old(io.stdin()))
      case Err(err) =>
        io.stdin() == ReadStdinAfterFields(raw.input, old(io.stdin()), old(io.trustedStreams())) &&
        (if raw.input.Stdin? then
           PartialStdinFailure(io, raw, err, plannedStdout, plannedStderr, exit)
         else
           io.fs() == old(io.fs()) && plannedStdout == [] &&
           plannedStderr == ReadErrorMessage(raw.input, err) && exit == 1)
      case Ok(data) =>
        exists numberStatus: NumberStatus, processed: nat,
          warnings: BenchWorld.Bytes ::
          NumberAnalysisRelation(
            raw.lineNumbers, numberStatus, processed, warnings
          ) &&
          match numberStatus
          case NumberZero =>
            io.fs() == old(io.fs()) &&
            io.stdin() == old(io.stdin()) &&
            plannedStdout == [] &&
            plannedStderr ==
            warnings + ZeroLineMessage(0) &&
            exit == 1
          case NumberBackwards(current, previous) =>
            io.fs() == old(io.fs()) &&
            io.stdin() == old(io.stdin()) &&
            plannedStdout == [] &&
            plannedStderr ==
            warnings +
            BackwardLineMessage(current, previous) &&
            exit == 1
          case NumbersOk =>
            io.stdin() == ReadStdinAfterFields(raw.input, old(io.stdin()), old(io.trustedStreams())) &&
            exists splitPlan: SplitPlan ::
              SplitPlanRelation(data, raw.lineNumbers, splitPlan) &&
              match splitPlan
              case SplitOutOfRange(pieces, line) =>
                exists writeErr: BenchWorld.Bytes ::
                  WritePiecesThenErrorSummary(io, pieces, 0, line, plannedStdout, writeErr, exit) &&
                  plannedStderr == warnings + writeErr
              case SplitComplete(pieces) =>
                exists writeErr: BenchWorld.Bytes ::
                  WritePiecesSummary(io, pieces, 0, plannedStdout, writeErr, exit) &&
                  plannedStderr == warnings + writeErr
  }

  /** Formats a diagnostic for a standard output write failure. */
  function StreamWriteErrorMessage(message: string): BenchWorld.Bytes
  {
    StreamUtf8.Encode("csplit: write error: " + message + "\n")
  }

  /** Relates planned output to stream writes and the exit status, including write failures. */
  twostate predicate Emit(io: BenchIO.IO,
                          out: BenchWorld.Bytes, diagnostics: BenchWorld.Bytes,
                          normalExit: int, exit: int)
    reads io.stdoutRegion, io.stderrRegion
  {
    var observations := old(io.trustedStreams());
    var stdoutResult := if out == [] then BenchWorld.StreamWriteResult(0, old(io.stdout()), 0)
                        else observations(BenchWorld.StreamWriteStdout(old(io.stdout()), out));
    stdoutResult.StreamWriteResult? &&
    var errors := diagnostics + (if stdoutResult.err == 0 then [] else
                                 StreamWriteErrorMessage(StreamContract.CLocaleErrnoTextResult(stdoutResult.err)));
    var stderrResult := if errors == [] then BenchWorld.StreamWriteResult(0, old(io.stderr()), 0)
                        else observations(BenchWorld.StreamWriteStderr(old(io.stderr()), errors));
    stderrResult.StreamWriteResult? &&
    (if out == [] then io.stdout() == old(io.stdout()) else StreamContract.WriteStdoutSpec(
       old(io.stdout()), observations, io.stdout(), out, stdoutResult.committed, stdoutResult.err)) &&
    (if errors == [] then io.stderr() == old(io.stderr()) else StreamContract.WriteStderrSpec(
       old(io.stderr()), observations, io.stderr(), errors, stderrResult.committed, stderrResult.err)) &&
    exit == (if stdoutResult.err != 0 || stderrResult.err != 0 then 1 else normalExit)
  }

  /** Specifies the command's file effects, input consumption, output streams, and exit status. */
  twostate predicate Spec(raw: Schema.CsplitCmdRaw, io: BenchIO.IO, exit: int)
    reads io.fsRegion, io.stdinRegion, io.stdoutRegion, io.stderrRegion
  {
    exists out: BenchWorld.Bytes, diagnostics: BenchWorld.Bytes, normalExit: int ::
      PreparedSpec(raw, io, normalExit,
                   out, diagnostics) &&
      Emit(io, out, diagnostics, normalExit, exit)
  }

  /** Relates input bytes to their longest prefix ending at a complete newline. */
  ghost predicate CompleteInputPrefixRelation(data: BenchWorld.Bytes, complete: BenchWorld.Bytes)
  {
    |complete| <= |data| && complete == data[..|complete|] &&
    (complete == [] || complete[|complete| - 1] == '\n') &&
    forall i: nat | |complete| <= i < |data| :: data[i] != '\n'
  }

  /** Relates partially read input to pieces formed from its complete lines. */
  ghost predicate ReadFailurePiecesRelation(data: BenchWorld.Bytes, lines: seq<nat>,
                                            pieces: seq<BenchWorld.Bytes>)
  {
    exists complete: BenchWorld.Bytes, plan: SplitPlan ::
      CompleteInputPrefixRelation(data, complete) && SplitPlanRelation(complete, lines, plan) &&
      pieces == plan.pieces
  }

  /** Specifies piece writes, cleanup, warnings, and diagnostics after a stdin read failure. */
  twostate predicate PartialStdinFailure(
    io: BenchIO.IO,
    raw: Schema.CsplitCmdRaw,
    error: BenchWorld.IOError,
    output: BenchWorld.Bytes,
    diagnostics: BenchWorld.Bytes,
    exit: int
  )
    reads io.fsRegion
  {
    exists pieces: seq<BenchWorld.Bytes>, warnings: BenchWorld.Bytes, writeDiagnostics: BenchWorld.Bytes ::
      DuplicateWarningsRelation(raw.lineNumbers, warnings) &&
      ReadFailurePiecesRelation(IOContract.ReadResultData(Result.Err(error)), raw.lineNumbers, pieces) &&
      WriteTraceRelation(io, pieces, 0, ReadErrorMessage(raw.input, error), true, output, writeDiagnostics, exit) &&
      diagnostics == warnings + writeDiagnostics && exit == 1
  }
}
