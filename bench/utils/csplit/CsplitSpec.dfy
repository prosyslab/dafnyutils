include "../../core/World.dfy"
include "../../core/IO.dfy"
include "../../core/IOContract.dfy"
include "CsplitSchema.dfy"

module CsplitSpec {
  import BenchIO
  import Utf8 = Utf8Semantics
  import BenchWorld
  import IOContract
  import Schema = CsplitSchema

  datatype NumberStatus = NumbersOk | NumberZero | NumberBackwards(current: nat, previous: nat)
  datatype SplitPlan = SplitComplete(pieces: seq<BenchWorld.Bytes>) |
                       SplitOutOfRange(pieces: seq<BenchWorld.Bytes>, line: nat)














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

  function ReadErrnoText(err: BenchWorld.IOError): string
  {
    match err
    case NoSuchFile => "No such file or directory"
    case IsDirectory => "Is a directory"
    case NotDirectory => "Not a directory"
    case PermissionDenied => "Permission denied"
    case InvalidPath => "Too many levels of symbolic links"
    case Other(msg) => msg
  }

  function WriteErrnoText(err: int): string
  {
    if err == 2 then "No such file or directory"
    else if err == 13 then "Permission denied"
    else if err == 20 then "Not a directory"
    else if err == 21 then "Is a directory"
    else if err == 28 then "No space left on device"
    else if err == 40 then "Too many levels of symbolic links"
    else "unknown error"
  }

  function ReadErrorMessage(input: Schema.Input, err: BenchWorld.IOError): BenchWorld.Bytes
  {
    match input
    case Stdin => []
    case File(path) => Utf8.Encode("csplit: cannot open '" + path + "' for reading: " + ReadErrnoText(err) + "\n")
  }

  function WriteErrorMessage(path: BenchWorld.Path, err: int): BenchWorld.Bytes
  {
    Utf8.Encode("csplit: " + path + ": " + WriteErrnoText(err) + "\n")
  }

  function ZeroLineMessage(line: nat): BenchWorld.Bytes
  {
    "csplit: " + Schema.DigitsNat(line) + ": line number must be greater than zero\n"
  }

  function BackwardLineMessage(current: nat, previous: nat): BenchWorld.Bytes
  {
    "csplit: line number '" + Schema.DigitsNat(current) + "' is smaller than preceding line number, " +
    Schema.DigitsNat(previous) + "\n"
  }

  function OutOfRangeMessage(line: nat): BenchWorld.Bytes
  {
    "csplit: '" + Schema.DigitsNat(line) + "': line number out of range\n"
  }

  function DuplicateWarning(line: nat): BenchWorld.Bytes
  {
    "csplit: warning: line number '" + Schema.DigitsNat(line) + "' is the same as preceding line number\n"
  }



  function CountLine(n: nat): BenchWorld.Bytes
  {
    Schema.DigitsNat(n) + "\n"
  }

  function OutputName(index: nat): BenchWorld.Path
  {
    if index < 10 then
      "xx0" + Schema.DigitsNat(index)
    else
      "xx" + Schema.DigitsNat(index)
  }

  ghost predicate ValidNumberPrefix(lines: seq<nat>, count: nat)
  {
    count <= |lines| &&
    forall i :: 0 <= i < count ==>
                  lines[i] > 0 &&
                  (i == 0 || lines[i - 1] <= lines[i])
  }

  ghost predicate NumberStatusRelation(lines: seq<nat>, status: NumberStatus)
  {
    exists processed: nat ::
      NumberStatusAtRelation(lines, status, processed)
  }

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
  ghost predicate SplitPlanRelation(
    data: BenchWorld.Bytes,
    lines: seq<nat>,
    plan: SplitPlan
  )
  {
    match plan
    case SplitComplete(pieces) =>
      exists cuts: seq<nat> ::
        |cuts| == |lines| + 2 &&
        PiecePartitionRelation(data, pieces, cuts) &&
        (forall i :: 0 <= i < |lines| ==>
                       LineCutRelation(data, lines[i], cuts[i + 1]) &&
                       cuts[i + 1] < |data|)
    case SplitOutOfRange(pieces, line) =>
      exists failed: nat, cuts: seq<nat> ::
        failed < |lines| &&
        line == lines[failed] &&
        |cuts| == failed + 2 &&
        PiecePartitionRelation(data, pieces, cuts) &&
        (forall i :: 0 <= i <= failed ==>
                       LineCutRelation(data, lines[i], cuts[i + 1])) &&
        (forall i {:trigger cuts[i + 1]} ::
           0 <= i < failed ==> cuts[i + 1] < |data|) &&
        cuts[failed + 1] == |data|
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
                                     cuts[i] <= cuts[i + 1] <= |combined| &&
                                     cuts[i + 1] == cuts[i] + |fragments[i]| &&
                                     combined[cuts[i]..cuts[i + 1]] == fragments[i]
  }

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

  function ReadStdinAfterFields(input: Schema.Input, preStdin: BenchWorld.Bytes): BenchWorld.Bytes
  {
    match input
    case Stdin => IOContract.AfterReadStdinFields(preStdin)
    case File(_) => preStdin
  }

  function ReadResultFields(
    input: Schema.Input,
    preFs: BenchWorld.FileSystem,
    preStdin: BenchWorld.Bytes
  ): BenchWorld.Result<BenchWorld.Bytes>
  {
    match input
    case Stdin => BenchWorld.Ok(preStdin)
    case File(path) => IOContract.ReadFileResultFields(preFs, path)
  }

  ghost predicate WriteAttemptsRelation(
    pieces: seq<BenchWorld.Bytes>,
    index: nat,
    count: nat,
    preFs: BenchWorld.FileSystem,
    preNow: int,
    states: seq<BenchWorld.FileSystem>,
    oks: seq<bool>,
    errs: seq<int>
  )
  {
    count <= |pieces| &&
    |states| == count + 1 &&
    |oks| == count &&
    |errs| == count &&
    states[0] == preFs &&
    forall i :: 0 <= i < count ==>
                  IOContract.WriteFileContractFields(
                    states[i],
                    preNow,
                    OutputName(index + i),
                    pieces[i],
                    oks[i],
                    errs[i],
                    states[i + 1]
                  )
  }

  ghost predicate CleanupWitnessRelation(
    index: nat,
    count: nat,
    preFs: BenchWorld.FileSystem,
    fs2: BenchWorld.FileSystem,
    states: seq<BenchWorld.FileSystem>,
    oks: seq<bool>,
    errs: seq<int>
  )
  {
    |states| == count + 1 &&
    states[0] == preFs &&
    states[count] == fs2 &&
    |oks| == count &&
    |errs| == count &&
    forall i :: 0 <= i < count ==>
                  IOContract.DeletePathContractFields(
                    states[i],
                    OutputName(index + count - 1 - i),
                    oks[i],
                    errs[i],
                    states[i + 1]
                  )
  }

  ghost predicate CleanupRelation(
    index: nat,
    count: nat,
    preFs: BenchWorld.FileSystem,
    fs2: BenchWorld.FileSystem,
    states: seq<BenchWorld.FileSystem>
  )
  {
    exists oks: seq<bool>, errs: seq<int> ::
      CleanupWitnessRelation(
        index, count, preFs, fs2, states, oks, errs
      )
  }

  ghost predicate CountOutputRelation(
    pieces: seq<BenchWorld.Bytes>,
    count: nat,
    output: BenchWorld.Bytes
  )
  {
    count <= |pieces| &&
    exists fragments: seq<BenchWorld.Bytes>, cuts: seq<nat> ::
      |fragments| == count &&
      (forall i :: 0 <= i < count ==>
                     fragments[i] == CountLine(|pieces[i]|)) &&
      FragmentsConcatenate(fragments, output, cuts)
  }

  ghost predicate WriteTraceWitnessRelation(
    pieces: seq<BenchWorld.Bytes>,
    index: nat,
    terminalError: BenchWorld.Bytes,
    hasTerminalError: bool,
    preFs: BenchWorld.FileSystem,
    preNow: int,
    fs2: BenchWorld.FileSystem,
    stdout: BenchWorld.Bytes,
    stderr: BenchWorld.Bytes,
    exit: int,
    attempted: nat,
    writeStates: seq<BenchWorld.FileSystem>,
    writeOk: seq<bool>,
    writeErr: seq<int>,
    cleanupStates: seq<BenchWorld.FileSystem>
  )
  {
    attempted <= |pieces| &&
    WriteAttemptsRelation(
      pieces, index, attempted, preFs, preNow, writeStates, writeOk, writeErr
    ) &&
    (forall i :: 0 <= i && i + 1 < attempted ==> writeOk[i]) &&
    if attempted > 0 && !writeOk[attempted - 1] then
      CountOutputRelation(pieces, attempted - 1, stdout) &&
      CleanupRelation(
        index, attempted - 1, writeStates[attempted], fs2, cleanupStates
      ) &&
      stderr == WriteErrorMessage(
        OutputName(index + attempted - 1),
        writeErr[attempted - 1]
      ) &&
      exit == 1
    else
      attempted == |pieces| &&
      (forall i :: 0 <= i < attempted ==> writeOk[i]) &&
      CountOutputRelation(pieces, attempted, stdout) &&
      if hasTerminalError then
        CleanupRelation(
          index, attempted, writeStates[attempted], fs2, cleanupStates
        ) &&
        stderr == terminalError &&
        exit == 1
      else
        fs2 == writeStates[attempted] &&
        stderr == [] &&
        exit == 0
  }

  ghost predicate WriteTraceRelation(
    pieces: seq<BenchWorld.Bytes>,
    index: nat,
    terminalError: BenchWorld.Bytes,
    hasTerminalError: bool,
    preFs: BenchWorld.FileSystem,
    preNow: int,
    fs2: BenchWorld.FileSystem,
    stdout: BenchWorld.Bytes,
    stderr: BenchWorld.Bytes,
    exit: int
  )
  {
    exists attempted: nat,
      writeStates: seq<BenchWorld.FileSystem>,
      writeOk: seq<bool>,
      writeErr: seq<int>,
      cleanupStates: seq<BenchWorld.FileSystem> ::
      WriteTraceWitnessRelation(
        pieces,
        index,
        terminalError,
        hasTerminalError,
        preFs,
        preNow,
        fs2,
        stdout,
        stderr,
        exit,
        attempted,
        writeStates,
        writeOk,
        writeErr,
        cleanupStates
      )
  }

  ghost predicate WritePiecesSummaryFields(
    pieces: seq<BenchWorld.Bytes>,
    index: nat,
    preFs: BenchWorld.FileSystem,
    preNow: int,
    fs2: BenchWorld.FileSystem,
    stdout: BenchWorld.Bytes,
    stderr: BenchWorld.Bytes,
    exit: int
  )
  {
    WriteTraceRelation(
      pieces, index, [], false, preFs, preNow, fs2, stdout, stderr, exit
    )
  }

  ghost predicate WritePiecesThenErrorSummaryFields(
    pieces: seq<BenchWorld.Bytes>,
    index: nat,
    line: nat,
    preFs: BenchWorld.FileSystem,
    preNow: int,
    fs2: BenchWorld.FileSystem,
    stdout: BenchWorld.Bytes,
    stderr: BenchWorld.Bytes,
    exit: int
  ) {
    WriteTraceRelation(
      pieces,
      index,
      OutOfRangeMessage(line),
      true,
      preFs,
      preNow,
      fs2,
      stdout,
      stderr,
      exit
    )
  }

  twostate predicate Spec(raw: Schema.CsplitCmdRaw, io: BenchIO.IO, exit: int)
    reads io.Footprint()
  {
    if raw.mode == Schema.ModeHelp then
      io.fs() == old(io.fs()) &&
      io.stdin() == old(io.stdin()) &&
      io.stdout() == old(io.stdout()) + HelpText() &&
      io.stderr() == old(io.stderr()) &&
      exit == 0
    else if raw.mode == Schema.ModeVersion then
      io.fs() == old(io.fs()) &&
      io.stdin() == old(io.stdin()) &&
      io.stdout() == old(io.stdout()) + VersionText() &&
      io.stderr() == old(io.stderr()) &&
      exit == 0
    else
      match ReadResultFields(raw.input, old(io.fs()), old(io.stdin()))
      case Err(err) =>
        io.fs() == old(io.fs()) &&
        io.stdin() == ReadStdinAfterFields(raw.input, old(io.stdin())) &&
        io.stdout() == old(io.stdout()) &&
        io.stderr() == old(io.stderr()) + ReadErrorMessage(raw.input, err) &&
        exit == 1
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
            io.stdout() == old(io.stdout()) &&
            io.stderr() ==
            old(io.stderr()) + warnings + ZeroLineMessage(0) &&
            exit == 1
          case NumberBackwards(current, previous) =>
            io.fs() == old(io.fs()) &&
            io.stdin() == old(io.stdin()) &&
            io.stdout() == old(io.stdout()) &&
            io.stderr() ==
            old(io.stderr()) + warnings +
            BackwardLineMessage(current, previous) &&
            exit == 1
          case NumbersOk =>
            io.stdin() == ReadStdinAfterFields(raw.input, old(io.stdin())) &&
            exists splitPlan: SplitPlan ::
              SplitPlanRelation(data, raw.lineNumbers, splitPlan) &&
              match splitPlan
              case SplitOutOfRange(pieces, line) =>
                exists writeFs: BenchWorld.FileSystem, writeOut: BenchWorld.Bytes,
                  writeErr: BenchWorld.Bytes, writeExit: int ::
                  WritePiecesThenErrorSummaryFields(
                    pieces,
                    0,
                    line,
                    old(io.fs()),
                    old(io.now()),
                    writeFs,
                    writeOut,
                    writeErr,
                    writeExit
                  ) &&
                  io.fs() == writeFs &&
                  io.stdout() == old(io.stdout()) + writeOut &&
                  io.stderr() == old(io.stderr()) + warnings + writeErr &&
                  exit == writeExit
              case SplitComplete(pieces) =>
                exists writeFs: BenchWorld.FileSystem, writeOut: BenchWorld.Bytes,
                  writeErr: BenchWorld.Bytes, writeExit: int ::
                  WritePiecesSummaryFields(
                    pieces,
                    0,
                    old(io.fs()),
                    old(io.now()),
                    writeFs,
                    writeOut,
                    writeErr,
                    writeExit
                  ) &&
                  io.fs() == writeFs &&
                  io.stdout() == old(io.stdout()) + writeOut &&
                  io.stderr() == old(io.stderr()) + warnings + writeErr &&
                  exit == writeExit
  }
}
