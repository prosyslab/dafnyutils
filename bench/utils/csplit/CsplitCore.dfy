include "../../core/World.dfy"
include "../../core/IO.dfy"
include "../../core/IOContract.dfy"
include "CsplitSchema.dfy"
include "CsplitSpec.dfy"

module CsplitCore {
  import BenchIO
  import Utf8 = Utf8Semantics
  import BenchWorld
  import IOContract
  import Schema = CsplitSchema
  import Spec = CsplitSpec
  datatype NumberStatus = NumbersOk | NumberZero | NumberBackwards(current: nat, previous: nat)
  datatype NumberValidation = NumberValidation(status: NumberStatus, processed: nat)
  datatype NumberAnalysis = NumberAnalysis(
    status: NumberStatus,
    processed: nat,
    warnings: BenchWorld.Bytes
  )
  datatype SplitPlan = SplitComplete(pieces: seq<BenchWorld.Bytes>) |
                       SplitOutOfRange(pieces: seq<BenchWorld.Bytes>, line: nat)
  datatype LifetimeMutation =
    FreshObject(id: BenchWorld.InodeId) |
    RemovedLastObject(id: BenchWorld.InodeId)

  function LineStart(data: BenchWorld.Bytes, line: nat): nat
    ensures LineStart(data, line) <= |data|
    decreases |data| + line
  {
    if line <= 1 then
      0
    else if |data| == 0 then
      0
    else if data[0] == '\n' then
      1 + LineStart(data[1..], line - 1)
    else
      1 + LineStart(data[1..], line)
  }

  function LineExists(data: BenchWorld.Bytes, line: nat): bool
  {
    line > 0 && LineStart(data, line) < |data|
  }

  function SafeSlice(
    data: BenchWorld.Bytes, start: nat, end: nat
  ): BenchWorld.Bytes
  {
    if start <= end <= |data| then data[start..end] else []
  }

  function ValidateNumbersFrom(
    lines: seq<nat>, previous: nat
  ): NumberValidation
    ensures ValidateNumbersFrom(lines, previous).processed <= |lines|
    decreases |lines|
  {
    if |lines| == 0 then
      NumberValidation(NumbersOk, 0)
    else if lines[0] == 0 then
      NumberValidation(NumberZero, 0)
    else if lines[0] < previous then
      NumberValidation(NumberBackwards(lines[0], previous), 0)
    else
      var tail := ValidateNumbersFrom(lines[1..], lines[0]);
      NumberValidation(tail.status, tail.processed + 1)
  }

  function ValidateNumbers(lines: seq<nat>): NumberValidation
  {
    ValidateNumbersFrom(lines, 0)
  }

  function SplitPlanFrom(
    data: BenchWorld.Bytes, lines: seq<nat>, start: nat
  ): SplitPlan
    decreases |lines|
  {
    if |lines| == 0 then
      SplitComplete([SafeSlice(data, start, |data|)])
    else
      var next := LineStart(data, lines[0]);
      var piece := SafeSlice(data, start, next);
      if !LineExists(data, lines[0]) then
        SplitOutOfRange([piece], lines[0])
      else
        match SplitPlanFrom(data, lines[1..], next)
        case SplitComplete(tail) => SplitComplete([piece] + tail)
        case SplitOutOfRange(tail, line) =>
          SplitOutOfRange([piece] + tail, line)
  }

  function SplitPlanFor(
    data: BenchWorld.Bytes, lines: seq<nat>
  ): SplitPlan
  {
    SplitPlanFrom(data, lines, 0)
  }

  function DuplicateWarningsFrom(
    lines: seq<nat>, previous: nat, hasPrevious: bool
  ): BenchWorld.Bytes
    decreases |lines|
  {
    if |lines| == 0 then
      []
    else
      (if hasPrevious && lines[0] == previous
       then Spec.DuplicateWarning(lines[0])
       else []) +
      DuplicateWarningsFrom(lines[1..], lines[0], true)
  }

  function DuplicateWarnings(
    lines: seq<nat>
  ): BenchWorld.Bytes
  {
    DuplicateWarningsFrom(lines, 0, false)
  }

  function AnalyzeNumbers(lines: seq<nat>): NumberAnalysis
  {
    var validation := ValidateNumbers(lines);
    NumberAnalysis(
      validation.status,
      validation.processed,
      DuplicateWarnings(lines[..validation.processed])
    )
  }

  ghost predicate WriteTraceSummaryFields(
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
    decreases |pieces|
  {
    if |pieces| == 0 then
      fs2 == preFs &&
      stdout == [] &&
      stderr == (if hasTerminalError then terminalError else []) &&
      exit == (if hasTerminalError then 1 else 0)
    else
      exists afterWriteFs: BenchWorld.FileSystem, ok: bool, err: int ::
        IOContract.WriteFileContractFields(
          preFs, preNow, OutputName(index), pieces[0], ok, err, afterWriteFs
        ) &&
        if ok then
          exists tailFs: BenchWorld.FileSystem, tailOut: BenchWorld.Bytes,
            tailErr: BenchWorld.Bytes, tailExit: int
            {:trigger WriteTraceSummaryFields(
              pieces[1..],
              index + 1,
              terminalError,
              hasTerminalError,
              afterWriteFs,
              preNow,
              tailFs,
              tailOut,
              tailErr,
              tailExit
            )} ::
            WriteTraceSummaryFields(
              pieces[1..],
              index + 1,
              terminalError,
              hasTerminalError,
              afterWriteFs,
              preNow,
              tailFs,
              tailOut,
              tailErr,
              tailExit
            ) &&
            (if hasTerminalError || tailExit != 0 then
               exists deleteOk: bool, deleteErr: int ::
                 IOContract.DeletePathContractFields(
                   tailFs, OutputName(index), deleteOk, deleteErr, fs2
                 )
             else
               fs2 == tailFs) &&
            stdout == CountLine(|pieces[0]|) + tailOut &&
            stderr == tailErr &&
            exit == tailExit
        else
          fs2 == afterWriteFs &&
          stdout == [] &&
          stderr == Spec.WriteErrorMessage(OutputName(index), err) &&
          exit == 1
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
    WriteTraceSummaryFields(
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
  )
  {
    WriteTraceSummaryFields(
      pieces,
      index,
      Spec.OutOfRangeMessage(line),
      true,
      preFs,
      preNow,
      fs2,
      stdout,
      stderr,
      exit
    )
  }

  twostate predicate CoreSummary(raw: Schema.CsplitCmdRaw, io: BenchIO.IO, exit: int)
    reads io.Footprint()
  {
    if raw.mode == Schema.ModeHelp then
      io.fs() == old(io.fs()) &&
      io.stdin() == old(io.stdin()) &&
      io.stdout() == old(io.stdout()) + Spec.HelpText() &&
      io.stderr() == old(io.stderr()) &&
      exit == 0
    else if raw.mode == Schema.ModeVersion then
      io.fs() == old(io.fs()) &&
      io.stdin() == old(io.stdin()) &&
      io.stdout() == old(io.stdout()) + Spec.VersionText() &&
      io.stderr() == old(io.stderr()) &&
      exit == 0
    else
      match Spec.ReadResultFields(raw.input, old(io.fs()), old(io.stdin()))
      case Err(err) =>
        io.fs() == old(io.fs()) &&
        io.stdin() == Spec.ReadStdinAfterFields(raw.input, old(io.stdin())) &&
        io.stdout() == old(io.stdout()) &&
        io.stderr() == old(io.stderr()) + Spec.ReadErrorMessage(raw.input, err) &&
        exit == 1
      case Ok(data) =>
        var analysis := AnalyzeNumbers(raw.lineNumbers);
        match analysis.status
        case NumberZero =>
          io.fs() == old(io.fs()) &&
          io.stdin() == old(io.stdin()) &&
          io.stdout() == old(io.stdout()) &&
          io.stderr() ==
          old(io.stderr()) + analysis.warnings + Spec.ZeroLineMessage(0) &&
          exit == 1
        case NumberBackwards(current, previous) =>
          io.fs() == old(io.fs()) &&
          io.stdin() == old(io.stdin()) &&
          io.stdout() == old(io.stdout()) &&
          io.stderr() ==
          old(io.stderr()) + analysis.warnings +
          Spec.BackwardLineMessage(current, previous) &&
          exit == 1
        case NumbersOk =>
          io.stdin() == Spec.ReadStdinAfterFields(raw.input, old(io.stdin())) &&
          match SplitPlanFor(data, raw.lineNumbers)
          case SplitOutOfRange(pieces, line) =>
            exists writeOut: BenchWorld.Bytes, writeErr: BenchWorld.Bytes ::
              WritePiecesThenErrorSummaryFields(
                pieces,
                0,
                line,
                old(io.fs()),
                old(io.now()),
                io.fs(),
                writeOut,
                writeErr,
                exit
              ) &&
              io.stdout() == old(io.stdout()) + writeOut &&
              io.stderr() ==
              old(io.stderr()) + analysis.warnings + writeErr
          case SplitComplete(pieces) =>
            exists writeOut: BenchWorld.Bytes, writeErr: BenchWorld.Bytes ::
              WritePiecesSummaryFields(
                pieces,
                0,
                old(io.fs()),
                old(io.now()),
                io.fs(),
                writeOut,
                writeErr,
                exit
              ) &&
              io.stdout() == old(io.stdout()) + writeOut &&
              io.stderr() ==
              old(io.stderr()) + analysis.warnings + writeErr
  }

  function DigitChar(d: nat): char
    requires d < 10
  {
    if d == 0 then '0'
    else if d == 1 then '1'
    else if d == 2 then '2'
    else if d == 3 then '3'
    else if d == 4 then '4'
    else if d == 5 then '5'
    else if d == 6 then '6'
    else if d == 7 then '7'
    else if d == 8 then '8'
    else '9'
  } by method {
    var ch: char;
    if d == 0 { ch := '0'; }
    else if d == 1 { ch := '1'; }
    else if d == 2 { ch := '2'; }
    else if d == 3 { ch := '3'; }
    else if d == 4 { ch := '4'; }
    else if d == 5 { ch := '5'; }
    else if d == 6 { ch := '6'; }
    else if d == 7 { ch := '7'; }
    else if d == 8 { ch := '8'; }
    else { ch := '9'; }
    return ch;
  }

  function DigitsNat(n: nat): BenchWorld.Bytes
    decreases n
  {
    if n < 10 then [DigitChar(n)]
    else DigitsNat(n / 10) + [DigitChar(n % 10)]
  } by method {
    var digits: BenchWorld.Bytes;
    if n < 10 {
      var ch := DigitChar(n);
      digits := [ch];
    } else {
      var prefix := DigitsNat(n / 10);
      var ch := DigitChar(n % 10);
      digits := prefix + [ch];
    }
    return digits;
  }

  function CountLine(n: nat): BenchWorld.Bytes
  {
    DigitsNat(n) + "\n"
  } by method {
    var digits := DigitsNat(n);
    return digits + "\n";
  }

  function OutputName(index: nat): BenchWorld.Path
  {
    if index < 10 then
      "xx0" + DigitsNat(index)
    else
      "xx" + DigitsNat(index)
  } by method {
    var digits := DigitsNat(index);
    if index < 10 {
      return "xx0" + digits;
    } else {
      return "xx" + digits;
    }
  }

  ghost predicate NoFreshObjectAfterLastRemoval(events: seq<LifetimeMutation>)
  {
    forall i: int, j: int ::
      0 <= i < j < |events| && events[i].RemovedLastObject? ==>
        !events[j].FreshObject?
  }

  ghost function FreshWriteEventList(
    before: BenchWorld.FileSystem,
    after: BenchWorld.FileSystem,
    path: BenchWorld.Path
  ): seq<LifetimeMutation>
  {
    if !BenchWorld.FsContainsPath(before, path) &&
       BenchWorld.FsContainsPath(after, path) then
      [FreshObject(BenchWorld.FsIdAt(after, path))]
    else
      []
  }

  ghost predicate FreshWriteEvents(
    before: BenchWorld.FileSystem,
    after: BenchWorld.FileSystem,
    path: BenchWorld.Path,
    events: seq<LifetimeMutation>
  )
  {
    events == FreshWriteEventList(before, after, path)
  }

  ghost function LastRemovalEventList(
    before: BenchWorld.FileSystem,
    after: BenchWorld.FileSystem,
    path: BenchWorld.Path
  ): seq<LifetimeMutation>
  {
    if BenchWorld.FsContainsPath(before, path) &&
       !BenchWorld.FsContainsPath(after, path) &&
       BenchWorld.InodeLinkCountAt(before, path) ==
       BenchWorld.LinkCountKnown(1) then
      [RemovedLastObject(BenchWorld.FsIdAt(before, path))]
    else
      []
  }

  ghost predicate LastRemovalEvents(
    before: BenchWorld.FileSystem,
    after: BenchWorld.FileSystem,
    path: BenchWorld.Path,
    events: seq<LifetimeMutation>
  )
  {
    events == LastRemovalEventList(before, after, path)
  }

  ghost predicate LifetimeEvidence(
    pieces: seq<BenchWorld.Bytes>,
    index: nat,
    preFs: BenchWorld.FileSystem,
    preNow: int,
    fs2: BenchWorld.FileSystem,
    exit: int,
    lifetimeEvents: seq<LifetimeMutation>,
    alwaysCleanup: bool
  )
    decreases |pieces|
  {
    if |pieces| == 0 then
      fs2 == preFs &&
      exit == (if alwaysCleanup then 1 else 0) &&
      lifetimeEvents == []
    else
      exists afterWriteFs: BenchWorld.FileSystem, ok: bool, err: int ::
        IOContract.WriteFileContractFields(
          preFs,
          preNow,
          OutputName(index),
          pieces[0],
          ok,
          err,
          afterWriteFs
        ) &&
        if ok then
          exists tailFs: BenchWorld.FileSystem, tailExit: int,
            writeEvents: seq<LifetimeMutation>,
            tailEvents: seq<LifetimeMutation>,
            cleanupEvents: seq<LifetimeMutation>
            {:trigger
            LifetimeEvidence(
              pieces[1..],
              index + 1,
              afterWriteFs,
              preNow,
              tailFs,
              tailExit,
              tailEvents,
              alwaysCleanup
            ),
            FreshWriteEvents(
              preFs,
              afterWriteFs,
              OutputName(index),
              writeEvents
            ),
            LastRemovalEvents(
              tailFs,
              fs2,
              OutputName(index),
              cleanupEvents
            )}
            ::
              FreshWriteEvents(
                preFs,
                afterWriteFs,
                OutputName(index),
                writeEvents
              ) &&
              LifetimeEvidence(
                pieces[1..],
                index + 1,
                afterWriteFs,
                preNow,
                tailFs,
                tailExit,
                tailEvents,
                alwaysCleanup
              ) &&
              (if alwaysCleanup || tailExit != 0 then
                 exists deleteOk: bool, deleteErr: int ::
                   IOContract.DeletePathContractFields(
                     tailFs,
                     OutputName(index),
                     deleteOk,
                     deleteErr,
                     fs2
                   ) &&
                   LastRemovalEvents(
                     tailFs,
                     fs2,
                     OutputName(index),
                     cleanupEvents
                   )
               else
                 fs2 == tailFs && cleanupEvents == []) &&
              exit == tailExit &&
              lifetimeEvents == writeEvents + tailEvents + cleanupEvents
        else
          fs2 == afterWriteFs && exit == 1 && lifetimeEvents == []
  }

  ghost predicate WritePiecesLifetimeEvidence(
    pieces: seq<BenchWorld.Bytes>,
    index: nat,
    preFs: BenchWorld.FileSystem,
    preNow: int,
    fs2: BenchWorld.FileSystem,
    exit: int,
    lifetimeEvents: seq<LifetimeMutation>
  )
  {
    LifetimeEvidence(
      pieces,
      index,
      preFs,
      preNow,
      fs2,
      exit,
      lifetimeEvents,
      false
    )
  }

  ghost predicate WritePiecesThenErrorLifetimeEvidence(
    pieces: seq<BenchWorld.Bytes>,
    index: nat,
    line: nat,
    preFs: BenchWorld.FileSystem,
    preNow: int,
    fs2: BenchWorld.FileSystem,
    exit: int,
    lifetimeEvents: seq<LifetimeMutation>
  )
  {
    LifetimeEvidence(
      pieces,
      index,
      preFs,
      preNow,
      fs2,
      exit,
      lifetimeEvents,
      true
    )
  }

  lemma ComposeLifetimeEvents(
    writeEvents: seq<LifetimeMutation>,
    tailEvents: seq<LifetimeMutation>,
    cleanupEvents: seq<LifetimeMutation>
  )
    requires writeEvents == [] ||
             exists id: BenchWorld.InodeId :: writeEvents == [FreshObject(id)]
    requires NoFreshObjectAfterLastRemoval(tailEvents)
    requires cleanupEvents == [] ||
             exists id: BenchWorld.InodeId ::
               cleanupEvents == [RemovedLastObject(id)]
    ensures NoFreshObjectAfterLastRemoval(
              writeEvents + tailEvents + cleanupEvents
            )
  {
  }

  method {:isolate_assertions} WritePieces(
    pieces: seq<BenchWorld.Bytes>,
    index: nat,
    io: BenchIO.IO
  ) returns (
      stdout: BenchWorld.Bytes,
      stderr: BenchWorld.Bytes,
      exit: int,
      ghost lifetimeEvents: seq<LifetimeMutation>
    )
    modifies io.fsRegion
    ensures WritePiecesSummaryFields(pieces, index, old(io.fs()), old(io.now()), io.fs(), stdout, stderr, exit)
    ensures WritePiecesLifetimeEvidence(
              pieces,
              index,
              old(io.fs()),
              old(io.now()),
              io.fs(),
              exit,
              lifetimeEvents
            )
    ensures NoFreshObjectAfterLastRemoval(lifetimeEvents)
    decreases |pieces|
  {
    ghost var preFs := io.fs();
    ghost var preNow := io.now();
    if |pieces| == 0 {
      stdout := [];
      stderr := [];
      exit := 0;
      lifetimeEvents := [];
      assert WritePiecesSummaryFields(pieces, index, preFs, preNow, io.fs(), stdout, stderr, exit);
      return;
    }

    ghost var beforeWriteFs := io.fs();
    ghost var beforeWriteNow := io.now();
    var path := OutputName(index);
    var ok, err := io.WriteFile(path, pieces[0]);
    ghost var afterWriteFs := io.fs();
    assert path == OutputName(index);
    assert IOContract.WriteFileContractFields(beforeWriteFs, beforeWriteNow, OutputName(index), pieces[0], ok, err, afterWriteFs);

    if ok {
      ghost var writeEvents :=
        FreshWriteEventList(beforeWriteFs, afterWriteFs, path);
      assert FreshWriteEvents(
          beforeWriteFs,
          afterWriteFs,
          path,
          writeEvents
        );
      var tailOut, tailErr, tailExit;
      ghost var tailEvents;
      tailOut, tailErr, tailExit, tailEvents :=
        WritePieces(pieces[1..], index + 1, io);
      ghost var tailFs := io.fs();
      assert LifetimeEvidence(
          pieces[1..],
          index + 1,
          afterWriteFs,
          beforeWriteNow,
          tailFs,
          tailExit,
          tailEvents,
          false
        );
      var count := CountLine(|pieces[0]|);
      ghost var cleanupEvents: seq<LifetimeMutation> := [];
      if tailExit != 0 {
        var deleteOk, deleteErr := io.DeletePath(path);
        assert IOContract.DeletePathContractFields(tailFs, OutputName(index), deleteOk, deleteErr, io.fs());
        cleanupEvents := LastRemovalEventList(tailFs, io.fs(), path);
        assert LastRemovalEvents(
            tailFs,
            io.fs(),
            path,
            cleanupEvents
          );
        assert exists cleanupOk: bool, cleanupErr: int ::
            IOContract.DeletePathContractFields(tailFs, OutputName(index), cleanupOk, cleanupErr, io.fs());
      } else {
        assert LastRemovalEvents(
            tailFs,
            io.fs(),
            path,
            cleanupEvents
          );
      }
      stdout := count + tailOut;
      stderr := tailErr;
      exit := tailExit;
      lifetimeEvents := writeEvents + tailEvents + cleanupEvents;
      assert writeEvents == [] ||
             exists id: BenchWorld.InodeId :: writeEvents == [FreshObject(id)];
      assert cleanupEvents == [] ||
             exists id: BenchWorld.InodeId ::
               cleanupEvents == [RemovedLastObject(id)];
      ComposeLifetimeEvents(writeEvents, tailEvents, cleanupEvents);
      assert WritePiecesSummaryFields(pieces[1..], index + 1, afterWriteFs, beforeWriteNow, tailFs, tailOut, tailErr, tailExit);
      assert WritePiecesSummaryFields(pieces, index, beforeWriteFs, beforeWriteNow, io.fs(), stdout, stderr, exit);
      assert LifetimeEvidence(
          pieces,
          index,
          beforeWriteFs,
          beforeWriteNow,
          io.fs(),
          exit,
          lifetimeEvents,
          false
        );
    } else {
      stdout := [];
      stderr := Spec.WriteErrorMessage(path, err);
      exit := 1;
      lifetimeEvents := [];
      assert stderr == Spec.WriteErrorMessage(OutputName(index), err);
      assert WritePiecesSummaryFields(pieces, index, beforeWriteFs, beforeWriteNow, io.fs(), stdout, stderr, exit);
    }
  }

  method {:isolate_assertions} WritePiecesThenError(
    pieces: seq<BenchWorld.Bytes>,
    index: nat,
    line: nat,
    io: BenchIO.IO
  ) returns (
      stdout: BenchWorld.Bytes,
      stderr: BenchWorld.Bytes,
      exit: int,
      ghost lifetimeEvents: seq<LifetimeMutation>
    )
    modifies io.fsRegion
    ensures WritePiecesThenErrorSummaryFields(pieces, index, line, old(io.fs()), old(io.now()), io.fs(), stdout, stderr, exit)
    ensures WritePiecesThenErrorLifetimeEvidence(
              pieces,
              index,
              line,
              old(io.fs()),
              old(io.now()),
              io.fs(),
              exit,
              lifetimeEvents
            )
    ensures NoFreshObjectAfterLastRemoval(lifetimeEvents)
    decreases |pieces|
  {
    ghost var preFs := io.fs();
    ghost var preNow := io.now();
    if |pieces| == 0 {
      stdout := [];
      stderr := Spec.OutOfRangeMessage(line);
      exit := 1;
      lifetimeEvents := [];
      assert WritePiecesThenErrorSummaryFields(pieces, index, line, preFs, preNow, io.fs(), stdout, stderr, exit);
      return;
    }

    ghost var beforeWriteFs := io.fs();
    ghost var beforeWriteNow := io.now();
    var path := OutputName(index);
    var ok, err := io.WriteFile(path, pieces[0]);
    ghost var afterWriteFs := io.fs();
    assert path == OutputName(index);
    assert IOContract.WriteFileContractFields(beforeWriteFs, beforeWriteNow, OutputName(index), pieces[0], ok, err, afterWriteFs);

    if ok {
      ghost var writeEvents :=
        FreshWriteEventList(beforeWriteFs, afterWriteFs, path);
      assert FreshWriteEvents(
          beforeWriteFs,
          afterWriteFs,
          path,
          writeEvents
        );
      var tailOut, tailErr, tailExit;
      ghost var tailEvents;
      tailOut, tailErr, tailExit, tailEvents :=
        WritePiecesThenError(pieces[1..], index + 1, line, io);
      ghost var tailFs := io.fs();
      assert LifetimeEvidence(
          pieces[1..],
          index + 1,
          afterWriteFs,
          beforeWriteNow,
          tailFs,
          tailExit,
          tailEvents,
          true
        );
      var deleteOk, deleteErr := io.DeletePath(path);
      assert IOContract.DeletePathContractFields(tailFs, OutputName(index), deleteOk, deleteErr, io.fs());
      ghost var cleanupEvents :=
        LastRemovalEventList(tailFs, io.fs(), path);
      assert LastRemovalEvents(
          tailFs,
          io.fs(),
          path,
          cleanupEvents
        );
      var count := CountLine(|pieces[0]|);
      stdout := count + tailOut;
      stderr := tailErr;
      exit := tailExit;
      lifetimeEvents := writeEvents + tailEvents + cleanupEvents;
      assert writeEvents == [] ||
             exists id: BenchWorld.InodeId :: writeEvents == [FreshObject(id)];
      assert cleanupEvents == [] ||
             exists id: BenchWorld.InodeId ::
               cleanupEvents == [RemovedLastObject(id)];
      ComposeLifetimeEvents(writeEvents, tailEvents, cleanupEvents);
      assert WritePiecesThenErrorSummaryFields(pieces[1..], index + 1, line, afterWriteFs, beforeWriteNow, tailFs, tailOut, tailErr, tailExit);
      assert exists cleanupOk: bool, cleanupErr: int ::
          IOContract.DeletePathContractFields(tailFs, OutputName(index), cleanupOk, cleanupErr, io.fs());
      assert WritePiecesThenErrorSummaryFields(pieces, index, line, beforeWriteFs, beforeWriteNow, io.fs(), stdout, stderr, exit);
      assert LifetimeEvidence(
          pieces,
          index,
          beforeWriteFs,
          beforeWriteNow,
          io.fs(),
          exit,
          lifetimeEvents,
          true
        );
    } else {
      stdout := [];
      stderr := Spec.WriteErrorMessage(path, err);
      exit := 1;
      lifetimeEvents := [];
      assert stderr == Spec.WriteErrorMessage(OutputName(index), err);
      assert WritePiecesThenErrorSummaryFields(pieces, index, line, beforeWriteFs, beforeWriteNow, io.fs(), stdout, stderr, exit);
    }
  }

  method {:isolate_assertions} RunCore(raw: Schema.CsplitCmdRaw, io: BenchIO.IO) returns (exit: int)
    modifies io.fsRegion, io.stdinRegion, io.stdoutRegion, io.stderrRegion
    ensures CoreSummary(raw, io, exit)
    decreases *
  {
    ghost var preFs := io.fs();
    ghost var preStdin := io.stdin();
    ghost var preNow := io.now();
    if raw.mode == Schema.ModeHelp {
      var help := Spec.HelpText();
      io.AppendStdout(help);
      exit := 0;
      assert CoreSummary(raw, io, exit);
      return;
    }

    if raw.mode == Schema.ModeVersion {
      var version := Spec.VersionText();
      io.AppendStdout(version);
      exit := 0;
      assert CoreSummary(raw, io, exit);
      return;
    }

    var data: BenchWorld.Bytes := [];
    match raw.input {
      case Stdin =>
        assert Spec.ReadResultFields(raw.input, preFs, preStdin) ==
               BenchWorld.Ok(preStdin);
      case File(path) =>
        var readResult := io.ReadFile(path);
        assert readResult == Spec.ReadResultFields(raw.input, preFs, preStdin);
        match readResult
        case Err(err) =>
          var msg := Spec.ReadErrorMessage(raw.input, err);
          io.AppendStderr(msg);
          exit := 1;
          assert CoreSummary(raw, io, exit);
          return;
        case Ok(fileData) =>
          data := fileData;
          assert Spec.ReadResultFields(raw.input, preFs, preStdin) ==
                 BenchWorld.Ok(data);
    }

    var numberAnalysis := AnalyzeNumbers(raw.lineNumbers);
    assert numberAnalysis == AnalyzeNumbers(raw.lineNumbers);
    var warnings := numberAnalysis.warnings;
    match numberAnalysis.status
    case NumberZero =>
      assert AnalyzeNumbers(raw.lineNumbers).status == NumberZero;
      var msg := Spec.ZeroLineMessage(0);
      io.AppendStderr(warnings + msg);
      exit := 1;
      assert CoreSummary(raw, io, exit);
      return;
    case NumberBackwards(current, previous) =>
      assert AnalyzeNumbers(raw.lineNumbers).status ==
             NumberBackwards(current, previous);
      var msg := Spec.BackwardLineMessage(current, previous);
      io.AppendStderr(warnings + msg);
      exit := 1;
      assert CoreSummary(raw, io, exit);
      return;
    case NumbersOk =>

      match raw.input {
        case Stdin =>
          data := io.ReadStdinAll();
          assert data == preStdin;
        case File(path) =>
      }
      assert Spec.ReadResultFields(raw.input, preFs, preStdin) ==
             BenchWorld.Ok(data);
      assert io.stdin() == Spec.ReadStdinAfterFields(raw.input, preStdin);

      var splitPlan := SplitPlanFor(data, raw.lineNumbers);
      match splitPlan
      case SplitOutOfRange(pieces, line) =>
        assert splitPlan == SplitPlanFor(data, raw.lineNumbers);
        assert SplitPlanFor(data, raw.lineNumbers) == SplitOutOfRange(pieces, line);
        var out, errOut, writeExit;
        ghost var lifetimeEvents;
        out, errOut, writeExit, lifetimeEvents :=
          WritePiecesThenError(pieces, 0, line, io);
        io.AppendStdout(out);
        io.AppendStderr(warnings + errOut);
        assert warnings == AnalyzeNumbers(raw.lineNumbers).warnings;
        assert io.stderr() == old(io.stderr()) + (warnings + errOut);
        exit := writeExit;
        assert WritePiecesThenErrorSummaryFields(pieces, 0, line, preFs, preNow, io.fs(), out, errOut, writeExit);
        assert io.stdin() == Spec.ReadStdinAfterFields(raw.input, preStdin);
        assert CoreSummary(raw, io, exit) by {
          assert AnalyzeNumbers(raw.lineNumbers).status == NumbersOk;
          assert Spec.ReadResultFields(raw.input, preFs, preStdin) ==
                 BenchWorld.Ok(data);
          assert WritePiecesThenErrorSummaryFields(
              pieces,
              0,
              line,
              preFs,
              preNow,
              io.fs(),
              out,
              errOut,
              writeExit
            );
          assert io.stdout() == old(io.stdout()) + out;
          calc {
             io.stderr();
          == old(io.stderr()) + (warnings + errOut);
          == old(io.stderr()) + AnalyzeNumbers(raw.lineNumbers).warnings + errOut;
          }
          assert exit == writeExit;
          assert exists writeFs: BenchWorld.FileSystem,
              writeOut: BenchWorld.Bytes,
              writeErr: BenchWorld.Bytes,
              witnessedExit: int ::
              WritePiecesThenErrorSummaryFields(
                pieces,
                0,
                line,
                preFs,
                preNow,
                writeFs,
                writeOut,
                writeErr,
                witnessedExit
              ) &&
              io.fs() == writeFs &&
              io.stdout() == old(io.stdout()) + writeOut &&
              io.stderr() ==
              old(io.stderr()) +
              AnalyzeNumbers(raw.lineNumbers).warnings +
              writeErr &&
              exit == witnessedExit;
        }
      case SplitComplete(pieces) =>
        assert splitPlan == SplitPlanFor(data, raw.lineNumbers);
        assert SplitPlanFor(data, raw.lineNumbers) == SplitComplete(pieces);
        var out, errOut, writeExit;
        ghost var lifetimeEvents;
        out, errOut, writeExit, lifetimeEvents :=
          WritePieces(pieces, 0, io);
        io.AppendStdout(out);
        io.AppendStderr(warnings + errOut);
        assert warnings == AnalyzeNumbers(raw.lineNumbers).warnings;
        assert io.stderr() == old(io.stderr()) + (warnings + errOut);
        exit := writeExit;
        assert WritePiecesSummaryFields(pieces, 0, preFs, preNow, io.fs(), out, errOut, writeExit);
        assert io.stdin() == Spec.ReadStdinAfterFields(raw.input, preStdin);
        assert CoreSummary(raw, io, exit) by {
          assert AnalyzeNumbers(raw.lineNumbers).status == NumbersOk;
          assert Spec.ReadResultFields(raw.input, preFs, preStdin) ==
                 BenchWorld.Ok(data);
          assert WritePiecesSummaryFields(
              pieces,
              0,
              preFs,
              preNow,
              io.fs(),
              out,
              errOut,
              writeExit
            );
          assert io.stdout() == old(io.stdout()) + out;
          calc {
             io.stderr();
          == old(io.stderr()) + (warnings + errOut);
          == old(io.stderr()) + AnalyzeNumbers(raw.lineNumbers).warnings + errOut;
          }
          assert exit == writeExit;
          assert exists writeFs: BenchWorld.FileSystem,
              writeOut: BenchWorld.Bytes,
              writeErr: BenchWorld.Bytes,
              witnessedExit: int ::
              WritePiecesSummaryFields(
                pieces,
                0,
                preFs,
                preNow,
                writeFs,
                writeOut,
                writeErr,
                witnessedExit
              ) &&
              io.fs() == writeFs &&
              io.stdout() == old(io.stdout()) + writeOut &&
              io.stderr() ==
              old(io.stderr()) +
              AnalyzeNumbers(raw.lineNumbers).warnings +
              writeErr &&
              exit == witnessedExit;
        }
  }
}
