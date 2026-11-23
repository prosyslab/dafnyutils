include "../../../core/World.dfy"
include "../Spec/CsplitSchema.dfy"
include "../Impl/CsplitCore.dfy"
include "../Spec/CsplitSpec.dfy"

module CsplitProof {
  ghost function TraceStates(trace: Spec.FileTrace): (states: seq<BenchWorld.FileSystem>)
    ensures |states| == |trace.steps| + 1 && states[0] == trace.start
    ensures forall i: nat | i < |trace.steps| :: states[i + 1] == trace.steps[i].state
    ensures forall i: nat | i <= |trace.steps| :: states[i] == Spec.StateAt(trace, i)
  {
    var projection := [trace.start] + seq(|trace.steps|, i requires 0 <= i < |trace.steps| => trace.steps[i].state);
    assert |projection| == |trace.steps| + 1 && projection[0] == trace.start by {
      hide *;
    }
    assert forall i: nat | i < |trace.steps| :: projection[i + 1] == trace.steps[i].state by {
      hide *;
    }
    assert forall i: nat | i <= |trace.steps| :: projection[i] == Spec.StateAt(trace, i) by {
      hide *;
      reveal Spec.StateAt();
    }
    projection
  }

  ghost function TraceOks(trace: Spec.FileTrace): (oks: seq<bool>)
    ensures |oks| == |trace.steps|
    ensures forall i: nat | i < |trace.steps| :: oks[i] == trace.steps[i].ok
  {
    seq(|trace.steps|, i requires 0 <= i < |trace.steps| => trace.steps[i].ok)
  }

  ghost function TraceErrors(trace: Spec.FileTrace): (errs: seq<int>)
    ensures |errs| == |trace.steps|
    ensures forall i: nat | i < |trace.steps| :: errs[i] == trace.steps[i].err
  {
    seq(|trace.steps|, i requires 0 <= i < |trace.steps| => trace.steps[i].err)
  }

  ghost function {:isolate_assertions} EncodeTrace(states: seq<BenchWorld.FileSystem>, oks: seq<bool>, errs: seq<int>):
    (trace: Spec.FileTrace)
    requires |states| == |oks| + 1 && |errs| == |oks|
    ensures TraceStates(trace) == states && TraceOks(trace) == oks && TraceErrors(trace) == errs
  {
    var encoded := Spec.FileTrace(states[0], seq(|oks|, i requires 0 <= i < |oks| =>
                                    Spec.FileStep(states[i + 1], oks[i], errs[i])));
    assert TraceStates(encoded) == states by {
      hide *;
      forall i | 0 <= i < |states|
        ensures TraceStates(encoded)[i] == states[i]
      {
        if i > 0 {
          assert encoded.steps[i - 1].state == states[i];
        }
      }
    }
    assert TraceOks(encoded) == oks by {
      hide *;
      forall i | 0 <= i < |oks|
        ensures TraceOks(encoded)[i] == oks[i]
      {
        assert encoded.steps[i].ok == oks[i];
      }
    }
    assert TraceErrors(encoded) == errs by {
      hide *;
      forall i | 0 <= i < |errs|
        ensures TraceErrors(encoded)[i] == errs[i]
      {
        assert encoded.steps[i].err == errs[i];
      }
    }
    encoded
  }

  twostate lemma WriteAttemptsMatchTrace(io: BenchIO.IO,
                                         pieces: seq<BenchWorld.Bytes>, index: nat,
                                         new trace: Spec.FileTrace)
    ensures Spec.WriteAttemptsRelation(io, pieces, index, trace) <==>
            StateModel.ValueWriteAttemptsRelation(old(Spec.Context(io)), pieces, index,
                                                  |trace.steps|, trace.start, old(io.now()), TraceStates(trace), TraceOks(trace), TraceErrors(trace))
  {
    hide *;
    reveal Spec.Context(), Spec.WriteAttemptsRelation(), StateModel.ValueWriteAttemptsRelation(),
           Core.WriteObservationFields(), Spec.StateAt(), TraceStates(), TraceOks(), TraceErrors();
    if Spec.WriteAttemptsRelation(io, pieces, index, trace) {
      forall i | 0 <= i < |trace.steps|
        ensures Core.WriteObservationFields(old(Spec.Context(io)), TraceStates(trace)[i], old(io.now()),
                                            Spec.OutputName(index + i), pieces[i], TraceOks(trace)[i], TraceErrors(trace)[i], TraceStates(trace)[i + 1])
      {
        var committed: nat, stage: BenchWorld.FileWriteStage :|
          IOContract.WriteFileSpec(Spec.StateAt(trace, i), old(io.props()), old(io.now()),
                                   old(io.credentials()), old(io.trustedFilesystem()), trace.steps[i].state,
                                   Spec.OutputName(index + i), pieces[i], trace.steps[i].ok, trace.steps[i].err, committed, stage);
      }
      assert StateModel.ValueWriteAttemptsRelation(old(Spec.Context(io)), pieces, index,
                                                   |trace.steps|, trace.start, old(io.now()), TraceStates(trace), TraceOks(trace), TraceErrors(trace));
    }
    if StateModel.ValueWriteAttemptsRelation(old(Spec.Context(io)), pieces, index,
                                             |trace.steps|, trace.start, old(io.now()), TraceStates(trace), TraceOks(trace), TraceErrors(trace)) {
      forall i: nat | i < |trace.steps|
        ensures exists committed: nat, stage: BenchWorld.FileWriteStage
                  {:trigger IOContract.WriteFileSpec(Spec.StateAt(trace, i), old(io.props()), old(io.now()),
                                                     old(io.credentials()), old(io.trustedFilesystem()), trace.steps[i].state,
                                                     Spec.OutputName(index + i), pieces[i], trace.steps[i].ok, trace.steps[i].err, committed, stage)} ::
                  IOContract.WriteFileSpec(Spec.StateAt(trace, i), old(io.props()), old(io.now()),
                                           old(io.credentials()), old(io.trustedFilesystem()), trace.steps[i].state,
                                           Spec.OutputName(index + i), pieces[i], trace.steps[i].ok, trace.steps[i].err, committed, stage)
      {
        assert Core.WriteObservationFields(old(Spec.Context(io)), TraceStates(trace)[i], old(io.now()),
                                           Spec.OutputName(index + i), pieces[i], TraceOks(trace)[i], TraceErrors(trace)[i], TraceStates(trace)[i + 1]);
      }
      assert Spec.WriteAttemptsRelation(io, pieces, index, trace);
    }
  }

  twostate lemma CleanupMatchesTrace(io: BenchIO.IO, index: nat, new trace: Spec.FileTrace)
    ensures Spec.CleanupRelation(io, index, trace) <==>
            StateModel.ValueCleanupWitnessRelation(old(Spec.Context(io)), index, |trace.steps|,
                                                   trace.start, Spec.EndState(trace), TraceStates(trace), TraceOks(trace), TraceErrors(trace))
  {
    hide *;
    reveal TraceStates(), TraceOks(), TraceErrors(), Spec.StateAt(), Spec.EndState(), Spec.Context(), Spec.CleanupRelation(), StateModel.ValueCleanupWitnessRelation(), Core.DeleteObservationFields();
    reveal Spec.Context();
  }

  lemma FailedCleanupMatchesNative(
    observations: Spec.ObservationContext,
    preFs: BenchWorld.FileSystem, now: int, path: BenchWorld.Path,
    data: BenchWorld.Bytes, err: int,
    afterWriteFs: BenchWorld.FileSystem, afterCleanupFs: BenchWorld.FileSystem)
    ensures Core.FailedWriteCleanupFields(observations, preFs, now, path, data, err,
                                          afterWriteFs, afterCleanupFs) <==>
            (exists committed: nat, stage: BenchWorld.FileWriteStage ::
               IOContract.WriteFileSpec(preFs, observations.props, now, observations.credentials,
                                        observations.filesystem, afterWriteFs, path, data, false, err, committed, stage) &&
               (if stage == BenchWorld.WriteOpenFailed then afterCleanupFs == afterWriteFs
                else exists deleteOk: bool, deleteErr: int ::
                       IOContract.DeletePathSpec(afterWriteFs, observations.now, observations.failures,
                                                 afterCleanupFs, path, deleteOk, deleteErr)))
  {
    hide *;
    reveal Core.FailedWriteCleanupFields(), Core.DeleteObservationFields();
    if exists committed: nat, stage: BenchWorld.FileWriteStage ::
        IOContract.WriteFileSpec(preFs, observations.props, now, observations.credentials,
                                 observations.filesystem, afterWriteFs, path, data, false, err, committed, stage) &&
        (if stage == BenchWorld.WriteOpenFailed then afterCleanupFs == afterWriteFs
         else exists deleteOk: bool, deleteErr: int ::
                IOContract.DeletePathSpec(afterWriteFs, observations.now, observations.failures,
                                          afterCleanupFs, path, deleteOk, deleteErr)) {
      var committed: nat, stage: BenchWorld.FileWriteStage :|
        IOContract.WriteFileSpec(preFs, observations.props, now, observations.credentials,
                                 observations.filesystem, afterWriteFs, path, data, false, err, committed, stage) &&
        (if stage == BenchWorld.WriteOpenFailed then afterCleanupFs == afterWriteFs
         else exists deleteOk: bool, deleteErr: int ::
                IOContract.DeletePathSpec(afterWriteFs, observations.now, observations.failures,
                                          afterCleanupFs, path, deleteOk, deleteErr));
      if stage != BenchWorld.WriteOpenFailed {
        var deleteOk: bool, deleteErr: int :|
          IOContract.DeletePathSpec(afterWriteFs, observations.now, observations.failures,
                                    afterCleanupFs, path, deleteOk, deleteErr);
        assert Core.DeleteObservationFields(observations, afterWriteFs, path,
                                            deleteOk, deleteErr, afterCleanupFs);
      }
      assert Core.FailedWriteCleanupFields(observations, preFs, now, path, data, err,
                                           afterWriteFs, afterCleanupFs);
    }
  }

  twostate lemma {:isolate_assertions} FailedCleanupMatchesTrace(io: BenchIO.IO,
                                           pieces: seq<BenchWorld.Bytes>, index: nat,
                                           new history: Spec.WriteRun)
    requires 0 < |history.writes.steps| <= |pieces|
    ensures Spec.FailedWriteCleanupRelation(io, pieces, index, history) <==>
            Core.FailedWriteCleanupFields(old(Spec.Context(io)),
                                          Spec.StateAt(history.writes, |history.writes.steps| - 1), old(io.now()),
                                          Spec.OutputName(index + |history.writes.steps| - 1), pieces[|history.writes.steps| - 1],
                                          history.writes.steps[|history.writes.steps| - 1].err, Spec.EndState(history.writes), history.cleanup.start)
  {
    FailedCleanupMatchesNative(old(Spec.Context(io)),
                               Spec.StateAt(history.writes, |history.writes.steps| - 1), old(io.now()),
                               Spec.OutputName(index + |history.writes.steps| - 1), pieces[|history.writes.steps| - 1],
                               history.writes.steps[|history.writes.steps| - 1].err,
                               Spec.EndState(history.writes), history.cleanup.start);

    hide *;
    reveal TraceStates(), TraceOks(), TraceErrors(), Spec.StateAt(), Spec.EndState(), Spec.Context(), Spec.FailedWriteCleanupRelation(), Core.FailedWriteCleanupFields(), Core.DeleteObservationFields();
    reveal Spec.Context();
  }

  twostate lemma WriteTraceRelationMatchesStateModel(
    io: BenchIO.IO, pieces: seq<BenchWorld.Bytes>, index: nat,
    terminalError: BenchWorld.Bytes, hasTerminalError: bool,
    stdout: BenchWorld.Bytes, stderr: BenchWorld.Bytes, exit: int)
    ensures Spec.WriteTraceRelation(io, pieces, index, terminalError, hasTerminalError, stdout, stderr, exit) <==>
            StateModel.ValueWriteTraceRelation(old(Spec.Context(io)), pieces, index, terminalError, hasTerminalError,
                                               old(io.fs()), old(io.now()), io.fs(), stdout, stderr, exit)
  {
    hide *;
    reveal Spec.WriteTraceRelation(), Spec.WriteTraceWitnessRelation(),
           StateModel.ValueWriteTraceRelation(), StateModel.ValueWriteTraceWitnessRelation(),
           StateModel.ValueWriteAttemptsRelation(), StateModel.ValueCleanupRelation(),
           StateModel.ValueCleanupWitnessRelation(), Spec.EndState();
    if Spec.WriteTraceRelation(io, pieces, index, terminalError, hasTerminalError, stdout, stderr, exit) {
      var history: Spec.WriteRun :| Spec.WriteTraceWitnessRelation(io, pieces, index, terminalError,
                                                                   hasTerminalError, history, stdout, stderr, exit);
      var writes := history.writes;
      var cleanup := history.cleanup;
      var attempted := |writes.steps|;
      WriteAttemptsMatchTrace(io, pieces, index, writes);
      CleanupMatchesTrace(io, index, cleanup);
      if attempted > 0 && !writes.steps[attempted - 1].ok {
        FailedCleanupMatchesTrace(io, pieces, index, history);
        assert StateModel.ValueCleanupRelation(old(Spec.Context(io)), index, attempted - 1,
                                               cleanup.start, io.fs(), TraceStates(cleanup));
      } else if hasTerminalError {
        assert StateModel.ValueCleanupRelation(old(Spec.Context(io)), index, attempted,
                                               Spec.EndState(writes), io.fs(), TraceStates(cleanup));
      }
      assert StateModel.ValueWriteTraceWitnessRelation(old(Spec.Context(io)), pieces, index,
                                                       terminalError, hasTerminalError, old(io.fs()), old(io.now()), io.fs(), stdout, stderr, exit,
                                                       attempted, TraceStates(writes), TraceOks(writes), TraceErrors(writes), TraceStates(cleanup));
    }
    if StateModel.ValueWriteTraceRelation(old(Spec.Context(io)), pieces, index, terminalError,
                                          hasTerminalError, old(io.fs()), old(io.now()), io.fs(), stdout, stderr, exit) {
      var attempted: nat, states: seq<BenchWorld.FileSystem>, oks: seq<bool>, errs: seq<int>,
          cleanupStates: seq<BenchWorld.FileSystem> :|
        StateModel.ValueWriteTraceWitnessRelation(old(Spec.Context(io)), pieces, index, terminalError,
                                                  hasTerminalError, old(io.fs()), old(io.now()), io.fs(), stdout, stderr, exit,
                                                  attempted, states, oks, errs, cleanupStates);
      var writes := EncodeTrace(states, oks, errs);
      assert |writes.steps| == attempted && writes.start == old(io.fs());
      assert Spec.EndState(writes) == states[attempted];
      var cleanup := Spec.FileTrace(Spec.EndState(writes), []);
      if (attempted > 0 && !oks[attempted - 1]) || hasTerminalError {
        var count := if attempted > 0 && !oks[attempted - 1] then attempted - 1 else attempted;
        var cleanupOks: seq<bool>, cleanupErrs: seq<int> :|
          StateModel.ValueCleanupWitnessRelation(old(Spec.Context(io)), index, count,
                                                 cleanupStates[0], io.fs(), cleanupStates, cleanupOks, cleanupErrs);
        cleanup := EncodeTrace(cleanupStates, cleanupOks, cleanupErrs);
        assert |cleanup.steps| == count && cleanup.start == cleanupStates[0];
        assert Spec.EndState(cleanup) == io.fs();
      }
      var history := Spec.WriteRun(writes, cleanup);
      WriteAttemptsMatchTrace(io, pieces, index, writes);
      assert Spec.WriteAttemptsRelation(io, pieces, index, writes);
      CleanupMatchesTrace(io, index, cleanup);
      if attempted > 0 && !oks[attempted - 1] {
        FailedCleanupMatchesTrace(io, pieces, index, history);
        assert Spec.FailedWriteCleanupRelation(io, pieces, index, history);
        assert Spec.CleanupRelation(io, index, cleanup);
      } else if hasTerminalError {
        assert cleanup.start == Spec.EndState(writes);
        assert Spec.CleanupRelation(io, index, cleanup);
      }
      assert Spec.WriteTraceWitnessRelation(io, pieces, index, terminalError, hasTerminalError,
                                            history, stdout, stderr, exit);
    }
  }

  twostate lemma PartialStdinFailureFieldsMatchesStateModel(io: BenchIO.IO,
                                                            raw: Schema.CsplitCmdRaw, error: BenchWorld.IOError,
                                                            output: BenchWorld.Bytes, diagnostics: BenchWorld.Bytes, exit: int)
    ensures Spec.PartialStdinFailure(io, raw, error, output, diagnostics, exit) <==>
            StateModel.ValuePartialStdinFailureFields(old(Spec.Context(io)), raw, error,
                                                      old(io.fs()), old(io.now()), io.fs(), output, diagnostics, exit)
  {
    forall pieces: seq<BenchWorld.Bytes>, writeDiagnostics: BenchWorld.Bytes
      ensures Spec.WriteTraceRelation(io, pieces, 0, Spec.ReadErrorMessage(raw.input, error), true,
                                      output, writeDiagnostics, exit) <==>
              StateModel.ValueWriteTraceRelation(old(Spec.Context(io)), pieces, 0,
                                                 Spec.ReadErrorMessage(raw.input, error), true, old(io.fs()), old(io.now()), io.fs(),
                                                 output, writeDiagnostics, exit)
    {
      WriteTraceRelationMatchesStateModel(io, pieces, 0, Spec.ReadErrorMessage(raw.input, error),
                                          true, output, writeDiagnostics, exit);
    }
  }

  import StateModel = CsplitTransitionModel
  import BenchIO
  import Result = Results
  import BenchWorld
  import IOContract
  import Schema = CsplitSchema
  import Core = CsplitCore
  import Spec = CsplitSpec

  function NumberStatusView(status: Core.NumberStatus): Spec.NumberStatus
  {
    match status
    case NumbersOk => Spec.NumbersOk
    case NumberZero => Spec.NumberZero
    case NumberBackwards(current, previous) =>
      Spec.NumberBackwards(current, previous)
  }

  function SplitPlanView(plan: Core.SplitPlan): Spec.SplitPlan
  {
    match plan
    case SplitComplete(pieces) => Spec.SplitComplete(pieces)
    case SplitOutOfRange(pieces, line) => Spec.SplitOutOfRange(pieces, line)
  }

  lemma ValidateNumbersFromRefines(
    all: seq<nat>,
    offset: nat,
    previous: nat
  )
    requires offset <= |all|
    requires previous == (if offset == 0 then 0 else all[offset - 1])
    requires Spec.ValidNumberPrefix(all, offset)
    ensures Spec.NumberStatusAtRelation(
              all,
              NumberStatusView(
                Core.ValidateNumbersFrom(all[offset..], previous).status
              ),
              offset + Core.ValidateNumbersFrom(
                all[offset..], previous
              ).processed
            )
    decreases |all| - offset
  {
    if offset == |all| {
      assert Core.ValidateNumbersFrom(all[offset..], previous) ==
             Core.NumberValidation(Core.NumbersOk, 0);
      assert Spec.NumberStatusAtRelation(
          all, Spec.NumbersOk, |all|
        ) by {
        reveal Spec.NumberStatusAtRelation();
      }
    } else if all[offset] == 0 {
      assert Core.ValidateNumbersFrom(all[offset..], previous) ==
             Core.NumberValidation(Core.NumberZero, 0);
      assert Spec.NumberStatusAtRelation(
          all, Spec.NumberZero, offset
        ) by {
        reveal Spec.NumberStatusAtRelation();
      }
    } else if all[offset] < previous {
      assert offset > 0;
      assert Core.ValidateNumbersFrom(all[offset..], previous) ==
             Core.NumberValidation(
               Core.NumberBackwards(all[offset], previous), 0
             );
      assert Spec.NumberStatusAtRelation(
          all,
          Spec.NumberBackwards(all[offset], previous),
          offset
        ) by {
        reveal Spec.NumberStatusAtRelation();
      }
    } else {
      assert Spec.ValidNumberPrefix(all, offset + 1) by {
        reveal Spec.ValidNumberPrefix();
        forall i | 0 <= i < offset + 1
          ensures all[i] > 0 &&
                  (i == 0 || all[i - 1] <= all[i])
        {
          if i < offset {
            assert all[i] > 0 &&
                   (i == 0 || all[i - 1] <= all[i]);
          } else {
            assert i == offset;
          }
        }
      }
      ValidateNumbersFromRefines(all, offset + 1, all[offset]);
      var tailValidation :=
        Core.ValidateNumbersFrom(all[offset + 1..], all[offset]);
      assert all[offset..][0] == all[offset];
      assert all[offset..][1..] == all[offset + 1..];
      assert Core.ValidateNumbersFrom(all[offset..], previous) ==
             Core.NumberValidation(
               tailValidation.status, tailValidation.processed + 1
             );
      assert offset + tailValidation.processed + 1 ==
             offset + 1 + tailValidation.processed;
    }
  }

  lemma ValidateNumbersRefines(lines: seq<nat>)
    ensures Spec.NumberStatusAtRelation(
              lines,
              NumberStatusView(Core.ValidateNumbers(lines).status),
              Core.ValidateNumbers(lines).processed
            )
  {
    assert Spec.ValidNumberPrefix(lines, 0);
    ValidateNumbersFromRefines(lines, 0, 0);
  }

  lemma AnalyzeNumbersRefines(lines: seq<nat>)
    ensures Spec.NumberAnalysisRelation(
              lines,
              NumberStatusView(Core.AnalyzeNumbers(lines).status),
              Core.AnalyzeNumbers(lines).processed,
              Core.AnalyzeNumbers(lines).warnings
            )
  {
    ValidateNumbersRefines(lines);
    var validation := Core.ValidateNumbers(lines);
    reveal Spec.NumberStatusAtRelation();
    assert validation.processed <= |lines|;
    DuplicateWarningsRefines(lines[..validation.processed]);
  }

  lemma LineStartRefines(data: BenchWorld.Bytes, line: nat)
    ensures Spec.LineCutRelation(data, line, Core.LineStart(data, line))
    decreases |data| + line
  {
    if line <= 1 {
    } else if |data| == 0 {
      assert multiset(data)['\n'] == 0;
    } else if data[0] == '\n' {
      LineStartRefines(data[1..], line - 1);
      var tailCut := Core.LineStart(data[1..], line - 1);
      assert Core.LineStart(data, line) == 1 + tailCut;
      assert data == [data[0]] + data[1..];
      assert data[..1 + tailCut] == [data[0]] + data[1..][..tailCut];
      assert multiset(data) ==
             multiset([data[0]]) + multiset(data[1..]);
      assert multiset(data[..1 + tailCut]) ==
             multiset([data[0]]) + multiset(data[1..][..tailCut]);
    } else {
      LineStartRefines(data[1..], line);
      var tailCut := Core.LineStart(data[1..], line);
      assert Core.LineStart(data, line) == 1 + tailCut;
      assert data == [data[0]] + data[1..];
      assert data[..1 + tailCut] == [data[0]] + data[1..][..tailCut];
      assert multiset(data) ==
             multiset([data[0]]) + multiset(data[1..]);
      assert multiset(data[..1 + tailCut]) ==
             multiset([data[0]]) + multiset(data[1..][..tailCut]);
    }
  }

  lemma LineStartMonotone(
    data: BenchWorld.Bytes,
    first: nat,
    second: nat
  )
    requires first <= second
    ensures Core.LineStart(data, first) <= Core.LineStart(data, second)
    decreases |data| + first + second
  {
    if first <= 1 {
    } else if |data| == 0 {
    } else if data[0] == '\n' {
      LineStartMonotone(data[1..], first - 1, second - 1);
    } else {
      LineStartMonotone(data[1..], first, second);
    }
  }

  lemma TailIndex<T>(values: seq<T>, index: nat)
    requires index + 1 < |values|
    ensures values[1..][index] == values[index + 1]
  {
  }

  lemma {:isolate_assertions} SplitPlanFromRefines(
    data: BenchWorld.Bytes,
    lines: seq<nat>,
    start: nat
  ) returns (plan: Spec.SplitPlan, cuts: seq<nat>)
    requires start <= |data|
    requires Spec.ValidNumberPrefix(lines, |lines|)
    requires |lines| > 0 ==> start <= Core.LineStart(data, lines[0])
    ensures plan == SplitPlanView(Core.SplitPlanFrom(data, lines, start))
    ensures 0 < |plan.pieces| <= |lines| + 1
    ensures |cuts| == |plan.pieces| + 1
    ensures cuts[0] == start && cuts[|cuts| - 1] == |data|
    ensures forall i {:trigger cuts[i]} | 0 <= i < |plan.pieces| ::
      cuts[i] <= cuts[i + 1] <= |data| && plan.pieces[i] == data[cuts[i]..cuts[i + 1]]
    ensures forall i {:trigger cuts[i + 1]} | 0 <= i < |plan.pieces| - 1 ::
      Spec.LineCutRelation(data, lines[i], cuts[i + 1]) && cuts[i + 1] < |data|
    ensures plan.SplitComplete? ==> |plan.pieces| - 1 == |lines|
    ensures plan.SplitOutOfRange? ==>
      |plan.pieces| - 1 < |lines| && plan.line == lines[|plan.pieces| - 1] &&
      Spec.LineCutRelation(data, plan.line, |data|)
    decreases |lines|
  {
    hide *;
    reveal Core.SplitPlanFrom(), Core.LineExists(), Core.SafeSlice(), SplitPlanView();
    plan := SplitPlanView(Core.SplitPlanFrom(data, lines, start));
    if |lines| == 0 {
      cuts := [start, |data|];
      return;
    }

    assert lines[0] > 0 by { reveal Spec.ValidNumberPrefix(); }
    var next := Core.LineStart(data, lines[0]);
    LineStartRefines(data, lines[0]);
    if !Core.LineExists(data, lines[0]) {
      cuts := [start, next];
      return;
    }

    if |lines| > 1 {
      assert lines[0] <= lines[1] by { reveal Spec.ValidNumberPrefix(); }
      LineStartMonotone(data, lines[0], lines[1]);
    }
    assert Spec.ValidNumberPrefix(lines[1..], |lines[1..]|) by {
      reveal Spec.ValidNumberPrefix();
      forall i | 0 <= i < |lines[1..]|
        ensures lines[1..][i] > 0 && (i == 0 || lines[1..][i - 1] <= lines[1..][i])
      {
        TailIndex(lines, i);
        if i > 0 {
          TailIndex(lines, i - 1);
        }
      }
    }
    var tail, tailCuts := SplitPlanFromRefines(data, lines[1..], next);
    var pieces := plan.pieces;
    assert pieces == [data[start..next]] + tail.pieces by {
      match Core.SplitPlanFrom(data, lines[1..], next)
      case SplitComplete(_) =>
      case SplitOutOfRange(_, _) =>
    }
    cuts := [start] + tailCuts;
    forall i {:trigger cuts[i]} | 0 <= i < |pieces|
      ensures cuts[i] <= cuts[i + 1] <= |data| && pieces[i] == data[cuts[i]..cuts[i + 1]]
    {
      if i == 0 {
        assert cuts[1] == next;
      } else {
        var j := i - 1;
        assert cuts[i] == tailCuts[j] && cuts[i + 1] == tailCuts[j + 1];
        assert tailCuts[j] <= tailCuts[j + 1] <= |data|;
      }
    }
    forall i {:trigger cuts[i + 1]} | 0 <= i < |pieces| - 1
      ensures Spec.LineCutRelation(data, lines[i], cuts[i + 1]) && cuts[i + 1] < |data|
    {
      if i == 0 {
        assert cuts[1] == next;
      } else {
        var j := i - 1;
        TailIndex(lines, j);
        assert cuts[i + 1] == tailCuts[j + 1];
      }
    }
    match Core.SplitPlanFrom(data, lines[1..], next)
    case SplitComplete(_) =>
    case SplitOutOfRange(_, _) =>
      TailIndex(lines, |tail.pieces| - 1);
  }

  lemma SplitPlanRefines(data: BenchWorld.Bytes, lines: seq<nat>)
    requires Spec.ValidNumberPrefix(lines, |lines|)
    ensures Spec.SplitPlanRelation(
              data,
              lines,
              SplitPlanView(Core.SplitPlanFor(data, lines))
            )
  {
    hide *;
    var plan, cuts := SplitPlanFromRefines(data, lines, 0);
    reveal Core.SplitPlanFor(), Spec.SplitPlanRelation(), Spec.PiecePartitionRelation();
    assert Spec.PiecePartitionRelation(data, plan.pieces, cuts);
  }

  lemma ReadFailurePiecesRefines(data: BenchWorld.Bytes, lines: seq<nat>)
    requires Spec.ValidNumberPrefix(lines, |lines|)
    ensures Spec.ReadFailurePiecesRelation(data, lines, Core.ReadFailurePieces(data, lines))
  {
    var complete := Core.CompletedInputPrefix(data);
    var plan := Core.SplitPlanFor(complete, lines);
    SplitPlanRefines(complete, lines);
    assert Spec.ReadFailurePiecesRelation(data, lines, Core.ReadFailurePieces(data, lines)) by {
      reveal Spec.ReadFailurePiecesRelation();
      assert Spec.CompleteInputPrefixRelation(data, complete);
      assert Spec.SplitPlanRelation(complete, lines, SplitPlanView(plan));
      match plan
      case SplitComplete(pieces) =>
      case SplitOutOfRange(pieces, _) =>
    }
  }

  ghost predicate WarningsFromWitnessRelation(
    lines: seq<nat>,
    previous: nat,
    hasPrevious: bool,
    warnings: BenchWorld.Bytes,
    fragments: seq<BenchWorld.Bytes>,
    cuts: seq<nat>
  )
  {
    |fragments| == |lines| &&
    (forall i {:trigger fragments[i]} :: 0 <= i < |lines| ==>
                                           fragments[i] ==
                                           if (i == 0 && hasPrevious && lines[0] == previous) ||
                                              (i > 0 && lines[i] == lines[i - 1])
                                           then Spec.DuplicateWarning(lines[i])
                                           else []) &&
    Spec.FragmentsConcatenate(fragments, warnings, cuts)
  }

  ghost predicate WarningsFromRelation(
    lines: seq<nat>,
    previous: nat,
    hasPrevious: bool,
    warnings: BenchWorld.Bytes
  )
  {
    exists fragments: seq<BenchWorld.Bytes>, cuts: seq<nat> ::
      WarningsFromWitnessRelation(
        lines, previous, hasPrevious, warnings, fragments, cuts
      )
  }

  lemma PrefixShiftSlice(
    prefix: BenchWorld.Bytes,
    data: BenchWorld.Bytes,
    lo: nat,
    hi: nat
  )
    requires lo <= hi <= |data|
    ensures (prefix + data)[|prefix| + lo..|prefix| + hi] == data[lo..hi]
  {
  }

  lemma PrependFragment(
    head: BenchWorld.Bytes,
    tailFragments: seq<BenchWorld.Bytes>,
    tail: BenchWorld.Bytes,
    tailCuts: seq<nat>
  )
    requires Spec.FragmentsConcatenate(tailFragments, tail, tailCuts)
    ensures exists cuts: seq<nat> ::
              Spec.FragmentsConcatenate(
                [head] + tailFragments, head + tail, cuts
              )
  {
    reveal Spec.FragmentsConcatenate();
    var shiftedTailCuts :=
      seq(|tailCuts|, i requires 0 <= i < |tailCuts| =>
        |head| + tailCuts[i]);
    var cuts := [0] + shiftedTailCuts;
    assert |cuts| == |[head] + tailFragments| + 1;
    assert cuts[0] == 0;
    assert cuts[|cuts| - 1] == |head + tail|;
    forall i {:trigger cuts[i]} | 0 <= i < |[head] + tailFragments|
      ensures cuts[i] <= cuts[i + 1] <= |head + tail| &&
              cuts[i + 1] == cuts[i] + |([head] + tailFragments)[i]| &&
              (head + tail)[cuts[i]..cuts[i + 1]] ==
              ([head] + tailFragments)[i]
    {
      if i == 0 {
        assert cuts[1] == |head|;
        assert (head + tail)[..|head|] == head;
      } else {
        var j := i - 1;
        assert 0 <= j < |tailFragments|;
        assert cuts[i] == |head| + tailCuts[j];
        assert cuts[i + 1] == |head| + tailCuts[j + 1];
        PrefixShiftSlice(head, tail, tailCuts[j], tailCuts[j + 1]);
      }
    }
    assert Spec.FragmentsConcatenate(
        [head] + tailFragments, head + tail, cuts
      );
  }

  lemma {:isolate_assertions} DuplicateWarningsFromRefines(
    lines: seq<nat>,
    previous: nat,
    hasPrevious: bool
  )
    ensures WarningsFromRelation(
              lines,
              previous,
              hasPrevious,
              Core.DuplicateWarningsFrom(lines, previous, hasPrevious)
            )
    decreases |lines|
  {
    if |lines| == 0 {
      var fragments: seq<BenchWorld.Bytes> := [];
      var cuts: seq<nat> := [0];
      assert Spec.FragmentsConcatenate(fragments, [], cuts);
      assert WarningsFromWitnessRelation(
          lines, previous, hasPrevious, [], fragments, cuts
        );
      assert WarningsFromRelation(lines, previous, hasPrevious, []);
    } else {
      DuplicateWarningsFromRefines(lines[1..], lines[0], true);
      var tail := Core.DuplicateWarningsFrom(lines[1..], lines[0], true);
      assert WarningsFromRelation(lines[1..], lines[0], true, tail);
      reveal WarningsFromRelation();
      var tailFragments: seq<BenchWorld.Bytes>, tailCuts: seq<nat> :|
        WarningsFromWitnessRelation(
          lines[1..], lines[0], true, tail, tailFragments, tailCuts
        );
      reveal WarningsFromWitnessRelation();
      assert |tailFragments| + 1 == |lines| by {
        hide *;
        reveal WarningsFromWitnessRelation();
        assert WarningsFromWitnessRelation(lines[1..], lines[0], true, tail, tailFragments, tailCuts);
        assert |tailFragments| == |lines[1..]|;
      }
      var head :=
        if hasPrevious && lines[0] == previous
        then Spec.DuplicateWarning(lines[0])
        else [];
      PrependFragment(head, tailFragments, tail, tailCuts);
      var cuts: seq<nat> :| Spec.FragmentsConcatenate(
          [head] + tailFragments, head + tail, cuts
        );
      assert forall i :: 0 <= i < |lines| ==>
                           ([head] + tailFragments)[i] ==
                           if (i == 0 && hasPrevious && lines[0] == previous) ||
                              (i > 0 && lines[i] == lines[i - 1])
                           then Spec.DuplicateWarning(lines[i])
                           else [] by {
        forall i | 0 <= i < |lines|
          ensures ([head] + tailFragments)[i] ==
                  if (i == 0 && hasPrevious && lines[0] == previous) ||
                     (i > 0 && lines[i] == lines[i - 1])
                  then Spec.DuplicateWarning(lines[i])
                  else []
        {
          if i == 0 {
          } else {
            var j := i - 1;
            assert 0 <= j < |lines[1..]|;
            assert lines[i] == lines[1..][i - 1];
            assert 0 <= i < |[head] + tailFragments|;
            assert 0 <= i - 1 < |tailFragments|;
            assert ([head] + tailFragments)[i] == tailFragments[i - 1] by {
              hide *;
              reveal WarningsFromWitnessRelation();
            }
            if i == 1 {
              assert j == 0;
              assert (j == 0 && lines[1..][j] == lines[0]) ==
                     (lines[i] == lines[i - 1]);
            } else {
              assert j > 0;
              assert lines[1..][j - 1] == lines[i - 1];
              assert (j > 0 &&
                      lines[1..][j] == lines[1..][j - 1]) ==
                     (lines[i] == lines[i - 1]);
            }
            assert ((j == 0 && lines[1..][j] == lines[0]) ||
                    (j > 0 && lines[1..][j] == lines[1..][j - 1])) ==
                   (lines[i] == lines[i - 1]);
            assert tailFragments[j] ==
                   if (j == 0 && lines[1..][0] == lines[0]) ||
                      (j > 0 && lines[1..][j] == lines[1..][j - 1])
                   then Spec.DuplicateWarning(lines[1..][j])
                   else [];
            assert tailFragments[j] ==
                   if lines[i] == lines[i - 1]
                   then Spec.DuplicateWarning(lines[i])
                   else [];
          }
        }
      }
      assert Core.DuplicateWarningsFrom(lines, previous, hasPrevious) == head + tail by {
        hide *;
        reveal Core.DuplicateWarningsFrom();
      }
      assert WarningsFromWitnessRelation(
          lines,
          previous,
          hasPrevious,
          Core.DuplicateWarningsFrom(lines, previous, hasPrevious),
          [head] + tailFragments,
          cuts
        ) by {
        hide *;
        reveal WarningsFromWitnessRelation(), Core.DuplicateWarningsFrom();
      }
      assert WarningsFromRelation(
          lines, previous, hasPrevious,
          Core.DuplicateWarningsFrom(lines, previous, hasPrevious)
        );
    }
  }

  lemma DuplicateWarningsRefines(lines: seq<nat>)
    ensures Spec.DuplicateWarningsRelation(
              lines,
              Core.DuplicateWarnings(lines)
            )
  {
    DuplicateWarningsFromRefines(lines, 0, false);
    reveal WarningsFromRelation();
  }

  lemma PrependCountOutput(
    head: BenchWorld.Bytes,
    tailPieces: seq<BenchWorld.Bytes>,
    count: nat,
    tailOut: BenchWorld.Bytes
  )
    requires count <= |tailPieces|
    requires Spec.CountOutputRelation(tailPieces, count, tailOut)
    ensures Spec.CountOutputRelation(
              [head] + tailPieces,
              count + 1,
              Spec.CountLine(|head|) + tailOut
            )
  {
    reveal Spec.CountOutputRelation();
    var tailFragments: seq<BenchWorld.Bytes>, tailCuts: seq<nat> :|
      |tailFragments| == count &&
      (forall i :: 0 <= i < count ==>
                     tailFragments[i] == Spec.CountLine(|tailPieces[i]|)) &&
      Spec.FragmentsConcatenate(tailFragments, tailOut, tailCuts);
    var headFragment := Spec.CountLine(|head|);
    PrependFragment(headFragment, tailFragments, tailOut, tailCuts);
  }

  lemma EmptyCountOutput(pieces: seq<BenchWorld.Bytes>)
    ensures Spec.CountOutputRelation(pieces, 0, [])
  {
    var fragments: seq<BenchWorld.Bytes> := [];
    var cuts: seq<nat> := [0];
    assert Spec.FragmentsConcatenate(fragments, [], cuts);
  }

  lemma {:isolate_assertions} {:induction false} PrependWriteAttempt(observations: Spec.ObservationContext,
                                                                     pieces: seq<BenchWorld.Bytes>,
                                                                     index: nat,
                                                                     count: nat,
                                                                     preFs: BenchWorld.FileSystem,
                                                                     preNow: int,
                                                                     afterHeadFs: BenchWorld.FileSystem,
                                                                     headOk: bool,
                                                                     headErr: int,
                                                                     tailStates: seq<BenchWorld.FileSystem>,
                                                                     tailOks: seq<bool>,
                                                                     tailErrs: seq<int>
  )
    requires |pieces| > 0
    requires count <= |pieces[1..]|
    requires Core.WriteObservationFields(observations,
                                         preFs,
                                         preNow,
                                         Spec.OutputName(index),
                                         pieces[0],
                                         headOk,
                                         headErr,
                                         afterHeadFs
             )
    requires StateModel.ValueWriteAttemptsRelation(observations,
                                                   pieces[1..],
                                                   index + 1,
                                                   count,
                                                   afterHeadFs,
                                                   preNow,
                                                   tailStates,
                                                   tailOks,
                                                   tailErrs
             )
    ensures StateModel.ValueWriteAttemptsRelation(observations,
                                                  pieces,
                                                  index,
                                                  count + 1,
                                                  preFs,
                                                  preNow,
                                                  [preFs] + tailStates,
                                                  [headOk] + tailOks,
                                                  [headErr] + tailErrs
            )
  {
    reveal StateModel.ValueWriteAttemptsRelation();
    forall i | 0 <= i < count + 1
      ensures Core.WriteObservationFields(observations,
                                          ([preFs] + tailStates)[i],
                                          preNow,
                                          Spec.OutputName(index + i),
                                          ([pieces[0]] + pieces[1..])[i],
                                          ([headOk] + tailOks)[i],
                                          ([headErr] + tailErrs)[i],
                                          ([preFs] + tailStates)[i + 1]
              )
    {
      if i == 0 {
        assert ([preFs] + tailStates)[i] == preFs;
        assert ([preFs] + tailStates)[i + 1] == afterHeadFs;
      } else {
        var j := i - 1;
        assert 0 <= j < count;
        TailIndex(pieces, j);
        TailIndex([preFs] + tailStates, i);
        TailIndex([headOk] + tailOks, j);
        TailIndex([headErr] + tailErrs, j);
        assert index + 1 + (i - 1) == index + i;
        assert ([preFs] + tailStates)[i] == tailStates[i - 1];
        assert ([preFs] + tailStates)[i + 1] == tailStates[i];
        assert ([headOk] + tailOks)[i] == tailOks[i - 1];
        assert ([headErr] + tailErrs)[i] == tailErrs[i - 1];
        assert Core.WriteObservationFields(observations, tailStates[i - 1], preNow,
                                           Spec.OutputName(index + 1 + (i - 1)), pieces[1..][i - 1],
                                           tailOks[i - 1], tailErrs[i - 1], tailStates[i]);
      }
    }
  }

  lemma {:isolate_assertions} AppendCleanup(observations: Spec.ObservationContext,
                                            index: nat,
                                            count: nat,
                                            preFs: BenchWorld.FileSystem,
                                            middleFs: BenchWorld.FileSystem,
                                            fs2: BenchWorld.FileSystem,
                                            states: seq<BenchWorld.FileSystem>,
                                            ok: bool,
                                            err: int
  )
    requires StateModel.ValueCleanupRelation(observations, index + 1, count, preFs, middleFs, states)
    requires Core.DeleteObservationFields(observations,
                                          middleFs, Spec.OutputName(index), ok, err, fs2
             )
    ensures StateModel.ValueCleanupRelation(observations,
                                            index, count + 1, preFs, fs2, states + [fs2]
            )
  {
    reveal StateModel.ValueCleanupRelation();
    var priorOks, priorErrs :|
      StateModel.ValueCleanupWitnessRelation(observations,
                                             index + 1, count, preFs, middleFs, states, priorOks, priorErrs
      );
    reveal StateModel.ValueCleanupWitnessRelation();
    var oks := priorOks + [ok];
    var errs := priorErrs + [err];
    assert |states| == count + 1;
    assert |oks| == count + 1 && |errs| == count + 1;
    forall i | 0 <= i < count + 1
      ensures
        Core.DeleteObservationFields(observations,
                                     (states + [fs2])[i],
                                     Spec.OutputName(index + count - i),
                                     oks[i],
                                     errs[i],
                                     (states + [fs2])[i + 1]
        )
    {
      if i < count {
        assert (states + [fs2])[i] == states[i];
        assert (states + [fs2])[i + 1] == states[i + 1];
        assert index + count - i ==
               (index + 1) + count - 1 - i;
      } else {
        assert i == count;
        assert (states + [fs2])[i] == middleFs;
        assert (states + [fs2])[i + 1] == fs2;
        assert Core.DeleteObservationFields(observations,
                                            (states + [fs2])[i],
                                            Spec.OutputName(index + count - i),
                                            oks[i],
                                            errs[i],
                                            (states + [fs2])[i + 1]
          ) by {
          hide *;
        }
      }
    }
    assert StateModel.ValueCleanupWitnessRelation(observations,
                                                  index, count + 1, preFs, fs2, states + [fs2], oks, errs
      );
    assert StateModel.ValueCleanupRelation(observations,
                                           index, count + 1, preFs, fs2, states + [fs2]
      );
  }

  lemma EmptyCleanup(observations: Spec.ObservationContext,
                     index: nat,
                     fs: BenchWorld.FileSystem,
                     states: seq<BenchWorld.FileSystem>
  )
    requires states == [fs]
    ensures StateModel.ValueCleanupRelation(observations, index, 0, fs, fs, states)
  {
    var oks: seq<bool> := [];
    var errs: seq<int> := [];
    assert StateModel.ValueCleanupWitnessRelation(observations,
                                                  index, 0, fs, fs, states, oks, errs
      );
    assert StateModel.ValueCleanupRelation(observations, index, 0, fs, fs, states);
  }

  lemma {:isolate_assertions} {:induction false} SingleWriteFailureRefines(observations: Spec.ObservationContext,
                                                                           pieces: seq<BenchWorld.Bytes>,
                                                                           index: nat,
                                                                           terminalError: BenchWorld.Bytes,
                                                                           hasTerminalError: bool,
                                                                           preFs: BenchWorld.FileSystem,
                                                                           preNow: int,
                                                                           afterWriteFs: BenchWorld.FileSystem,
                                                                           err: int,
                                                                           fs2: BenchWorld.FileSystem
  )
    requires |pieces| > 0
    requires Core.WriteObservationFields(observations,
                                         preFs,
                                         preNow,
                                         Spec.OutputName(index),
                                         pieces[0],
                                         false,
                                         err,
                                         afterWriteFs
             )
    requires Core.FailedWriteCleanupFields(observations, preFs, preNow, Spec.OutputName(index), pieces[0], err, afterWriteFs, fs2)
    ensures StateModel.ValueWriteTraceRelation(observations,
                                               pieces,
                                               index,
                                               terminalError,
                                               hasTerminalError,
                                               preFs,
                                               preNow,
                                               fs2,
                                               [],
                                               Spec.WriteErrorMessage(Spec.OutputName(index), err),
                                               1
            )
  {
    var writeStates := [preFs, afterWriteFs];
    var writeOk := [false];
    var writeErr := [err];
    var cleanupStates := [fs2];
    assert StateModel.ValueWriteAttemptsRelation(observations,
                                                 pieces,
                                                 index,
                                                 1,
                                                 preFs,
                                                 preNow,
                                                 writeStates,
                                                 writeOk,
                                                 writeErr
      );
    EmptyCountOutput(pieces);
    EmptyCleanup(observations, index, fs2, cleanupStates);
    assert cleanupStates[0] == fs2;
    assert StateModel.ValueWriteTraceWitnessRelation(observations,
                                                     pieces,
                                                     index,
                                                     terminalError,
                                                     hasTerminalError,
                                                     preFs,
                                                     preNow,
                                                     fs2,
                                                     [],
                                                     Spec.WriteErrorMessage(Spec.OutputName(index), err),
                                                     1,
                                                     1,
                                                     writeStates,
                                                     writeOk,
                                                     writeErr,
                                                     cleanupStates
      );
    assert StateModel.ValueWriteTraceRelation(observations,
                                              pieces,
                                              index,
                                              terminalError,
                                              hasTerminalError,
                                              preFs,
                                              preNow,
                                              fs2,
                                              [],
                                              Spec.WriteErrorMessage(Spec.OutputName(index), err),
                                              1
      ) by {
      reveal StateModel.ValueWriteTraceRelation();
    }
  }

  lemma WriteTraceWitnessGivesRelation(observations: Spec.ObservationContext,
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
    requires StateModel.ValueWriteTraceWitnessRelation(observations,
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
    ensures StateModel.ValueWriteTraceRelation(observations,
                                               pieces,
                                               index,
                                               terminalError,
                                               hasTerminalError,
                                               preFs,
                                               preNow,
                                               fs2,
                                               stdout,
                                               stderr,
                                               exit
            )
  {
  }

  lemma ExtractWriteTraceWitness(observations: Spec.ObservationContext,
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
  ) returns (
      attempted: nat,
      writeStates: seq<BenchWorld.FileSystem>,
      writeOk: seq<bool>,
      writeErr: seq<int>,
      cleanupStates: seq<BenchWorld.FileSystem>
    )
    requires StateModel.ValueWriteTraceRelation(observations,
                                                pieces,
                                                index,
                                                terminalError,
                                                hasTerminalError,
                                                preFs,
                                                preNow,
                                                fs2,
                                                stdout,
                                                stderr,
                                                exit
             )
    ensures StateModel.ValueWriteTraceWitnessRelation(observations,
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
  {
    reveal StateModel.ValueWriteTraceRelation();
    attempted, writeStates, writeOk, writeErr, cleanupStates :|
      StateModel.ValueWriteTraceWitnessRelation(observations,
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
      );
  }

  lemma {:isolate_assertions} {:induction false} PrependSuccessfulWriteWitness(observations: Spec.ObservationContext,
                                                                               pieces: seq<BenchWorld.Bytes>,
                                                                               index: nat,
                                                                               terminalError: BenchWorld.Bytes,
                                                                               hasTerminalError: bool,
                                                                               preFs: BenchWorld.FileSystem,
                                                                               preNow: int,
                                                                               afterWriteFs: BenchWorld.FileSystem,
                                                                               headErr: int,
                                                                               tailFs: BenchWorld.FileSystem,
                                                                               tailOut: BenchWorld.Bytes,
                                                                               tailErr: BenchWorld.Bytes,
                                                                               tailExit: int,
                                                                               fs2: BenchWorld.FileSystem,
                                                                               deleteOk: bool,
                                                                               deleteErr: int,
                                                                               attempted: nat,
                                                                               tailWriteStates: seq<BenchWorld.FileSystem>,
                                                                               tailWriteOk: seq<bool>,
                                                                               tailWriteErr: seq<int>,
                                                                               tailCleanupStates: seq<BenchWorld.FileSystem>
  )
    requires |pieces| > 0
    requires Core.WriteObservationFields(observations,
                                         preFs,
                                         preNow,
                                         Spec.OutputName(index),
                                         pieces[0],
                                         true,
                                         headErr,
                                         afterWriteFs
             )
    requires StateModel.ValueWriteTraceWitnessRelation(observations,
                                                       pieces[1..],
                                                       index + 1,
                                                       terminalError,
                                                       hasTerminalError,
                                                       afterWriteFs,
                                                       preNow,
                                                       tailFs,
                                                       tailOut,
                                                       tailErr,
                                                       tailExit,
                                                       attempted,
                                                       tailWriteStates,
                                                       tailWriteOk,
                                                       tailWriteErr,
                                                       tailCleanupStates
             )
    requires if hasTerminalError || tailExit != 0 then
               Core.DeleteObservationFields(observations,
                                            tailFs, Spec.OutputName(index), deleteOk, deleteErr, fs2
               )
             else
               fs2 == tailFs
    ensures StateModel.ValueWriteTraceRelation(observations,
                                               pieces,
                                               index,
                                               terminalError,
                                               hasTerminalError,
                                               preFs,
                                               preNow,
                                               fs2,
                                               Spec.CountLine(|pieces[0]|) + tailOut,
                                               tailErr,
                                               tailExit
            )
  {
    hide *;
    reveal StateModel.ValueWriteTraceWitnessRelation(), StateModel.ValueWriteAttemptsRelation();
    assert pieces == [pieces[0]] + pieces[1..];
    var writeStates := [preFs] + tailWriteStates;
    var writeOk := [true] + tailWriteOk;
    var writeErr := [headErr] + tailWriteErr;
    PrependWriteAttempt(observations,
                        pieces,
                        index,
                        attempted,
                        preFs,
                        preNow,
                        afterWriteFs,
                        true,
                        headErr,
                        tailWriteStates,
                        tailWriteOk,
                        tailWriteErr
    );
    if attempted > 0 && !tailWriteOk[attempted - 1] {
      var failedCleanupFs := tailCleanupStates[0];
      PrependCountOutput(pieces[0], pieces[1..], attempted - 1, tailOut);
      AppendCleanup(observations,
                    index,
                    attempted - 1,
                    failedCleanupFs,
                    tailFs,
                    fs2,
                    tailCleanupStates,
                    deleteOk,
                    deleteErr
      );
      var cleanupStates := tailCleanupStates + [fs2];
      assert Core.FailedWriteCleanupFields(observations, writeStates[attempted], preNow,
                                           Spec.OutputName(index + attempted), pieces[attempted], writeErr[attempted],
                                           writeStates[attempted + 1], failedCleanupFs);
      assert StateModel.ValueCleanupRelation(observations, index, attempted, failedCleanupFs, fs2, cleanupStates);
      assert StateModel.ValueWriteTraceWitnessRelation(observations,
                                                       pieces,
                                                       index,
                                                       terminalError,
                                                       hasTerminalError,
                                                       preFs,
                                                       preNow,
                                                       fs2,
                                                       Spec.CountLine(|pieces[0]|) + tailOut,
                                                       tailErr,
                                                       tailExit,
                                                       attempted + 1,
                                                       writeStates,
                                                       writeOk,
                                                       writeErr,
                                                       cleanupStates
        );
      WriteTraceWitnessGivesRelation(observations,
                                     pieces, index, terminalError, hasTerminalError, preFs, preNow,
                                     fs2, Spec.CountLine(|pieces[0]|) + tailOut, tailErr, tailExit,
                                     attempted + 1, writeStates, writeOk, writeErr, cleanupStates
      );
    } else {
      PrependCountOutput(pieces[0], pieces[1..], attempted, tailOut);
      if hasTerminalError {
        AppendCleanup(observations,
                      index,
                      attempted,
                      tailWriteStates[attempted],
                      tailFs,
                      fs2,
                      tailCleanupStates,
                      deleteOk,
                      deleteErr
        );
        var cleanupStates := tailCleanupStates + [fs2];
        assert StateModel.ValueWriteTraceWitnessRelation(observations,
                                                         pieces,
                                                         index,
                                                         terminalError,
                                                         hasTerminalError,
                                                         preFs,
                                                         preNow,
                                                         fs2,
                                                         Spec.CountLine(|pieces[0]|) + tailOut,
                                                         tailErr,
                                                         tailExit,
                                                         attempted + 1,
                                                         writeStates,
                                                         writeOk,
                                                         writeErr,
                                                         cleanupStates
          );
        WriteTraceWitnessGivesRelation(observations,
                                       pieces, index, terminalError, hasTerminalError, preFs, preNow,
                                       fs2, Spec.CountLine(|pieces[0]|) + tailOut, tailErr, tailExit,
                                       attempted + 1, writeStates, writeOk, writeErr, cleanupStates
        );
      } else {
        var cleanupStates := [fs2];
        assert StateModel.ValueWriteTraceWitnessRelation(observations,
                                                         pieces,
                                                         index,
                                                         terminalError,
                                                         hasTerminalError,
                                                         preFs,
                                                         preNow,
                                                         fs2,
                                                         Spec.CountLine(|pieces[0]|) + tailOut,
                                                         tailErr,
                                                         tailExit,
                                                         attempted + 1,
                                                         writeStates,
                                                         writeOk,
                                                         writeErr,
                                                         cleanupStates
          );
        WriteTraceWitnessGivesRelation(observations,
                                       pieces, index, terminalError, hasTerminalError, preFs, preNow,
                                       fs2, Spec.CountLine(|pieces[0]|) + tailOut, tailErr, tailExit,
                                       attempted + 1, writeStates, writeOk, writeErr, cleanupStates
        );
      }
    }
  }

  lemma {:isolate_assertions} WriteTraceSummaryRefines(observations: Spec.ObservationContext,
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
    requires Core.WriteTraceSummaryFields(observations,
                                          pieces,
                                          index,
                                          terminalError,
                                          hasTerminalError,
                                          preFs,
                                          preNow,
                                          fs2,
                                          stdout,
                                          stderr,
                                          exit
             )
    ensures StateModel.ValueWriteTraceRelation(observations,
                                               pieces,
                                               index,
                                               terminalError,
                                               hasTerminalError,
                                               preFs,
                                               preNow,
                                               fs2,
                                               stdout,
                                               stderr,
                                               exit
            )
    decreases |pieces|
  {

    if |pieces| == 0 {
      var writeStates := [preFs];
      var writeOk: seq<bool> := [];
      var writeErr: seq<int> := [];
      var cleanupStates := [preFs];
      assert StateModel.ValueWriteAttemptsRelation(observations,
                                                   pieces, index, 0, preFs, preNow, writeStates, writeOk, writeErr
        );
      EmptyCountOutput(pieces);
      EmptyCleanup(observations, index, preFs, cleanupStates);
      assert StateModel.ValueWriteTraceWitnessRelation(observations,
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
                                                       0,
                                                       writeStates,
                                                       writeOk,
                                                       writeErr,
                                                       cleanupStates
        );
      WriteTraceWitnessGivesRelation(observations,
                                     pieces, index, terminalError, hasTerminalError, preFs, preNow,
                                     fs2, stdout, stderr, exit, 0, writeStates, writeOk, writeErr,
                                     cleanupStates
      );
    } else {

      var afterWriteFs, ok, err :|
        Core.WriteObservationFields(observations,
                                    preFs,
                                    preNow,
                                    Spec.OutputName(index),
                                    pieces[0],
                                    ok,
                                    err,
                                    afterWriteFs
        ) &&
        if ok then
          exists tailFs: BenchWorld.FileSystem, tailOut: BenchWorld.Bytes,
            tailErr: BenchWorld.Bytes, tailExit: int
            {:trigger Core.WriteTraceSummaryFields(observations,
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
            Core.WriteTraceSummaryFields(observations,
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
                 Core.DeleteObservationFields(observations,
                                              tailFs, Spec.OutputName(index), deleteOk, deleteErr, fs2
                 )
             else
               fs2 == tailFs) &&
            stdout == Spec.CountLine(|pieces[0]|) + tailOut &&
            stderr == tailErr &&
            exit == tailExit
        else
          Core.FailedWriteCleanupFields(observations, preFs, preNow, Spec.OutputName(index), pieces[0], err, afterWriteFs, fs2) &&
          stdout == [] &&
          stderr == Spec.WriteErrorMessage(Spec.OutputName(index), err) &&
          exit == 1;
      if !ok {
        SingleWriteFailureRefines(observations,
                                  pieces,
                                  index,
                                  terminalError,
                                  hasTerminalError,
                                  preFs,
                                  preNow,
                                  afterWriteFs,
                                  err,
                                  fs2
        );
      } else {
        var tailFs, tailOut, tailErr, tailExit :|
          Core.WriteTraceSummaryFields(observations,
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
               Core.DeleteObservationFields(observations,
                                            tailFs, Spec.OutputName(index), deleteOk, deleteErr, fs2
               )
           else
             fs2 == tailFs) &&
          stdout == Spec.CountLine(|pieces[0]|) + tailOut &&
          stderr == tailErr &&
          exit == tailExit;
        WriteTraceSummaryRefines(observations,
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
        );
        var attempted, tailWriteStates, tailWriteOk, tailWriteErr,
            tailCleanupStates := ExtractWriteTraceWitness(observations,
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
        );
        var deleteOk: bool := false;
        var deleteErr: int := 0;
        if hasTerminalError || tailExit != 0 {
          deleteOk, deleteErr :|
            Core.DeleteObservationFields(observations,
                                         tailFs, Spec.OutputName(index), deleteOk, deleteErr, fs2
            );
        } else {
          assert fs2 == tailFs;
        }
        PrependSuccessfulWriteWitness(observations,
                                      pieces,
                                      index,
                                      terminalError,
                                      hasTerminalError,
                                      preFs,
                                      preNow,
                                      afterWriteFs,
                                      err,
                                      tailFs,
                                      tailOut,
                                      tailErr,
                                      tailExit,
                                      fs2,
                                      deleteOk,
                                      deleteErr,
                                      attempted,
                                      tailWriteStates,
                                      tailWriteOk,
                                      tailWriteErr,
                                      tailCleanupStates
        );
      }
    }
  }

  twostate lemma WritePiecesSummaryRefines(io: BenchIO.IO,
                                           pieces: seq<BenchWorld.Bytes>, index: nat,
                                           stdout: BenchWorld.Bytes, stderr: BenchWorld.Bytes, exit: int)
    requires Core.WritePiecesSummary(io, pieces, index, stdout, stderr, exit)
    ensures Spec.WritePiecesSummary(io, pieces, index, stdout, stderr, exit)
  {
    WriteTraceSummaryRefines(old(Spec.Context(io)), pieces, index, [], false,
                             old(io.fs()), old(io.now()), io.fs(), stdout, stderr, exit);
    WriteTraceRelationMatchesStateModel(io, pieces, index, [], false, stdout, stderr, exit);
  }

  twostate lemma WritePiecesThenErrorSummaryRefines(io: BenchIO.IO,
                                                    pieces: seq<BenchWorld.Bytes>, index: nat, line: nat,
                                                    stdout: BenchWorld.Bytes, stderr: BenchWorld.Bytes, exit: int)
    requires Core.WritePiecesThenErrorSummary(io, pieces, index, line, stdout, stderr, exit)
    ensures Spec.WritePiecesThenErrorSummary(io, pieces, index, line, stdout, stderr, exit)
  {
    WriteTraceSummaryRefines(old(Spec.Context(io)), pieces, index, Spec.OutOfRangeMessage(line), true,
                             old(io.fs()), old(io.now()), io.fs(), stdout, stderr, exit);
    WriteTraceRelationMatchesStateModel(io, pieces, index, Spec.OutOfRangeMessage(line), true, stdout, stderr, exit);
  }

  lemma DeferredReadResultRefines(raw: Schema.CsplitCmdRaw,
                                  preFs: BenchWorld.FileSystem, preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult,
                                  preStdin: BenchWorld.Bytes)
    ensures Core.DeferredReadResultFields(raw, preFs, preStreams, preStdin) ==
            Spec.DeferredReadResultFields(raw, preFs, preStreams, preStdin)
  {
    AnalyzeNumbersRefines(raw.lineNumbers);
    var analysis := Core.AnalyzeNumbers(raw.lineNumbers);
    assert (analysis.status == Core.NumbersOk) == Spec.ValidNumberPrefix(raw.lineNumbers, |raw.lineNumbers|) by {
      match analysis.status
      case NumbersOk =>
      case NumberZero =>
    assert raw.lineNumbers[analysis.processed] == 0;
      case NumberBackwards(current, previous) =>
    assert raw.lineNumbers[analysis.processed] < raw.lineNumbers[analysis.processed - 1];
    }
  }

  twostate lemma {:isolate_assertions} PreparedSummaryImpliesPreparedSpec(raw: Schema.CsplitCmdRaw, io: BenchIO.IO, exit: int, new plannedStdout: BenchWorld.Bytes, new plannedStderr: BenchWorld.Bytes)
    requires Core.PreparedSummary(raw, io, exit, plannedStdout, plannedStderr)
    ensures Spec.PreparedSpec(raw, io, exit, plannedStdout, plannedStderr)
  {
    if raw.mode == Schema.ModeHelp {
      assert Spec.PreparedSpec(raw, io, exit, plannedStdout, plannedStderr);
      return;
    }
    if raw.mode == Schema.ModeVersion {
      assert Spec.PreparedSpec(raw, io, exit, plannedStdout, plannedStderr);
      return;
    }

    DeferredReadResultRefines(raw, old(io.fs()), old(io.trustedStreams()), old(io.stdin()));
    AnalyzeNumbersRefines(raw.lineNumbers);
    match Spec.DeferredReadResultFields(raw, old(io.fs()), old(io.trustedStreams()), old(io.stdin()))
    case Err(err) =>
      PartialStdinFailureFieldsMatchesStateModel(io, raw, err, plannedStdout, plannedStderr, exit);
      assert io.stdin() == Spec.ReadStdinAfterFields(raw.input, old(io.stdin()), old(io.trustedStreams()));
      if raw.input.Stdin? {
        var analysis := Core.AnalyzeNumbers(raw.lineNumbers);
        assert analysis.status == Core.NumbersOk;
        assert analysis.processed == |raw.lineNumbers|;
        assert Spec.NumberAnalysisRelation(raw.lineNumbers, Spec.NumbersOk,
                                           analysis.processed, analysis.warnings);
        assert Spec.ValidNumberPrefix(raw.lineNumbers, |raw.lineNumbers|);
        assert Spec.DuplicateWarningsRelation(raw.lineNumbers, analysis.warnings) by {
          hide *;
          reveal Spec.NumberAnalysisRelation();
          assert raw.lineNumbers[..analysis.processed] == raw.lineNumbers;
        }
        var pieces := Core.ReadFailurePieces(IOContract.ReadResultData(Result.Err(err)), raw.lineNumbers);
        ReadFailurePiecesRefines(IOContract.ReadResultData(Result.Err(err)), raw.lineNumbers);
        assert Core.PartialStdinFailureSummary(io, raw, err, plannedStdout, plannedStderr, exit) by {
          hide *;
          reveal Core.PreparedSummary();
        }
        reveal Core.PartialStdinFailureSummary();
        var writeDiagnostics :|
          Core.WriteTraceSummary(io, pieces, 0, Spec.ReadErrorMessage(raw.input, err), true,
                                 plannedStdout, writeDiagnostics, exit) &&
          plannedStderr == analysis.warnings + writeDiagnostics && exit == 1;
        assert Core.WriteTraceSummaryFields(old(Spec.Context(io)), pieces, 0, Spec.ReadErrorMessage(raw.input, err), true,
                                            old(io.fs()), old(io.now()), io.fs(), plannedStdout, writeDiagnostics, exit) by {
          hide *;
          reveal Core.WriteTraceSummary(), Core.WriteTraceSummaryFields();
          assert Core.WriteTraceSummary(io, pieces, 0, Spec.ReadErrorMessage(raw.input, err), true,
                                        plannedStdout, writeDiagnostics, exit);
        }
        WriteTraceSummaryRefines(old(Spec.Context(io)), pieces, 0, Spec.ReadErrorMessage(raw.input, err), true,
                                 old(io.fs()), old(io.now()), io.fs(), plannedStdout, writeDiagnostics, exit);
        assert StateModel.ValuePartialStdinFailureFields(old(Spec.Context(io)), raw, err, old(io.fs()), old(io.now()), io.fs(),
                                                         plannedStdout, plannedStderr, exit) by {
          hide *;
          reveal StateModel.ValuePartialStdinFailureFields();
        }
      } else {
        assert io.fs() == old(io.fs());
        assert plannedStdout == [];
        assert plannedStderr == Spec.ReadErrorMessage(raw.input, err);
        assert exit == 1;
      }
      assert Spec.PreparedSpec(raw, io, exit, plannedStdout, plannedStderr) by {
        hide *;
        reveal Spec.PreparedSpec();
      }
    case Ok(data) =>
      AnalyzeNumbersRefines(raw.lineNumbers);
      var analysis := Core.AnalyzeNumbers(raw.lineNumbers);
      match analysis.status
      case NumberZero =>
        assert Spec.PreparedSpec(raw, io, exit, plannedStdout, plannedStderr) by {
          assert exists status: Spec.NumberStatus, processed: nat,
              warnings: BenchWorld.Bytes ::
              Spec.NumberAnalysisRelation(
                raw.lineNumbers, status, processed, warnings
              ) &&
              status == Spec.NumberZero &&
              processed == analysis.processed &&
              warnings == analysis.warnings;
        }
      case NumberBackwards(current, previous) =>
        assert Spec.PreparedSpec(raw, io, exit, plannedStdout, plannedStderr) by {
          assert exists status: Spec.NumberStatus, processed: nat,
              warnings: BenchWorld.Bytes ::
              Spec.NumberAnalysisRelation(
                raw.lineNumbers, status, processed, warnings
              ) &&
              status == Spec.NumberBackwards(current, previous) &&
              processed == analysis.processed &&
              warnings == analysis.warnings;
        }
      case NumbersOk =>
        assert Spec.NumberAnalysisRelation(
            raw.lineNumbers,
            Spec.NumbersOk,
            analysis.processed,
            analysis.warnings
          );
        SplitPlanRefines(data, raw.lineNumbers);
        var splitPlan := Core.SplitPlanFor(data, raw.lineNumbers);
        var warnings := analysis.warnings;
        match splitPlan
        case SplitOutOfRange(pieces, line) =>
          var writeOut, writeErr :|
            Core.WritePiecesThenErrorSummary(io, pieces, 0, line, writeOut, writeErr, exit) &&
            plannedStdout == writeOut &&
            plannedStderr == warnings + writeErr;
          WritePiecesThenErrorSummaryRefines(io, pieces, 0, line, writeOut, writeErr, exit);
          assert Spec.PreparedSpec(raw, io, exit, plannedStdout, plannedStderr) by {
            assert exists status: Spec.NumberStatus, processed: nat,
                warningOutput: BenchWorld.Bytes ::
                Spec.NumberAnalysisRelation(
                  raw.lineNumbers, status, processed, warningOutput
                ) &&
                status == Spec.NumbersOk &&
                processed == analysis.processed &&
                warningOutput == warnings;
            assert exists plan: Spec.SplitPlan ::
                Spec.SplitPlanRelation(data, raw.lineNumbers, plan) &&
                plan == Spec.SplitOutOfRange(pieces, line);
          }
        case SplitComplete(pieces) =>
          var writeOut, writeErr :|
            Core.WritePiecesSummary(io, pieces, 0, writeOut, writeErr, exit) &&
            plannedStdout == writeOut &&
            plannedStderr == warnings + writeErr;
          WritePiecesSummaryRefines(io, pieces, 0, writeOut, writeErr, exit);
          assert Spec.PreparedSpec(raw, io, exit, plannedStdout, plannedStderr) by {
            assert exists status: Spec.NumberStatus, processed: nat,
                warningOutput: BenchWorld.Bytes ::
                Spec.NumberAnalysisRelation(
                  raw.lineNumbers, status, processed, warningOutput
                ) &&
                status == Spec.NumbersOk &&
                processed == analysis.processed &&
                warningOutput == warnings;
            assert exists plan: Spec.SplitPlan ::
                Spec.SplitPlanRelation(data, raw.lineNumbers, plan) &&
                plan == Spec.SplitComplete(pieces);
          }
  }

  twostate lemma CoreSummaryImpliesSpec(raw: Schema.CsplitCmdRaw, io: BenchIO.IO, exit: int)
    requires Core.CoreSummary(raw, io, exit)
    ensures Spec.Spec(raw, io, exit)
  {
    var out: BenchWorld.Bytes, diagnostics: BenchWorld.Bytes, normalExit: int :|
      Core.PreparedSummary(raw, io, normalExit,
                           out, diagnostics) &&
      Spec.Emit(io, out, diagnostics, normalExit, exit);
    PreparedSummaryImpliesPreparedSpec(raw, io, normalExit,
                                       out, diagnostics);
  }
}

// Snapshot judgments for composing intermediate implementation evidence.
module CsplitTransitionModel {
  import Core = CsplitCore
  import opened Spec = CsplitSpec
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

  ghost predicate ValueWriteAttemptsRelation(observations: ObservationContext,
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
    forall i {:trigger states[i]} {:split false} :: 0 <= i < count ==>
                                                      Core.WriteObservationFields(observations,
                                                                                  states[i],
                                                                                  preNow,
                                                                                  OutputName(index + i),
                                                                                  pieces[i],
                                                                                  oks[i],
                                                                                  errs[i],
                                                                                  states[i + 1]
                                                      )
  }

  ghost predicate ValueCleanupWitnessRelation(observations: ObservationContext,
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
    forall i {:trigger states[i]} {:split false} :: 0 <= i < count ==>
                                                      Core.DeleteObservationFields(observations,
                                                                                   states[i],
                                                                                   OutputName(index + count - 1 - i),
                                                                                   oks[i],
                                                                                   errs[i],
                                                                                   states[i + 1]
                                                      )
  }

  ghost predicate ValueCleanupRelation(observations: ObservationContext,
                                       index: nat,
                                       count: nat,
                                       preFs: BenchWorld.FileSystem,
                                       fs2: BenchWorld.FileSystem,
                                       states: seq<BenchWorld.FileSystem>
  )
  {
    exists oks: seq<bool>, errs: seq<int> ::
      ValueCleanupWitnessRelation(observations,
                                  index, count, preFs, fs2, states, oks, errs
      )
  }

  ghost predicate ValueWriteTraceWitnessRelation(observations: ObservationContext,
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
    ValueWriteAttemptsRelation(observations,
                               pieces, index, attempted, preFs, preNow, writeStates, writeOk, writeErr
    ) &&
    (forall i :: 0 <= i && i + 1 < attempted ==> writeOk[i]) &&
    if attempted > 0 && !writeOk[attempted - 1] then
      CountOutputRelation(pieces, attempted - 1, stdout) &&
      |cleanupStates| > 0 &&
      Core.FailedWriteCleanupFields(observations, writeStates[attempted - 1], preNow,
                                    OutputName(index + attempted - 1), pieces[attempted - 1], writeErr[attempted - 1],
                                    writeStates[attempted], cleanupStates[0]) &&
      ValueCleanupRelation(observations, index, attempted - 1, cleanupStates[0], fs2, cleanupStates) &&
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
        ValueCleanupRelation(observations,
                             index, attempted, writeStates[attempted], fs2, cleanupStates
        ) &&
        stderr == terminalError &&
        exit == 1
      else
        fs2 == writeStates[attempted] &&
        stderr == [] &&
        exit == 0
  }

  ghost predicate ValueWriteTraceRelation(observations: ObservationContext,
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
      ValueWriteTraceWitnessRelation(observations,
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

  ghost predicate ValueWritePiecesSummaryFields(observations: ObservationContext,
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
    ValueWriteTraceRelation(observations,
                            pieces, index, [], false, preFs, preNow, fs2, stdout, stderr, exit
    )
  }

  ghost predicate ValueWritePiecesThenErrorSummaryFields(observations: ObservationContext,
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
    ValueWriteTraceRelation(observations,
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

  ghost predicate ValuePartialStdinFailureFields(observations: ObservationContext, raw: Schema.CsplitCmdRaw, error: BenchWorld.IOError,
                                                 beforeFs: BenchWorld.FileSystem, beforeNow: int, afterFs: BenchWorld.FileSystem,
                                                 output: BenchWorld.Bytes, diagnostics: BenchWorld.Bytes, exit: int)
  {
    exists pieces: seq<BenchWorld.Bytes>, warnings: BenchWorld.Bytes, writeDiagnostics: BenchWorld.Bytes ::
      DuplicateWarningsRelation(raw.lineNumbers, warnings) &&
      ReadFailurePiecesRelation(IOContract.ReadResultData(Result.Err(error)), raw.lineNumbers, pieces) &&
      ValueWriteTraceRelation(observations, pieces, 0, ReadErrorMessage(raw.input, error), true,
                              beforeFs, beforeNow, afterFs, output, writeDiagnostics, exit) &&
      diagnostics == warnings + writeDiagnostics && exit == 1
  }

}
