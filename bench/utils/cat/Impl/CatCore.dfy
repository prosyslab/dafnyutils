include "../Spec/CatSpec.dfy"
include "../../../core/World.dfy"
include "../../../core/IO.dfy"
include "../../../core/IOContract.dfy"
include "../Spec/CatSchema.dfy"

// Execution state used by the cat loop and proof helpers.
module CatCoreModel {
  import BenchWorld

  datatype RenderState = RenderState(nextLine: int, atLineStart: bool, blankStreak: int)
  datatype RenderResult = RenderResult(out: BenchWorld.Bytes, state: RenderState)

  function InitState(): RenderState
  {
    RenderState(1, true, 0)
  }

}

// Public core surface: executable loop plus summary predicates.
module CatCore {
  import StreamContract = IOContract
  import Result = Results
  import BenchIO
  import BenchWorld
  import IOContract
  import CatSchema
  import Model = CatCoreModel
  import Spec = CatSpec

  datatype RenderStep = RenderStep(
    before: Model.RenderState,
    after: Model.RenderState,
    chunk: BenchWorld.Bytes,
    number: nat
  )

  datatype RenderWitness = RenderWitness(
    steps: seq<RenderStep>,
    cuts: seq<nat>
  )

  datatype InputObservation = InputObservation(
    input: CatSchema.Input,
    result: BenchWorld.IOResult<BenchWorld.Bytes>
  )

  datatype CoreWitness =
      NonRunWitness
    | RunWitness(
        observations: seq<InputObservation>,
        data: BenchWorld.Bytes,
        dataCuts: seq<nat>,
        errors: BenchWorld.Bytes,
        errorCuts: seq<nat>,
        hadError: bool,
        processed: Model.RenderResult,
        renderTrace: RenderWitness
      )

  opaque ghost predicate RenderStepRelation(
    cmd: CatSchema.CatCmd,
    ch: BenchWorld.RawByte,
    nextIsNewline: bool,
    step: RenderStep
  )
  {
    1 <= step.before.nextLine &&
    0 <= step.before.blankStreak &&
    if ch == '\n' then
      var blankStreak :=
        if step.before.atLineStart then
          step.before.blankStreak + 1
        else
          0;
      if cmd.squeezeBlank &&
         step.before.atLineStart &&
         blankStreak >= 2
      then
        step.number == 0 &&
        step.chunk == [] &&
        step.after ==
        Model.RenderState(
          step.before.nextLine,
          true,
          blankStreak
        )
      else
        var numbered :=
          cmd.number == CatSchema.NumberAll &&
          step.before.atLineStart;
        step.number ==
        (if numbered then step.before.nextLine as nat else 0) &&
        step.chunk ==
        (if numbered then
           Spec.LineNumberText(step.before.nextLine)
         else
           []) +
        (if cmd.showEnds then ['$'] else []) +
        ['\n'] &&
        step.after ==
        Model.RenderState(
          step.before.nextLine + (if numbered then 1 else 0),
          true,
          blankStreak
        )
    else
      var numbered :=
        step.before.atLineStart &&
        cmd.number != CatSchema.NoNumber;
      step.number ==
      (if numbered then step.before.nextLine as nat else 0) &&
      step.chunk ==
      (if numbered then
         Spec.LineNumberText(step.before.nextLine)
       else
         []) +
      Spec.TransformChar(cmd, ch, nextIsNewline) &&
      step.after ==
      Model.RenderState(
        step.before.nextLine + (if numbered then 1 else 0),
        false,
        0
      )
  }

  opaque ghost predicate NumberTraceRelation(
    steps: seq<RenderStep>,
    count: nat,
    currentState: Model.RenderState
  )
  {
    |steps| == count &&
    currentState.nextLine ==
    1 + |set q: nat |
    q < count && steps[q].number > 0| &&
    forall p: nat {:trigger steps[p]} | p < count ::
      steps[p].before.nextLine ==
      1 + |set q: nat |
      q < p && steps[q].number > 0|
  }

  opaque ghost predicate RenderPrefixEvidence(
    cmd: CatSchema.CatCmd,
    data: BenchWorld.Bytes,
    count: nat,
    currentState: Model.RenderState,
    output: BenchWorld.Bytes,
    steps: seq<RenderStep>,
    cuts: seq<nat>
  )
  {
    count <= |data| &&
    1 <= currentState.nextLine &&
    0 <= currentState.blankStreak &&
    |steps| == count &&
    |cuts| == count + 1 &&
    cuts[0] == 0 &&
    cuts[|cuts| - 1] == |output| &&
    currentState ==
    (if count == 0 then Model.InitState()
     else steps[count - 1].after) &&
    NumberTraceRelation(steps, count, currentState) &&
    (forall p: nat {:trigger steps[p]} | p < count ::
       RenderStepRelation(
         cmd,
         data[p],
         p + 1 < |data| && data[p + 1] == '\n',
         steps[p]
       ) &&
       steps[p].before ==
       (if p == 0 then Model.InitState() else steps[p - 1].after) &&
       cuts[p + 1] == cuts[p] + |steps[p].chunk| &&
       cuts[p + 1] <= |output| &&
       output[cuts[p]..cuts[p + 1]] == steps[p].chunk)
  }

  ghost predicate RenderWitnessRelation(
    cmd: CatSchema.CatCmd,
    data: BenchWorld.Bytes,
    processed: Model.RenderResult,
    renderTrace: RenderWitness
  )
  {
    RenderPrefixEvidence(
      cmd,
      data,
      |data|,
      processed.state,
      processed.out,
      renderTrace.steps,
      renderTrace.cuts
    )
  }

  ghost function ExpectedStdinAt(
    cmd: CatSchema.CatCmd,
    preStdin: BenchWorld.Bytes,
    count: nat
  , preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult): BenchWorld.Bytes
    requires count <= |cmd.inputs|
    decreases count
  {
    if count == 0 then preStdin else
    var previous := ExpectedStdinAt(cmd, preStdin, count - 1, preStreams);
    if cmd.inputs[count - 1].Stdin? then IOContract.ObservedReadStdinRemainingFields(previous, preStreams) else previous
  }

  ghost predicate InputObservationRelation(
    cmd: CatSchema.CatCmd,
    preFs: BenchWorld.FileSystem, preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult,
    preStdin: BenchWorld.Bytes,
    i: nat,
    observation: InputObservation
  )
    requires i < |cmd.inputs|
  {
    observation.input == cmd.inputs[i] &&
    observation.result ==
    match observation.input
    case Stdin => IOContract.ObservedReadStdinResultFields(ExpectedStdinAt(cmd, preStdin, i, preStreams), preStreams)
    case File(path) => IOContract.ObservedReadFileResultFields(preFs, preStreams, path)
  }

  ghost function InputDataPiece(
    observation: InputObservation
  ): BenchWorld.Bytes
  {
    match observation.result
    case Ok(data) => data
    case Err(error) => IOContract.ReadResultData(observation.result)
  }

  ghost function InputErrorPiece(
    observation: InputObservation
  ): BenchWorld.Bytes
  {
    match observation.input
    case Stdin => if observation.result.Err? then Spec.ErrorMessageSpec("-", observation.result.e) else []
    case File(path) =>
      match observation.result
      case Ok(_) => []
      case Err(err) => Spec.ErrorMessageSpec(path, err)
  }

  ghost predicate InputFailed(observation: InputObservation)
  {
    observation.result.Err?
  }

  ghost function ObservationDataFragments(
    observations: seq<InputObservation>
  ): seq<BenchWorld.Bytes>
  {
    seq(
    |observations|,
    i requires 0 <= i < |observations| => InputDataPiece(observations[i])
      )
  }

  ghost function ObservationErrorFragments(
    observations: seq<InputObservation>
  ): seq<BenchWorld.Bytes>
  {
    seq(
    |observations|,
    i requires 0 <= i < |observations| => InputErrorPiece(observations[i])
      )
  }

  ghost predicate HasFailedObservation(observations: seq<InputObservation>)
  {
    exists i: nat :: i < |observations| && InputFailed(observations[i])
  }

  opaque ghost predicate InputTraceWitnessRelation(
    cmd: CatSchema.CatCmd,
    preFs: BenchWorld.FileSystem, preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult,
    preStdin: BenchWorld.Bytes,
    count: nat,
    currentStdin: BenchWorld.Bytes,
    observations: seq<InputObservation>,
    data: BenchWorld.Bytes,
    dataCuts: seq<nat>,
    errors: BenchWorld.Bytes,
    errorCuts: seq<nat>,
    hadError: bool
  )
  {
    count <= |cmd.inputs| &&
    |observations| == count &&
    (forall i: nat | i < |observations| ::
       InputObservationRelation(
         cmd,
         preFs, preStreams,
         preStdin,
         i,
         observations[i]
       )) &&
    |dataCuts| == |observations| + 1 &&
    dataCuts[0] == 0 &&
    dataCuts[|dataCuts| - 1] == |data| &&
    (forall i: nat {:trigger dataCuts[i]} | i < |observations| ::
       dataCuts[i] <= dataCuts[i + 1] &&
       dataCuts[i + 1] <= |data| &&
       dataCuts[i + 1] ==
       dataCuts[i] + |InputDataPiece(observations[i])| &&
       data[dataCuts[i]..dataCuts[i + 1]] ==
       InputDataPiece(observations[i])) &&
    |errorCuts| == |observations| + 1 &&
    errorCuts[0] == 0 &&
    errorCuts[|errorCuts| - 1] == |errors| &&
    (forall i: nat {:trigger errorCuts[i]} | i < |observations| ::
       errorCuts[i] <= errorCuts[i + 1] &&
       errorCuts[i + 1] <= |errors| &&
       errorCuts[i + 1] ==
       errorCuts[i] + |InputErrorPiece(observations[i])| &&
       errors[errorCuts[i]..errorCuts[i + 1]] ==
       InputErrorPiece(observations[i])) &&
    currentStdin == ExpectedStdinAt(cmd, preStdin, count, preStreams) &&
    hadError == HasFailedObservation(observations)
  }

  twostate predicate CoreWitnessRelation(
    raw: CatSchema.CatCmdRaw,
    io: BenchIO.IO,
    exit: int,
    trace: CoreWitness
  , plannedStdout: BenchWorld.Bytes, plannedStderr: BenchWorld.Bytes)
    reads io.stdinRegion
  {
    var cmd := Spec.Command(raw);
    if cmd.mode == CatSchema.ModeHelp then
      io.stdin() == old(io.stdin()) &&
      plannedStdout == Spec.HelpTextSpec() &&
      plannedStderr == [] &&
      exit == 0
    else if cmd.mode == CatSchema.ModeVersion then
      io.stdin() == old(io.stdin()) &&
      plannedStdout == Spec.VersionTextSpec() &&
      plannedStderr == [] &&
      exit == 0
    else
      match trace
      case NonRunWitness => false
      case RunWitness(
        observations,
        data,
        dataCuts,
        errors,
        errorCuts,
        hadError,
        processed,
        renderTrace
        ) =>
        InputTraceWitnessRelation(
          cmd,
          old(io.fs()), old(io.trustedStreams()),
          old(io.stdin()),
          |cmd.inputs|,
          io.stdin(),
          observations,
          data,
          dataCuts,
          errors,
          errorCuts,
          hadError
        ) &&
        RenderWitnessRelation(cmd, data, processed, renderTrace) &&
        plannedStdout == processed.out &&
        plannedStderr == errors &&
        exit == (if hadError then 1 else 0)
  }

  twostate predicate PreparedSummary(raw: CatSchema.CatCmdRaw, io: BenchIO.IO, exit: int, plannedStdout: BenchWorld.Bytes, plannedStderr: BenchWorld.Bytes)
    reads io.stdinRegion
  {
    exists trace: CoreWitness ::
      CoreWitnessRelation(
        raw,
        io,
        exit,
        trace
      , plannedStdout, plannedStderr)
  }

  lemma PrefixSliceUnchanged<T>(
    prefix: seq<T>,
    suffix: seq<T>,
    low: nat,
    high: nat
  )
    requires low <= high <= |prefix|
    ensures (prefix + suffix)[low..high] == prefix[low..high]
  {
  }

  lemma {:isolate_assertions} ExtendNumberTrace(
    steps: seq<RenderStep>,
    count: nat,
    currentState: Model.RenderState,
    step: RenderStep
  )
    requires NumberTraceRelation(steps, count, currentState)
    requires step.before == currentState
    requires step.after.nextLine ==
             currentState.nextLine + (if step.number > 0 then 1 else 0)
    ensures NumberTraceRelation(
              steps + [step],
              count + 1,
              step.after
            )
  {
    reveal NumberTraceRelation();
    ghost var numberedBefore :=
      set q: nat | q < count && steps[q].number > 0;
    ghost var numberedAfter :=
      set q: nat |
      q < count + 1 && (steps + [step])[q].number > 0;
    assert count !in numberedBefore;
    assert numberedAfter ==
           (if step.number > 0 then numberedBefore + {count}
            else numberedBefore) by {
      assert forall q: nat ::
          q in numberedAfter <==>
               q in (if step.number > 0 then numberedBefore + {count}
                          else numberedBefore) by {
        forall q: nat
          ensures
            q in numberedAfter <==>
                 q in (if step.number > 0 then numberedBefore + {count}
                            else numberedBefore)
        {
          if q < count {
            assert (steps + [step])[q] == steps[q];
          } else if q < count + 1 {
            assert q == count;
            assert (steps + [step])[q] == step;
          }
        }
      }
    }
    assert step.after.nextLine == 1 + |numberedAfter|;
    forall p: nat {:trigger (steps + [step])[p]} | p < count + 1
      ensures
        (steps + [step])[p].before.nextLine ==
        1 + |set q: nat |
        q < p && (steps + [step])[q].number > 0|
    {
      if p < count {
        assert (steps + [step])[p] == steps[p];
        assert (set q: nat |
                q < p && (steps + [step])[q].number > 0) ==
               (set q: nat |
                q < p && steps[q].number > 0) by {
          assert forall q: nat
              {:trigger (steps + [step])[q]} ::
              q in (set q: nat |
                    q < p && (steps + [step])[q].number > 0) <==>
                   q in (set q: nat |
                              q < p && steps[q].number > 0);
        }
      } else {
        assert p == count;
        assert (steps + [step])[p] == step;
        assert (set q: nat |
                q < p && (steps + [step])[q].number > 0) ==
               numberedBefore by {
          assert forall q: nat {:trigger (steps + [step])[q]} ::
              q in (set q: nat |
                    q < p && (steps + [step])[q].number > 0) <==>
                   q in numberedBefore by {
            forall q: nat {:trigger (steps + [step])[q]}
              ensures
                q in (set q: nat |
                      q < p && (steps + [step])[q].number > 0) <==>
                     q in numberedBefore
            {
              if q < count {
                assert (steps + [step])[q] == steps[q];
              }
            }
          }
        }
      }
    }
  }

  lemma ExpectedStdinAtExtend(
    cmd: CatSchema.CatCmd,
    preStdin: BenchWorld.Bytes,
    count: nat
  , preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult)
    requires count < |cmd.inputs|
    ensures ExpectedStdinAt(cmd, preStdin, count + 1, preStreams) ==
            (if cmd.inputs[count].Stdin? then IOContract.ObservedReadStdinRemainingFields(
                                                ExpectedStdinAt(cmd, preStdin, count, preStreams), preStreams)
             else ExpectedStdinAt(cmd, preStdin, count, preStreams))
  {
  }

  lemma ObservationRelationsSnoc(
    cmd: CatSchema.CatCmd,
    preFs: BenchWorld.FileSystem, preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult,
    preStdin: BenchWorld.Bytes,
    observations: seq<InputObservation>,
    observation: InputObservation
  )
    requires |observations| < |cmd.inputs|
    requires forall i: nat | i < |observations| ::
               InputObservationRelation(cmd, preFs, preStreams, preStdin, i, observations[i])
    requires InputObservationRelation(
               cmd,
               preFs, preStreams,
               preStdin,
               |observations|,
               observation
             )
    ensures forall i: nat | i < |observations + [observation]| ::
              InputObservationRelation(
                cmd,
                preFs, preStreams,
                preStdin,
                i,
                (observations + [observation])[i]
              )
  {
    hide InputObservationRelation();
    forall i: nat | i < |observations + [observation]|
      ensures InputObservationRelation(
                cmd,
                preFs, preStreams,
                preStdin,
                i,
                (observations + [observation])[i]
              )
    {
      if i < |observations| {
        assert (observations + [observation])[i] == observations[i];
      } else {
        assert i == |observations|;
        assert (observations + [observation])[i] == observation;
      }
    }
  }

  lemma FailedObservationSnoc(
    observations: seq<InputObservation>,
    observation: InputObservation
  )
    ensures HasFailedObservation(observations + [observation]) ==
            (HasFailedObservation(observations) || InputFailed(observation))
  {
    reveal HasFailedObservation();
    if exists i: nat ::
        i < |observations + [observation]| &&
        InputFailed((observations + [observation])[i]) {
      var i: nat :|
        i < |observations + [observation]| &&
        InputFailed((observations + [observation])[i]);
      if i >= |observations| {
        assert i == |observations|;
      }
    }
    if InputFailed(observation) {
      assert exists i: nat ::
          i < |observations + [observation]| &&
          InputFailed((observations + [observation])[i]) by {
        assert (observations + [observation])[|observations|] ==
               observation;
      }
    } else if exists i: nat ::
        i < |observations| && InputFailed(observations[i]) {
      var i: nat :|
        i < |observations| && InputFailed(observations[i]);
      assert i < |observations + [observation]|;
      assert (observations + [observation])[i] == observations[i];
    }
  }

  lemma {:isolate_assertions} ExtendInputTraceWitness(
    cmd: CatSchema.CatCmd,
    preFs: BenchWorld.FileSystem, preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult,
    preStdin: BenchWorld.Bytes,
    count: nat,
    currentStdin: BenchWorld.Bytes,
    observations: seq<InputObservation>,
    data: BenchWorld.Bytes,
    dataCuts: seq<nat>,
    errors: BenchWorld.Bytes,
    errorCuts: seq<nat>,
    hadError: bool,
    observation: InputObservation,
    nextStdin: BenchWorld.Bytes
  )
    requires InputTraceWitnessRelation(
               cmd,
               preFs, preStreams,
               preStdin,
               count,
               currentStdin,
               observations,
               data,
               dataCuts,
               errors,
               errorCuts,
               hadError
             )
    requires count < |cmd.inputs|
    requires InputObservationRelation(
               cmd,
               preFs, preStreams,
               preStdin,
               count,
               observation
             )
    requires nextStdin ==
             (if cmd.inputs[count] == CatSchema.Stdin then IOContract.ObservedReadStdinRemainingFields(currentStdin, preStreams) else currentStdin)
    ensures InputTraceWitnessRelation(
              cmd,
              preFs, preStreams,
              preStdin,
              count + 1,
              nextStdin,
              observations + [observation],
              data + InputDataPiece(observation),
              dataCuts + [|data + InputDataPiece(observation)|],
              errors + InputErrorPiece(observation),
              errorCuts + [|errors + InputErrorPiece(observation)|],
              hadError || InputFailed(observation)
            )
  {
    reveal InputTraceWitnessRelation();
    assert forall i: nat
        {:trigger (dataCuts +
                   [|data + InputDataPiece(observation)|])[i]} |
        i < |observations + [observation]| ::
        (dataCuts + [|data + InputDataPiece(observation)|])[i] <=
        (dataCuts + [|data + InputDataPiece(observation)|])[i + 1] &&
        (dataCuts + [|data + InputDataPiece(observation)|])[i + 1] <=
        |data + InputDataPiece(observation)| &&
        (dataCuts + [|data + InputDataPiece(observation)|])[i + 1] ==
        (dataCuts + [|data + InputDataPiece(observation)|])[i] +
        |InputDataPiece((observations + [observation])[i])| &&
        (data + InputDataPiece(observation))[
        (dataCuts + [|data + InputDataPiece(observation)|])[i]..
        (dataCuts + [|data + InputDataPiece(observation)|])[i + 1]
        ] == InputDataPiece((observations + [observation])[i]) by {
      forall i: nat
        {:trigger (dataCuts +
        [|data + InputDataPiece(observation)|])[i]} |
    i < |observations + [observation]|
        ensures
          (dataCuts + [|data + InputDataPiece(observation)|])[i] <=
          (dataCuts + [|data + InputDataPiece(observation)|])[i + 1] &&
          (dataCuts + [|data + InputDataPiece(observation)|])[i + 1] <=
          |data + InputDataPiece(observation)| &&
          (dataCuts + [|data + InputDataPiece(observation)|])[i + 1] ==
          (dataCuts + [|data + InputDataPiece(observation)|])[i] +
          |InputDataPiece((observations + [observation])[i])| &&
          (data + InputDataPiece(observation))[
          (dataCuts + [|data + InputDataPiece(observation)|])[i]..
          (dataCuts + [|data + InputDataPiece(observation)|])[i + 1]
          ] == InputDataPiece((observations + [observation])[i])
      {
        if i >= |observations| {
          assert i == |observations|;
        }
      }
    }
    assert forall i: nat
        {:trigger (errorCuts +
                   [|errors + InputErrorPiece(observation)|])[i]} |
        i < |observations + [observation]| ::
        (errorCuts + [|errors + InputErrorPiece(observation)|])[i] <=
        (errorCuts + [|errors + InputErrorPiece(observation)|])[i + 1] &&
        (errorCuts + [|errors + InputErrorPiece(observation)|])[i + 1] <=
        |errors + InputErrorPiece(observation)| &&
        (errorCuts + [|errors + InputErrorPiece(observation)|])[i + 1] ==
        (errorCuts + [|errors + InputErrorPiece(observation)|])[i] +
        |InputErrorPiece((observations + [observation])[i])| &&
        (errors + InputErrorPiece(observation))[
        (errorCuts + [|errors + InputErrorPiece(observation)|])[i]..
        (errorCuts + [|errors + InputErrorPiece(observation)|])[i + 1]
        ] == InputErrorPiece((observations + [observation])[i]) by {
      forall i: nat
        {:trigger (errorCuts +
        [|errors + InputErrorPiece(observation)|])[i]} |
    i < |observations + [observation]|
        ensures
          (errorCuts + [|errors + InputErrorPiece(observation)|])[i] <=
          (errorCuts + [|errors + InputErrorPiece(observation)|])[i + 1] &&
          (errorCuts + [|errors + InputErrorPiece(observation)|])[i + 1] <=
          |errors + InputErrorPiece(observation)| &&
          (errorCuts + [|errors + InputErrorPiece(observation)|])[i + 1] ==
          (errorCuts + [|errors + InputErrorPiece(observation)|])[i] +
          |InputErrorPiece((observations + [observation])[i])| &&
          (errors + InputErrorPiece(observation))[
          (errorCuts + [|errors + InputErrorPiece(observation)|])[i]..
          (errorCuts + [|errors + InputErrorPiece(observation)|])[i + 1]
          ] == InputErrorPiece((observations + [observation])[i])
      {
        if i >= |observations| {
          assert i == |observations|;
          assert errorCuts[i] == |errors|;
          assert (errors + InputErrorPiece(observation))[|errors|..] ==
                 InputErrorPiece(observation);
        } else {
          assert errorCuts[i + 1] <= |errors|;
          PrefixSliceUnchanged(errors, InputErrorPiece(observation), errorCuts[i], errorCuts[i + 1]);
        }
      }
    }
    ObservationRelationsSnoc(
      cmd,
      preFs, preStreams,
      preStdin,
      observations,
      observation
    );
    FailedObservationSnoc(observations, observation);
    ExpectedStdinAtExtend(cmd, preStdin, count, preStreams);
    assert InputTraceWitnessRelation(
        cmd,
        preFs, preStreams,
        preStdin,
        count + 1,
        nextStdin,
        observations + [observation],
        data + InputDataPiece(observation),
        dataCuts + [|data + InputDataPiece(observation)|],
        errors + InputErrorPiece(observation),
        errorCuts + [|errors + InputErrorPiece(observation)|],
        hadError || InputFailed(observation)
      ) by {
      reveal InputTraceWitnessRelation();
    }
  }

  method {:isolate_assertions} ProcessBytesMethod(
    cmd: CatSchema.CatCmd,
    data: BenchWorld.Bytes,
    state: Model.RenderState
  )
    returns (processed: Model.RenderResult, ghost renderTrace: RenderWitness)
    requires state == Model.InitState()
    ensures RenderWitnessRelation(cmd, data, processed, renderTrace)
  {
    var out: BenchWorld.Bytes := [];
    var currentState := state;
    ghost var steps: seq<RenderStep> := [];
    ghost var cuts: seq<nat> := [0];
    var i := 0;
    reveal Model.InitState();
    assert currentState.nextLine == 1;
    assert currentState.atLineStart;
    assert currentState.blankStreak == 0;
    assert RenderPrefixEvidence(
        cmd,
        data,
        i,
        currentState,
        out,
        steps,
        cuts
      ) by {
      reveal RenderPrefixEvidence();
      reveal NumberTraceRelation();
    }
    while i < |data|
      invariant 0 <= i <= |data|
      invariant RenderPrefixEvidence(
                  cmd,
                  data,
                  i,
                  currentState,
                  out,
                  steps,
                  cuts
                )
      decreases |data| - i
    {
      assert 1 <= currentState.nextLine by {
        reveal RenderPrefixEvidence();
      }
      assert 0 <= currentState.blankStreak by {
        reveal RenderPrefixEvidence();
      }
      assert |steps| == i by {
        reveal RenderPrefixEvidence();
      }
      assert |cuts| == i + 1 by {
        reveal RenderPrefixEvidence();
      }
      assert NumberTraceRelation(steps, i, currentState) by {
        reveal RenderPrefixEvidence();
      }
      assert cuts[|cuts| - 1] == |out| by {
        reveal RenderPrefixEvidence();
      }
      ghost var oldState := currentState;

      var ch := data[i];
      var rest := data[i + 1..];

      var chunk: BenchWorld.Bytes := [];
      var nextState := currentState;
      ghost var number: nat := 0;
      if ch == '\n' {
        var blankStreak :=
          if currentState.atLineStart then
            currentState.blankStreak + 1
          else
            0;
        if cmd.squeezeBlank && currentState.atLineStart && blankStreak >= 2 {
          nextState := Model.RenderState(currentState.nextLine, true, blankStreak);
        } else {
          var prefix: BenchWorld.Bytes := [];
          var nextLine := currentState.nextLine;
          if cmd.number == CatSchema.NumberAll && currentState.atLineStart {
            prefix := Spec.LineNumberText(currentState.nextLine);
            number := currentState.nextLine as nat;
            nextLine := currentState.nextLine + 1;
          }
          chunk := prefix + (if cmd.showEnds then ['$'] else []) + ['\n'];
          nextState := Model.RenderState(nextLine, true, blankStreak);
        }
      } else {
        var prefix: BenchWorld.Bytes := [];
        var nextLine := currentState.nextLine;
        if currentState.atLineStart && cmd.number != CatSchema.NoNumber {
          prefix := Spec.LineNumberText(currentState.nextLine);
          number := currentState.nextLine as nat;
          nextLine := currentState.nextLine + 1;
        }
        var transformed := Spec.TransformChar(cmd, ch, |rest| > 0 && rest[0] == '\n');
        chunk := prefix + transformed;
        nextState := Model.RenderState(nextLine, false, 0);
      }

      ghost var step := RenderStep(
        oldState,
        nextState,
        chunk,
        number
      );
      assert RenderStepRelation(
          cmd,
          ch,
          |rest| > 0 && rest[0] == '\n',
          step
        ) by {
        reveal RenderStepRelation();
      }
      assert (|rest| > 0 && rest[0] == '\n') ==
             (i + 1 < |data| && data[i + 1] == '\n');
      ghost var nextSteps := steps + [step];
      ghost var nextCuts := cuts + [|out + chunk|];
      assert nextState.nextLine ==
             currentState.nextLine + (if number > 0 then 1 else 0);
      ExtendNumberTrace(steps, i, currentState, step);
      assert RenderPrefixEvidence(
          cmd,
          data,
          i + 1,
          nextState,
          out + chunk,
          nextSteps,
          nextCuts
        ) by {
        reveal RenderPrefixEvidence();
        assert 1 <= nextState.nextLine;
        assert 0 <= nextState.blankStreak;
        assert |nextSteps| == i + 1;
        assert |nextCuts| == i + 2;
        assert nextCuts[0] == 0;
        assert nextCuts[i + 1] == |out + chunk|;
        assert nextState == nextSteps[i].after;
        assert NumberTraceRelation(nextSteps, i + 1, nextState);
        forall p: nat {:trigger nextSteps[p]} | p < i + 1
          ensures
            RenderStepRelation(
              cmd,
              data[p],
              p + 1 < |data| && data[p + 1] == '\n',
              nextSteps[p]
            ) &&
            nextSteps[p].before ==
            (if p == 0 then Model.InitState()
             else nextSteps[p - 1].after) &&
            nextCuts[p + 1] ==
            nextCuts[p] + |nextSteps[p].chunk| &&
            nextCuts[p + 1] <= |out + chunk| &&
            (out + chunk)[nextCuts[p]..nextCuts[p + 1]] ==
            nextSteps[p].chunk
        {
          if p < i {
            assert nextSteps[p] == steps[p];
            assert nextCuts[p] == cuts[p];
            assert nextCuts[p + 1] == cuts[p + 1];
            PrefixSliceUnchanged(
              out,
              chunk,
              nextCuts[p],
              nextCuts[p + 1]
            );
          } else {
            assert p == i;
            assert nextSteps[p] == step;
            assert nextCuts[p] == |out|;
            assert nextCuts[p + 1] == |out + chunk|;
            if p == 0 {
              assert oldState == state;
            }
          }
        }
      }

      out := out + chunk;
      currentState := nextState;
      steps := nextSteps;
      cuts := nextCuts;
      i := i + 1;
    }

    assert i == |data|;
    processed := Model.RenderResult(out, currentState);
    renderTrace := RenderWitness(
      steps,
      cuts
    );
    assert RenderWitnessRelation(cmd, data, processed, renderTrace) by {
      reveal RenderWitnessRelation();
    }
  }

  method {:isolate_assertions} Prepare(
    raw: CatSchema.CatCmdRaw,
    io: BenchIO.IO
  ) returns (exit: int, plannedOut: BenchWorld.Bytes, plannedErr: BenchWorld.Bytes)
    modifies io.stdinRegion
    ensures PreparedSummary(raw, io, exit, plannedOut, plannedErr)
    decreases *
  {
    plannedOut := [];
    plannedErr := [];

    ghost var preFs := io.fs();
    ghost var preStreams := io.trustedStreams();
    ghost var preStdin := io.stdin();
    var cmd := Spec.Command(raw);

    if cmd.mode == CatSchema.ModeHelp {
      var help := Spec.HelpTextSpec();
      plannedOut := plannedOut + help;
      exit := 0;
      assert io.stdin() == preStdin;
      assert plannedOut == Spec.HelpTextSpec();
      assert plannedErr == [];
      assert CoreWitnessRelation(
          raw,
          io,
          exit,
          NonRunWitness
        , plannedOut, plannedErr);
      assert PreparedSummary(raw, io, exit, plannedOut, plannedErr) by { hide *; reveal PreparedSummary(); }
      return;
    }

    if cmd.mode == CatSchema.ModeVersion {
      var version := Spec.VersionTextSpec();
      plannedOut := plannedOut + version;
      exit := 0;
      assert io.stdin() == preStdin;
      assert plannedOut == Spec.VersionTextSpec();
      assert plannedErr == [];
      assert CoreWitnessRelation(
          raw,
          io,
          exit,
          NonRunWitness
        , plannedOut, plannedErr);
      assert PreparedSummary(raw, io, exit, plannedOut, plannedErr) by { hide *; reveal PreparedSummary(); }
      return;
    }

    var combined: BenchWorld.Bytes := [];
    var err: BenchWorld.Bytes := [];
    var hadError := false;
    ghost var observations: seq<InputObservation> := [];
    ghost var dataCuts: seq<nat> := [0];
    ghost var errorCuts: seq<nat> := [0];
    assert InputTraceWitnessRelation(
        cmd,
        preFs, preStreams,
        preStdin,
        0,
        io.stdin(),
        observations,
        combined,
        dataCuts,
        err,
        errorCuts,
        hadError
      ) by {
      reveal InputTraceWitnessRelation();
    }

    var i := 0;
    while i < |cmd.inputs|
      invariant 0 <= i <= |cmd.inputs|
      invariant plannedOut == []
      invariant plannedErr == []
      invariant InputTraceWitnessRelation(
                  cmd,
                  preFs, preStreams,
                  preStdin,
                  i,
                  io.stdin(),
                  observations,
                  combined,
                  dataCuts,
                  err,
                  errorCuts,
                  hadError
                )
      decreases |cmd.inputs| - i
    {
      var input := cmd.inputs[i];
      ghost var beforeStdin := io.stdin();
      assert beforeStdin == ExpectedStdinAt(cmd, preStdin, i, preStreams) by {
        reveal InputTraceWitnessRelation();
      }
      var read: BenchWorld.IOResult<BenchWorld.Bytes>;
      match input {
        case Stdin => read := io.ReadStdin();
        case File(path) => read := io.ReadFile(path);
      }
      var data := IOContract.ReadResultData(read);
      var diagnostic := if read.Err? then
        Spec.ErrorMessageSpec(if input.Stdin? then "-" else input.path, read.e) else [];
      ghost var observation := InputObservation(input, read);
      assert InputObservationRelation(cmd, preFs, preStreams, preStdin, i, observation) by {
        reveal InputObservationRelation();
      }
      assert InputDataPiece(observation) == data;
      assert InputErrorPiece(observation) == diagnostic;
      assert InputFailed(observation) == read.Err?;
      ExtendInputTraceWitness(cmd, preFs, preStreams, preStdin, i, beforeStdin,
                              observations, combined, dataCuts, err, errorCuts, hadError, observation, io.stdin());
      combined := combined + data;
      err := err + diagnostic;
      hadError := hadError || read.Err?;
      observations := observations + [observation];
      dataCuts := dataCuts + [|combined|];
      errorCuts := errorCuts + [|err|];
      i := i + 1;
      assert InputTraceWitnessRelation(cmd, preFs, preStreams, preStdin, i, io.stdin(),
                                       observations, combined, dataCuts, err, errorCuts, hadError) by { hide *; }
    }

    var initialState := Model.InitState();
    var processed, renderWitness := ProcessBytesMethod(cmd, combined, initialState);
    plannedOut := processed.out;
    assert plannedOut == processed.out by { hide *; }
    plannedErr := err;
    assert plannedErr == err by { hide *; }
    exit := if hadError then 1 else 0;
    assert InputTraceWitnessRelation(
        cmd,
        preFs, preStreams,
        preStdin,
        |cmd.inputs|,
        io.stdin(),
        observations,
        combined,
        dataCuts,
        err,
        errorCuts,
        hadError
      );
    ghost var trace := RunWitness(
      observations,
      combined,
      dataCuts,
      err,
      errorCuts,
      hadError,
      processed,
      renderWitness
    );
    assert CoreWitnessRelation(
        raw,
        io,
        exit,
        trace
      , plannedOut, plannedErr);
    assert PreparedSummary(raw, io, exit, plannedOut, plannedErr) by { hide *; reveal PreparedSummary(); }
  }

  twostate predicate CoreSummary(raw: CatSchema.CatCmdRaw, io: BenchIO.IO, exit: int)
    reads io.stdinRegion, io.stdoutRegion, io.stderrRegion
  {
    exists out: BenchWorld.Bytes, diagnostics: BenchWorld.Bytes, normalExit: int ::
      PreparedSummary(raw, io, normalExit,
                      out, diagnostics) &&
      Spec.Emission(raw, io, out, diagnostics, normalExit, exit)
  }

  method Flush(io: BenchIO.IO, out: BenchWorld.Bytes,
               diagnostics: BenchWorld.Bytes, normalExit: int) returns (exit: int)
    modifies io.stdoutRegion, io.stderrRegion
    ensures Spec.Emit(io, out, diagnostics, normalExit, exit)
  {
    var outErr := 0;
    if out != [] {
      var written := io.WriteStdout(out);
      outErr := StreamContract.ResultErrno(written);
    }
    var errors := diagnostics;
    if outErr != 0 {
      var message := io.GetCLocaleErrnoText(outErr);
      errors := errors + Spec.StreamWriteErrorMessage(message);
    }
    assert errors == diagnostics + (if outErr == 0 then [] else
                                    Spec.StreamWriteErrorMessage(StreamContract.CLocaleErrnoTextResult(outErr)));
    var errErr := 0;
    if errors != [] {
      var diagnosed := io.WriteStderr(errors);
      errErr := StreamContract.ResultErrno(diagnosed);
      assert StreamContract.WriteStderrSpec(old(io.stderr()), io.trustedStreams(), io.stderr(),
                                            errors, StreamContract.WriteResultCommitted(diagnosed), errErr);
    }
    exit := if outErr != 0 || errErr != 0 then 1 else normalExit;
  }

  method RunCore(raw: CatSchema.CatCmdRaw, io: BenchIO.IO) returns (exit: int)
    modifies io.stdinRegion, io.stdoutRegion, io.stderrRegion
    ensures CoreSummary(raw, io, exit)
    decreases *
  {
    var normalExit, out, diagnostics := Prepare(raw, io);

    assert PreparedSummary(raw, io, normalExit, out, diagnostics);
    if Spec.Emits(raw) {
      exit := Flush(io, out, diagnostics, normalExit);
    } else {
      exit := normalExit;
    }
    assert PreparedSummary(raw, io, normalExit, out, diagnostics);
    assert Spec.Emission(raw, io, out, diagnostics, normalExit, exit);
  }
}
