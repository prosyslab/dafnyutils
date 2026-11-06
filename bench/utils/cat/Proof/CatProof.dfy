include "../Spec/CatSpec.dfy"
include "../../../core/World.dfy"
include "../../../core/IO.dfy"
include "../Spec/CatSchema.dfy"
include "../Impl/CatCore.dfy"

module CatProof {
  import IOContract
  import BenchWorld
  import Result = Results
  import BenchIO
  import BW = BenchWorld
  import Schema = CatSchema
  import Core = CatCore
  import Model = CatCoreModel
  import Spec = CatSpec

  ghost function ObservationResults(
    observations: seq<Core.InputObservation>
  ): seq<BW.IOResult<BW.Bytes>>
  {
    seq(
    |observations|,
    i requires 0 <= i < |observations| => observations[i].result
      )
  }

  ghost function RenderedFragments(
    steps: seq<Core.RenderStep>
  ): seq<BW.Bytes>
  {
    seq(
    |steps|,
    p requires 0 <= p < |steps| => steps[p].chunk
      )
  }

  ghost function RenderedNumbers(
    steps: seq<Core.RenderStep>
  ): seq<nat>
  {
    seq(
    |steps|,
    p requires 0 <= p < |steps| => steps[p].number
      )
  }

  lemma LineStartFromEvidence(
    cmd: Schema.CatCmd,
    data: BW.Bytes,
    processed: Model.RenderResult,
    renderTrace: Core.RenderWitness,
    p: nat
  )
    requires p < |data|
    requires |renderTrace.steps| == |data|
    requires Core.RenderWitnessRelation(
               cmd,
               data,
               processed,
               renderTrace
             )
    ensures renderTrace.steps[p].before.atLineStart ==
            Spec.LineStartAt(data, p)
  {
    reveal Core.RenderWitnessRelation();
    reveal Core.RenderPrefixEvidence();
    reveal Spec.LineStartAt();
    if p == 0 {
      reveal Model.InitState();
    } else {
      reveal Core.RenderStepRelation();
    }
  }

  lemma BlankBeforeFromEvidence(
    cmd: Schema.CatCmd,
    data: BW.Bytes,
    processed: Model.RenderResult,
    renderTrace: Core.RenderWitness,
    p: nat
  )
    requires p < |data|
    requires |renderTrace.steps| == |data|
    requires Core.RenderWitnessRelation(
               cmd,
               data,
               processed,
               renderTrace
             )
    ensures (renderTrace.steps[p].before.blankStreak > 0) ==
            (0 < p &&
             data[p - 1] == '\n' &&
             (p == 1 || data[p - 2] == '\n'))
  {
    reveal Core.RenderWitnessRelation();
    reveal Core.RenderPrefixEvidence();
    if p == 0 {
      reveal Model.InitState();
    } else {
      LineStartFromEvidence(
        cmd,
        data,
        processed,
        renderTrace,
        p - 1
      );
      reveal Core.RenderStepRelation();
    }
  }

  lemma {:isolate_assertions} StepClassificationRefines(
    cmd: Schema.CatCmd,
    data: BW.Bytes,
    processed: Model.RenderResult,
    renderTrace: Core.RenderWitness,
    p: nat
  )
    requires p < |data|
    requires |renderTrace.steps| == |data|
    requires Core.RenderWitnessRelation(
               cmd,
               data,
               processed,
               renderTrace
             )
    ensures Spec.KeptAt(cmd, data, p) ==
            !(cmd.squeezeBlank &&
              data[p] == '\n' &&
              renderTrace.steps[p].before.atLineStart &&
              (if renderTrace.steps[p].before.atLineStart then
                 renderTrace.steps[p].before.blankStreak + 1
               else
                 0) >= 2)
    ensures Spec.NumberedAt(cmd, data, p) ==
            (renderTrace.steps[p].number > 0)
  {
    reveal Core.RenderWitnessRelation();
    reveal Core.RenderPrefixEvidence();
    LineStartFromEvidence(
      cmd,
      data,
      processed,
      renderTrace,
      p
    );
    BlankBeforeFromEvidence(
      cmd,
      data,
      processed,
      renderTrace,
      p
    );
    reveal Spec.LineStartAt();
    reveal Spec.KeptAt();
    reveal Spec.NumberedAt();
    reveal Core.RenderStepRelation();
    if data[p] == '\n' {
      if renderTrace.steps[p].before.atLineStart {
        if renderTrace.steps[p].before.blankStreak > 0 {
          assert 0 < p;
        }
      }
    }
  }

  lemma {:isolate_assertions} NumberedPrefixSetRefines(
    cmd: Schema.CatCmd,
    data: BW.Bytes,
    processed: Model.RenderResult,
    renderTrace: Core.RenderWitness,
    p: nat
  )
    requires p <= |data|
    requires |renderTrace.steps| == |data|
    requires Core.RenderWitnessRelation(
               cmd,
               data,
               processed,
               renderTrace
             )
    ensures (set q: nat |
             q < p && renderTrace.steps[q].number > 0) ==
            (set q: nat |
             q < p && Spec.NumberedAt(cmd, data, q))
  {
    reveal Core.RenderWitnessRelation();
    reveal Core.RenderPrefixEvidence();
    assert forall q: nat {:trigger renderTrace.steps[q]} ::
        q in (set q: nat |
              q < p && renderTrace.steps[q].number > 0) <==>
             q in (set q: nat |
                        q < p && Spec.NumberedAt(cmd, data, q)) by {
      forall q: nat {:trigger renderTrace.steps[q]}
        ensures
          q in (set q: nat |
                q < p && renderTrace.steps[q].number > 0) <==>
               q in (set q: nat |
                          q < p && Spec.NumberedAt(cmd, data, q))
      {
        if q < p {
          StepClassificationRefines(
            cmd,
            data,
            processed,
            renderTrace,
            q
          );
        }
      }
    }
  }

  lemma {:isolate_assertions} StepChunkRefines(
    cmd: Schema.CatCmd,
    data: BW.Bytes,
    processed: Model.RenderResult,
    renderTrace: Core.RenderWitness,
    p: nat
  )
    requires p < |data|
    requires |renderTrace.steps| == |data|
    requires Core.RenderWitnessRelation(
               cmd,
               data,
               processed,
               renderTrace
             )
    ensures renderTrace.steps[p].chunk ==
            Spec.RenderFragment(
              cmd,
              data,
              p,
              renderTrace.steps[p].number
            )
  {
    reveal Core.RenderWitnessRelation();
    reveal Core.RenderPrefixEvidence();
    StepClassificationRefines(
      cmd,
      data,
      processed,
      renderTrace,
      p
    );
    reveal Spec.RenderFragment();
    reveal Core.RenderStepRelation();
    if data[p] == '\n' {
      if cmd.squeezeBlank &&
         renderTrace.steps[p].before.atLineStart &&
         (if renderTrace.steps[p].before.atLineStart then
            renderTrace.steps[p].before.blankStreak + 1
          else
            0) >= 2 {
      } else if renderTrace.steps[p].number > 0 {
      }
    } else if renderTrace.steps[p].number > 0 {
    }
  }

  lemma {:isolate_assertions} RenderWitnessRefines(
    cmd: Schema.CatCmd,
    data: BW.Bytes,
    processed: Model.RenderResult,
    renderTrace: Core.RenderWitness
  )
    requires Core.RenderWitnessRelation(
               cmd,
               data,
               processed,
               renderTrace
             )
    ensures Spec.RenderRelation(
              cmd,
              data,
              processed.out,
              RenderedFragments(renderTrace.steps),
              renderTrace.cuts,
              RenderedNumbers(renderTrace.steps)
            )
  {
    reveal Core.RenderWitnessRelation();
    reveal Core.RenderPrefixEvidence();
    reveal Core.NumberTraceRelation();
    reveal Spec.RenderRelation();
    assert Spec.LineNumberRelation(
        cmd,
        data,
        RenderedNumbers(renderTrace.steps)
      ) by {
      reveal Spec.LineNumberRelation();
      forall p: nat | p < |data|
        ensures RenderedNumbers(renderTrace.steps)[p] ==
                (if Spec.NumberedAt(cmd, data, p) then
                   1 + |set q: nat |
                   q < p && Spec.NumberedAt(cmd, data, q)|
                 else
                   0)
      {
        StepClassificationRefines(
          cmd,
          data,
          processed,
          renderTrace,
          p
        );
        NumberedPrefixSetRefines(
          cmd,
          data,
          processed,
          renderTrace,
          p
        );
        reveal Core.RenderStepRelation();
      }
    }
    assert forall p: nat | p < |data| ::
        RenderedFragments(renderTrace.steps)[p] ==
        Spec.RenderFragment(
          cmd,
          data,
          p,
          RenderedNumbers(renderTrace.steps)[p]
        ) by {
      forall p: nat | p < |data|
        ensures RenderedFragments(renderTrace.steps)[p] ==
                Spec.RenderFragment(
                  cmd,
                  data,
                  p,
                  RenderedNumbers(renderTrace.steps)[p]
                )
      {
        StepChunkRefines(
          cmd,
          data,
          processed,
          renderTrace,
          p
        );
      }
    }
    assert Spec.FragmentsConcatenate(
        RenderedFragments(renderTrace.steps),
        processed.out,
        renderTrace.cuts
      ) by {
      reveal Spec.FragmentsConcatenate();
      forall p: nat {:trigger renderTrace.cuts[p]} | p < |data|
        ensures renderTrace.cuts[p] <= renderTrace.cuts[p + 1] &&
                renderTrace.cuts[p + 1] <= |processed.out| &&
                renderTrace.cuts[p + 1] ==
                renderTrace.cuts[p] +
                |RenderedFragments(renderTrace.steps)[p]| &&
                processed.out[
                renderTrace.cuts[p]..renderTrace.cuts[p + 1]
                ] == RenderedFragments(renderTrace.steps)[p]
      {
        assert RenderedFragments(renderTrace.steps)[p] ==
               renderTrace.steps[p].chunk;
      }
    }
  }

  lemma InputObservationRefines(
    cmd: Schema.CatCmd,
    preFs: BW.FileSystem, preStreams: (BW.TrustedStreamRequest) -> BW.TrustedStreamResult,
    preStdin: BW.Bytes,
    i: nat,
    observation: Core.InputObservation
  )
    requires i < |cmd.inputs|
    requires Core.InputObservationRelation(
               cmd,
               preFs, preStreams,
               preStdin,
               i,
               observation
             )
    ensures Spec.InputReadOutcomeRelation(cmd, preFs, preStreams, Core.ExpectedStdinAt(cmd, preStdin, i, preStreams), i,
                                          observation.result
            )
    ensures Core.InputDataPiece(observation) ==
            Spec.InputDataPiece(observation.result)
    ensures Core.InputErrorPiece(observation) ==
            Spec.InputErrorPiece(cmd.inputs[i], observation.result)
    ensures Core.InputFailed(observation) ==
            Spec.InputFailed(cmd.inputs[i], observation.result)
  {
    reveal Core.InputObservationRelation();
    reveal Spec.InputReadOutcomeRelation();
    reveal Core.ExpectedStdinAt();
    reveal Core.InputDataPiece();
    reveal Spec.InputDataPiece();
    reveal Core.InputErrorPiece();
    reveal Spec.InputErrorPiece();
    reveal Core.InputFailed();
    reveal Spec.InputFailed();
  }

  lemma ExpectedStdinTrace(
    cmd: Schema.CatCmd,
    preStdin: BW.Bytes,
    preStreams: (BW.TrustedStreamRequest) -> BW.TrustedStreamResult
  ) returns (states: seq<BW.Bytes>)
    ensures |states| == |cmd.inputs| + 1
    ensures forall i: nat | i < |states| ::
              states[i] == Core.ExpectedStdinAt(cmd, preStdin, i, preStreams)
    ensures Spec.StdinTraceRelation(
              cmd, preStdin,
              Core.ExpectedStdinAt(cmd, preStdin, |cmd.inputs|, preStreams),
              preStreams, states)
  {
    states := seq(|cmd.inputs| + 1, i requires 0 <= i <= |cmd.inputs| =>
      Core.ExpectedStdinAt(cmd, preStdin, i, preStreams));
    forall i: nat | i < |cmd.inputs|
      ensures states[i + 1] ==
              (if cmd.inputs[i].Stdin? then
                 IOContract.ObservedReadStdinRemainingFields(states[i], preStreams)
               else states[i])
    {
      assert states[i] == Core.ExpectedStdinAt(cmd, preStdin, i, preStreams);
      assert states[i + 1] == Core.ExpectedStdinAt(cmd, preStdin, i + 1, preStreams);
      Core.ExpectedStdinAtExtend(cmd, preStdin, i, preStreams);
    }
    reveal Spec.StdinTraceRelation();
  }

  lemma {:isolate_assertions} InputTraceWitnessRefines(
    cmd: Schema.CatCmd,
    preFs: BW.FileSystem, preStreams: (BW.TrustedStreamRequest) -> BW.TrustedStreamResult,
    preStdin: BW.Bytes,
    currentStdin: BW.Bytes,
    observations: seq<Core.InputObservation>,
    data: BW.Bytes,
    dataCuts: seq<nat>,
    errors: BW.Bytes,
    errorCuts: seq<nat>,
    hadError: bool
  )
    requires Core.InputTraceWitnessRelation(
               cmd,
               preFs, preStreams,
               preStdin,
               |cmd.inputs|,
               currentStdin,
               observations,
               data,
               dataCuts,
               errors,
               errorCuts,
               hadError
             )
    ensures Spec.InputTraceRelation(
              cmd,
              preFs, preStreams,
              preStdin,
              currentStdin,
              data,
              errors,
              hadError,
              ObservationResults(observations),
              Core.ObservationDataFragments(observations),
              dataCuts,
              Core.ObservationErrorFragments(observations),
              errorCuts
            )
  {
    reveal Core.InputTraceWitnessRelation();
    reveal Spec.InputTraceRelation();
    var states := ExpectedStdinTrace(cmd, preStdin, preStreams);
    assert |ObservationResults(observations)| == |cmd.inputs|;
    assert |Core.ObservationDataFragments(observations)| ==
           |cmd.inputs|;
    assert |Core.ObservationErrorFragments(observations)| ==
           |cmd.inputs|;
    assert forall i: nat | i < |cmd.inputs| ::
        Spec.InputReadOutcomeRelation(cmd, preFs, preStreams, states[i], i,
                                      ObservationResults(observations)[i]
        ) &&
        Core.ObservationDataFragments(observations)[i] ==
        Spec.InputDataPiece(ObservationResults(observations)[i]) &&
        Core.ObservationErrorFragments(observations)[i] ==
        Spec.InputErrorPiece(
          cmd.inputs[i],
          ObservationResults(observations)[i]
        ) by {
      forall i: nat | i < |cmd.inputs|
        ensures Spec.InputReadOutcomeRelation(cmd, preFs, preStreams, states[i], i,
                                              ObservationResults(observations)[i]
                ) &&
                Core.ObservationDataFragments(observations)[i] ==
                Spec.InputDataPiece(ObservationResults(observations)[i]) &&
                Core.ObservationErrorFragments(observations)[i] ==
                Spec.InputErrorPiece(
                  cmd.inputs[i],
                  ObservationResults(observations)[i]
                )
      {
        assert i < |observations|;
        InputObservationRefines(
          cmd,
          preFs, preStreams,
          preStdin,
          i,
          observations[i]
        );
      }
    }
    assert Spec.FragmentsConcatenate(
        Core.ObservationDataFragments(observations),
        data,
        dataCuts
      ) by {
      reveal Spec.FragmentsConcatenate();
      forall i: nat {:trigger dataCuts[i]} | i < |observations|
        ensures dataCuts[i] <= dataCuts[i + 1] &&
                dataCuts[i + 1] <= |data| &&
                dataCuts[i + 1] ==
                dataCuts[i] +
                |Core.ObservationDataFragments(observations)[i]| &&
                data[dataCuts[i]..dataCuts[i + 1]] ==
                Core.ObservationDataFragments(observations)[i]
      {
        assert Core.ObservationDataFragments(observations)[i] ==
               Core.InputDataPiece(observations[i]);
      }
    }
    assert Spec.FragmentsConcatenate(
        Core.ObservationErrorFragments(observations),
        errors,
        errorCuts
      ) by {
      reveal Spec.FragmentsConcatenate();
      forall i: nat {:trigger errorCuts[i]} | i < |observations|
        ensures errorCuts[i] <= errorCuts[i + 1] &&
                errorCuts[i + 1] <= |errors| &&
                errorCuts[i + 1] ==
                errorCuts[i] +
                |Core.ObservationErrorFragments(observations)[i]| &&
                errors[errorCuts[i]..errorCuts[i + 1]] ==
                Core.ObservationErrorFragments(observations)[i]
      {
        assert Core.ObservationErrorFragments(observations)[i] ==
               Core.InputErrorPiece(observations[i]);
      }
    }
    assert currentStdin == Core.ExpectedStdinAt(cmd, preStdin, |cmd.inputs|, preStreams);
    assert hadError ==
           (exists i: nat ::
              i < |cmd.inputs| &&
              Spec.InputFailed(
                cmd.inputs[i],
                ObservationResults(observations)[i]
              )) by {
      reveal Core.HasFailedObservation();
      if Core.HasFailedObservation(observations) {
        var i: nat :|
          i < |observations| && Core.InputFailed(observations[i]);
        InputObservationRefines(
          cmd,
          preFs, preStreams,
          preStdin,
          i,
          observations[i]
        );
      }
      if exists i: nat ::
          i < |cmd.inputs| &&
          Spec.InputFailed(
            cmd.inputs[i],
            ObservationResults(observations)[i]
          ) {
        var i: nat :|
          i < |cmd.inputs| &&
          Spec.InputFailed(
            cmd.inputs[i],
            ObservationResults(observations)[i]
          );
        InputObservationRefines(
          cmd,
          preFs, preStreams,
          preStdin,
          i,
          observations[i]
        );
        assert Core.HasFailedObservation(observations);
      }
    }
    assert Spec.StdinTraceRelation(cmd, preStdin, currentStdin, preStreams, states);
  }

  twostate lemma {:isolate_assertions}
    PreparedSummaryImpliesPreparedSpec(
    raw: Schema.CatCmdRaw,
    io: BenchIO.IO,
    exit: int
  , new plannedStdout: BenchWorld.Bytes, new plannedStderr: BenchWorld.Bytes)
    requires Core.PreparedSummary(raw, io, exit, plannedStdout, plannedStderr)
    ensures Spec.PreparedSpec(raw, io, exit, plannedStdout, plannedStderr)
  {
    var trace: Core.CoreWitness :|
      Core.CoreWitnessRelation(
        raw,
        io,
        exit,
        trace
      , plannedStdout, plannedStderr);
    var cmd := Spec.Command(raw);
    if cmd.mode == Schema.ModeHelp {
      assert Spec.PreparedSpec(raw, io, exit, plannedStdout, plannedStderr);
    } else if cmd.mode == Schema.ModeVersion {
      assert Spec.PreparedSpec(raw, io, exit, plannedStdout, plannedStderr);
    } else {
      match trace
      case NonRunWitness =>
        assert false;
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
        InputTraceWitnessRefines(
          cmd,
          old(io.fs()), old(io.trustedStreams()),
          old(io.stdin()),
          io.stdin(),
          observations,
          data,
          dataCuts,
          errors,
          errorCuts,
          hadError
        );
        RenderWitnessRefines(cmd, data, processed, renderTrace);
        assert Spec.RunRelation(
            cmd,
            old(io.fs()), old(io.trustedStreams()),
            old(io.stdin()),
            io.stdin(),
            processed.out,
            errors,
            exit
          ) by {
          reveal Spec.RunRelation();
        }
        assert Spec.PreparedSpec(raw, io, exit, plannedStdout, plannedStderr) by {
          reveal Spec.PreparedSpec();
        }
    }
  }

  lemma FragmentCutsAgreeAt(
    fragments: seq<BW.Bytes>,
    first: BW.Bytes,
    firstCuts: seq<nat>,
    second: BW.Bytes,
    secondCuts: seq<nat>,
    i: nat
  )
    requires Spec.FragmentsConcatenate(fragments, first, firstCuts)
    requires Spec.FragmentsConcatenate(fragments, second, secondCuts)
    requires i < |firstCuts|
    ensures firstCuts[i] == secondCuts[i]
    decreases i
  {
    reveal Spec.FragmentsConcatenate();
    if i > 0 {
      FragmentCutsAgreeAt(
        fragments,
        first,
        firstCuts,
        second,
        secondCuts,
        i - 1
      );
    }
  }

  lemma CutIntervalExists(cuts: seq<nat>, length: nat, index: nat)
    requires |cuts| >= 2
    requires cuts[|cuts| - 1] == length
    requires forall i: nat :: i + 1 < |cuts| ==>
                                cuts[i] <= cuts[i + 1]
    requires cuts[0] <= index < length
    ensures exists i: nat ::
              i + 1 < |cuts| && cuts[i] <= index < cuts[i + 1]
    decreases |cuts|
  {
    if index < cuts[1] {
    } else if |cuts| > 2 {
      assert forall i: nat :: i + 1 < |cuts[1..]| ==>
                                cuts[1..][i] <= cuts[1..][i + 1] by {
        forall i: nat | i + 1 < |cuts[1..]|
          ensures cuts[1..][i] <= cuts[1..][i + 1]
        {
        }
      }
      CutIntervalExists(cuts[1..], length, index);
    }
  }

  // Kept outside the revealed FragmentsConcatenate context: inline, these slice
  // facts timed out at 30 s with the gate's random seed 42.
  lemma EqualSlicesAgreeAt(
    first: BW.Bytes,
    second: BW.Bytes,
    lo: nat,
    hi: nat,
    index: nat
  )
    requires lo <= index < hi
    requires hi <= |first| && hi <= |second|
    requires first[lo..hi] == second[lo..hi]
    ensures first[index] == second[index]
  {
    assert first[index] == first[lo..hi][index - lo];
    assert second[index] == second[lo..hi][index - lo];
  }

  lemma {:isolate_assertions} FragmentsConcatenateFunctional(
    fragments: seq<BW.Bytes>,
    first: BW.Bytes,
    firstCuts: seq<nat>,
    second: BW.Bytes,
    secondCuts: seq<nat>
  )
    requires Spec.FragmentsConcatenate(fragments, first, firstCuts)
    requires Spec.FragmentsConcatenate(fragments, second, secondCuts)
    ensures first == second
  {
    reveal Spec.FragmentsConcatenate();
    assert |firstCuts| == |secondCuts|;
    assert forall i: nat :: i < |firstCuts| ==>
                              firstCuts[i] == secondCuts[i] by {
      forall i: nat | i < |firstCuts|
        ensures firstCuts[i] == secondCuts[i]
      {
        FragmentCutsAgreeAt(
          fragments,
          first,
          firstCuts,
          second,
          secondCuts,
          i
        );
      }
    }
    assert firstCuts == secondCuts;
    assert |first| == |second|;
    assert forall index: nat :: index < |first| ==>
                                  first[index] == second[index] by {
      forall index: nat | index < |first|
        ensures first[index] == second[index]
      {
        assert forall i: nat :: i + 1 < |firstCuts| ==>
                                  firstCuts[i] <= firstCuts[i + 1] by {
          forall i: nat | i + 1 < |firstCuts|
            ensures firstCuts[i] <= firstCuts[i + 1]
          {
          }
        }
        CutIntervalExists(firstCuts, |first|, index);
        var i: nat :|
          i + 1 < |firstCuts| &&
          firstCuts[i] <= index < firstCuts[i + 1];
        assert first[firstCuts[i]..firstCuts[i + 1]] == fragments[i];
        assert second[firstCuts[i]..firstCuts[i + 1]] == fragments[i];
        EqualSlicesAgreeAt(first, second, firstCuts[i], firstCuts[i + 1], index);
      }
    }
  }

  lemma InputTraceRelationFunctional(
    cmd: Schema.CatCmd,
    preFs: BW.FileSystem, preStreams: (BW.TrustedStreamRequest) -> BW.TrustedStreamResult,
    preStdin: BW.Bytes,
    postStdin1: BW.Bytes,
    data1: BW.Bytes,
    errors1: BW.Bytes,
    hadError1: bool,
    postStdin2: BW.Bytes,
    data2: BW.Bytes,
    errors2: BW.Bytes,
    hadError2: bool
  )
    requires exists readResults: seq<BW.IOResult<BW.Bytes>>,
               dataFragments: seq<BW.Bytes>,
               dataCuts: seq<nat>,
               errorFragments: seq<BW.Bytes>,
               errorCuts: seq<nat> ::
               Spec.InputTraceRelation(
                 cmd,
                 preFs, preStreams,
                 preStdin,
                 postStdin1,
                 data1,
                 errors1,
                 hadError1,
                 readResults,
                 dataFragments,
                 dataCuts,
                 errorFragments,
                 errorCuts
               )
    requires exists readResults: seq<BW.IOResult<BW.Bytes>>,
               dataFragments: seq<BW.Bytes>,
               dataCuts: seq<nat>,
               errorFragments: seq<BW.Bytes>,
               errorCuts: seq<nat> ::
               Spec.InputTraceRelation(
                 cmd,
                 preFs, preStreams,
                 preStdin,
                 postStdin2,
                 data2,
                 errors2,
                 hadError2,
                 readResults,
                 dataFragments,
                 dataCuts,
                 errorFragments,
                 errorCuts
               )
    ensures postStdin1 == postStdin2
    ensures data1 == data2
    ensures errors1 == errors2
    ensures hadError1 == hadError2
  {
    var readResults1: seq<BW.IOResult<BW.Bytes>>,
        dataFragments1: seq<BW.Bytes>,
        dataCuts1: seq<nat>,
        errorFragments1: seq<BW.Bytes>,
        errorCuts1: seq<nat> :|
      Spec.InputTraceRelation(
        cmd,
        preFs, preStreams,
        preStdin,
        postStdin1,
        data1,
        errors1,
        hadError1,
        readResults1,
        dataFragments1,
        dataCuts1,
        errorFragments1,
        errorCuts1
      );
    var readResults2: seq<BW.IOResult<BW.Bytes>>,
        dataFragments2: seq<BW.Bytes>,
        dataCuts2: seq<nat>,
        errorFragments2: seq<BW.Bytes>,
        errorCuts2: seq<nat> :|
      Spec.InputTraceRelation(
        cmd,
        preFs, preStreams,
        preStdin,
        postStdin2,
        data2,
        errors2,
        hadError2,
        readResults2,
        dataFragments2,
        dataCuts2,
        errorFragments2,
        errorCuts2
      );
    reveal Spec.InputTraceRelation();
    var states1: seq<BW.Bytes> :| Spec.StdinTraceRelation(cmd, preStdin, postStdin1, preStreams, states1) &&
                                  forall i: nat | i < |cmd.inputs| :: Spec.InputReadOutcomeRelation(cmd, preFs, preStreams, states1[i], i, readResults1[i]);
    var states2: seq<BW.Bytes> :| Spec.StdinTraceRelation(cmd, preStdin, postStdin2, preStreams, states2) &&
                                  forall i: nat | i < |cmd.inputs| :: Spec.InputReadOutcomeRelation(cmd, preFs, preStreams, states2[i], i, readResults2[i]);
    forall i: nat | i <= |cmd.inputs|
      ensures states1[i] == states2[i]
    { Spec.StdinStatePrefixFunctional(cmd, preStdin, preStreams, states1, states2, i); }
    assert |readResults1| == |readResults2|;
    assert forall i: nat | i < |readResults1| ::
        readResults1[i] == readResults2[i] by {
      forall i: nat | i < |readResults1|
        ensures readResults1[i] == readResults2[i]
      {
        reveal Spec.InputReadOutcomeRelation();
      }
    }
    assert readResults1 == readResults2;
    assert |dataFragments1| == |dataFragments2|;
    assert forall i: nat | i < |dataFragments1| ::
        dataFragments1[i] == dataFragments2[i] by {
      forall i: nat | i < |dataFragments1|
        ensures dataFragments1[i] == dataFragments2[i]
      {
      }
    }
    assert dataFragments1 == dataFragments2;
    assert |errorFragments1| == |errorFragments2|;
    assert forall i: nat | i < |errorFragments1| ::
        errorFragments1[i] == errorFragments2[i] by {
      forall i: nat | i < |errorFragments1|
        ensures errorFragments1[i] == errorFragments2[i]
      {
      }
    }
    assert errorFragments1 == errorFragments2;
    FragmentsConcatenateFunctional(
      dataFragments1,
      data1,
      dataCuts1,
      data2,
      dataCuts2
    );
    FragmentsConcatenateFunctional(
      errorFragments1,
      errors1,
      errorCuts1,
      errors2,
      errorCuts2
    );
  }

  lemma LineNumberRelationFunctional(
    cmd: Schema.CatCmd,
    data: BW.Bytes,
    numbers1: seq<nat>,
    numbers2: seq<nat>
  )
    requires Spec.LineNumberRelation(cmd, data, numbers1)
    requires Spec.LineNumberRelation(cmd, data, numbers2)
    ensures numbers1 == numbers2
  {
    reveal Spec.LineNumberRelation();
    assert |numbers1| == |numbers2|;
    assert forall p: nat | p < |numbers1| ::
        numbers1[p] == numbers2[p] by {
      forall p: nat | p < |numbers1|
        ensures numbers1[p] == numbers2[p]
      {
      }
    }
  }

  lemma RenderRelationFunctional(
    cmd: Schema.CatCmd,
    data: BW.Bytes,
    output1: BW.Bytes,
    output2: BW.Bytes
  )
    requires exists fragments: seq<BW.Bytes>,
               cuts: seq<nat>,
               numbers: seq<nat> ::
               Spec.RenderRelation(
                 cmd,
                 data,
                 output1,
                 fragments,
                 cuts,
                 numbers
               )
    requires exists fragments: seq<BW.Bytes>,
               cuts: seq<nat>,
               numbers: seq<nat> ::
               Spec.RenderRelation(
                 cmd,
                 data,
                 output2,
                 fragments,
                 cuts,
                 numbers
               )
    ensures output1 == output2
  {
    var fragments1: seq<BW.Bytes>,
        cuts1: seq<nat>,
        numbers1: seq<nat> :|
      Spec.RenderRelation(
        cmd,
        data,
        output1,
        fragments1,
        cuts1,
        numbers1
      );
    var fragments2: seq<BW.Bytes>,
        cuts2: seq<nat>,
        numbers2: seq<nat> :|
      Spec.RenderRelation(
        cmd,
        data,
        output2,
        fragments2,
        cuts2,
        numbers2
      );
    reveal Spec.RenderRelation();
    LineNumberRelationFunctional(cmd, data, numbers1, numbers2);
    assert |fragments1| == |fragments2|;
    assert forall p: nat | p < |fragments1| ::
        fragments1[p] == fragments2[p] by {
      forall p: nat | p < |fragments1|
        ensures fragments1[p] == fragments2[p]
      {
      }
    }
    assert fragments1 == fragments2;
    FragmentsConcatenateFunctional(
      fragments1,
      output1,
      cuts1,
      output2,
      cuts2
    );
  }

  lemma RunRelationWitness(
    cmd: Schema.CatCmd, preFs: BW.FileSystem, preStreams: (BW.TrustedStreamRequest) -> BW.TrustedStreamResult, preStdin: BW.Bytes,
    postStdin: BW.Bytes, output: BW.Bytes, errors: BW.Bytes, exit: int
  ) returns (
      readResults: seq<BW.IOResult<BW.Bytes>>, data: BW.Bytes,
      dataFragments: seq<BW.Bytes>, dataCuts: seq<nat>,
      errorFragments: seq<BW.Bytes>, errorCuts: seq<nat>, hadError: bool,
      byteFragments: seq<BW.Bytes>, outputCuts: seq<nat>, numbers: seq<nat>
    )
    requires Spec.RunRelation(cmd, preFs, preStreams, preStdin, postStdin, output, errors, exit)
    ensures Spec.InputTraceRelation(cmd, preFs, preStreams, preStdin, postStdin, data,
                                    errors, hadError, readResults, dataFragments, dataCuts, errorFragments, errorCuts)
    ensures Spec.RenderRelation(cmd, data, output, byteFragments, outputCuts, numbers)
    ensures exit == (if hadError then 1 else 0)
  {
    readResults, data, dataFragments, dataCuts, errorFragments, errorCuts,
    hadError, byteFragments, outputCuts, numbers :|
      Spec.InputTraceRelation(cmd, preFs, preStreams, preStdin, postStdin, data,
                              errors, hadError, readResults, dataFragments, dataCuts, errorFragments, errorCuts) &&
      Spec.RenderRelation(cmd, data, output, byteFragments, outputCuts, numbers) &&
      exit == (if hadError then 1 else 0);
  }

  lemma RunRelationFunctional(
    cmd: Schema.CatCmd,
    preFs: BW.FileSystem, preStreams: (BW.TrustedStreamRequest) -> BW.TrustedStreamResult,
    preStdin: BW.Bytes,
    postStdin1: BW.Bytes,
    output1: BW.Bytes,
    errors1: BW.Bytes,
    exit1: int,
    postStdin2: BW.Bytes,
    output2: BW.Bytes,
    errors2: BW.Bytes,
    exit2: int
  )
    requires Spec.RunRelation(
               cmd,
               preFs, preStreams,
               preStdin,
               postStdin1,
               output1,
               errors1,
               exit1
             )
    requires Spec.RunRelation(
               cmd,
               preFs, preStreams,
               preStdin,
               postStdin2,
               output2,
               errors2,
               exit2
             )
    ensures postStdin1 == postStdin2
    ensures output1 == output2
    ensures errors1 == errors2
    ensures exit1 == exit2
  {
    var readResults1, data1, dataFragments1, dataCuts1, errorFragments1,
        errorCuts1, hadError1, byteFragments1, outputCuts1, numbers1 :=
      RunRelationWitness(cmd, preFs, preStreams, preStdin, postStdin1, output1, errors1, exit1);
    var readResults2, data2, dataFragments2, dataCuts2, errorFragments2,
        errorCuts2, hadError2, byteFragments2, outputCuts2, numbers2 :=
      RunRelationWitness(cmd, preFs, preStreams, preStdin, postStdin2, output2, errors2, exit2);
    InputTraceRelationFunctional(
      cmd,
      preFs, preStreams,
      preStdin,
      postStdin1,
      data1,
      errors1,
      hadError1,
      postStdin2,
      data2,
      errors2,
      hadError2
    );
    RenderRelationFunctional(cmd, data1, output1, output2);
  }

  twostate lemma {:isolate_assertions} PreparedRunObservationFunctional(
    raw: Schema.CatCmdRaw,
    io1: BenchIO.IO,
    io2: BenchIO.IO,
    exit1: int,
    exit2: int
  , new plannedOut1: BW.Bytes, new plannedErr1: BW.Bytes,
    new plannedOut2: BW.Bytes, new plannedErr2: BW.Bytes)
    requires old(io1.stdin()) == old(io2.stdin())
    requires old(io1.stdout()) == old(io2.stdout())
    requires old(io1.stderr()) == old(io2.stderr())
    requires old(io1.fs()) == old(io2.fs())
    requires old(io1.trustedStreams()) == old(io2.trustedStreams())
    requires Spec.PreparedSpec(raw, io1, exit1, plannedOut1, plannedErr1)
    requires Spec.PreparedSpec(raw, io2, exit2, plannedOut2, plannedErr2)
    ensures io1.stdin() == io2.stdin()
    ensures plannedOut1 ==
            plannedOut2
    ensures plannedErr1 ==
            plannedErr2
    ensures exit1 == exit2
  {
    var cmd := Spec.Command(raw);
    if cmd.mode == Schema.ModeHelp {
    } else if cmd.mode == Schema.ModeVersion {
    } else {
      assert exists output: BW.Bytes, errors: BW.Bytes ::
          Spec.RunRelation(
            cmd,
            old(io1.fs()),
            old(io1.trustedStreams()),
            old(io1.stdin()),
            io1.stdin(),
            output,
            errors,
            exit1
          ) &&
          plannedOut1 == output &&
          plannedErr1 == errors by {
        reveal Spec.PreparedSpec();
        reveal Spec.RunRelation();
      }
      var output1: BW.Bytes, errors1: BW.Bytes :|
        Spec.RunRelation(
          cmd,
          old(io1.fs()),
          old(io1.trustedStreams()),
          old(io1.stdin()),
          io1.stdin(),
          output1,
          errors1,
          exit1
        ) &&
        plannedOut1 == output1 &&
        plannedErr1 == errors1;
      assert exists output: BW.Bytes, errors: BW.Bytes ::
          Spec.RunRelation(
            cmd,
            old(io2.fs()),
            old(io2.trustedStreams()),
            old(io2.stdin()),
            io2.stdin(),
            output,
            errors,
            exit2
          ) &&
          plannedOut2 == output &&
          plannedErr2 == errors by {
        reveal Spec.PreparedSpec();
        reveal Spec.RunRelation();
      }
      var output2: BW.Bytes, errors2: BW.Bytes :|
        Spec.RunRelation(
          cmd,
          old(io2.fs()),
          old(io2.trustedStreams()),
          old(io2.stdin()),
          io2.stdin(),
          output2,
          errors2,
          exit2
        ) &&
        plannedOut2 == output2 &&
        plannedErr2 == errors2;
      RunRelationFunctional(
        cmd,
        old(io1.fs()),
        old(io1.trustedStreams()),
        old(io1.stdin()),
        io1.stdin(),
        output1,
        errors1,
        exit1,
        io2.stdin(),
        output2,
        errors2,
        exit2
      );
      assert plannedOut1 == output1;
      assert plannedOut2 == output2;
      assert plannedErr1 == errors1;
      assert plannedErr2 == errors2;
    }
  }

  twostate lemma {:isolate_assertions} RunObservationFunctional(
    raw: Schema.CatCmdRaw,
    io1: BenchIO.IO,
    io2: BenchIO.IO,
    exit1: int,
    exit2: int
  )
    requires old(io1.stdin()) == old(io2.stdin())
    requires old(io1.stdout()) == old(io2.stdout())
    requires old(io1.stderr()) == old(io2.stderr())
    requires old(io1.fs()) == old(io2.fs())
    requires old(io1.trustedStreams()) == old(io2.trustedStreams())
    requires Spec.Spec(raw, io1, exit1)
    requires Spec.Spec(raw, io2, exit2)
    ensures io1.stdin() == io2.stdin()
    ensures io1.stdout()[|old(io1.stdout())|..] ==
            io2.stdout()[|old(io2.stdout())|..]
    ensures io1.stderr()[|old(io1.stderr())|..] ==
            io2.stderr()[|old(io2.stderr())|..]
    ensures exit1 == exit2
  {
    var out1: BW.Bytes, diagnostics1: BW.Bytes, normal1: int :|
      Spec.PreparedSpec(raw, io1, normal1, out1, diagnostics1) &&
      Spec.Emission(raw, io1, out1, diagnostics1, normal1, exit1);
    var out2: BW.Bytes, diagnostics2: BW.Bytes, normal2: int :|
      Spec.PreparedSpec(raw, io2, normal2, out2, diagnostics2) &&
      Spec.Emission(raw, io2, out2, diagnostics2, normal2, exit2);
    PreparedRunObservationFunctional(raw, io1, io2, normal1, normal2,
                                     out1, diagnostics1,
                                     out2, diagnostics2);
    assert out1 == out2 && diagnostics1 == diagnostics2 && normal1 == normal2;
  }

  twostate lemma CoreSummaryImpliesSpec(raw: Schema.CatCmdRaw, io: BenchIO.IO, exit: int)
    requires Core.CoreSummary(raw, io, exit)
    ensures Spec.Spec(raw, io, exit)
  {
    var out: BenchWorld.Bytes, diagnostics: BenchWorld.Bytes, normalExit: int :|
      Core.PreparedSummary(raw, io, normalExit,
                           out, diagnostics) &&
      Spec.Emission(raw, io, out, diagnostics, normalExit, exit);
    PreparedSummaryImpliesPreparedSpec(raw, io, normalExit,
                                       out, diagnostics);
  }
}
