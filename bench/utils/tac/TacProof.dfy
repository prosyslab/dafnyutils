include "../../core/World.dfy"
include "../../core/IO.dfy"
include "TacSchema.dfy"
include "TacCore.dfy"
include "TacSpec.dfy"

module TacProof {
  import BenchIO
  import BW = BenchWorld
  import CliTypes
  import Schema = TacSchema
  import Core = TacCore
  import Spec = TacSpec

  lemma InputsFromOperandsEq(operands: seq<string>)
    ensures Core.InputsFromOperands(operands) == Spec.InputsFromOperands(operands)
    decreases |operands|
  {
    if |operands| > 0 {
      InputsFromOperandsEq(operands[1..]);
    }
  }

  lemma SeparatorValueEq(raw: CliTypes.OptionalString)
    ensures Core.SeparatorValue(raw) == Spec.SeparatorValue(raw)
  {
  }

  lemma CommandEq(raw: Schema.TacCmdRaw)
    ensures Core.Command(raw) == Spec.Command(raw)
  {
    InputsFromOperandsEq(raw.operands);
    SeparatorValueEq(raw.separator);
  }

  lemma ValidStartAt(
    data: BW.Bytes,
    sep: BW.Bytes,
    starts: seq<nat>,
    i: nat
  )
    requires Core.ValidStarts(data, sep, starts)
    requires i < |starts|
    ensures starts[i] + |sep| <= |data|
    ensures data[starts[i]..starts[i] + |sep|] == sep
  {
    reveal Core.ValidStarts();
  }

  lemma ValidStartOrder(
    data: BW.Bytes,
    sep: BW.Bytes,
    starts: seq<nat>,
    i: nat
  )
    requires Core.ValidStarts(data, sep, starts)
    requires i + 1 < |starts|
    ensures starts[i] + |sep| <= starts[i + 1]
  {
    reveal Core.ValidStarts();
  }

  lemma CutsOrderedAt(
    data: BW.Bytes,
    cuts: seq<nat>,
    i: nat
  )
    requires i + 1 < |cuts|
    requires forall j: nat {:trigger cuts[j]} | j + 1 < |cuts| ::
               cuts[j] <= cuts[j + 1] <= |data|
    ensures cuts[i] <= cuts[i + 1] <= |data|
  {
    assert cuts[i] <= cuts[i + 1] && cuts[i + 1] <= |data|;
  }

  lemma CutsMonotone(
    data: BW.Bytes,
    cuts: seq<nat>,
    lo: nat,
    hi: nat
  )
    requires lo <= hi < |cuts|
    requires 0 < hi
    requires forall j: nat {:trigger cuts[j], cuts[j + 1]} | j + 1 < |cuts| ::
               cuts[j] <= cuts[j + 1] <= |data|
    ensures cuts[lo] <= cuts[hi] <= |data|
    decreases hi - lo
  {
    if lo < hi {
      CutsOrderedAt(data, cuts, lo);
      CutsMonotone(data, cuts, lo + 1, hi);
    } else {
      CutsOrderedAt(data, cuts, hi - 1);
    }
  }

  lemma SeparatorMatchCovered(
    data: BW.Bytes,
    sep: BW.Bytes,
    start: nat
  )
    requires |sep| > 0
    requires start + |sep| <= |data|
    requires data[start..start + |sep|] == sep
    ensures
      start in Core.SelectedStarts(data, sep) ||
      exists i: nat ::
        i < |Core.SelectedStarts(data, sep)| &&
        start < Core.SelectedStarts(data, sep)[i] < start + |sep|
  {
    reveal Core.SelectedStarts();
    reveal Core.SearchLimit();
    assert start < Core.SearchLimit(|data|, sep);
    assert Core.MatchAt(data, sep, start);
    SelectedStartsScanCovers(
      data,
      sep,
      Core.SearchLimit(|data|, sep),
      start
    );
  }

  lemma ConcatShiftSlice<T>(
    left: seq<T>,
    right: seq<T>,
    lo: nat,
    hi: nat
  )
    requires lo <= hi <= |right|
    ensures (left + right)[|left| + lo..|left| + hi] == right[lo..hi]
  {
  }

  lemma SelectedStartsScanCovers(
    data: BW.Bytes,
    sep: BW.Bytes,
    limit: nat,
    start: nat
  )
    requires |sep| > 0
    requires limit <= Core.SearchLimit(|data|, sep)
    requires start < limit
    requires Core.MatchAt(data, sep, start)
    ensures
      start in Core.SelectedStartsScan(data, sep, limit) ||
      exists i: nat ::
        i < |Core.SelectedStartsScan(data, sep, limit)| &&
        start < Core.SelectedStartsScan(data, sep, limit)[i] < start + |sep|
    decreases limit
  {
    if limit > 0 {
      var candidate := limit - 1;
      if Core.MatchAt(data, sep, candidate) {
        var nextLimit := Core.BackedLimit(candidate, sep);
        var prefix := Core.SelectedStartsScan(data, sep, nextLimit);
        assert Core.SelectedStartsScan(data, sep, limit) == prefix + [candidate];
        if start < nextLimit {
          SelectedStartsScanCovers(data, sep, nextLimit, start);
          if start in prefix {
            assert start in prefix + [candidate];
          } else {
            var i: nat :|
              i < |prefix| &&
              start < prefix[i] < start + |sep|;
            assert (prefix + [candidate])[i] == prefix[i];
            assert exists j: nat ::
                j < |prefix + [candidate]| &&
                start < (prefix + [candidate])[j] < start + |sep|;
          }
        } else if start == candidate {
          assert start in prefix + [candidate];
        } else {
          assert start < candidate;
          assert candidate < start + |sep|;
          assert (prefix + [candidate])[|prefix|] == candidate;
          assert exists i: nat ::
              i < |Core.SelectedStartsScan(data, sep, limit)| &&
              start < Core.SelectedStartsScan(data, sep, limit)[i] < start + |sep|;
        }
      } else {
        assert start < candidate;
        SelectedStartsScanCovers(data, sep, limit - 1, start);
      }
    }
  }

  lemma SelectedStartsGivesCutColumn(data: BW.Bytes, sep: BW.Bytes)
    requires |sep| > 0
    ensures Spec.SeparatorCutColumn(data, sep, Core.SelectedStarts(data, sep))
  {
    var starts := Core.SelectedStarts(data, sep);
    reveal Spec.SeparatorCutColumn();
    assert Core.ValidStarts(data, sep, starts);
    assert forall i: nat {:trigger starts[i]} | i < |starts| ::
        starts[i] + |sep| <= |data| &&
        data[starts[i]..starts[i] + |sep|] == sep by {
      forall i: nat {:trigger starts[i]} | i < |starts|
        ensures starts[i] + |sep| <= |data| &&
                data[starts[i]..starts[i] + |sep|] == sep
      {
        ValidStartAt(data, sep, starts, i);
      }
    }
    assert forall i: nat {:trigger starts[i], starts[i + 1]} | i + 1 < |starts| ::
        starts[i] + |sep| <= starts[i + 1] by {
      forall i: nat {:trigger starts[i], starts[i + 1]} | i + 1 < |starts|
        ensures starts[i] + |sep| <= starts[i + 1]
      {
        ValidStartOrder(data, sep, starts, i);
      }
    }
    assert forall start: nat
        {:trigger start in Spec.SeparatorStartSet(data, sep)} |
                                     start in Spec.SeparatorStartSet(data, sep) ::
        start in starts ||
        exists i: nat ::
          i < |starts| &&
          start < starts[i] < start + |sep| by {
      forall start: nat
        {:trigger start in Spec.SeparatorStartSet(data, sep)} |
    start in Spec.SeparatorStartSet(data, sep)
        ensures
          start in starts ||
          exists i: nat ::
            i < |starts| &&
            start < starts[i] < start + |sep|
      {
        reveal Spec.SeparatorStartSet();
        SeparatorMatchCovered(data, sep, start);
        if start in Core.SelectedStarts(data, sep) {
          assert start in starts;
        } else {
          var i: nat :|
            i < |Core.SelectedStarts(data, sep)| &&
            start < Core.SelectedStarts(data, sep)[i] < start + |sep|;
          assert starts[i] == Core.SelectedStarts(data, sep)[i];
          assert exists j: nat ::
              j < |starts| &&
              start < starts[j] < start + |sep|;
        }
      }
    }
  }

  lemma InputCutsBounds(
    data: BW.Bytes,
    sep: BW.Bytes,
    before: bool,
    starts: seq<nat>
  )
    requires |sep| > 0
    requires Core.ValidStarts(data, sep, starts)
    ensures |Core.InputCuts(data, sep, before, starts)| == |starts| + 2
    ensures Core.InputCuts(data, sep, before, starts)[0] == 0
    ensures Core.InputCuts(data, sep, before, starts)[|starts| + 1] == |data|
    ensures forall i: nat
              {:trigger Core.InputCuts(data, sep, before, starts)[i],
              Core.InputCuts(data, sep, before, starts)[i + 1]} |
              i + 1 < |Core.InputCuts(data, sep, before, starts)| ::
              Core.InputCuts(data, sep, before, starts)[i] <=
              Core.InputCuts(data, sep, before, starts)[i + 1] <= |data|
  {
    var cuts := Core.InputCuts(data, sep, before, starts);
    forall i: nat
      {:trigger cuts[i], cuts[i + 1]} |
      i + 1 < |cuts|
      ensures cuts[i] <= cuts[i + 1] <= |data|
    {
      if i == 0 {
        if |starts| > 0 {
          ValidStartAt(data, sep, starts, 0);
          assert cuts[1] == starts[0] + (if before then 0 else |sep|);
          assert starts[0] + |sep| <= |data|;
          assert cuts[0] == 0;
        } else {
          assert cuts == [0, |data|];
        }
      } else if i < |starts| {
        ValidStartOrder(data, sep, starts, i - 1);
        ValidStartAt(data, sep, starts, i);
        assert cuts[i] ==
               starts[i - 1] + (if before then 0 else |sep|);
        assert cuts[i + 1] ==
               starts[i] + (if before then 0 else |sep|);
        assert starts[i - 1] + |sep| <= starts[i];
        assert starts[i] + |sep| <= |data|;
      } else {
        assert i == |starts|;
        if |starts| > 0 {
          ValidStartAt(data, sep, starts, i - 1);
          assert cuts[i] ==
                 starts[i - 1] + (if before then 0 else |sep|);
          assert starts[i - 1] + |sep| <= |data|;
        } else {
          assert cuts == [0, |data|];
        }
      }
    }
  }

  lemma ReverseIntervalsLength(
    data: BW.Bytes,
    cuts: seq<nat>,
    count: nat
  )
    requires 0 < |cuts|
    requires count < |cuts|
    requires forall i: nat {:trigger cuts[i], cuts[i + 1]} | i + 1 < |cuts| ::
               cuts[i] <= cuts[i + 1] <= |data|
    ensures |Core.ReverseIntervals(data, cuts, count)| == cuts[count] - cuts[0]
    decreases count
  {
    if count > 0 {
      CutsOrderedAt(data, cuts, count - 1);
      assert !(cuts[count - 1] > cuts[count] || cuts[count] > |data|);
      ReverseIntervalsLength(data, cuts, count - 1);
      assert |data[cuts[count - 1]..cuts[count]]| ==
             cuts[count] - cuts[count - 1];
    }
  }

  lemma ReverseIntervalsSlice(
    data: BW.Bytes,
    cuts: seq<nat>,
    count: nat,
    i: nat
  )
    requires 0 < count < |cuts|
    requires i < count
    requires forall j: nat {:trigger cuts[j], cuts[j + 1]} | j + 1 < |cuts| ::
               cuts[j] <= cuts[j + 1] <= |data|
    requires |Core.ReverseIntervals(data, cuts, count)| == cuts[count] - cuts[0]
    requires cuts[count - 1] <= cuts[count] <= |data|
    requires cuts[count - i - 1] <= cuts[count - i] <= |data|
    requires cuts[count - i] <= cuts[count]
    requires cuts[count] - cuts[count - i - 1] <=
             |Core.ReverseIntervals(data, cuts, count)|
    ensures
      Core.ReverseIntervals(data, cuts, count)[
      cuts[count] - cuts[count - i]..
      cuts[count] - cuts[count - i - 1]
      ] ==
      data[cuts[count - i - 1]..cuts[count - i]]
    decreases count
  {
    assert cuts[count - 1] <= cuts[count] <= |data|;
    var piece := data[cuts[count - 1]..cuts[count]];
    var rest := Core.ReverseIntervals(data, cuts, count - 1);
    assert Core.ReverseIntervals(data, cuts, count) == piece + rest;
    if i == 0 {
      assert cuts[count] - cuts[count] == 0;
      assert cuts[count] - cuts[count - 1] == |piece|;
    } else {
      ReverseIntervalsLength(data, cuts, count - 1);
      assert |rest| == cuts[count - 1] - cuts[0];
      CutsOrderedAt(data, cuts, count - i - 1);
      assert cuts[count - i - 1] <= cuts[count - i] <= |data|;
      assert cuts[count - 1] - cuts[count - i - 1] <= |rest|;
      CutsOrderedAt(data, cuts, count - 2);
      CutsMonotone(data, cuts, count - i, count - 1);
      ReverseIntervalsSlice(data, cuts, count - 1, i - 1);
      assert cuts[count] - cuts[count - i] ==
             |piece| + cuts[count - 1] - cuts[count - i];
      assert cuts[count] - cuts[count - i - 1] ==
             |piece| + cuts[count - 1] - cuts[count - i - 1];
      ConcatShiftSlice(
        piece,
        rest,
        cuts[count - 1] - cuts[count - i],
        cuts[count - 1] - cuts[count - i - 1]
      );
    }
  }

  lemma ReverseRecordsGivesRelation(
    data: BW.Bytes,
    sep: BW.Bytes,
    before: bool
  )
    requires |sep| > 0
    ensures Spec.ReverseRecordsRelation(
              data,
              sep,
              before,
              Core.ReverseRecords(data, sep, before)
            )
  {
    var starts := Core.SelectedStarts(data, sep);
    var inputCuts := Core.InputCuts(data, sep, before, starts);
    var out := Core.ReverseRecords(data, sep, before);
    InputCutsBounds(data, sep, before, starts);
    SelectedStartsGivesCutColumn(data, sep);
    var count := |inputCuts| - 1;
    var outputCuts := seq(
    |inputCuts|,
    i requires 0 <= i < |inputCuts| =>
      inputCuts[count] - inputCuts[count - i]
      );
    ReverseIntervalsLength(data, inputCuts, count);
    assert |out| == |data|;
    assert Spec.ReverseIntervalOrder(data, out, inputCuts, outputCuts) by {
      forall i: nat
        {:trigger inputCuts[i], inputCuts[i + 1]}
    {:trigger outputCuts[i], outputCuts[i + 1]} |
    i + 2 <= |inputCuts|
        ensures
          inputCuts[|inputCuts| - i - 2] <=
          inputCuts[|inputCuts| - i - 1] <= |data| &&
          outputCuts[i] <= outputCuts[i + 1] <= |out| &&
          out[outputCuts[i]..outputCuts[i + 1]] ==
          data[
          inputCuts[|inputCuts| - i - 2]..
          inputCuts[|inputCuts| - i - 1]
          ]
      {
        CutsOrderedAt(data, inputCuts, |inputCuts| - i - 2);
        CutsOrderedAt(data, inputCuts, count - 1);
        assert outputCuts[i] ==
               inputCuts[count] - inputCuts[count - i];
        assert outputCuts[i + 1] ==
               inputCuts[count] - inputCuts[count - i - 1];
        assert inputCuts[count] - inputCuts[count - i - 1] <= |out|;
        CutsMonotone(data, inputCuts, count - i, count);
        ReverseIntervalsSlice(data, inputCuts, count, i);
      }
    }
  }

  lemma PrefixStdinCharacterization(
    cmd: Schema.TacCmd,
    preStdin: BW.Bytes,
    count: nat
  )
    requires count <= |cmd.inputs|
    ensures Core.PrefixStdin(cmd, preStdin, count) ==
            (if exists i: nat :: i < count && cmd.inputs[i].Stdin? then [] else preStdin)
    decreases count
  {
    if count > 0 {
      PrefixStdinCharacterization(cmd, preStdin, count - 1);
    }
  }

  lemma ReadResultGivesRelation(
    cmd: Schema.TacCmd,
    preFs: BW.FileSystem,
    preStdin: BW.Bytes,
    i: nat
  )
    requires i < |cmd.inputs|
    ensures Spec.ReadResultRelation(
              cmd,
              preFs,
              preStdin,
              i,
              Core.ReadResult(cmd, preFs, preStdin, i)
            )
  {
    PrefixStdinCharacterization(cmd, preStdin, i);
  }

  lemma OutputPieceGivesRelation(
    cmd: Schema.TacCmd,
    result: BW.Result<BW.Bytes>
  )
    requires |cmd.separator| > 0
    ensures Spec.OutputFragmentRelation(
              cmd,
              result,
              Core.OutputPiece(cmd, result)
            )
  {
    match result
    case Ok(data) =>
      ReverseRecordsGivesRelation(data, cmd.separator, cmd.before);
    case Err(_) =>
  }

  lemma AppendFragment(
    fragments: seq<BW.Bytes>,
    combined: BW.Bytes,
    cuts: seq<nat>,
    fragment: BW.Bytes
  )
    requires Spec.FragmentsConcatenate(fragments, combined, cuts)
    ensures Spec.FragmentsConcatenate(
              fragments + [fragment],
              combined + fragment,
              cuts + [|combined + fragment|]
            )
  {
    reveal Spec.FragmentsConcatenate();
    var nextFragments := fragments + [fragment];
    var nextCombined := combined + fragment;
    var nextCuts := cuts + [|nextCombined|];
    forall i: nat {:trigger nextCuts[i], nextCuts[i + 1]} | i < |nextFragments|
      ensures
        nextCuts[i] <= nextCuts[i + 1] <= |nextCombined| &&
        nextCuts[i + 1] == nextCuts[i] + |nextFragments[i]| &&
        nextCombined[nextCuts[i]..nextCuts[i + 1]] == nextFragments[i]
    {
      if i < |fragments| {
        assert nextCuts[i] == cuts[i];
        assert nextCuts[i + 1] == cuts[i + 1];
        assert nextFragments[i] == fragments[i];
        assert cuts[i] <= cuts[i + 1] <= |combined|;
        assert combined[cuts[i]..cuts[i + 1]] == fragments[i];
      } else {
        assert i == |fragments|;
        assert cuts[i] == |combined|;
        assert nextCuts[i] == |combined|;
        assert nextCuts[i + 1] == |nextCombined|;
        assert nextCombined[|combined|..] == fragment;
      }
    }
  }

  lemma ObservationFragmentsAppend(
    observations: seq<Spec.InputObservation>,
    observation: Spec.InputObservation
  )
    ensures Spec.ObservationStdoutFragments(observations + [observation]) ==
            Spec.ObservationStdoutFragments(observations) + [observation.stdoutFragment]
    ensures Spec.ObservationStderrFragments(observations + [observation]) ==
            Spec.ObservationStderrFragments(observations) + [observation.stderrFragment]
  {
    assert |Spec.ObservationStdoutFragments(observations + [observation])| ==
           |Spec.ObservationStdoutFragments(observations) + [observation.stdoutFragment]|;
    assert forall i: nat |
        i < |Spec.ObservationStdoutFragments(observations + [observation])| ::
        Spec.ObservationStdoutFragments(observations + [observation])[i] ==
        (Spec.ObservationStdoutFragments(observations) +
         [observation.stdoutFragment])[i] by {
      forall i: nat |
        i < |Spec.ObservationStdoutFragments(observations + [observation])|
        ensures
          Spec.ObservationStdoutFragments(observations + [observation])[i] ==
          (Spec.ObservationStdoutFragments(observations) +
           [observation.stdoutFragment])[i]
      {
      }
    }
    assert |Spec.ObservationStderrFragments(observations + [observation])| ==
           |Spec.ObservationStderrFragments(observations) + [observation.stderrFragment]|;
    assert forall i: nat |
        i < |Spec.ObservationStderrFragments(observations + [observation])| ::
        Spec.ObservationStderrFragments(observations + [observation])[i] ==
        (Spec.ObservationStderrFragments(observations) +
         [observation.stderrFragment])[i] by {
      forall i: nat |
        i < |Spec.ObservationStderrFragments(observations + [observation])|
        ensures
          Spec.ObservationStderrFragments(observations + [observation])[i] ==
          (Spec.ObservationStderrFragments(observations) +
           [observation.stderrFragment])[i]
      {
      }
    }
  }

  ghost function CoreObservations(
    cmd: Schema.TacCmd,
    preFs: BW.FileSystem,
    preStdin: BW.Bytes,
    count: nat
  ): seq<Spec.InputObservation>
    requires |cmd.separator| > 0
    requires count <= |cmd.inputs|
    ensures |CoreObservations(cmd, preFs, preStdin, count)| == count
    decreases count
  {
    if count == 0 then
      []
    else
      var prior := CoreObservations(cmd, preFs, preStdin, count - 1);
      var i := count - 1;
      var result := Core.ReadResult(cmd, preFs, preStdin, i);
      prior + [
        Spec.InputObservation(
          result,
          Core.OutputPiece(cmd, result),
          Spec.ErrorPiece(cmd.inputs[i], result),
          Spec.HadErrorPiece(cmd.inputs[i], result)
        )
      ]
  }

  lemma CoreObservationsFailure(
    cmd: Schema.TacCmd,
    preFs: BW.FileSystem,
    preStdin: BW.Bytes,
    count: nat
  )
    requires |cmd.separator| > 0
    requires count <= |cmd.inputs|
    ensures Core.PrefixHadError(cmd, preFs, preStdin, count) ==
            (exists i: nat ::
               i < |CoreObservations(cmd, preFs, preStdin, count)| &&
               CoreObservations(cmd, preFs, preStdin, count)[i].failed)
    decreases count
  {
    if count > 0 {
      CoreObservationsFailure(cmd, preFs, preStdin, count - 1);
      var prior := CoreObservations(cmd, preFs, preStdin, count - 1);
      var observations := CoreObservations(cmd, preFs, preStdin, count);
      var i := count - 1;
      var failed := Spec.HadErrorPiece(
        cmd.inputs[i],
        Core.ReadResult(cmd, preFs, preStdin, i)
      );
      assert observations == prior + [
                               Spec.InputObservation(
                                 Core.ReadResult(cmd, preFs, preStdin, i),
                                 Core.OutputPiece(cmd, Core.ReadResult(cmd, preFs, preStdin, i)),
                                 Spec.ErrorPiece(cmd.inputs[i], Core.ReadResult(cmd, preFs, preStdin, i)),
                                 failed
                               )
                             ];
      assert |prior| == count - 1;
      assert |observations| == count;
      assert i < |observations|;
      assert observations[i].failed == failed;
      assert Core.PrefixHadError(cmd, preFs, preStdin, count) ==
             (Core.PrefixHadError(cmd, preFs, preStdin, count - 1) || failed);
      if failed {
        assert observations[i].failed;
        assert exists j: nat ::
            j < |observations| && observations[j].failed;
        assert Core.PrefixHadError(cmd, preFs, preStdin, count);
      } else {
        if exists j: nat :: j < |observations| && observations[j].failed {
          var j: nat :| j < |observations| && observations[j].failed;
          assert j != i;
          assert j < |prior|;
          assert observations[j] == prior[j];
          assert exists k: nat :: k < |prior| && prior[k].failed;
        }
        if exists j: nat :: j < |prior| && prior[j].failed {
          var j: nat :| j < |prior| && prior[j].failed;
          assert observations[j] == prior[j];
          assert exists k: nat ::
              k < |observations| && observations[k].failed;
        }
        assert
          (exists j: nat :: j < |observations| && observations[j].failed) ==
          (exists j: nat :: j < |prior| && prior[j].failed);
      }
      assert Core.PrefixHadError(cmd, preFs, preStdin, count) ==
             (exists j: nat ::
                j < |observations| && observations[j].failed);
      assert observations == CoreObservations(cmd, preFs, preStdin, count);
      assert Core.PrefixHadError(cmd, preFs, preStdin, count) ==
             (exists j: nat ::
                j < |CoreObservations(cmd, preFs, preStdin, count)| &&
                CoreObservations(cmd, preFs, preStdin, count)[j].failed);
    }
  }

  lemma {:isolate_assertions} BuildPrefixWitness(
    cmd: Schema.TacCmd,
    preFs: BW.FileSystem,
    preStdin: BW.Bytes,
    count: nat
  ) returns (
      observations: seq<Spec.InputObservation>,
      stdoutCuts: seq<nat>,
      stderrCuts: seq<nat>
    )
    requires |cmd.separator| > 0
    requires count <= |cmd.inputs|
    ensures |observations| == count
    ensures observations == CoreObservations(cmd, preFs, preStdin, count)
    ensures forall i: nat {:trigger observations[i]} | i < |observations| ::
              Spec.InputObservationRelation(cmd, preFs, preStdin, i, observations[i])
    ensures Spec.FragmentsConcatenate(
              Spec.ObservationStdoutFragments(observations),
              Core.PrefixOutput(cmd, preFs, preStdin, count),
              stdoutCuts
            )
    ensures Spec.FragmentsConcatenate(
              Spec.ObservationStderrFragments(observations),
              Core.PrefixErrorOutput(cmd, preFs, preStdin, count),
              stderrCuts
            )
    decreases count
  {
    if count == 0 {
      observations := [];
      stdoutCuts := [0];
      stderrCuts := [0];
      assert Spec.FragmentsConcatenate([], [], [0]);
    } else {
      var priorObservations, priorStdoutCuts, priorStderrCuts :=
        BuildPrefixWitness(cmd, preFs, preStdin, count - 1);
      var i := count - 1;
      var result := Core.ReadResult(cmd, preFs, preStdin, i);
      var stdoutFragment := Core.OutputPiece(cmd, result);
      var stderrFragment := Spec.ErrorPiece(cmd.inputs[i], result);
      var failed := Spec.HadErrorPiece(cmd.inputs[i], result);
      var observation := Spec.InputObservation(
        result,
        stdoutFragment,
        stderrFragment,
        failed
      );
      ReadResultGivesRelation(cmd, preFs, preStdin, i);
      OutputPieceGivesRelation(cmd, result);
      assert Spec.InputObservationRelation(
          cmd,
          preFs,
          preStdin,
          i,
          observation
        );
      observations := priorObservations + [observation];
      stdoutCuts := priorStdoutCuts +
      [|Core.PrefixOutput(cmd, preFs, preStdin, count)|];
      stderrCuts := priorStderrCuts +
      [|Core.PrefixErrorOutput(cmd, preFs, preStdin, count)|];
      ObservationFragmentsAppend(priorObservations, observation);
      AppendFragment(
        Spec.ObservationStdoutFragments(priorObservations),
        Core.PrefixOutput(cmd, preFs, preStdin, count - 1),
        priorStdoutCuts,
        stdoutFragment
      );
      AppendFragment(
        Spec.ObservationStderrFragments(priorObservations),
        Core.PrefixErrorOutput(cmd, preFs, preStdin, count - 1),
        priorStderrCuts,
        stderrFragment
      );
      assert Core.PrefixOutput(cmd, preFs, preStdin, count) ==
             Core.PrefixOutput(cmd, preFs, preStdin, count - 1) + stdoutFragment;
      assert Core.PrefixErrorOutput(cmd, preFs, preStdin, count) ==
             Core.PrefixErrorOutput(cmd, preFs, preStdin, count - 1) + stderrFragment;
      assert forall j: nat {:trigger observations[j]} | j < |observations| ::
          Spec.InputObservationRelation(cmd, preFs, preStdin, j, observations[j]) by {
        forall j: nat {:trigger observations[j]} | j < |observations|
          ensures Spec.InputObservationRelation(
                    cmd,
                    preFs,
                    preStdin,
                    j,
                    observations[j]
                  )
        {
          if j < |priorObservations| {
            assert observations[j] == priorObservations[j];
          } else {
            assert j == i;
            assert observations[j] == observation;
          }
        }
      }
    }
  }

  lemma CoreSummaryImpliesTrace(
    cmd: Schema.TacCmd,
    preFs: BW.FileSystem,
    preStdin: BW.Bytes
  )
    requires |cmd.separator| > 0
    ensures Spec.InputTraceRelation(
              cmd,
              preFs,
              preStdin,
              Core.PrefixStdin(cmd, preStdin, |cmd.inputs|),
              Core.PrefixOutput(cmd, preFs, preStdin, |cmd.inputs|),
              Core.PrefixErrorOutput(cmd, preFs, preStdin, |cmd.inputs|),
              Core.PrefixHadError(cmd, preFs, preStdin, |cmd.inputs|)
            )
  {
    var observations, stdoutCuts, stderrCuts :=
      BuildPrefixWitness(cmd, preFs, preStdin, |cmd.inputs|);
    CoreObservationsFailure(cmd, preFs, preStdin, |cmd.inputs|);
    PrefixStdinCharacterization(cmd, preStdin, |cmd.inputs|);
    assert Spec.InputTraceWitnessRelation(
        cmd,
        preFs,
        preStdin,
        Core.PrefixStdin(cmd, preStdin, |cmd.inputs|),
        Core.PrefixOutput(cmd, preFs, preStdin, |cmd.inputs|),
        Core.PrefixErrorOutput(cmd, preFs, preStdin, |cmd.inputs|),
        Core.PrefixHadError(cmd, preFs, preStdin, |cmd.inputs|),
        observations,
        stdoutCuts,
        stderrCuts
      );
  }

  twostate lemma CoreSummaryImpliesSpec(
    raw: Schema.TacCmdRaw,
    io: BenchIO.IO,
    exit: int
  )
    requires Core.CoreSummary(raw, io, exit)
    ensures Spec.Spec(raw, io, exit)
  {
    CommandEq(raw);
    var cmd := Core.Command(raw);
    assert cmd == Spec.Command(raw);
    if cmd.mode == Schema.ModeHelp {
    } else if cmd.mode == Schema.ModeVersion {
    } else {
      CoreSummaryImpliesTrace(cmd, old(io.fs()), old(io.stdin()));
    }
  }
}
