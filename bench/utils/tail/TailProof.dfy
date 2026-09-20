include "../../core/World.dfy"
include "../../core/IO.dfy"
include "TailSchema.dfy"
include "TailRecordCore.dfy"
include "TailRecordSpec.dfy"
include "TailCore.dfy"
include "TailSpec.dfy"

module TailProof {
  import BenchIO
  import BW = BenchWorld
  import Schema = TailSchema
  import RCore = TailRecordCore
  import RSpec = TailRecordSpec
  import Core = TailCore
  import Spec = TailSpec

  lemma InputsFromOperandsEq(operands: seq<string>)
    ensures Core.InputsFromOperands(operands) == Spec.InputsFromOperands(operands)
    decreases |operands|
  {
    if |operands| > 0 {
      InputsFromOperandsEq(operands[1..]);
    }
  }

  lemma CommandEq(raw: Schema.TailCmdRaw)
    ensures Core.Command(raw) == Spec.Command(raw)
  {
    InputsFromOperandsEq(raw.operands);
  }

  lemma PrefixStdinCharacterization(
    cmd: Schema.TailCmd,
    preStdin: BW.Bytes,
    count: nat
  )
    requires count <= |cmd.inputs|
    ensures Core.PrefixStdinCore(cmd, preStdin, count) ==
            (if exists i: nat :: i < count && cmd.inputs[i].Stdin? then [] else preStdin)
    decreases count
  {
    if count > 0 {
      PrefixStdinCharacterization(cmd, preStdin, count - 1);
    }
  }

  lemma ReadResultGivesRelation(
    cmd: Schema.TailCmd,
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
              Core.ReadResultCore(cmd, preFs, preStdin, i)
            )
  {
    PrefixStdinCharacterization(cmd, preStdin, i);
  }

  lemma ShiftCutsLength(cuts: seq<nat>, delta: nat)
    ensures |RCore.ShiftCuts(cuts, delta)| == |cuts|
  {
  }

  lemma ShiftCutsIndex(cuts: seq<nat>, delta: nat, i: nat)
    requires i < |cuts|
    ensures RCore.ShiftCuts(cuts, delta)[i] == cuts[i] + delta
  {
  }

  lemma RecordCutElement(
    data: BW.Bytes,
    delimiter: char,
    cuts: seq<nat>,
    i: nat
  )
    requires RSpec.RecordCutColumn(data, delimiter, cuts)
    requires i + 1 < |cuts|
    ensures cuts[i] < cuts[i + 1] <= |data|
    ensures forall j: nat {:trigger data[j]} |
              cuts[i] <= j && j + 1 < cuts[i + 1] :: data[j] != delimiter
    ensures data[cuts[i + 1] - 1] == delimiter || cuts[i + 1] == |data|
  {
    reveal RSpec.RecordCutColumn();
    reveal RSpec.RecordInterval();
  }

  lemma RecordCutsGiveRelation(data: BW.Bytes, delimiter: char)
    ensures RSpec.RecordCutColumn(
              data,
              delimiter,
              RCore.RecordCuts(data, delimiter)
            )
    decreases |data|
  {
    reveal RSpec.RecordCutColumn();
    var cuts := RCore.RecordCuts(data, delimiter);
    if |data| == 0 {
      assert cuts == [0];
    } else if |data| == 1 {
      assert cuts == [0, 1];
    } else {
      var tail := data[1..];
      var tailCuts := RCore.RecordCuts(tail, delimiter);
      RecordCutsGiveRelation(tail, delimiter);
      var shifted := RCore.ShiftCuts(tailCuts, 1);
      ShiftCutsLength(tailCuts, 1);
      assert 1 < |tailCuts|;
      assert tailCuts[0] == 0;
      assert tailCuts[|tailCuts| - 1] == |tail|;
      if data[0] == delimiter {
        assert cuts == [0] + shifted;
        forall i: nat {:trigger cuts[i], cuts[i + 1]} | i + 1 < |cuts|
          ensures RSpec.RecordInterval(
                    data, delimiter, cuts[i], cuts[i + 1]
                  )
        {
          if i == 0 {
            ShiftCutsIndex(tailCuts, 1, 0);
            assert cuts[0] == 0;
            assert cuts[1] == 1;
          } else {
            RecordCutElement(tail, delimiter, tailCuts, i - 1);
            ShiftCutsIndex(tailCuts, 1, i - 1);
            ShiftCutsIndex(tailCuts, 1, i);
            assert cuts[i] == tailCuts[i - 1] + 1;
            assert cuts[i + 1] == tailCuts[i] + 1;
            assert tailCuts[i - 1] < tailCuts[i] <= |tail|;
            assert cuts[i] < cuts[i + 1] <= |data|;
            forall j: nat {:trigger data[j]} |
              cuts[i] <= j && j + 1 < cuts[i + 1]
              ensures data[j] != delimiter
            {
              assert 0 < j;
              assert tailCuts[i - 1] <= j - 1;
              assert (j - 1) + 1 < tailCuts[i];
              assert tail[j - 1] == data[j];
              assert tail[j - 1] != delimiter;
            }
            if tail[tailCuts[i] - 1] == delimiter {
              assert data[cuts[i + 1] - 1] ==
                     tail[tailCuts[i] - 1];
            } else {
              assert tailCuts[i] == |tail|;
              assert cuts[i + 1] == |data|;
            }
          }
          assert RSpec.RecordInterval(
              data, delimiter, cuts[i], cuts[i + 1]
            ) by {
            reveal RSpec.RecordInterval();
          }
        }
        assert 0 < |cuts|;
        assert cuts[0] == 0;
        assert cuts[|cuts| - 1] == |data|;
        assert RSpec.RecordCutColumn(data, delimiter, cuts) by {
          reveal RSpec.RecordCutColumn();
        }
      } else {
        assert cuts == [0] + shifted[1..];
        forall i: nat {:trigger cuts[i], cuts[i + 1]} | i + 1 < |cuts|
          ensures RSpec.RecordInterval(
                    data, delimiter, cuts[i], cuts[i + 1]
                  )
        {
          RecordCutElement(tail, delimiter, tailCuts, i);
          ShiftCutsIndex(tailCuts, 1, i);
          ShiftCutsIndex(tailCuts, 1, i + 1);
          assert cuts[i + 1] == tailCuts[i + 1] + 1;
          if i > 0 {
            assert cuts[i] == tailCuts[i] + 1;
          } else {
            assert cuts[i] == 0;
          }
          assert tailCuts[i] < tailCuts[i + 1] <= |tail|;
          assert cuts[i] < cuts[i + 1] <= |data|;
          forall j: nat {:trigger data[j]} |
            cuts[i] <= j && j + 1 < cuts[i + 1]
            ensures data[j] != delimiter
          {
            if j == 0 {
              assert data[j] != delimiter;
            } else {
              assert tailCuts[i] <= j - 1;
              assert (j - 1) + 1 < tailCuts[i + 1];
              assert tail[j - 1] == data[j];
              assert tail[j - 1] != delimiter;
            }
          }
          if tail[tailCuts[i + 1] - 1] == delimiter {
            assert data[cuts[i + 1] - 1] ==
                   tail[tailCuts[i + 1] - 1];
          } else {
            assert tailCuts[i + 1] == |tail|;
            assert cuts[i + 1] == |data|;
          }
          assert RSpec.RecordInterval(
              data, delimiter, cuts[i], cuts[i + 1]
            ) by {
            reveal RSpec.RecordInterval();
          }
        }
        assert 0 < |cuts|;
        assert cuts[0] == 0;
        assert cuts[|cuts| - 1] == |data|;
        assert RSpec.RecordCutColumn(data, delimiter, cuts) by {
          reveal RSpec.RecordCutColumn();
        }
      }
    }
  }

  lemma DropFirstRecordsGivesRelation(
    data: BW.Bytes,
    count: nat,
    delimiter: char
  )
    ensures RSpec.DropFirstRecordsRelation(
              data,
              count,
              delimiter,
              RCore.DropFirstRecords(data, count, delimiter)
            )
  {
    var cuts := RCore.RecordCuts(data, delimiter);
    RecordCutsGiveRelation(data, delimiter);
    var recordCount := |cuts| - 1;
    var drop := if count < recordCount then count else recordCount;
    assert drop < |cuts|;
    RecordCutElementOrEnd(data, delimiter, cuts, drop);
  }

  lemma RecordCutElementOrEnd(
    data: BW.Bytes,
    delimiter: char,
    cuts: seq<nat>,
    i: nat
  )
    requires RSpec.RecordCutColumn(data, delimiter, cuts)
    requires i < |cuts|
    ensures cuts[i] <= |data|
  {
    reveal RSpec.RecordCutColumn();
    if i + 1 < |cuts| {
      RecordCutElement(data, delimiter, cuts, i);
    } else {
      assert cuts[i] == |data|;
    }
  }

  lemma TakeLastRecordsGivesRelation(
    data: BW.Bytes,
    count: nat,
    delimiter: char
  )
    ensures RSpec.TakeLastRecordsRelation(
              data,
              count,
              delimiter,
              RCore.TakeLastRecords(data, count, delimiter)
            )
  {
    var cuts := RCore.RecordCuts(data, delimiter);
    RecordCutsGiveRelation(data, delimiter);
    var recordCount := |cuts| - 1;
    var drop := if recordCount <= count then 0 else recordCount - count;
    assert drop < |cuts|;
    RecordCutElementOrEnd(data, delimiter, cuts, drop);
  }

  lemma RenderDataGivesRelation(cmd: Schema.TailCmd, data: BW.Bytes)
    ensures Spec.RenderDataRelation(cmd, data, Core.RenderData(cmd, data))
  {
    if cmd.selection.unit == Schema.CountBytes {
    } else {
      var delimiter := RCore.RecordDelimiter(cmd.zeroTerminated);
      assert delimiter == RSpec.RecordDelimiter(cmd.zeroTerminated);
      if cmd.selection.fromStart {
        DropFirstRecordsGivesRelation(
          data,
          if cmd.selection.amount == 0 then 0 else cmd.selection.amount - 1,
          delimiter
        );
      } else {
        TakeLastRecordsGivesRelation(data, cmd.selection.amount, delimiter);
      }
    }
  }

  lemma OutputPieceGivesRelation(
    cmd: Schema.TailCmd,
    input: Schema.Input,
    result: BW.Result<BW.Bytes>,
                      printedHeaders: nat
  )
    ensures Spec.OutputFragmentRelation(
              cmd,
              input,
              result,
              printedHeaders,
              Core.OutputPiece(cmd, input, result, printedHeaders)
            )
  {
    match result
    case Ok(data) =>
      if !Core.SuppressZeroTrailingSelection(cmd) {
        RenderDataGivesRelation(cmd, data);
      }
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
    assert forall i: nat |
        i < |Spec.ObservationStdoutFragments(observations + [observation])| ::
        Spec.ObservationStdoutFragments(observations + [observation])[i] ==
        (Spec.ObservationStdoutFragments(observations) +
         [observation.stdoutFragment])[i];
    assert forall i: nat |
        i < |Spec.ObservationStderrFragments(observations + [observation])| ::
        Spec.ObservationStderrFragments(observations + [observation])[i] ==
        (Spec.ObservationStderrFragments(observations) +
         [observation.stderrFragment])[i];
  }

  ghost function CoreObservations(
    cmd: Schema.TailCmd,
    preFs: BW.FileSystem,
    preStdin: BW.Bytes,
    count: nat
  ): seq<Spec.InputObservation>
    requires count <= |cmd.inputs|
    ensures |CoreObservations(cmd, preFs, preStdin, count)| == count
    decreases count
  {
    if count == 0 then
      []
    else
      var prior := CoreObservations(cmd, preFs, preStdin, count - 1);
      var i := count - 1;
      var result := Core.ReadResultCore(cmd, preFs, preStdin, i);
      prior + [
        Spec.InputObservation(
          result,
          Core.OutputPiece(
            cmd,
            cmd.inputs[i],
            result,
            Core.PrefixHeaderCountCore(cmd, preFs, preStdin, i)
          ),
          Core.ErrorPiece(cmd.inputs[i], result),
          Core.HadErrorPiece(cmd.inputs[i], result),
          Core.ResultHasHeader(cmd, result)
        )
      ]
  }

  lemma CoreObservationsFailure(
    cmd: Schema.TailCmd,
    preFs: BW.FileSystem,
    preStdin: BW.Bytes,
    count: nat
  )
    requires count <= |cmd.inputs|
    ensures Core.PrefixHadErrorCore(cmd, preFs, preStdin, count) ==
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
      var failed := Core.HadErrorPiece(
        cmd.inputs[i],
        Core.ReadResultCore(cmd, preFs, preStdin, i)
      );
      assert observations[i].failed == failed;
      if failed {
        assert exists j: nat :: j < |observations| && observations[j].failed;
        assert Core.PrefixHadErrorCore(cmd, preFs, preStdin, count);
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
          assert exists k: nat :: k < |observations| && observations[k].failed;
        }
        assert
          (exists j: nat :: j < |observations| && observations[j].failed) ==
          (exists j: nat :: j < |prior| && prior[j].failed);
      }
      assert Core.PrefixHadErrorCore(cmd, preFs, preStdin, count) ==
             (exists j: nat :: j < |observations| && observations[j].failed);
      assert observations == CoreObservations(cmd, preFs, preStdin, count);
      assert Core.PrefixHadErrorCore(cmd, preFs, preStdin, count) ==
             (exists j: nat ::
                j < |CoreObservations(cmd, preFs, preStdin, count)| &&
                CoreObservations(cmd, preFs, preStdin, count)[j].failed);
    }
  }

  lemma {:isolate_assertions} BuildPrefixWitness(
    cmd: Schema.TailCmd,
    preFs: BW.FileSystem,
    preStdin: BW.Bytes,
    count: nat
  ) returns (
      observations: seq<Spec.InputObservation>,
      headerCounts: seq<nat>,
      stdoutCuts: seq<nat>,
      stderrCuts: seq<nat>
    )
    requires count <= |cmd.inputs|
    ensures observations == CoreObservations(cmd, preFs, preStdin, count)
    ensures |observations| == count
    ensures |headerCounts| == |observations| + 1
    ensures headerCounts[0] == 0
    ensures headerCounts[|headerCounts| - 1] ==
            Core.PrefixHeaderCountCore(cmd, preFs, preStdin, count)
    ensures forall i: nat {:trigger headerCounts[i], headerCounts[i + 1]} |
              i < |observations| ::
              headerCounts[i + 1] ==
              headerCounts[i] + (if observations[i].hasHeader then 1 else 0)
    ensures forall i: nat {:trigger observations[i]} | i < |observations| ::
              Spec.InputObservationRelation(
                cmd,
                preFs,
                preStdin,
                i,
                observations[i],
                headerCounts[i]
              )
    ensures Spec.FragmentsConcatenate(
              Spec.ObservationStdoutFragments(observations),
              Core.PrefixOutputCore(cmd, preFs, preStdin, count),
              stdoutCuts
            )
    ensures Spec.FragmentsConcatenate(
              Spec.ObservationStderrFragments(observations),
              Core.PrefixErrorOutputCore(cmd, preFs, preStdin, count),
              stderrCuts
            )
    decreases count
  {
    if count == 0 {
      observations := [];
      headerCounts := [0];
      stdoutCuts := [0];
      stderrCuts := [0];
      assert Spec.FragmentsConcatenate([], [], [0]);
    } else {
      var priorObservations, priorHeaderCounts, priorStdoutCuts, priorStderrCuts :=
        BuildPrefixWitness(cmd, preFs, preStdin, count - 1);
      var i := count - 1;
      var result := Core.ReadResultCore(cmd, preFs, preStdin, i);
      var stdoutFragment := Core.OutputPiece(
        cmd,
        cmd.inputs[i],
        result,
        Core.PrefixHeaderCountCore(cmd, preFs, preStdin, i)
      );
      var stderrFragment := Core.ErrorPiece(cmd.inputs[i], result);
      var failed := Core.HadErrorPiece(cmd.inputs[i], result);
      var hasHeader := Core.ResultHasHeader(cmd, result);
      var observation := Spec.InputObservation(
        result,
        stdoutFragment,
        stderrFragment,
        failed,
        hasHeader
      );
      observations := priorObservations + [observation];
      headerCounts := priorHeaderCounts + [
        priorHeaderCounts[|priorHeaderCounts| - 1] +
        (if hasHeader then 1 else 0)
      ];
      stdoutCuts := priorStdoutCuts +
      [|Core.PrefixOutputCore(cmd, preFs, preStdin, count)|];
      stderrCuts := priorStderrCuts +
      [|Core.PrefixErrorOutputCore(cmd, preFs, preStdin, count)|];
      ReadResultGivesRelation(cmd, preFs, preStdin, i);
      OutputPieceGivesRelation(
        cmd,
        cmd.inputs[i],
        result,
        Core.PrefixHeaderCountCore(cmd, preFs, preStdin, i)
      );
      assert priorHeaderCounts[|priorHeaderCounts| - 1] ==
             Core.PrefixHeaderCountCore(cmd, preFs, preStdin, i);
      ObservationFragmentsAppend(priorObservations, observation);
      AppendFragment(
        Spec.ObservationStdoutFragments(priorObservations),
        Core.PrefixOutputCore(cmd, preFs, preStdin, i),
        priorStdoutCuts,
        stdoutFragment
      );
      AppendFragment(
        Spec.ObservationStderrFragments(priorObservations),
        Core.PrefixErrorOutputCore(cmd, preFs, preStdin, i),
        priorStderrCuts,
        stderrFragment
      );
      assert forall j: nat {:trigger observations[j]} | j < |observations| ::
          Spec.InputObservationRelation(
            cmd,
            preFs,
            preStdin,
            j,
            observations[j],
            headerCounts[j]
          ) by {
        forall j: nat {:trigger observations[j]} | j < |observations|
          ensures Spec.InputObservationRelation(
                    cmd,
                    preFs,
                    preStdin,
                    j,
                    observations[j],
                    headerCounts[j]
                  )
        {
          if j < |priorObservations| {
            assert observations[j] == priorObservations[j];
            assert headerCounts[j] == priorHeaderCounts[j];
          } else {
            assert j == i;
          }
        }
      }
    }
  }

  lemma CoreSummaryImpliesTrace(
    cmd: Schema.TailCmd,
    preFs: BW.FileSystem,
    preStdin: BW.Bytes
  )
    ensures Spec.InputTraceRelation(
              cmd,
              preFs,
              preStdin,
              Core.PrefixStdinCore(cmd, preStdin, |cmd.inputs|),
              Core.PrefixOutputCore(cmd, preFs, preStdin, |cmd.inputs|),
              Core.PrefixErrorOutputCore(cmd, preFs, preStdin, |cmd.inputs|),
              Core.PrefixHadErrorCore(cmd, preFs, preStdin, |cmd.inputs|)
            )
  {
    var observations, headerCounts, stdoutCuts, stderrCuts :=
      BuildPrefixWitness(cmd, preFs, preStdin, |cmd.inputs|);
    CoreObservationsFailure(cmd, preFs, preStdin, |cmd.inputs|);
    PrefixStdinCharacterization(cmd, preStdin, |cmd.inputs|);
    assert Spec.InputTraceWitnessRelation(
        cmd,
        preFs,
        preStdin,
        Core.PrefixStdinCore(cmd, preStdin, |cmd.inputs|),
        Core.PrefixOutputCore(cmd, preFs, preStdin, |cmd.inputs|),
        Core.PrefixErrorOutputCore(cmd, preFs, preStdin, |cmd.inputs|),
        Core.PrefixHadErrorCore(cmd, preFs, preStdin, |cmd.inputs|),
        observations,
        headerCounts,
        stdoutCuts,
        stderrCuts
      );
  }

  twostate lemma CoreSummaryImpliesSpec(
    raw: Schema.TailCmdRaw,
    io: BenchIO.IO,
    exit: int
  )
    requires Core.CoreSummary(raw, io, exit)
    ensures Spec.Spec(raw, io, exit)
  {
    CommandEq(raw);
    var cmd := Core.Command(raw);
    if cmd.mode == Schema.ModeHelp {
    } else if cmd.mode == Schema.ModeVersion {
    } else if cmd.mode == Schema.ModeInvalidCount {
    } else if Core.SuppressZeroTrailingSelection(cmd) {
    } else {
      CoreSummaryImpliesTrace(cmd, old(io.fs()), old(io.stdin()));
    }
  }
}
