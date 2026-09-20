include "../../core/World.dfy"
include "../../core/IO.dfy"
include "HeadSchema.dfy"
include "HeadRecordCore.dfy"
include "HeadRecordSpec.dfy"
include "HeadCore.dfy"
include "HeadSpec.dfy"

module HeadProof {
  import BenchIO
  import BW = BenchWorld
  import Schema = HeadSchema
  import RCore = HeadRecordCore
  import RSpec = HeadRecordSpec
  import Core = HeadCore
  import Spec = HeadSpec

  lemma InputsFromOperandsEq(operands: seq<string>)
    ensures Core.InputsFromOperands(operands) == Spec.InputsFromOperands(operands)
    decreases |operands|
  {
    if |operands| > 0 {
      InputsFromOperandsEq(operands[1..]);
    }
  }

  lemma CommandEq(raw: Schema.HeadCmdRaw)
    ensures Core.Command(raw) == Spec.Command(raw)
  {
    InputsFromOperandsEq(raw.operands);
  }

  lemma IsStdinInputEq(input: Schema.Input)
    ensures Core.IsStdinInput(input) == Spec.IsStdinInput(input)
  {
  }

  lemma InputNameEq(input: Schema.Input)
    ensures Core.InputName(input) == Spec.InputName(input)
  {
  }

  lemma PrefixStdinRelation(cmd: Schema.HeadCmd, preStdin: BW.Bytes, i: nat)
    requires i <= |cmd.inputs|
    ensures Core.PrefixStdinCore(cmd, preStdin, i) ==
            (if exists j: nat :: j < i && Spec.IsStdinInput(cmd.inputs[j])
             then []
             else preStdin)
    decreases i
  {
    if i > 0 {
      PrefixStdinRelation(cmd, preStdin, i - 1);
      IsStdinInputEq(cmd.inputs[i - 1]);
    }
  }

  lemma ReadResultRelation(
    cmd: Schema.HeadCmd,
    preFs: BW.FileSystem,
    preStdin: BW.Bytes,
    i: nat
  )
    requires i < |cmd.inputs|
    ensures Spec.ReadResultRelation(
              cmd, preFs, preStdin, i,
              Core.ReadResultCore(cmd, preFs, preStdin, i)
            )
  {
    PrefixStdinRelation(cmd, preStdin, i);
  }

  lemma RecordCountRelation(data: BW.Bytes, delimiter: char)
    ensures RSpec.RecordCountRelation(
              data, delimiter, RCore.RecordCount(data, delimiter)
            )
    decreases |data|
  {
    reveal RSpec.RecordCountRelation();
    if |data| > 0 {
      assert data == [data[0]] + data[1..];
      assert multiset(data) == multiset([data[0]]) + multiset(data[1..]);
      if data[0] == delimiter {
        RecordCountRelation(data[1..], delimiter);
      } else if |data| > 1 {
        RecordCountRelation(data[1..], delimiter);
      }
    }
  }

  lemma TakeFirstRecordsProperties(
    data: BW.Bytes,
    count: nat,
    delimiter: char
  )
    ensures |RCore.TakeFirstRecords(data, count, delimiter)| <= |data|
    ensures RCore.TakeFirstRecords(data, count, delimiter) ==
            data[..|RCore.TakeFirstRecords(data, count, delimiter)|]
    ensures RCore.RecordCount(
              RCore.TakeFirstRecords(data, count, delimiter), delimiter
            ) ==
            (if RCore.RecordCount(data, delimiter) <= count
             then RCore.RecordCount(data, delimiter)
             else count)
    ensures |RCore.TakeFirstRecords(data, count, delimiter)| == 0 ||
            |RCore.TakeFirstRecords(data, count, delimiter)| == |data| ||
            RCore.TakeFirstRecords(data, count, delimiter)[
            |RCore.TakeFirstRecords(data, count, delimiter)| - 1
            ] == delimiter
    decreases |data|
  {
    if |data| == 0 || count == 0 {
    } else if data[0] == delimiter {
      TakeFirstRecordsProperties(data[1..], count - 1, delimiter);
      assert data == [data[0]] + data[1..];
    } else {
      TakeFirstRecordsProperties(data[1..], count, delimiter);
      assert data == [data[0]] + data[1..];
    }
  }

  lemma TakeFirstRecordsCut(
    data: BW.Bytes,
    count: nat,
    delimiter: char
  )
    ensures RSpec.RecordCutPointRelation(
              data,
              delimiter,
              |RCore.TakeFirstRecords(data, count, delimiter)|,
              if RCore.RecordCount(data, delimiter) <= count
              then RCore.RecordCount(data, delimiter)
              else count
            )
    ensures RCore.TakeFirstRecords(data, count, delimiter) ==
            data[..|RCore.TakeFirstRecords(data, count, delimiter)|]
  {
    var output := RCore.TakeFirstRecords(data, count, delimiter);
    TakeFirstRecordsProperties(data, count, delimiter);
    RecordCountRelation(output, delimiter);
    reveal RSpec.RecordCutPointRelation();
  }

  lemma RecordSelectionRelation(
    data: BW.Bytes,
    count: nat,
    delimiter: char,
    fromEnd: bool
  )
    ensures RSpec.RecordSelectionRelation(
              data,
              count,
              delimiter,
              fromEnd,
              if fromEnd
              then RCore.TakeAllButLastRecords(data, count, delimiter)
              else RCore.TakeFirstRecords(data, count, delimiter)
            )
  {
    RecordCountRelation(data, delimiter);
    var total := RCore.RecordCount(data, delimiter);
    var keep :=
      if fromEnd
      then if total <= count then 0 else total - count
      else if total <= count then total else count;
    var selectionCount := if fromEnd then keep else count;
    TakeFirstRecordsCut(data, selectionCount, delimiter);
    reveal RSpec.RecordSelectionRelation();
    reveal RSpec.RecordCountRelation();
    var cut := |RCore.TakeFirstRecords(data, selectionCount, delimiter)|;
    assert RSpec.RecordCutPointRelation(
        data,
        delimiter,
        cut,
        keep
      );
    assert (if fromEnd
            then RCore.TakeAllButLastRecords(data, count, delimiter)
            else RCore.TakeFirstRecords(data, count, delimiter)) ==
           RCore.TakeFirstRecords(data, selectionCount, delimiter);
    assert exists totalWitness: nat, keepWitness: nat, cutWitness: nat ::
        RSpec.RecordCountRelation(data, delimiter, totalWitness) &&
        keepWitness ==
        (if fromEnd
         then if totalWitness <= count then 0 else totalWitness - count
         else if totalWitness <= count then totalWitness else count) &&
        RSpec.RecordCutPointRelation(
          data, delimiter, cutWitness, keepWitness
        ) &&
        (if fromEnd
         then RCore.TakeAllButLastRecords(data, count, delimiter)
         else RCore.TakeFirstRecords(data, count, delimiter)) ==
        data[..cutWitness] by {
      assert RSpec.RecordCountRelation(data, delimiter, total);
    }
  }

  lemma DataSelectionRelation(cmd: Schema.HeadCmd, data: BW.Bytes)
    ensures Spec.DataSelectionRelation(cmd, data, Core.RenderData(cmd, data))
  {
    if cmd.selection.unit == Schema.CountBytes {
      reveal Spec.DataSelectionRelation();
      reveal Spec.ByteSelectionRelation();
      var cut :=
        if cmd.selection.fromEnd
        then if |data| <= cmd.selection.amount
             then 0
             else |data| - cmd.selection.amount
        else if |data| <= cmd.selection.amount
          then |data|
          else cmd.selection.amount;
      assert Core.RenderData(cmd, data) == data[..cut];
      assert exists cutWitness: nat ::
          cutWitness == cut &&
          Core.RenderData(cmd, data) == data[..cutWitness];
    } else {
      RecordSelectionRelation(
        data,
        cmd.selection.amount,
        RCore.RecordDelimiter(cmd.zeroTerminated),
        cmd.selection.fromEnd
      );
      reveal Spec.DataSelectionRelation();
    }
  }

  lemma HeaderForInputEq(
    cmd: Schema.HeadCmd,
    input: Schema.Input,
    printedHeaders: int
  )
    ensures Core.HeaderForInput(cmd, input, printedHeaders) ==
            Spec.HeaderForInput(cmd, input, printedHeaders)
  {
    InputNameEq(input);
  }

  ghost function SuccessfulIndicesCore(
    cmd: Schema.HeadCmd,
    preFs: BW.FileSystem,
    preStdin: BW.Bytes,
    count: nat
  ): set<nat>
    requires count <= |cmd.inputs|
  {
    set i: nat |
    i < count &&
    Core.IsSuccessfulRead(
      Core.ReadResultCore(cmd, preFs, preStdin, i)
    )
  }

  lemma PrefixSuccessCountCardinality(
    cmd: Schema.HeadCmd,
    preFs: BW.FileSystem,
    preStdin: BW.Bytes,
    count: nat
  )
    requires count <= |cmd.inputs|
    ensures Core.PrefixSuccessCountCore(cmd, preFs, preStdin, count) ==
            |SuccessfulIndicesCore(cmd, preFs, preStdin, count)|
    decreases count
  {
    if count > 0 {
      PrefixSuccessCountCardinality(
        cmd, preFs, preStdin, count - 1
      );
      var previous := SuccessfulIndicesCore(
        cmd, preFs, preStdin, count - 1
      );
      var currentSuccessful := Core.IsSuccessfulRead(
        Core.ReadResultCore(cmd, preFs, preStdin, count - 1)
      );
      assert SuccessfulIndicesCore(cmd, preFs, preStdin, count) ==
             (if currentSuccessful
              then previous + {count - 1}
              else previous) by {
        assert forall i: nat ::
            (i in SuccessfulIndicesCore(cmd, preFs, preStdin, count)) ==
            (i in (if currentSuccessful
                   then previous + {count - 1}
                   else previous));
      }
      assert count - 1 !in previous;
    }
  }

  lemma InputObservationRelation(
    cmd: Schema.HeadCmd,
    preFs: BW.FileSystem,
    preStdin: BW.Bytes,
    i: nat
  )
    requires i < |cmd.inputs|
    ensures Spec.InputObservationRelation(
              cmd,
              preFs,
              preStdin,
              i,
              Core.ReadResultCore(cmd, preFs, preStdin, i),
              Core.PrefixSuccessCountCore(cmd, preFs, preStdin, i),
              Core.OutputPiece(
                cmd,
                cmd.inputs[i],
                Core.ReadResultCore(cmd, preFs, preStdin, i),
                Core.PrefixSuccessCountCore(cmd, preFs, preStdin, i)
              ),
              Core.ErrorPiece(
                cmd.inputs[i],
                Core.ReadResultCore(cmd, preFs, preStdin, i)
              ),
              Core.IsSuccessfulRead(
                Core.ReadResultCore(cmd, preFs, preStdin, i)
              ),
              Core.HadErrorPiece(
                cmd.inputs[i],
                Core.ReadResultCore(cmd, preFs, preStdin, i)
              )
            )
  {
    ReadResultRelation(cmd, preFs, preStdin, i);
    HeaderForInputEq(
      cmd,
      cmd.inputs[i],
      Core.PrefixSuccessCountCore(cmd, preFs, preStdin, i)
    );
    match Core.ReadResultCore(cmd, preFs, preStdin, i)
    case Ok(data) =>
      DataSelectionRelation(cmd, data);
    case Err(_) =>
  }

  ghost function CoreResults(
    cmd: Schema.HeadCmd,
    preFs: BW.FileSystem,
    preStdin: BW.Bytes,
    count: nat
  ): seq<BW.Result<BW.Bytes>>
    requires count <= |cmd.inputs|
  {
    seq(count, i requires 0 <= i < count =>
      Core.ReadResultCore(cmd, preFs, preStdin, i as nat))
  }

  ghost function CoreOutputFragments(
    cmd: Schema.HeadCmd,
    preFs: BW.FileSystem,
    preStdin: BW.Bytes,
    count: nat
  ): seq<BW.Bytes>
    requires count <= |cmd.inputs|
    ensures |CoreOutputFragments(cmd, preFs, preStdin, count)| == count
    decreases count
  {
    if count == 0 then
      []
    else
      CoreOutputFragments(cmd, preFs, preStdin, count - 1) +
      [Core.OutputPiece(
         cmd,
         cmd.inputs[count - 1],
         Core.ReadResultCore(cmd, preFs, preStdin, count - 1),
         Core.PrefixSuccessCountCore(cmd, preFs, preStdin, count - 1)
       )]
  }

  ghost function CoreErrorFragments(
    cmd: Schema.HeadCmd,
    preFs: BW.FileSystem,
    preStdin: BW.Bytes,
    count: nat
  ): seq<BW.Bytes>
    requires count <= |cmd.inputs|
    ensures |CoreErrorFragments(cmd, preFs, preStdin, count)| == count
    decreases count
  {
    if count == 0 then
      []
    else
      CoreErrorFragments(cmd, preFs, preStdin, count - 1) +
      [Core.ErrorPiece(
         cmd.inputs[count - 1],
         Core.ReadResultCore(cmd, preFs, preStdin, count - 1)
       )]
  }

  ghost function CoreOutputCuts(
    cmd: Schema.HeadCmd,
    preFs: BW.FileSystem,
    preStdin: BW.Bytes,
    count: nat
  ): seq<nat>
    requires count <= |cmd.inputs|
    ensures |CoreOutputCuts(cmd, preFs, preStdin, count)| == count + 1
    decreases count
  {
    if count == 0 then
      [0]
    else
      CoreOutputCuts(cmd, preFs, preStdin, count - 1) +
      [|Core.PrefixOutputCore(cmd, preFs, preStdin, count)|]
  }

  ghost function CoreErrorCuts(
    cmd: Schema.HeadCmd,
    preFs: BW.FileSystem,
    preStdin: BW.Bytes,
    count: nat
  ): seq<nat>
    requires count <= |cmd.inputs|
    ensures |CoreErrorCuts(cmd, preFs, preStdin, count)| == count + 1
    decreases count
  {
    if count == 0 then
      [0]
    else
      CoreErrorCuts(cmd, preFs, preStdin, count - 1) +
      [|Core.PrefixErrorOutputCore(cmd, preFs, preStdin, count)|]
  }

  lemma FragmentsConcatenateSnoc(
    fragments: seq<BW.Bytes>,
    combined: BW.Bytes,
    cuts: seq<nat>,
    piece: BW.Bytes
  )
    requires Spec.FragmentsConcatenate(fragments, combined, cuts)
    ensures Spec.FragmentsConcatenate(
              fragments + [piece],
              combined + piece,
              cuts + [|combined + piece|]
            )
  {
    reveal Spec.FragmentsConcatenate();
    assert forall i: nat {:trigger (cuts + [|combined + piece|])[i]} |
        i < |fragments + [piece]| ::
        (cuts + [|combined + piece|])[i] <=
        (cuts + [|combined + piece|])[i + 1] &&
        (cuts + [|combined + piece|])[i + 1] <= |combined + piece| &&
        (cuts + [|combined + piece|])[i + 1] ==
        (cuts + [|combined + piece|])[i] +
        |(fragments + [piece])[i]| &&
        (combined + piece)[
        (cuts + [|combined + piece|])[i]..
        (cuts + [|combined + piece|])[i + 1]
        ] == (fragments + [piece])[i] by {
      forall i: nat
        {:trigger (cuts + [|combined + piece|])[i]} |
    i < |fragments + [piece]|
        ensures (cuts + [|combined + piece|])[i] <=
                (cuts + [|combined + piece|])[i + 1]
        ensures (cuts + [|combined + piece|])[i + 1] <=
                |combined + piece|
        ensures (cuts + [|combined + piece|])[i + 1] ==
                (cuts + [|combined + piece|])[i] +
                |(fragments + [piece])[i]|
        ensures (combined + piece)[
                (cuts + [|combined + piece|])[i]..
                (cuts + [|combined + piece|])[i + 1]
                ] == (fragments + [piece])[i]
      {
        if i < |fragments| {
          assert combined <= combined + piece;
        } else {
          assert i == |fragments|;
        }
      }
    }
  }

  lemma {:isolate_assertions} OutputFragmentsConcatenateCore(
    cmd: Schema.HeadCmd,
    preFs: BW.FileSystem,
    preStdin: BW.Bytes,
    count: nat
  )
    requires count <= |cmd.inputs|
    ensures Spec.FragmentsConcatenate(
              CoreOutputFragments(cmd, preFs, preStdin, count),
              Core.PrefixOutputCore(cmd, preFs, preStdin, count),
              CoreOutputCuts(cmd, preFs, preStdin, count)
            )
    decreases count
  {
    if count == 0 {
      reveal Spec.FragmentsConcatenate();
    } else {
      var previous := count - 1;
      OutputFragmentsConcatenateCore(
        cmd, preFs, preStdin, previous
      );
      var piece := Core.OutputPiece(
        cmd,
        cmd.inputs[previous],
        Core.ReadResultCore(cmd, preFs, preStdin, previous),
        Core.PrefixSuccessCountCore(cmd, preFs, preStdin, previous)
      );
      Core.PrefixOutputCoreStep(cmd, preFs, preStdin, previous);
      assert CoreOutputFragments(cmd, preFs, preStdin, count) ==
             CoreOutputFragments(cmd, preFs, preStdin, previous) + [piece];
      assert CoreOutputCuts(cmd, preFs, preStdin, count) ==
             CoreOutputCuts(cmd, preFs, preStdin, previous) +
             [|Core.PrefixOutputCore(cmd, preFs, preStdin, count)|];
      FragmentsConcatenateSnoc(
        CoreOutputFragments(cmd, preFs, preStdin, previous),
        Core.PrefixOutputCore(cmd, preFs, preStdin, previous),
        CoreOutputCuts(cmd, preFs, preStdin, previous),
        piece
      );
    }
  }

  lemma {:isolate_assertions} ErrorFragmentsConcatenateCore(
    cmd: Schema.HeadCmd,
    preFs: BW.FileSystem,
    preStdin: BW.Bytes,
    count: nat
  )
    requires count <= |cmd.inputs|
    ensures Spec.FragmentsConcatenate(
              CoreErrorFragments(cmd, preFs, preStdin, count),
              Core.PrefixErrorOutputCore(cmd, preFs, preStdin, count),
              CoreErrorCuts(cmd, preFs, preStdin, count)
            )
    decreases count
  {
    if count == 0 {
      reveal Spec.FragmentsConcatenate();
    } else {
      var previous := count - 1;
      ErrorFragmentsConcatenateCore(
        cmd, preFs, preStdin, previous
      );
      var piece := Core.ErrorPiece(
        cmd.inputs[previous],
        Core.ReadResultCore(cmd, preFs, preStdin, previous)
      );
      Core.PrefixErrorOutputCoreStep(cmd, preFs, preStdin, previous);
      assert CoreErrorFragments(cmd, preFs, preStdin, count) ==
             CoreErrorFragments(cmd, preFs, preStdin, previous) + [piece];
      assert CoreErrorCuts(cmd, preFs, preStdin, count) ==
             CoreErrorCuts(cmd, preFs, preStdin, previous) +
             [|Core.PrefixErrorOutputCore(cmd, preFs, preStdin, count)|];
      FragmentsConcatenateSnoc(
        CoreErrorFragments(cmd, preFs, preStdin, previous),
        Core.PrefixErrorOutputCore(cmd, preFs, preStdin, previous),
        CoreErrorCuts(cmd, preFs, preStdin, previous),
        piece
      );
    }
  }

  lemma FragmentsConcatenateCore(
    cmd: Schema.HeadCmd,
    preFs: BW.FileSystem,
    preStdin: BW.Bytes,
    count: nat
  )
    requires count <= |cmd.inputs|
    ensures Spec.FragmentsConcatenate(
              CoreOutputFragments(cmd, preFs, preStdin, count),
              Core.PrefixOutputCore(cmd, preFs, preStdin, count),
              CoreOutputCuts(cmd, preFs, preStdin, count)
            )
    ensures Spec.FragmentsConcatenate(
              CoreErrorFragments(cmd, preFs, preStdin, count),
              Core.PrefixErrorOutputCore(cmd, preFs, preStdin, count),
              CoreErrorCuts(cmd, preFs, preStdin, count)
            )
  {
    OutputFragmentsConcatenateCore(cmd, preFs, preStdin, count);
    ErrorFragmentsConcatenateCore(cmd, preFs, preStdin, count);
  }

  ghost function CoreSuccessful(
    cmd: Schema.HeadCmd,
    preFs: BW.FileSystem,
    preStdin: BW.Bytes,
    count: nat
  ): seq<bool>
    requires count <= |cmd.inputs|
    ensures |CoreSuccessful(cmd, preFs, preStdin, count)| == count
    decreases count
  {
    if count == 0 then
      []
    else
      CoreSuccessful(cmd, preFs, preStdin, count - 1) +
      [Core.IsSuccessfulRead(
         Core.ReadResultCore(cmd, preFs, preStdin, count - 1)
       )]
  }

  ghost function CoreFailed(
    cmd: Schema.HeadCmd,
    preFs: BW.FileSystem,
    preStdin: BW.Bytes,
    count: nat
  ): seq<bool>
    requires count <= |cmd.inputs|
    ensures |CoreFailed(cmd, preFs, preStdin, count)| == count
    decreases count
  {
    if count == 0 then
      []
    else
      CoreFailed(cmd, preFs, preStdin, count - 1) +
      [Core.HadErrorPiece(
         cmd.inputs[count - 1],
         Core.ReadResultCore(cmd, preFs, preStdin, count - 1)
       )]
  }

  lemma CoreSuccessfulIndex(
    cmd: Schema.HeadCmd,
    preFs: BW.FileSystem,
    preStdin: BW.Bytes,
    count: nat,
    i: nat
  )
    requires count <= |cmd.inputs|
    requires i < count
    ensures CoreSuccessful(cmd, preFs, preStdin, count)[i] ==
            Core.IsSuccessfulRead(
              Core.ReadResultCore(cmd, preFs, preStdin, i)
            )
    decreases count
  {
    if i + 1 < count {
      CoreSuccessfulIndex(cmd, preFs, preStdin, count - 1, i);
    }
  }

  lemma CoreFailedIndex(
    cmd: Schema.HeadCmd,
    preFs: BW.FileSystem,
    preStdin: BW.Bytes,
    count: nat,
    i: nat
  )
    requires count <= |cmd.inputs|
    requires i < count
    ensures CoreFailed(cmd, preFs, preStdin, count)[i] ==
            Core.HadErrorPiece(
              cmd.inputs[i],
              Core.ReadResultCore(cmd, preFs, preStdin, i)
            )
    decreases count
  {
    if i + 1 < count {
      CoreFailedIndex(cmd, preFs, preStdin, count - 1, i);
    }
  }

  lemma CoreOutputFragmentsIndex(
    cmd: Schema.HeadCmd,
    preFs: BW.FileSystem,
    preStdin: BW.Bytes,
    count: nat,
    i: nat
  )
    requires count <= |cmd.inputs|
    requires i < count
    ensures CoreOutputFragments(cmd, preFs, preStdin, count)[i] ==
            Core.OutputPiece(
              cmd,
              cmd.inputs[i],
              Core.ReadResultCore(cmd, preFs, preStdin, i),
              Core.PrefixSuccessCountCore(cmd, preFs, preStdin, i)
            )
    decreases count
  {
    if i + 1 < count {
      CoreOutputFragmentsIndex(
        cmd, preFs, preStdin, count - 1, i
      );
    }
  }

  lemma CoreErrorFragmentsIndex(
    cmd: Schema.HeadCmd,
    preFs: BW.FileSystem,
    preStdin: BW.Bytes,
    count: nat,
    i: nat
  )
    requires count <= |cmd.inputs|
    requires i < count
    ensures CoreErrorFragments(cmd, preFs, preStdin, count)[i] ==
            Core.ErrorPiece(
              cmd.inputs[i],
              Core.ReadResultCore(cmd, preFs, preStdin, i)
            )
    decreases count
  {
    if i + 1 < count {
      CoreErrorFragmentsIndex(
        cmd, preFs, preStdin, count - 1, i
      );
    }
  }

  lemma InputObservationAt(
    cmd: Schema.HeadCmd,
    preFs: BW.FileSystem,
    preStdin: BW.Bytes,
    count: nat,
    i: nat
  )
    requires count <= |cmd.inputs|
    requires i < count
    ensures Spec.InputObservationRelation(
              cmd,
              preFs,
              preStdin,
              i,
              CoreResults(cmd, preFs, preStdin, count)[i],
              |set j: nat |
              j < i && CoreSuccessful(cmd, preFs, preStdin, count)[j]|,
              CoreOutputFragments(cmd, preFs, preStdin, count)[i],
              CoreErrorFragments(cmd, preFs, preStdin, count)[i],
              CoreSuccessful(cmd, preFs, preStdin, count)[i],
              CoreFailed(cmd, preFs, preStdin, count)[i]
            )
  {
    PrefixSuccessCountCardinality(cmd, preFs, preStdin, i);
    assert (set j: nat |
            j < i && CoreSuccessful(cmd, preFs, preStdin, count)[j]) ==
           SuccessfulIndicesCore(cmd, preFs, preStdin, i) by {
      assert forall j: nat ::
          (j in (set k: nat |
                 k < i && CoreSuccessful(cmd, preFs, preStdin, count)[k])) ==
          (j in SuccessfulIndicesCore(cmd, preFs, preStdin, i)) by {
        forall j: nat
          ensures
            (j in (set k: nat |
                   k < i &&
                   CoreSuccessful(cmd, preFs, preStdin, count)[k])) ==
            (j in SuccessfulIndicesCore(cmd, preFs, preStdin, i))
        {
          if j < i {
            CoreSuccessfulIndex(cmd, preFs, preStdin, count, j);
          }
        }
      }
    }
    CoreOutputFragmentsIndex(cmd, preFs, preStdin, count, i);
    CoreErrorFragmentsIndex(cmd, preFs, preStdin, count, i);
    InputObservationRelation(cmd, preFs, preStdin, i);
  }

  lemma AllInputObservations(
    cmd: Schema.HeadCmd,
    preFs: BW.FileSystem,
    preStdin: BW.Bytes,
    count: nat
  )
    requires count <= |cmd.inputs|
    ensures forall i: nat | i < count ::
              Spec.InputObservationRelation(
                cmd,
                preFs,
                preStdin,
                i,
                CoreResults(cmd, preFs, preStdin, count)[i],
                |set j: nat |
                j < i && CoreSuccessful(cmd, preFs, preStdin, count)[j]|,
                CoreOutputFragments(cmd, preFs, preStdin, count)[i],
                CoreErrorFragments(cmd, preFs, preStdin, count)[i],
                CoreSuccessful(cmd, preFs, preStdin, count)[i],
                CoreFailed(cmd, preFs, preStdin, count)[i]
              )
  {
    forall i: nat | i < count
      ensures Spec.InputObservationRelation(
                cmd,
                preFs,
                preStdin,
                i,
                CoreResults(cmd, preFs, preStdin, count)[i],
                |set j: nat |
                j < i && CoreSuccessful(cmd, preFs, preStdin, count)[j]|,
                CoreOutputFragments(cmd, preFs, preStdin, count)[i],
                CoreErrorFragments(cmd, preFs, preStdin, count)[i],
                CoreSuccessful(cmd, preFs, preStdin, count)[i],
                CoreFailed(cmd, preFs, preStdin, count)[i]
              )
    {
      InputObservationAt(cmd, preFs, preStdin, count, i);
    }
  }

  lemma PrefixHadErrorRelation(
    cmd: Schema.HeadCmd,
    preFs: BW.FileSystem,
    preStdin: BW.Bytes,
    count: nat
  )
    requires count <= |cmd.inputs|
    ensures Core.PrefixHadErrorCore(cmd, preFs, preStdin, count) ==
            (exists i: nat ::
               i < count && CoreFailed(cmd, preFs, preStdin, count)[i])
    decreases count
  {
    if count > 0 {
      PrefixHadErrorRelation(cmd, preFs, preStdin, count - 1);
      Core.PrefixHadErrorCoreStep(
        cmd, preFs, preStdin, count - 1
      );
      assert (exists i: nat ::
                i < count && CoreFailed(cmd, preFs, preStdin, count)[i]) ==
             ((exists i: nat
                 {:trigger CoreFailed(cmd, preFs, preStdin, count - 1)[i]} ::
                 i < count - 1 &&
                 CoreFailed(cmd, preFs, preStdin, count - 1)[i]) ||
              CoreFailed(cmd, preFs, preStdin, count)[count - 1]) by {
        if exists i: nat ::
            i < count && CoreFailed(cmd, preFs, preStdin, count)[i] {
          var i: nat :|
            i < count && CoreFailed(cmd, preFs, preStdin, count)[i];
          if i < count - 1 {
            CoreFailedIndex(cmd, preFs, preStdin, count, i);
            CoreFailedIndex(cmd, preFs, preStdin, count - 1, i);
          } else {
            assert i == count - 1;
          }
        } else if exists i: nat
            {:trigger CoreFailed(cmd, preFs, preStdin, count - 1)[i]} ::
            i < count - 1 &&
            CoreFailed(cmd, preFs, preStdin, count - 1)[i] {
          var i: nat :|
            i < count - 1 &&
            CoreFailed(cmd, preFs, preStdin, count - 1)[i];
          CoreFailedIndex(cmd, preFs, preStdin, count, i);
          CoreFailedIndex(cmd, preFs, preStdin, count - 1, i);
        }
      }
    }
  }

  lemma InputTraceWitnessImpliesRelation(
    cmd: Schema.HeadCmd,
    preFs: BW.FileSystem,
    preStdin: BW.Bytes,
    postStdin: BW.Bytes,
    output: BW.Bytes,
    errorOutput: BW.Bytes,
    hadError: bool,
    results: seq<BW.Result<BW.Bytes>>,
    outputFragments: seq<BW.Bytes>,
    errorFragments: seq<BW.Bytes>,
    successful: seq<bool>,
    failed: seq<bool>,
    outputCuts: seq<nat>,
    errorCuts: seq<nat>
  )
    requires Spec.InputTraceWitnessRelation(
               cmd, preFs, preStdin, postStdin, output, errorOutput, hadError,
               results, outputFragments, errorFragments, successful, failed,
               outputCuts, errorCuts
             )
    ensures Spec.InputTraceRelation(
              cmd, preFs, preStdin, postStdin, output, errorOutput, hadError
            )
  {
    reveal Spec.InputTraceRelation();
  }

  lemma {:isolate_assertions} CoreInputTraceWitnessRelation(
    cmd: Schema.HeadCmd,
    preFs: BW.FileSystem,
    preStdin: BW.Bytes
  )
    ensures Spec.InputTraceWitnessRelation(
              cmd,
              preFs,
              preStdin,
              Core.PrefixStdinCore(cmd, preStdin, |cmd.inputs|),
              Core.PrefixOutputCore(cmd, preFs, preStdin, |cmd.inputs|),
              Core.PrefixErrorOutputCore(cmd, preFs, preStdin, |cmd.inputs|),
              Core.PrefixHadErrorCore(cmd, preFs, preStdin, |cmd.inputs|),
              CoreResults(cmd, preFs, preStdin, |cmd.inputs|),
              CoreOutputFragments(cmd, preFs, preStdin, |cmd.inputs|),
              CoreErrorFragments(cmd, preFs, preStdin, |cmd.inputs|),
              CoreSuccessful(cmd, preFs, preStdin, |cmd.inputs|),
              CoreFailed(cmd, preFs, preStdin, |cmd.inputs|),
              CoreOutputCuts(cmd, preFs, preStdin, |cmd.inputs|),
              CoreErrorCuts(cmd, preFs, preStdin, |cmd.inputs|)
            )
  {
    var count := |cmd.inputs|;
    AllInputObservations(cmd, preFs, preStdin, count);
    FragmentsConcatenateCore(cmd, preFs, preStdin, count);
    PrefixStdinRelation(cmd, preStdin, count);
    PrefixHadErrorRelation(cmd, preFs, preStdin, count);
    reveal Spec.InputTraceWitnessRelation();
  }

  lemma {:isolate_assertions} InputTraceRelation(
    cmd: Schema.HeadCmd,
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
    var count := |cmd.inputs|;
    CoreInputTraceWitnessRelation(cmd, preFs, preStdin);
    InputTraceWitnessImpliesRelation(
      cmd,
      preFs,
      preStdin,
      Core.PrefixStdinCore(cmd, preStdin, count),
      Core.PrefixOutputCore(cmd, preFs, preStdin, count),
      Core.PrefixErrorOutputCore(cmd, preFs, preStdin, count),
      Core.PrefixHadErrorCore(cmd, preFs, preStdin, count),
      CoreResults(cmd, preFs, preStdin, count),
      CoreOutputFragments(cmd, preFs, preStdin, count),
      CoreErrorFragments(cmd, preFs, preStdin, count),
      CoreSuccessful(cmd, preFs, preStdin, count),
      CoreFailed(cmd, preFs, preStdin, count),
      CoreOutputCuts(cmd, preFs, preStdin, count),
      CoreErrorCuts(cmd, preFs, preStdin, count)
    );
  }

  twostate lemma {:isolate_assertions} CoreSummaryImpliesSpec(
    raw: Schema.HeadCmdRaw,
    io: BenchIO.IO,
    exit: int
  )
    requires Core.CoreSummary(raw, io, exit)
    ensures Spec.Spec(raw, io, exit)
  {
    CommandEq(raw);
    var cmd := Core.Command(raw);
    if cmd.mode == Schema.ModeRun {
      InputTraceRelation(cmd, old(io.fs()), old(io.stdin()));
    }
  }
}
