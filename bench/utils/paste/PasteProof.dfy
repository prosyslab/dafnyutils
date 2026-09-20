include "../../core/World.dfy"
include "PasteSchema.dfy"
include "PasteCore.dfy"
include "PasteSpec.dfy"

module PasteProof {
  import BenchIO
  import Utf8 = Utf8Semantics
  import BW = BenchWorld
  import Schema = PasteSchema
  import Core = PasteCore
  import Spec = PasteSpec

  function ToSpecEntry(entry: Core.Entry): Spec.Entry
  {
    Spec.Entry(entry.lines, entry.readOk)
  }

  function ToSpecEntries(entries: seq<Core.Entry>): seq<Spec.Entry>
    ensures |ToSpecEntries(entries)| == |entries|
    decreases |entries|
  {
    if |entries| == 0 then
      []
    else
      [ToSpecEntry(entries[0])] + ToSpecEntries(entries[1..])
  }

  function ToSpecDelimPlan(plan: Core.DelimPlan): Spec.DelimPlan
  {
    match plan
    case DelimsOk(delims) => Spec.DelimsOk(delims)
    case DelimsErr(stderr) => Spec.DelimsErr(stderr)
  }

  ghost function ShiftCuts(cuts: seq<nat>, offset: nat): seq<nat>
  {
    seq(|cuts|, i requires 0 <= i < |cuts| => cuts[i] + offset)
  }

  ghost function PrefixStdinPositions(
    inputs: seq<Schema.Input>,
    i: nat
  ): seq<nat>
    requires i <= |inputs|
    ensures |PrefixStdinPositions(inputs, i)| <= i
    decreases i
  {
    if i == 0 then
      []
    else
      var previous := PrefixStdinPositions(inputs, i - 1);
      if inputs[i - 1] == Schema.Stdin
      then previous + [i - 1]
      else previous
  }

  ghost function ObservationAt(
    cmd: Schema.PasteCmd,
    preFs: BW.FileSystem,
    preStdin: BW.Bytes,
    i: nat
  ): Spec.InputObservation
    requires i < |cmd.inputs|
  {
    var result := Core.ReadResultCore(cmd, preFs, preStdin, i);
    Spec.InputObservation(
      result,
      ToSpecEntry(Core.EntryForRead(
                    result, Core.RecordDelimiter(cmd.zeroTerminated))),
      Core.ErrorPiece(cmd.inputs[i], result),
      Core.HadErrorPiece(cmd.inputs[i], result),
      Core.HadBlockingErrorPiece(cmd.inputs[i], result))
  }

  ghost function Observations(
    cmd: Schema.PasteCmd,
    preFs: BW.FileSystem,
    preStdin: BW.Bytes
  ): seq<Spec.InputObservation>
  {
    seq(
    |cmd.inputs|,
    i requires 0 <= i < |cmd.inputs| =>
      ObservationAt(cmd, preFs, preStdin, i))
  }

  lemma ToSpecEntriesConcat(left: seq<Core.Entry>, right: seq<Core.Entry>)
    ensures ToSpecEntries(left + right) ==
            ToSpecEntries(left) + ToSpecEntries(right)
    decreases |left|
  {
    if |left| == 0 {
      assert left + right == right;
    } else {
      assert (left + right)[0] == left[0];
      assert (left + right)[1..] == left[1..] + right;
      ToSpecEntriesConcat(left[1..], right);
      assert ToSpecEntries(left + right) ==
             [ToSpecEntry(left[0])] +
             ToSpecEntries(left[1..] + right);
      assert ToSpecEntries(left) ==
             [ToSpecEntry(left[0])] + ToSpecEntries(left[1..]);
    }
  }

  lemma ToSpecEntriesIndex(entries: seq<Core.Entry>, i: nat)
    requires i < |entries|
    ensures ToSpecEntries(entries)[i] == ToSpecEntry(entries[i])
    decreases i
  {
    if i > 0 {
      ToSpecEntriesIndex(entries[1..], i - 1);
    }
  }

  lemma RecordDelimiterEq(zeroTerminated: bool)
    ensures Core.RecordDelimiter(zeroTerminated) ==
            Spec.RecordDelimiter(zeroTerminated)
  {
  }

  lemma SliceAfterPrefix<T>(
    head: seq<T>,
    tail: seq<T>,
    start: nat,
    end: nat
  )
    requires start <= end <= |tail|
    ensures (head + tail)[|head| + start..|head| + end] ==
            tail[start..end]
  {
  }

  lemma PrependFragment<T>(
    head: seq<T>,
    tailFragments: seq<seq<T>>,
    tail: seq<T>,
    tailCuts: seq<nat>
  )
    requires Spec.FragmentsConcatenate(
               tailFragments, tail, tailCuts)
    ensures Spec.FragmentsConcatenate(
              [head] + tailFragments,
              head + tail,
              [0] + ShiftCuts(tailCuts, |head|))
  {
    reveal Spec.FragmentsConcatenate();
    forall i: nat {:trigger ([0] + ShiftCuts(
      tailCuts, |head|))[i]} | i < |[head] + tailFragments|
      ensures ([0] + ShiftCuts(tailCuts, |head|))[i] <=
              ([0] + ShiftCuts(tailCuts, |head|))[i + 1] <=
              |head + tail| &&
              ([0] + ShiftCuts(tailCuts, |head|))[i + 1] ==
              ([0] + ShiftCuts(tailCuts, |head|))[i] +
              |([head] + tailFragments)[i]| &&
              (head + tail)[
              ([0] + ShiftCuts(tailCuts, |head|))[i]..
              ([0] + ShiftCuts(tailCuts, |head|))[i + 1]
              ] == ([head] + tailFragments)[i]
    {
      if i > 0 {
        SliceAfterPrefix(
          head, tail, tailCuts[i - 1], tailCuts[i]);
      }
    }
  }

  lemma ReadLineShape(data: BW.Bytes, recordDelimiter: BW.RawByte)
    ensures
      match Core.ReadLine(data, recordDelimiter)
      case NoLine => data == []
      case SomeLine(line, rest) =>
        (forall j: nat :: j < |line| ==> line[j] != recordDelimiter) &&
        (data == line + [recordDelimiter] + rest ||
         (data == line && rest == []))
    decreases |data|
  {
    if |data| > 0 && data[0] != recordDelimiter {
      ReadLineShape(data[1..], recordDelimiter);
      match Core.ReadLine(data[1..], recordDelimiter)
      case NoLine =>
      case SomeLine(line, rest) =>
        assert forall j: nat :: j < |[data[0]] + line| ==>
                                  ([data[0]] + line)[j] != recordDelimiter by {
          forall j: nat | j < |[data[0]] + line|
            ensures ([data[0]] + line)[j] != recordDelimiter
          {
          }
        }
    }
  }

  lemma BuildLinePartition(
    data: BW.Bytes,
    recordDelimiter: BW.RawByte
  ) returns (
      terminated: seq<bool>,
      fragments: seq<BW.Bytes>,
      cuts: seq<nat>
    )
    ensures Spec.LinePartitionRelation(
              data,
              recordDelimiter,
              Core.Lines(data, recordDelimiter),
              terminated,
              fragments,
              cuts)
    decreases |data|
  {
    ReadLineShape(data, recordDelimiter);
    match Core.ReadLine(data, recordDelimiter)
    case NoLine =>
      terminated := [];
      fragments := [];
      cuts := [0];
      reveal Spec.LinePartitionRelation();
             reveal Spec.FragmentsConcatenate();
    case SomeLine(line, rest) =>
      if data == line + [recordDelimiter] + rest {
        var tailTerminated, tailFragments, tailCuts :=
          BuildLinePartition(rest, recordDelimiter);
        var head := line + [recordDelimiter];
        terminated := [true] + tailTerminated;
        fragments := [head] + tailFragments;
        cuts := [0] + ShiftCuts(tailCuts, |head|);
        PrependFragment(head, tailFragments, rest, tailCuts);
        reveal Spec.LinePartitionRelation();
        assert Core.Lines(data, recordDelimiter) ==
               [line] + Core.Lines(rest, recordDelimiter);
        assert forall i: nat :: i < |Core.Lines(data, recordDelimiter)| ==>
                                  |fragments[i]| > 0 &&
                                  fragments[i] ==
                                  Core.Lines(data, recordDelimiter)[i] +
                                  (if terminated[i] then [recordDelimiter] else []) &&
                                  (forall j: nat ::
                                     j < |Core.Lines(data, recordDelimiter)[i]| ==>
                                       Core.Lines(data, recordDelimiter)[i][j] !=
                                       recordDelimiter) &&
                                  (i + 1 < |Core.Lines(data, recordDelimiter)| ==>
                                     terminated[i]) by {
          forall i: nat | i < |Core.Lines(data, recordDelimiter)|
            ensures |fragments[i]| > 0 &&
                    fragments[i] ==
                    Core.Lines(data, recordDelimiter)[i] +
                    (if terminated[i] then [recordDelimiter] else []) &&
                    (forall j: nat ::
                       j < |Core.Lines(data, recordDelimiter)[i]| ==>
                         Core.Lines(data, recordDelimiter)[i][j] !=
                         recordDelimiter) &&
                    (i + 1 < |Core.Lines(data, recordDelimiter)| ==>
                       terminated[i])
          {
          }
        }
      } else {
        assert data == line && rest == [];
        terminated := [false];
        fragments := [line];
        cuts := [0, |line|];
        reveal Spec.LinePartitionRelation();
        reveal Spec.FragmentsConcatenate();
      }
  }

  lemma EntryRefines(
    result: BW.Result<BW.Bytes>,
                      recordDelimiter: BW.RawByte
  )
    ensures Spec.EntryRelation(
              result,
              recordDelimiter,
              ToSpecEntry(Core.EntryForRead(result, recordDelimiter)))
  {
    match result
    case Ok(data) =>
      var terminated, fragments, cuts :=
        BuildLinePartition(data, recordDelimiter);
      reveal Spec.EntryRelation();
    case Err(_) =>
      reveal Spec.EntryRelation();
  }

  lemma PrefixStdinCharacterization(
    cmd: Schema.PasteCmd,
    preStdin: BW.Bytes,
    i: nat
  )
    requires i <= |cmd.inputs|
    ensures Core.PrefixStdinCore(cmd, preStdin, i) ==
            if exists j: nat ::
                 j < i && cmd.inputs[j] == Schema.Stdin
            then []
            else preStdin
    decreases i
  {
    if i > 0 {
      PrefixStdinCharacterization(cmd, preStdin, i - 1);
    }
  }

  lemma ReadResultRefines(
    cmd: Schema.PasteCmd,
    preFs: BW.FileSystem,
    preStdin: BW.Bytes,
    i: nat
  )
    requires i < |cmd.inputs|
    ensures Spec.ReadResultRelation(
              cmd, preFs, preStdin, i,
              Core.ReadResultCore(cmd, preFs, preStdin, i))
  {
    PrefixStdinCharacterization(cmd, preStdin, i);
    reveal Spec.ReadResultRelation();
  }

  lemma ObservationRefines(
    cmd: Schema.PasteCmd,
    preFs: BW.FileSystem,
    preStdin: BW.Bytes,
    i: nat
  )
    requires i < |cmd.inputs|
    ensures Spec.InputObservationRelation(
              cmd, preFs, preStdin, i,
              ObservationAt(cmd, preFs, preStdin, i))
  {
    var result := Core.ReadResultCore(cmd, preFs, preStdin, i);
    ReadResultRefines(cmd, preFs, preStdin, i);
    RecordDelimiterEq(cmd.zeroTerminated);
    EntryRefines(result, Core.RecordDelimiter(cmd.zeroTerminated));
    reveal Spec.InputObservationRelation();
    match cmd.inputs[i]
    case Stdin =>
    case File(_) =>
      match result
      case Ok(_) =>
      case Err(_) =>
  }

  lemma PrefixEntriesIndex(
    cmd: Schema.PasteCmd,
    preFs: BW.FileSystem,
    preStdin: BW.Bytes,
    i: nat,
    j: nat
  )
    requires j < i <= |cmd.inputs|
    ensures Core.PrefixEntriesCore(cmd, preFs, preStdin, i)[j] ==
            Core.EntryForRead(
              Core.ReadResultCore(cmd, preFs, preStdin, j),
              Core.RecordDelimiter(cmd.zeroTerminated))
    decreases i
  {
    if j + 1 < i {
      PrefixEntriesIndex(cmd, preFs, preStdin, i - 1, j);
    }
  }

  lemma ObservationEntriesEq(
    cmd: Schema.PasteCmd,
    preFs: BW.FileSystem,
    preStdin: BW.Bytes
  )
    ensures Spec.ObservationEntries(
              Observations(cmd, preFs, preStdin)) ==
            ToSpecEntries(Core.EntriesCore(cmd, preFs, preStdin))
  {
    var observations := Observations(cmd, preFs, preStdin);
    var entries := Core.EntriesCore(cmd, preFs, preStdin);
    assert |observations| == |entries| == |cmd.inputs|;
    assert forall i: nat :: i < |observations| ==>
                              Spec.ObservationEntries(observations)[i] ==
                              ToSpecEntries(entries)[i] by {
      forall i: nat | i < |observations|
        ensures Spec.ObservationEntries(observations)[i] ==
                ToSpecEntries(entries)[i]
      {
        PrefixEntriesIndex(
          cmd, preFs, preStdin, |cmd.inputs|, i);
        ToSpecEntriesIndex(entries, i);
      }
    }
  }

  lemma PrefixPositionsLength(
    inputs: seq<Schema.Input>,
    i: nat
  )
    requires i <= |inputs|
    ensures |PrefixStdinPositions(inputs, i)| ==
            Core.CountStdinPrefix(inputs, i)
    decreases i
  {
    if i > 0 {
      PrefixPositionsLength(inputs, i - 1);
    }
  }

  lemma PrefixPositionsIndex(
    inputs: seq<Schema.Input>,
    i: nat,
    k: nat
  )
    requires i <= |inputs|
    requires k < |PrefixStdinPositions(inputs, i)|
    ensures PrefixStdinPositions(inputs, i)[k] < i
    ensures inputs[PrefixStdinPositions(inputs, i)[k]] ==
            Schema.Stdin
    ensures k > 0 ==>
              PrefixStdinPositions(inputs, i)[k - 1] <
              PrefixStdinPositions(inputs, i)[k]
    decreases i
  {
    if i > 0 {
      var previous := PrefixStdinPositions(inputs, i - 1);
      if inputs[i - 1] == Schema.Stdin {
        if k < |previous| {
          PrefixPositionsIndex(inputs, i - 1, k);
        } else {
          assert k == |previous|;
          if k > 0 {
            PrefixPositionsIndex(inputs, i - 1, k - 1);
          }
        }
      } else {
        PrefixPositionsIndex(inputs, i - 1, k);
      }
    }
  }

  lemma PrefixPositionsComplete(
    inputs: seq<Schema.Input>,
    i: nat,
    j: nat
  ) returns (k: nat)
    requires j < i <= |inputs|
    requires inputs[j] == Schema.Stdin
    ensures k < |PrefixStdinPositions(inputs, i)|
    ensures PrefixStdinPositions(inputs, i)[k] == j
    decreases i
  {
    if j + 1 == i {
      k := |PrefixStdinPositions(inputs, i - 1)|;
      assert PrefixStdinPositions(inputs, i)[k] == j;
    } else {
      k := PrefixPositionsComplete(inputs, i - 1, j);
      assert k < |PrefixStdinPositions(inputs, i - 1)|;
      assert k < |PrefixStdinPositions(inputs, i)|;
      assert PrefixStdinPositions(inputs, i)[k] == j;
    }
  }

  lemma StdinPositionsRefines(inputs: seq<Schema.Input>)
    ensures Spec.StdinPositionsRelation(
              inputs, PrefixStdinPositions(inputs, |inputs|))
  {
    var positions := PrefixStdinPositions(inputs, |inputs|);
    reveal Spec.StdinPositionsRelation();
    assert forall k: nat :: k < |positions| ==>
                              positions[k] < |inputs| &&
                              inputs[positions[k]] == Schema.Stdin &&
                              (k > 0 ==> positions[k - 1] < positions[k]) by {
      forall k: nat | k < |positions|
        ensures positions[k] < |inputs| &&
                inputs[positions[k]] == Schema.Stdin &&
                (k > 0 ==> positions[k - 1] < positions[k])
      {
        PrefixPositionsIndex(inputs, |inputs|, k);
      }
    }
    assert forall i: nat :: i < |inputs| ==>
                              inputs[i] == Schema.Stdin ==>
                                exists k: nat :: k < |positions| && positions[k] == i by {
      forall i: nat | i < |inputs|
        ensures inputs[i] == Schema.Stdin ==>
                  exists k: nat :: k < |positions| && positions[k] == i
      {
        if inputs[i] == Schema.Stdin {
          var k := PrefixPositionsComplete(
            inputs, |inputs|, i);
          assert exists rank: nat ::
              rank < |positions| && positions[rank] == i by {
            ghost var rank := k;
          }
        }
      }
    }
  }

  lemma PrefixPositionsExtendToFull(
    inputs: seq<Schema.Input>,
    i: nat
  )
    requires i < |inputs|
    requires inputs[i] == Schema.Stdin
    ensures |PrefixStdinPositions(inputs, i)| <
            |PrefixStdinPositions(inputs, |inputs|)|
    ensures PrefixStdinPositions(inputs, |inputs|)[
            |PrefixStdinPositions(inputs, i)|] == i
    decreases |inputs| - i
  {
    var rank := |PrefixStdinPositions(inputs, i)|;
    assert PrefixStdinPositions(inputs, i + 1)[rank] == i;
    PositionPersists(inputs, i + 1, |inputs|, rank);
  }

  lemma PositionPersists(
    inputs: seq<Schema.Input>,
    start: nat,
    end: nat,
    k: nat
  )
    requires start <= end <= |inputs|
    requires k < |PrefixStdinPositions(inputs, start)|
    ensures k < |PrefixStdinPositions(inputs, end)|
    ensures PrefixStdinPositions(inputs, end)[k] ==
            PrefixStdinPositions(inputs, start)[k]
    decreases end
  {
    if start < end {
      PositionPersists(inputs, start, end - 1, k);
    }
  }

  lemma CountStdinInputsEqPositions(inputs: seq<Schema.Input>)
    ensures Core.CountStdinInputs(inputs) ==
            |PrefixStdinPositions(inputs, |inputs|)|
    decreases |inputs|
  {
    PrefixPositionsLength(inputs, |inputs|);
  }

  lemma SelectedLinesRefines(
    lines: seq<BW.Bytes>,
    stdinIndex: nat,
    stdinCount: nat
  )
    requires stdinCount > 0
    ensures Spec.SelectedLinesRelation(
              lines,
              stdinIndex,
              stdinCount,
              Core.SelectStdinLines(lines, stdinIndex, stdinCount))
    decreases if stdinIndex <= |lines| then |lines| - stdinIndex else 0
  {
    if stdinIndex < |lines| {
      SelectedLinesRefines(
        lines, stdinIndex + stdinCount, stdinCount);
    }
    reveal Spec.SelectedLinesRelation();
  }

  lemma ParallelEntryAt(
    inputs: seq<Schema.Input>,
    entries: seq<Core.Entry>,
    stdinLines: seq<BW.Bytes>,
    stdinCount: nat,
    start: nat,
    j: nat
  )
    requires |entries| == |inputs|
    requires start <= j < |inputs|
    ensures Core.ParallelEntriesFrom(
              inputs, entries, stdinLines, stdinCount, start)[j - start] ==
            match inputs[j]
            case Stdin =>
              Core.Entry(
                Core.SelectStdinLines(
                  stdinLines,
                  Core.CountStdinPrefix(inputs, j),
                  stdinCount),
                true)
            case File(_) => entries[j]
    decreases j - start
  {
    assert |Core.ParallelEntriesFrom(
        inputs, entries, stdinLines, stdinCount, start)| ==
           |inputs| - start;
    if start < j {
      ParallelEntryAt(
        inputs, entries, stdinLines, stdinCount, start + 1, j);
    }
  }

  lemma {:isolate_assertions} EntriesForOutputRefines(
    cmd: Schema.PasteCmd,
    preStdin: BW.Bytes,
    rawEntries: seq<Core.Entry>
  )
    requires |rawEntries| == |cmd.inputs|
    ensures Spec.EntriesForOutputRelation(
              cmd,
              preStdin,
              ToSpecEntries(rawEntries),
              ToSpecEntries(Core.EntriesForOutputFromEntries(
                              cmd,
                              rawEntries,
                              if Spec.HasStdinInput(cmd.inputs) then preStdin else [])))
  {
    if cmd.serial {
      reveal Spec.EntriesForOutputRelation();
      assert Spec.EntriesForOutputRelation(
          cmd,
          preStdin,
          ToSpecEntries(rawEntries),
          ToSpecEntries(Core.EntriesForOutputFromEntries(
                          cmd,
                          rawEntries,
                          if Spec.HasStdinInput(cmd.inputs) then preStdin else [])));
    } else {
      var positions :=
        PrefixStdinPositions(cmd.inputs, |cmd.inputs|);
      StdinPositionsRefines(cmd.inputs);
      PrefixPositionsLength(cmd.inputs, |cmd.inputs|);
      CountStdinInputsEqPositions(cmd.inputs);
      var stdinData :=
        if Spec.HasStdinInput(cmd.inputs) then preStdin else [];
      var recordDelimiter := Core.RecordDelimiter(cmd.zeroTerminated);
      RecordDelimiterEq(cmd.zeroTerminated);
      var terminated, fragments, cuts :=
        BuildLinePartition(stdinData, recordDelimiter);
      var stdinLines := Core.Lines(stdinData, recordDelimiter);
      var outputEntries := Core.EntriesForOutputFromEntries(
        cmd, rawEntries, stdinData);
      assert |outputEntries| == |cmd.inputs|;
      assert |ToSpecEntries(outputEntries)| == |cmd.inputs|;
      assert |ToSpecEntries(rawEntries)| == |cmd.inputs|;
      reveal Spec.EntriesForOutputRelation();
      assert forall i: nat :: i < |cmd.inputs| ==>
                                match cmd.inputs[i]
                                case File(_) =>
                                  ToSpecEntries(outputEntries)[i] ==
                                  ToSpecEntries(rawEntries)[i]
                                case Stdin =>
                                  exists rank: nat, selected: seq<BW.Bytes> ::
                                    rank < |positions| &&
                                    positions[rank] == i &&
                                    Spec.SelectedLinesRelation(
                                      stdinLines, rank, |positions|, selected) &&
                                    ToSpecEntries(outputEntries)[i] ==
                                    Spec.Entry(selected, true) by {
        forall i: nat | i < |cmd.inputs|
          ensures
            match cmd.inputs[i]
            case File(_) =>
              ToSpecEntries(outputEntries)[i] ==
              ToSpecEntries(rawEntries)[i]
            case Stdin =>
              exists rank: nat, selected: seq<BW.Bytes> ::
                rank < |positions| &&
                positions[rank] == i &&
                Spec.SelectedLinesRelation(
                  stdinLines, rank, |positions|, selected) &&
                ToSpecEntries(outputEntries)[i] ==
                Spec.Entry(selected, true)
        {
          ParallelEntryAt(
            cmd.inputs,
            rawEntries,
            stdinLines,
            Core.CountStdinInputs(cmd.inputs),
            0,
            i);
          ToSpecEntriesIndex(outputEntries, i);
          match cmd.inputs[i]
          case File(_) =>
            ToSpecEntriesIndex(rawEntries, i);
          case Stdin =>
            var rank := Core.CountStdinPrefix(cmd.inputs, i);
            PrefixPositionsLength(cmd.inputs, i);
            PrefixPositionsExtendToFull(cmd.inputs, i);
      assert rank < |positions|;
      assert positions[rank] == i;
      SelectedLinesRefines(stdinLines, rank, |positions|);
      ghost var selected :=
        Core.SelectStdinLines(stdinLines, rank, |positions|);
        }
      }
      ghost var trace := Spec.EntriesForOutputWitness(
        positions, stdinLines, terminated, fragments, cuts);
      assert Spec.ParallelEntriesForOutputRelation(
          cmd,
          preStdin,
          ToSpecEntries(rawEntries),
          ToSpecEntries(outputEntries),
          trace) by {
        reveal Spec.ParallelEntriesForOutputRelation();
      }
      assert Spec.EntriesForOutputRelation(
          cmd,
          preStdin,
          ToSpecEntries(rawEntries),
          ToSpecEntries(outputEntries)) by {
        reveal Spec.EntriesForOutputRelation();
        assert exists witnessValue: Spec.EntriesForOutputWitness ::
            Spec.ParallelEntriesForOutputRelation(
              cmd,
              preStdin,
              ToSpecEntries(rawEntries),
              ToSpecEntries(outputEntries),
              witnessValue) by {
          ghost var witnessValue := trace;
        }
      }
    }
  }

  lemma PrefixHasStdinEq(
    inputs: seq<Schema.Input>,
    i: nat
  )
    requires i <= |inputs|
    ensures Core.PrefixHadStdinCore(inputs, i) ==
            (exists j: nat :: j < i && inputs[j] == Schema.Stdin)
    decreases i
  {
    if i > 0 {
      PrefixHasStdinEq(inputs, i - 1);
    }
  }

  lemma HasStdinEq(inputs: seq<Schema.Input>)
    ensures Core.PrefixHadStdinCore(inputs, |inputs|) ==
            Spec.HasStdinInput(inputs)
  {
    PrefixHasStdinEq(inputs, |inputs|);
    reveal Spec.HasStdinInput();
  }

  lemma VisibleErrorsRefine(
    cmd: Schema.PasteCmd,
    preFs: BW.FileSystem,
    preStdin: BW.Bytes,
    i: nat
  ) returns (assembly: Spec.VisibleErrorAssembly)
    requires i <= |cmd.inputs|
    ensures Spec.VisibleErrorPrefixRelation(
              cmd.serial,
              Observations(cmd, preFs, preStdin),
              i,
              Core.PrefixVisibleErrorOutputCore(
                cmd, preFs, preStdin, i),
              assembly)
    decreases i
  {
    if i == 0 {
      assembly := Spec.VisibleErrorsDone;
    } else {
      var rest :=
        VisibleErrorsRefine(cmd, preFs, preStdin, i - 1);
      PrefixHadBlockingRefines(cmd, preFs, preStdin, i - 1);
      assembly := Spec.VisibleErrorStep(
        Core.PrefixVisibleErrorOutputCore(
          cmd, preFs, preStdin, i - 1),
        rest);
    }
  }

  lemma PrefixHadErrorRefines(
    cmd: Schema.PasteCmd,
    preFs: BW.FileSystem,
    preStdin: BW.Bytes,
    i: nat
  )
    requires i <= |cmd.inputs|
    ensures Core.PrefixHadErrorCore(cmd, preFs, preStdin, i) ==
            (exists j: nat ::
               j < i &&
               Observations(cmd, preFs, preStdin)[j].failed)
    decreases i
  {
    if i > 0 {
      PrefixHadErrorRefines(cmd, preFs, preStdin, i - 1);
      assert Observations(cmd, preFs, preStdin)[i - 1].failed ==
             Core.HadErrorPiece(
               cmd.inputs[i - 1],
               Core.ReadResultCore(cmd, preFs, preStdin, i - 1));
      assert (exists j: nat ::
                j < i &&
                Observations(cmd, preFs, preStdin)[j].failed) <==>
             ((exists j: nat ::
                 j < i - 1 &&
                 Observations(cmd, preFs, preStdin)[j].failed) ||
              Observations(cmd, preFs, preStdin)[i - 1].failed) by {
      }
    }
  }

  lemma PrefixHadBlockingRefines(
    cmd: Schema.PasteCmd,
    preFs: BW.FileSystem,
    preStdin: BW.Bytes,
    i: nat
  )
    requires i <= |cmd.inputs|
    ensures Core.PrefixHadBlockingErrorCore(
              cmd, preFs, preStdin, i) ==
            (exists j: nat ::
               j < i &&
               Observations(cmd, preFs, preStdin)[j].blocking)
    decreases i
  {
    if i > 0 {
      PrefixHadBlockingRefines(cmd, preFs, preStdin, i - 1);
      assert Observations(cmd, preFs, preStdin)[i - 1].blocking ==
             Core.HadBlockingErrorPiece(
               cmd.inputs[i - 1],
               Core.ReadResultCore(cmd, preFs, preStdin, i - 1));
      assert (exists j: nat ::
                j < i &&
                Observations(cmd, preFs, preStdin)[j].blocking) <==>
             ((exists j: nat ::
                 j < i - 1 &&
                 Observations(cmd, preFs, preStdin)[j].blocking) ||
              Observations(cmd, preFs, preStdin)[i - 1].blocking) by {
      }
    }
  }

  lemma {:isolate_assertions} InputTraceRefines(
    cmd: Schema.PasteCmd,
    preFs: BW.FileSystem,
    preStdin: BW.Bytes
  )
    ensures Spec.InputTraceRelation(
              cmd,
              preFs,
              preStdin,
              Core.PrefixStdinCore(cmd, preStdin, |cmd.inputs|),
              ToSpecEntries(Core.EntriesForOutputCore(
                              cmd, preFs, preStdin)),
              Core.PrefixVisibleErrorOutputCore(
                cmd, preFs, preStdin, |cmd.inputs|),
              Core.PrefixHadErrorCore(
                cmd, preFs, preStdin, |cmd.inputs|),
              Core.PrefixHadBlockingErrorCore(
                cmd, preFs, preStdin, |cmd.inputs|))
  {
    var observations := Observations(cmd, preFs, preStdin);
    assert forall i: nat :: i < |observations| ==>
                              Spec.InputObservationRelation(
                                cmd, preFs, preStdin, i, observations[i]) by {
      forall i: nat | i < |observations|
        ensures Spec.InputObservationRelation(
                  cmd, preFs, preStdin, i, observations[i])
      {
        ObservationRefines(cmd, preFs, preStdin, i);
      }
    }
    ObservationEntriesEq(cmd, preFs, preStdin);
    HasStdinEq(cmd.inputs);
    var rawEntries := Core.EntriesCore(cmd, preFs, preStdin);
    EntriesForOutputRefines(cmd, preStdin, rawEntries);
    var visibleAssembly :=
      VisibleErrorsRefine(
        cmd, preFs, preStdin, |cmd.inputs|);
    PrefixHadErrorRefines(
      cmd, preFs, preStdin, |cmd.inputs|);
    PrefixHadBlockingRefines(
      cmd, preFs, preStdin, |cmd.inputs|);
    PrefixStdinCharacterization(
      cmd, preStdin, |cmd.inputs|);
    reveal Spec.VisibleErrorRelation();
    assert Spec.VisibleErrorRelation(
        cmd.serial,
        observations,
        Core.PrefixVisibleErrorOutputCore(
          cmd, preFs, preStdin, |cmd.inputs|)) by {
      ghost var assembly := visibleAssembly;
    }
    reveal Spec.InputTraceRelation();
    assert exists observationWitness: seq<Spec.InputObservation> ::
        |observationWitness| == |cmd.inputs| &&
        (forall i: nat | i < |observationWitness| ::
           Spec.InputObservationRelation(
             cmd, preFs, preStdin, i, observationWitness[i])) &&
        Spec.EntriesForOutputRelation(
          cmd,
          preStdin,
          Spec.ObservationEntries(observationWitness),
          ToSpecEntries(Core.EntriesForOutputCore(
                          cmd, preFs, preStdin))) &&
        Spec.VisibleErrorRelation(
          cmd.serial,
          observationWitness,
          Core.PrefixVisibleErrorOutputCore(
            cmd, preFs, preStdin, |cmd.inputs|)) &&
        Core.PrefixHadErrorCore(
          cmd, preFs, preStdin, |cmd.inputs|) ==
        (exists i: nat ::
           i < |observationWitness| &&
           observationWitness[i].failed) &&
        Core.PrefixHadBlockingErrorCore(
          cmd, preFs, preStdin, |cmd.inputs|) ==
        (exists i: nat ::
           i < |observationWitness| &&
           observationWitness[i].blocking) &&
        Core.PrefixStdinCore(
          cmd, preStdin, |cmd.inputs|) ==
        (if Spec.HasStdinInput(cmd.inputs) then [] else preStdin) by {
      ghost var observationWitness := observations;
    }
  }

  lemma EscapeDelimiterRefines(ch: BW.RawByte)
    ensures Spec.EscapedDelimiterRelation(
              ch, Core.EscapeDelimiter(ch))
  {
    reveal Spec.EscapedDelimiterRelation();
  }

  lemma BuildDelimiterParse(
    text: BW.Bytes,
    i: nat
  ) returns (assembly: Spec.DelimiterAssembly)
    requires i <= |text|
    ensures Spec.DelimiterParseRelation(
              text,
              i,
              ToSpecDelimPlan(Core.CollapseDelimitersFrom(text, i)),
              assembly)
    decreases |text| - i
  {
    if i == |text| {
      assembly := Spec.DelimiterDone;
    } else if text[i] == '\\' && i + 1 == |text| {
      assembly := Spec.DelimiterFailure;
    } else {
      var nextIndex :=
        if text[i] == '\\' then i + 2 else i + 1;
      var delimiter :=
        if text[i] == '\\'
        then Core.EscapeDelimiter(text[i + 1])
        else [text[i]];
      if text[i] == '\\' {
        EscapeDelimiterRefines(text[i + 1]);
      }
      var rest := BuildDelimiterParse(text, nextIndex);
      assembly :=
        Spec.DelimiterStep(i, nextIndex, delimiter, rest);
    }
  }

  lemma DelimiterPlanRefines(text: string)
    ensures Spec.DelimiterPlanRelation(
              text, ToSpecDelimPlan(Core.CollapseDelimiters(text)))
  {
    if |text| == 0 {
      reveal Spec.DelimiterPlanRelation();
    } else {
      var assembly := BuildDelimiterParse(Utf8.Encode(text), 0);
      assert Core.CollapseDelimiters(text) ==
             Core.CollapseDelimitersFrom(Utf8.Encode(text), 0);
      reveal Spec.DelimiterPlanRelation();
      assert exists a: Spec.DelimiterAssembly ::
          Spec.DelimiterParseRelation(
            Utf8.Encode(text),
            0,
            ToSpecDelimPlan(Core.CollapseDelimiters(text)),
            a) by {
        ghost var a := assembly;
      }
    }
  }

  lemma CollapseDelimitersFromNonEmpty(text: BW.Bytes, i: nat)
    requires i < |text|
    ensures
      match Core.CollapseDelimitersFrom(text, i)
      case DelimsOk(delims) => |delims| > 0
      case DelimsErr(_) => true
    decreases |text| - i
  {
    if text[i] == '\\' {
      if i + 1 < |text| {
        if i + 2 < |text| {
          CollapseDelimitersFromNonEmpty(text, i + 2);
        }
      }
    } else if i + 1 < |text| {
      CollapseDelimitersFromNonEmpty(text, i + 1);
    }
  }

  lemma CollapseDelimitersNonEmpty(text: string)
    ensures
      match Core.CollapseDelimiters(text)
      case DelimsOk(delims) => |delims| > 0
      case DelimsErr(_) => true
  {
    if |text| > 0 {
      CollapseDelimitersFromNonEmpty(Utf8.Encode(text), 0);
    }
  }

  lemma MaxEq(a: nat, b: nat)
    ensures Core.Max(a, b) == Spec.Max(a, b)
  {
  }

  lemma MaxLineCountEq(entries: seq<Core.Entry>)
    ensures Core.MaxLineCount(entries) ==
            Spec.MaxLineCount(ToSpecEntries(entries))
    decreases |entries|
  {
    if |entries| > 0 {
      MaxLineCountEq(entries[1..]);
      MaxEq(
        |entries[0].lines|,
        Core.MaxLineCount(entries[1..]));
    }
  }

  lemma DelimAtEq(delims: seq<BW.Bytes>, i: nat)
    requires |delims| > 0
    ensures Core.DelimAt(delims, i) == Spec.DelimAt(delims, i)
  {
  }

  lemma BuildParallelColumns(
    entries: seq<Core.Entry>,
    delims: seq<BW.Bytes>,
    row: nat,
    i: nat,
    before: BW.Bytes
  ) returns (assembly: Spec.ColumnAssembly)
    requires |delims| > 0
    requires |entries| > 0
    requires i <= |entries|
    ensures Spec.ParallelColumnsRelation(
              ToSpecEntries(entries), delims, row, i, before,
              before + Core.RenderParallelRow(
                entries, delims, row, i, |entries| - 1), assembly)
    decreases |entries| - i
  {
    if i == |entries| {
      assembly := Spec.ColumnsDone;
    } else {
      ToSpecEntriesIndex(entries, i);
      DelimAtEq(delims, i);
      var fragment :=
        (if row < |entries[i].lines| then entries[i].lines[row] else []) +
        (if i + 1 < |entries| then Core.DelimAt(delims, i) else []);
      var after := before + fragment;
      var rest := BuildParallelColumns(
        entries, delims, row, i + 1, after);
      assert before + Core.RenderParallelRow(
          entries, delims, row, i, |entries| - 1) ==
             after + Core.RenderParallelRow(
               entries, delims, row, i + 1, |entries| - 1);
      assembly := Spec.ColumnStep(
        |before|, |before| + |fragment|, after, rest);
    }
  }

  lemma BuildParallelRecords(
    entries: seq<Core.Entry>,
    delims: seq<BW.Bytes>,
    recordDelimiter: BW.RawByte,
    row: nat,
    limit: nat,
    before: BW.Bytes
  ) returns (assembly: Spec.RecordAssembly)
    requires |delims| > 0
    requires row <= limit
    requires limit == Core.MaxLineCount(entries)
    ensures Spec.ParallelRecordsRelation(
              ToSpecEntries(entries), delims, recordDelimiter, row, limit, before,
              before + Core.RenderParallelRows(
                entries, delims, recordDelimiter, row, limit), assembly)
    decreases limit - row
  {
    if row == limit {
      assembly := Spec.RecordsDone;
    } else {
      assert |entries| > 0;
      var columns := BuildParallelColumns(
        entries, delims, row, 0, []);
      var record := Core.RenderParallelRow(
        entries, delims, row, 0, |entries| - 1);
      assert [] + record == record;
      var after := before + record + [recordDelimiter];
      var rest := BuildParallelRecords(
        entries, delims, recordDelimiter, row + 1, limit, after);
      assert before + Core.RenderParallelRows(
          entries, delims, recordDelimiter, row, limit) ==
             after + Core.RenderParallelRows(
               entries, delims, recordDelimiter, row + 1, limit);
      assembly := Spec.RecordStep(
        |before|, |before| + |record| + 1,
        record, after, columns, rest);
    }
  }

  lemma BuildSerialColumns(
    lines: seq<BW.Bytes>,
    delims: seq<BW.Bytes>,
    i: nat,
    before: BW.Bytes
  ) returns (assembly: Spec.ColumnAssembly)
    requires |delims| > 0
    requires i <= |lines|
    ensures Spec.SerialColumnsRelation(
              lines, delims, i, before,
              before + Core.JoinLines(lines, delims, i), assembly)
    decreases |lines| - i
  {
    if i == |lines| {
      assembly := Spec.ColumnsDone;
    } else {
      DelimAtEq(delims, i);
      var fragment := lines[i] +
      (if i + 1 < |lines| then Core.DelimAt(delims, i) else []);
      var after := before + fragment;
      var rest := BuildSerialColumns(
        lines, delims, i + 1, after);
      assert before + Core.JoinLines(lines, delims, i) ==
             after + Core.JoinLines(lines, delims, i + 1);
      assembly := Spec.ColumnStep(
        |before|, |before| + |fragment|, after, rest);
    }
  }

  lemma BuildSerialRecords(
    entries: seq<Core.Entry>,
    delims: seq<BW.Bytes>,
    recordDelimiter: BW.RawByte,
    i: nat,
    before: BW.Bytes
  ) returns (assembly: Spec.RecordAssembly)
    requires |delims| > 0
    requires i <= |entries|
    ensures Spec.SerialRecordsRelation(
              ToSpecEntries(entries), delims, recordDelimiter, i, before,
              before + Core.RenderSerial(
                entries[i..], delims, recordDelimiter), assembly)
    decreases |entries| - i
  {
    if i == |entries| {
      assembly := Spec.RecordsDone;
    } else {
      ToSpecEntriesIndex(entries, i);
      if entries[i].readOk {
        var columns := BuildSerialColumns(
          entries[i].lines, delims, 0, []);
        var record := Core.JoinLines(
          entries[i].lines, delims, 0);
        assert [] + record == record;
        var after := before + record + [recordDelimiter];
        var rest := BuildSerialRecords(
          entries, delims, recordDelimiter, i + 1, after);
        assert before + Core.RenderSerial(
            entries[i..], delims, recordDelimiter) ==
               after + Core.RenderSerial(
                 entries[i + 1..], delims, recordDelimiter);
        assembly := Spec.RecordStep(
          |before|, |before| + |record| + 1,
          record, after, columns, rest);
      } else {
        var rest := BuildSerialRecords(
          entries, delims, recordDelimiter, i + 1, before);
        assert Core.RenderSerial(
            entries[i..], delims, recordDelimiter) ==
               Core.RenderSerial(
                 entries[i + 1..], delims, recordDelimiter);
        assembly := Spec.RecordStep(
          |before|, |before|, [], before,
          Spec.ColumnsDone, rest);
      }
    }
  }

  lemma OutputRefines(
    serial: bool,
    delims: seq<BW.Bytes>,
    recordDelimiter: BW.RawByte,
    entries: seq<Core.Entry>
  )
    requires |delims| > 0
    ensures Spec.OutputRelation(
              serial,
              delims,
              recordDelimiter,
              ToSpecEntries(entries),
              Core.RenderOutput(
                serial, delims, recordDelimiter, entries))
  {
    if serial {
      var records := BuildSerialRecords(
        entries, delims, recordDelimiter, 0, []);
      assert entries[0..] == entries;
      assert [] + Core.RenderSerial(
          entries, delims, recordDelimiter) ==
             Core.RenderSerial(entries, delims, recordDelimiter);
      assert exists r: Spec.RecordAssembly ::
          Spec.SerialRecordsRelation(
            ToSpecEntries(entries),
            delims,
            recordDelimiter,
            0,
            [],
            Core.RenderSerial(entries, delims, recordDelimiter),
            r) by {
        ghost var r := records;
      }
    } else {
      MaxLineCountEq(entries);
      var records := BuildParallelRecords(
        entries,
        delims,
        recordDelimiter,
        0,
        Core.MaxLineCount(entries),
        []);
      assert Core.MaxLineCount(entries) ==
             Spec.MaxLineCount(ToSpecEntries(entries));
      assert [] + Core.RenderParallelRows(
          entries,
          delims,
          recordDelimiter,
          0,
          Core.MaxLineCount(entries)) ==
             Core.RenderParallel(entries, delims, recordDelimiter);
      assert exists r: Spec.RecordAssembly ::
          Spec.ParallelRecordsRelation(
            ToSpecEntries(entries),
            delims,
            recordDelimiter,
            0,
            Spec.MaxLineCount(ToSpecEntries(entries)),
            [],
            Core.RenderParallel(entries, delims, recordDelimiter),
            r) by {
        ghost var r := records;
      }
    }
  }

  twostate lemma {:isolate_assertions} CoreSummaryImpliesSpec(
    raw: Schema.PasteCmdRaw,
    io: BenchIO.IO,
    exit: int
  )
    requires Core.CoreSummary(raw, io, exit)
    ensures Spec.Spec(raw, io, exit)
  {
    var cmd := Core.Command(raw);
    assert cmd == Schema.Command(raw);
    if cmd.mode == Schema.ModeHelp {
    } else if cmd.mode == Schema.ModeVersion {
    } else {
      DelimiterPlanRefines(cmd.delimiterText);
      CollapseDelimitersNonEmpty(cmd.delimiterText);
      ghost var plan :=
        ToSpecDelimPlan(
          Core.CollapseDelimiters(cmd.delimiterText));
      assert Spec.DelimiterPlanRelation(
          cmd.delimiterText, plan);
      match Core.CollapseDelimiters(cmd.delimiterText)
      case DelimsErr(stderr) =>
      case DelimsOk(delims) =>
        assert |delims| > 0;
        InputTraceRefines(
          cmd, old(io.fs()), old(io.stdin()));
        RecordDelimiterEq(cmd.zeroTerminated);
        OutputRefines(
          cmd.serial,
          delims,
          Core.RecordDelimiter(cmd.zeroTerminated),
          Core.EntriesForOutputCore(
            cmd, old(io.fs()), old(io.stdin())));
    }
  }
}
