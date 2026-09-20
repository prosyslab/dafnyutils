include "../../core/World.dfy"
include "../../core/IO.dfy"
include "WcSchema.dfy"
include "WcCore.dfy"
include "WcSpec.dfy"

module WcProof {
  import BenchIO
  import BW = BenchWorld
  import Schema = WcSchema
  import Core = WcCore
  import Spec = WcSpec

  ghost function ToSpecObservation(
    observation: Core.InputObservation
  ): Spec.InputObservation
  {
    Spec.InputObservation(
      observation.result,
      Core.ToSpecEntries(observation.entries),
      observation.errorOutput,
      observation.failed
    )
  }

  ghost function ToSpecObservations(
    observations: seq<Core.InputObservation>
  ): seq<Spec.InputObservation>
  {
    seq(
    |observations|,
    i requires 0 <= i < |observations| =>
      ToSpecObservation(observations[i])
      )
  }

  lemma IsStdinInputEq(input: Schema.Input)
    ensures Core.IsStdinInput(input) == Spec.IsStdinInput(input)
  {
  }

  lemma InputsFromOperandsEq(operands: seq<string>)
    ensures Core.InputsFromOperands(operands) ==
            Spec.InputsFromOperands(operands)
    decreases |operands|
  {
    if |operands| > 0 {
      InputsFromOperandsEq(operands[1..]);
    }
  }

  lemma CommandEq(raw: Schema.WcCmdRaw)
    ensures Core.Command(raw) == Spec.Command(raw)
  {
    InputsFromOperandsEq(raw.operands);
  }

  lemma IsWordSpaceEq(ch: char)
    ensures Core.IsWordSpace(ch) == Spec.IsWordSpace(ch)
  {
  }

  lemma NextLineLenEq(ch: char, current: int)
    requires 0 <= current
    ensures Core.NextLineLen(ch, current) ==
            Spec.NextLineLen(ch, current)
  {
  }

  lemma NewlineIndicesEq(data: BW.Bytes)
    ensures Core.NewlineIndices(data) == Spec.NewlineIndices(data)
  {
  }

  lemma WordStartIndicesEq(data: BW.Bytes)
    ensures Core.WordStartIndices(data) == Spec.WordStartIndices(data)
  {
    assert forall i: nat {:trigger i in Core.WordStartIndices(data)} ::
        i in Core.WordStartIndices(data) <==>
             i in Spec.WordStartIndices(data) by {
      forall i: nat {:trigger i in Core.WordStartIndices(data)}
        ensures
          i in Core.WordStartIndices(data) <==>
               i in Spec.WordStartIndices(data)
      {
        if i < |data| {
          IsWordSpaceEq(data[i]);
          if i > 0 {
            IsWordSpaceEq(data[i - 1]);
          }
        }
      }
    }
  }

  lemma LineColumnTraceRefines(
    data: BW.Bytes,
    columns: seq<nat>
  )
    requires Core.LineColumnTraceRelation(data, columns)
    ensures Spec.LineColumnTraceRelation(data, columns)
  {
    reveal Core.LineColumnTraceRelation();
    reveal Spec.LineColumnTraceRelation();
    forall i: nat | i < |data|
      ensures columns[i + 1] ==
              if data[i] == '\n' then 0
              else Spec.NextLineLen(data[i], columns[i])
    {
      NextLineLenEq(data[i], columns[i]);
    }
  }

  lemma MaximumRelationRefines(values: seq<nat>, maximum: int)
    requires Core.MaximumRelation(values, maximum)
    ensures Spec.MaximumRelation(values, maximum)
  {
    reveal Core.MaximumRelation();
    reveal Spec.MaximumRelation();
  }

  lemma CountWitnessImpliesRelation(
    data: BW.Bytes,
    counts: Core.Counts,
    countTrace: Core.CountWitness
  )
    requires Core.CountWitnessRelation(data, counts, countTrace)
    ensures Spec.CountRelation(data, Core.ToSpecCounts(counts))
  {
    reveal Core.CountWitnessRelation();
    reveal Spec.CountRelation();
    NewlineIndicesEq(data);
    WordStartIndicesEq(data);
    LineColumnTraceRefines(data, countTrace.columns);
    MaximumRelationRefines(countTrace.columns, counts.maxLine);
  }

  lemma ReadResultRefines(
    cmd: Schema.WcCmd,
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
    reveal Spec.ReadResultRelation();
    Core.PrefixStdinRelation(cmd, preStdin, i);
    match cmd.inputs[i]
    case Stdin(_) =>
      assert forall j: nat | j < i ::
          Core.IsStdinInput(cmd.inputs[j]) ==
          Spec.IsStdinInput(cmd.inputs[j]) by {
        forall j: nat | j < i
          ensures Core.IsStdinInput(cmd.inputs[j]) ==
                  Spec.IsStdinInput(cmd.inputs[j])
        {
          IsStdinInputEq(cmd.inputs[j]);
        }
      }
    case File(_) =>
  }

  lemma InputStepWitnessRefines(
    input: Schema.Input,
    result: BW.Result<BW.Bytes>,
                      entries: seq<Core.Entry>,
                      errorOutput: BW.Bytes,
                      failed: bool,
                      countWitnesses: seq<Core.CountWitness>
  )
    requires Core.InputStepWitnessRelation(
               input,
               result,
               entries,
               errorOutput,
               failed,
               countWitnesses
             )
    ensures Spec.InputStepRelation(
              input,
              result,
              Core.ToSpecEntries(entries),
              errorOutput,
              failed
            )
  {
    reveal Core.InputStepWitnessRelation();
    reveal Spec.InputStepRelation();
    match input {
      case Stdin(_) =>
        match result {
          case Ok(data) =>
            var counts, countTrace :|
              Core.CountWitnessRelation(data, counts, countTrace) &&
              countWitnesses == [countTrace] &&
              entries == [Core.Entry(input.displayName, counts, true)];
            CountWitnessImpliesRelation(data, counts, countTrace);
            assert Core.ToSpecEntries(entries) == [
                                                    Spec.Entry(
                                                      input.displayName,
                                                      Core.ToSpecCounts(counts),
                                                      true
                                                    )
                                                  ];
          case Err(_) =>
        }
      case File(_) =>
        match result {
          case Ok(data) =>
            var counts, countTrace :|
              Core.CountWitnessRelation(data, counts, countTrace) &&
              countWitnesses == [countTrace] &&
              entries == [Core.Entry(input.path, counts, false)];
            CountWitnessImpliesRelation(data, counts, countTrace);
            assert Core.ToSpecEntries(entries) == [
                                                    Spec.Entry(
                                                      input.path,
                                                      Core.ToSpecCounts(counts),
                                                      false
                                                    )
                                                  ];
          case Err(err) =>
            if err == BW.IsDirectory {
              ZeroCountsEq();
            }
        }
    }
  }

  lemma InputObservationRefines(
    cmd: Schema.WcCmd,
    preFs: BW.FileSystem,
    preStdin: BW.Bytes,
    i: nat,
    observation: Core.InputObservation
  )
    requires i < |cmd.inputs|
    requires Core.InputObservationRelation(
               cmd,
               preFs,
               preStdin,
               i,
               observation
             )
    ensures Spec.InputObservationRelation(
              cmd,
              preFs,
              preStdin,
              i,
              ToSpecObservation(observation)
            )
  {
    reveal Core.InputObservationRelation();
    reveal Spec.InputObservationRelation();
    ReadResultRefines(cmd, preFs, preStdin, i);
    InputStepWitnessRefines(
      cmd.inputs[i],
      observation.result,
      observation.entries,
      observation.errorOutput,
      observation.failed,
      observation.countWitnesses
    );
  }

  lemma ZeroCountsEq()
    ensures Core.ToSpecCounts(Core.ZeroCounts()) == Spec.ZeroCounts()
  {
  }

  lemma MaxEq(a: int, b: int)
    ensures Core.Max(a, b) == Spec.Max(a, b)
  {
  }

  lemma AddCountsEq(a: Core.Counts, b: Core.Counts)
    ensures Core.ToSpecCounts(Core.AddCounts(a, b)) ==
            Spec.AddCounts(Core.ToSpecCounts(a), Core.ToSpecCounts(b))
  {
    MaxEq(a.maxLine, b.maxLine);
  }

  lemma SelectedFieldCountEq(cmd: Schema.WcCmd)
    ensures Core.SelectedFieldCount(cmd) == Spec.SelectedFieldCount(cmd)
  {
  }

  lemma SelectedValuesEq(cmd: Schema.WcCmd, counts: Core.Counts)
    ensures Core.SelectedValues(cmd, counts) ==
            Spec.SelectedValues(cmd, Core.ToSpecCounts(counts))
  {
  }

  lemma MaxSelectedValueEq(cmd: Schema.WcCmd, counts: Core.Counts)
    ensures Core.MaxSelectedValue(cmd, counts) ==
            Spec.MaxSelectedValue(cmd, Core.ToSpecCounts(counts))
  {
  }

  lemma ShouldPrintTotalEq(cmd: Schema.WcCmd)
    ensures Core.ShouldPrintTotal(cmd) == Spec.ShouldPrintTotal(cmd)
  {
  }

  lemma CountsNonnegativeAfterAdd(a: Core.Counts, b: Core.Counts)
    requires Core.CountsNonnegative(a)
    requires Core.CountsNonnegative(b)
    ensures Core.CountsNonnegative(Core.AddCounts(a, b))
  {
    reveal Core.CountsNonnegative();
  }

  lemma TotalCountsWitnessForCore(entries: seq<Core.Entry>) returns (
      suffixes: seq<Spec.Counts>
    )
    requires Core.EntriesNonnegative(entries)
    ensures Spec.TotalCountsWitnessRelation(
              Core.ToSpecEntries(entries),
              Core.ToSpecCounts(Core.TotalCounts(entries)),
              suffixes
            )
    ensures Core.CountsNonnegative(Core.TotalCounts(entries))
    decreases |entries|
  {
    reveal Core.EntriesNonnegative();
    reveal Spec.TotalCountsWitnessRelation();
    if |entries| == 0 {
      suffixes := [Spec.ZeroCounts()];
      ZeroCountsEq();
      reveal Core.CountsNonnegative();
    } else {
      var tailSuffixes := TotalCountsWitnessForCore(entries[1..]);
      var tailTotal := Core.TotalCounts(entries[1..]);
      AddCountsEq(entries[0].counts, tailTotal);
      CountsNonnegativeAfterAdd(entries[0].counts, tailTotal);
      suffixes :=
        [Core.ToSpecCounts(Core.TotalCounts(entries))] + tailSuffixes;
      assert forall i: nat | i < |Core.ToSpecEntries(entries)| ::
          suffixes[i] ==
          Spec.AddCounts(
            Core.ToSpecEntries(entries)[i].counts,
            suffixes[i + 1]
          ) by {
        forall i: nat | i < |Core.ToSpecEntries(entries)|
          ensures suffixes[i] ==
                  Spec.AddCounts(
                    Core.ToSpecEntries(entries)[i].counts,
                    suffixes[i + 1]
                  )
        {
          if i == 0 {
          } else {
            assert i - 1 < |Core.ToSpecEntries(entries[1..])|;
          }
        }
      }
    }
  }

  lemma EntryMaximumWitnessForCore(
    cmd: Schema.WcCmd,
    entries: seq<Core.Entry>
  ) returns (
      selectedSuffixes: seq<int>,
      byteSuffixes: seq<int>
    )
    ensures Spec.EntryMaximumWitnessRelation(
              cmd,
              Core.ToSpecEntries(entries),
              selectedSuffixes,
              byteSuffixes
            )
    ensures selectedSuffixes[0] == Core.MaxEntrySelectedValue(cmd, entries)
    ensures byteSuffixes[0] == Core.MaxEntryBytes(entries)
    decreases |entries|
  {
    reveal Spec.EntryMaximumWitnessRelation();
    if |entries| == 0 {
      selectedSuffixes := [0];
      byteSuffixes := [0];
    } else {
      var tailSelected, tailBytes :=
        EntryMaximumWitnessForCore(cmd, entries[1..]);
      MaxSelectedValueEq(cmd, entries[0].counts);
      selectedSuffixes :=
        [Core.MaxEntrySelectedValue(cmd, entries)] + tailSelected;
      byteSuffixes := [Core.MaxEntryBytes(entries)] + tailBytes;
      assert forall i: nat | i < |Core.ToSpecEntries(entries)| ::
          selectedSuffixes[i] ==
          Spec.Max(
            Spec.MaxSelectedValue(
              cmd, Core.ToSpecEntries(entries)[i].counts
            ),
            selectedSuffixes[i + 1]
          ) &&
          byteSuffixes[i] ==
          Spec.Max(
            Core.ToSpecEntries(entries)[i].counts.bytes,
            byteSuffixes[i + 1]
          ) by {
        forall i: nat | i < |Core.ToSpecEntries(entries)|
          ensures selectedSuffixes[i] ==
                  Spec.Max(
                    Spec.MaxSelectedValue(
                      cmd, Core.ToSpecEntries(entries)[i].counts
                    ),
                    selectedSuffixes[i + 1]
                  ) &&
                  byteSuffixes[i] ==
                  Spec.Max(
                    Core.ToSpecEntries(entries)[i].counts.bytes,
                    byteSuffixes[i + 1]
                  )
        {
          if i == 0 {
          } else {
            assert i - 1 < |Core.ToSpecEntries(entries[1..])|;
          }
        }
      }
    }
  }

  lemma HasWideEntryRelation(entries: seq<Core.Entry>)
    ensures Core.HasWideEntry(entries) ==
            (exists i: nat ::
               i < |Core.ToSpecEntries(entries)| &&
               Core.ToSpecEntries(entries)[i].wide)
    decreases |entries|
  {
    ToSpecEntriesLength(entries);
    reveal Core.HasWideEntry();
    if |entries| > 0 {
      HasWideEntryRelation(entries[1..]);
      if Core.HasWideEntry(entries) {
        if entries[0].wide {
          assert exists i: nat ::
              i < |Core.ToSpecEntries(entries)| &&
              Core.ToSpecEntries(entries)[i].wide by {
            assert Core.ToSpecEntries(entries)[0].wide;
          }
        } else {
          var i: nat :|
            i < |Core.ToSpecEntries(entries[1..])| &&
            Core.ToSpecEntries(entries[1..])[i].wide;
          assert Core.ToSpecEntries(entries)[i + 1] ==
                 Core.ToSpecEntries(entries[1..])[i];
        }
      }
      if exists i: nat ::
          i < |Core.ToSpecEntries(entries)| &&
          Core.ToSpecEntries(entries)[i].wide {
        var i: nat :|
          i < |Core.ToSpecEntries(entries)| &&
          Core.ToSpecEntries(entries)[i].wide;
        if i > 0 {
          assert i - 1 < |Core.ToSpecEntries(entries[1..])|;
          assert Core.ToSpecEntries(entries)[i] ==
                 Core.ToSpecEntries(entries[1..])[i - 1];
        }
      }
    }
  }

  lemma DecimalTextForCore(n: nat) returns (
      text: BW.Bytes,
      digits: seq<nat>,
      values: seq<nat>
    )
    ensures text == Core.Digits(n)
    ensures Spec.DecimalTextWitness(n, text, digits, values)
    ensures Spec.DecimalText(n, text)
    decreases n
  {
    if n < 10 {
      text := [Core.DigitChar(n)];
      digits := [n];
      values := [0, n];
      reveal Spec.DecimalTextWitness();
    } else {
      var prefix, prefixDigits, prefixValues :=
        DecimalTextForCore(n / 10);
      var digit := n % 10;
      text := prefix + [Core.DigitChar(digit)];
      digits := prefixDigits + [digit];
      values := prefixValues + [n];
      reveal Spec.DecimalTextWitness();
      assert forall i: nat | i < |digits| ::
          digits[i] < 10 &&
          text[i] == (('0' as int) + digits[i]) as char &&
          values[i + 1] == values[i] * 10 + digits[i] by {
        forall i: nat | i < |digits|
          ensures digits[i] < 10 &&
                  text[i] == (('0' as int) + digits[i]) as char &&
                  values[i + 1] == values[i] * 10 + digits[i]
        {
          if i + 1 == |digits| {
            assert values[i] == n / 10;
            assert n == (n / 10) * 10 + n % 10;
          }
        }
      }
    }
    reveal Spec.DecimalText();
    assert exists ds: seq<nat>, vs: seq<nat> ::
        Spec.DecimalTextWitness(n, text, ds, vs) by {
      assert Spec.DecimalTextWitness(n, text, digits, values);
    }
  }

  lemma DigitCountLength(n: nat)
    ensures Core.DigitCount(n) == |Core.Digits(n)|
    decreases n
  {
    if n >= 10 {
      DigitCountLength(n / 10);
    }
  }

  lemma PadLeftRelation(text: BW.Bytes, width: int)
    ensures |text| <= |Core.PadLeft(text, width)|
    ensures |Core.PadLeft(text, width)| ==
            (if |text| >= width then |text| else width)
    ensures Core.PadLeft(text, width)[
            |Core.PadLeft(text, width)| - |text|..
            ] == text
    ensures forall i: nat | i < |Core.PadLeft(text, width)| - |text| ::
              Core.PadLeft(text, width)[i] == ' '
    decreases if |text| < width then width - |text| else 0
  {
    if |text| < width {
      PadLeftRelation([' '] + text, width);
    }
  }

  lemma PaddedDecimalForCore(n: nat, width: int)
    ensures Spec.PaddedDecimalText(
              n, width, Core.PadLeft(Core.Digits(n), width)
            )
  {
    var text, digits, values := DecimalTextForCore(n);
    PadLeftRelation(text, width);
    reveal Spec.PaddedDecimalText();
  }

  ghost function ShiftCuts(cuts: seq<nat>, amount: nat): seq<nat>
  {
    seq(|cuts|, i requires 0 <= i < |cuts| => cuts[i] + amount)
  }

  lemma ShiftCutsIndex(cuts: seq<nat>, amount: nat, i: nat)
    requires i < |cuts|
    ensures ShiftCuts(cuts, amount)[i] == cuts[i] + amount
  {
  }

  lemma PrependSlice<T>(
    head: seq<T>,
    tail: seq<T>,
    start: nat,
    end: nat
  )
    requires start <= end <= |tail|
    ensures (head + tail)[
            |head| + start..|head| + end
            ] == tail[start..end]
  {
  }

  lemma {:isolate_assertions} PrependFragment(
    head: BW.Bytes,
    tailFragments: seq<BW.Bytes>,
    tail: BW.Bytes,
    tailCuts: seq<nat>
  )
    requires Spec.FragmentsConcatenate(
               tailFragments, tail, tailCuts
             )
    ensures Spec.FragmentsConcatenate(
              [head] + tailFragments,
              head + tail,
              [0] + ShiftCuts(tailCuts, |head|)
            )
  {
    reveal Spec.FragmentsConcatenate();
    forall i: nat {:trigger ([0] + ShiftCuts(
      tailCuts, |head|
      ))[i]} | i < |[head] + tailFragments|
      ensures ([0] + ShiftCuts(tailCuts, |head|))[i] <=
              ([0] + ShiftCuts(tailCuts, |head|))[i + 1] &&
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
      ShiftCutsIndex(tailCuts, |head|, i);
      if i == 0 {
      } else {
        ShiftCutsIndex(tailCuts, |head|, i - 1);
        var k := i - 1;
        PrependSlice(head, tail, tailCuts[k], tailCuts[k + 1]);
      }
    }
  }

  lemma RenderValuesRelationForCore(
    values: seq<int>,
    width: int,
    i: nat
  ) returns (
      fragments: seq<BW.Bytes>,
      cuts: seq<nat>
    )
    requires i <= |values|
    requires forall j: nat | i <= j < |values| :: 0 <= values[j]
    ensures Spec.ValuesRenderWitnessRelation(
              values[i..],
              width,
              i == 0,
              Core.RenderValues(values, width, i),
              fragments,
              cuts
            )
    decreases |values| - i
  {
    reveal Spec.ValuesRenderWitnessRelation();
    if i == |values| {
      fragments := [];
      cuts := [0];
      reveal Spec.FragmentsConcatenate();
    } else {
      PaddedDecimalForCore(values[i] as nat, width);
      var padded := Core.PadLeft(Core.Digits(values[i]), width);
      var head := (if i == 0 then [] else [' ']) + padded;
      var tailFragments, tailCuts :=
        RenderValuesRelationForCore(values, width, i + 1);
      fragments := [head] + tailFragments;
      cuts := [0] + ShiftCuts(tailCuts, |head|);
      PrependFragment(
        head,
        tailFragments,
        Core.RenderValues(values, width, i + 1),
        tailCuts
      );
      assert forall j: nat | j < |values[i..]| ::
          Spec.ValueFragmentRelation(
            values[i..][j],
            width,
            i == 0 && j == 0,
            fragments[j]
          ) by {
        forall j: nat | j < |values[i..]|
          ensures Spec.ValueFragmentRelation(
                    values[i..][j],
                    width,
                    i == 0 && j == 0,
                    fragments[j]
                  )
        {
          if j == 0 {
            reveal Spec.ValueFragmentRelation();
          } else {
            assert j - 1 < |values[i + 1..]|;
          }
        }
      }
    }
  }

  lemma CountsLineRelationForCore(
    cmd: Schema.WcCmd,
    counts: Core.Counts,
    name: string,
    width: int
  )
    requires Core.CountsNonnegative(counts)
    ensures Spec.CountsLineRelation(
              cmd,
              Core.ToSpecCounts(counts),
              name,
              width,
              Core.RenderCountsLine(cmd, counts, name, width)
            )
  {
    SelectedValuesEq(cmd, counts);
    reveal Core.CountsNonnegative();
    assert forall i: nat | i < |Core.SelectedValues(cmd, counts)| ::
        0 <= Core.SelectedValues(cmd, counts)[i];
    var fragments, cuts :=
      RenderValuesRelationForCore(
        Core.SelectedValues(cmd, counts), width, 0
      );
    var valuesOutput :=
      Core.RenderValues(Core.SelectedValues(cmd, counts), width, 0);
    reveal Spec.ValuesRenderRelation();
    assert Spec.ValuesRenderRelation(
        Spec.SelectedValues(cmd, Core.ToSpecCounts(counts)),
        width,
        true,
        valuesOutput
      ) by {
      assert Spec.ValuesRenderWitnessRelation(
          Core.SelectedValues(cmd, counts),
          width,
          true,
          valuesOutput,
          fragments,
          cuts
        );
    }
    reveal Spec.CountsLineRelation();
    assert exists output: BW.Bytes ::
        Spec.ValuesRenderRelation(
          Spec.SelectedValues(cmd, Core.ToSpecCounts(counts)),
          width,
          true,
          output
        ) &&
        Core.RenderCountsLine(cmd, counts, name, width) ==
        output +
        (if name == "" then [] else [' '] + name) +
        ['\n'] by {
      assert valuesOutput ==
             Core.RenderValues(Core.SelectedValues(cmd, counts), width, 0);
    }
  }

  lemma RenderEntriesRelationForCore(
    cmd: Schema.WcCmd,
    entries: seq<Core.Entry>,
    width: int
  ) returns (
      lines: seq<BW.Bytes>,
      cuts: seq<nat>
    )
    requires Core.EntriesNonnegative(entries)
    ensures |lines| == |Core.ToSpecEntries(entries)|
    ensures forall i: nat | i < |Core.ToSpecEntries(entries)| ::
              Spec.CountsLineRelation(
                cmd,
                Core.ToSpecEntries(entries)[i].counts,
                Core.ToSpecEntries(entries)[i].name,
                width,
                lines[i]
              )
    ensures Spec.FragmentsConcatenate(
              lines, Core.RenderEntries(cmd, entries, width), cuts
            )
    decreases |entries|
  {
    reveal Core.EntriesNonnegative();
    if |entries| == 0 {
      lines := [];
      cuts := [0];
      reveal Spec.FragmentsConcatenate();
    } else {
      var head :=
        Core.RenderCountsLine(
          cmd, entries[0].counts, entries[0].name, width
        );
      CountsLineRelationForCore(
        cmd, entries[0].counts, entries[0].name, width
      );
      var tailLines, tailCuts :=
        RenderEntriesRelationForCore(cmd, entries[1..], width);
      lines := [head] + tailLines;
      cuts := [0] + ShiftCuts(tailCuts, |head|);
      PrependFragment(
        head,
        tailLines,
        Core.RenderEntries(cmd, entries[1..], width),
        tailCuts
      );
      assert forall i: nat | i < |Core.ToSpecEntries(entries)| ::
          Spec.CountsLineRelation(
            cmd,
            Core.ToSpecEntries(entries)[i].counts,
            Core.ToSpecEntries(entries)[i].name,
            width,
            lines[i]
          ) by {
        forall i: nat | i < |Core.ToSpecEntries(entries)|
          ensures Spec.CountsLineRelation(
                    cmd,
                    Core.ToSpecEntries(entries)[i].counts,
                    Core.ToSpecEntries(entries)[i].name,
                    width,
                    lines[i]
                  )
        {
          if i > 0 {
            assert i - 1 < |Core.ToSpecEntries(entries[1..])|;
          }
        }
      }
    }
  }

  lemma FieldWidthRelationForCore(
    cmd: Schema.WcCmd,
    entries: seq<Core.Entry>,
    total: Core.Counts
  )
    requires Core.EntriesNonnegative(entries)
    requires Core.CountsNonnegative(total)
    ensures Spec.FieldWidthRelation(
              cmd,
              Core.ToSpecEntries(entries),
              Core.ToSpecCounts(total),
              Core.FieldWidth(cmd, entries, total)
            )
  {
    ToSpecEntriesLength(entries);
    reveal Core.CountsNonnegative();
    SelectedFieldCountEq(cmd);
    MaxSelectedValueEq(cmd, total);
    var selectedSuffixes, byteSuffixes :=
      EntryMaximumWitnessForCore(cmd, entries);
    HasWideEntryRelation(entries);
    ShouldPrintTotalEq(cmd);
    var maximum :=
      Core.Max(
        Core.Max(Core.MaxSelectedValue(cmd, total), Core.MaxEntrySelectedValue(cmd, entries)),
        Core.Max(total.bytes, Core.MaxEntryBytes(entries))
      );
    assert 0 <= maximum;
    var maximumText, maximumDigits, maximumValues :=
      DecimalTextForCore(maximum as nat);
    DigitCountLength(maximum as nat);
    reveal Spec.FieldWidthRelation();
    assert Spec.EntryMaximumWitnessRelation(
        cmd,
        Core.ToSpecEntries(entries),
        selectedSuffixes,
        byteSuffixes
      );
    assert maximum ==
           Spec.Max(
             Spec.Max(
               Spec.MaxSelectedValue(cmd, Core.ToSpecCounts(total)),
               selectedSuffixes[0]
             ),
             Spec.Max(Core.ToSpecCounts(total).bytes, byteSuffixes[0])
           );
    assert Spec.DecimalText(maximum as nat, maximumText);
    assert exists selected: seq<int>,
        bytes: seq<int>,
        maxValue: int,
        maxText: BW.Bytes
        {:trigger Spec.EntryMaximumWitnessRelation(
          cmd, Core.ToSpecEntries(entries), selected, bytes
        ), Spec.DecimalText(maxValue as nat, maxText)} ::
        Spec.EntryMaximumWitnessRelation(
          cmd, Core.ToSpecEntries(entries), selected, bytes
        ) &&
        maxValue ==
        Spec.Max(
          Spec.Max(
            Spec.MaxSelectedValue(cmd, Core.ToSpecCounts(total)),
            selected[0]
          ),
          Spec.Max(Core.ToSpecCounts(total).bytes, bytes[0])
        ) &&
        0 <= maxValue &&
        Spec.DecimalText(maxValue as nat, maxText) &&
        Core.FieldWidth(cmd, entries, total) ==
        if Spec.SelectedFieldCount(cmd) <= 1 &&
           !Spec.ShouldPrintTotal(cmd) then
          1
        else if exists i: nat ::
                  i < |Core.ToSpecEntries(entries)| &&
                  Core.ToSpecEntries(entries)[i].wide then
          Spec.Max(7, |maxText|)
        else
          Spec.Max(1, |maxText|) by {
      assert selectedSuffixes[0] ==
             Core.MaxEntrySelectedValue(cmd, entries);
      assert byteSuffixes[0] == Core.MaxEntryBytes(entries);
    }
  }

  lemma RunOutputRelationForCore(
    cmd: Schema.WcCmd,
    entries: seq<Core.Entry>
  )
    requires Core.EntriesNonnegative(entries)
    ensures Spec.OutputRelation(
              cmd,
              Core.ToSpecEntries(entries),
              Core.RunOutputFromEntriesCore(cmd, entries)
            )
  {
    var totalSuffixes := TotalCountsWitnessForCore(entries);
    var total := Core.TotalCounts(entries);
    FieldWidthRelationForCore(cmd, entries, total);
    var width := Core.FieldWidth(cmd, entries, total);
    var entryLines, entryCuts :=
      RenderEntriesRelationForCore(cmd, entries, width);
    var entryOutput := Core.RenderEntries(cmd, entries, width);
    ShouldPrintTotalEq(cmd);
    var totalLine: BW.Bytes;
    if Core.ShouldPrintTotal(cmd) {
      totalLine :=
        Core.RenderCountsLine(cmd, total, Spec.TotalName(), width);
      CountsLineRelationForCore(
        cmd, total, Spec.TotalName(), width
      );
    } else {
      totalLine := [];
    }
    reveal Spec.OutputWitnessRelation();
    assert Spec.OutputWitnessRelation(
        cmd,
        Core.ToSpecEntries(entries),
        Core.RunOutputFromEntriesCore(cmd, entries),
        Core.ToSpecCounts(total),
        totalSuffixes,
        width,
        entryLines,
        entryOutput,
        entryCuts,
        totalLine
      );
    reveal Spec.OutputRelation();
    assert exists specTotal: Spec.Counts,
        specSuffixes: seq<Spec.Counts>,
        specWidth: int,
        specLines: seq<BW.Bytes>,
        specEntryOutput: BW.Bytes,
        specCuts: seq<nat>,
        specTotalLine: BW.Bytes ::
        Spec.OutputWitnessRelation(
          cmd,
          Core.ToSpecEntries(entries),
          Core.RunOutputFromEntriesCore(cmd, entries),
          specTotal,
          specSuffixes,
          specWidth,
          specLines,
          specEntryOutput,
          specCuts,
          specTotalLine
        ) by {
      assert Spec.OutputWitnessRelation(
          cmd,
          Core.ToSpecEntries(entries),
          Core.RunOutputFromEntriesCore(cmd, entries),
          Core.ToSpecCounts(total),
          totalSuffixes,
          width,
          entryLines,
          entryOutput,
          entryCuts,
          totalLine
        );
    }
  }

  ghost function ToSpecEntryFragments(
    fragments: seq<seq<Core.Entry>>
  ): seq<seq<Spec.Entry>>
  {
    seq(
    |fragments|,
    i requires 0 <= i < |fragments| =>
      Core.ToSpecEntries(fragments[i])
      )
  }

  lemma ToSpecEntriesLength(entries: seq<Core.Entry>)
    ensures |Core.ToSpecEntries(entries)| == |entries|
    decreases |entries|
  {
    if |entries| > 0 {
      ToSpecEntriesLength(entries[1..]);
    }
  }

  lemma ToSpecEntriesAt(entries: seq<Core.Entry>, i: nat)
    requires i < |entries|
    requires i < |Core.ToSpecEntries(entries)|
    ensures Core.ToSpecEntries(entries)[i] ==
            Core.ToSpecEntry(entries[i])
    decreases i
  {
    if i > 0 {
      ToSpecEntriesLength(entries[1..]);
      ToSpecEntriesAt(entries[1..], i - 1);
    }
  }

  lemma ToSpecEntriesSlice(
    entries: seq<Core.Entry>,
    start: nat,
    end: nat
  )
    requires start <= end <= |entries|
    requires end <= |Core.ToSpecEntries(entries)|
    ensures Core.ToSpecEntries(entries)[start..end] ==
            Core.ToSpecEntries(entries[start..end])
  {
    ToSpecEntriesLength(entries);
    ToSpecEntriesLength(entries[start..end]);
    assert |Core.ToSpecEntries(entries)[start..end]| == end - start;
    assert |Core.ToSpecEntries(entries[start..end])| == end - start;
    forall i: nat | i < end - start
      ensures Core.ToSpecEntries(entries)[start..end][i] ==
              Core.ToSpecEntries(entries[start..end])[i]
    {
      ToSpecEntriesAt(entries, start + i);
      ToSpecEntriesAt(entries[start..end], i);
      assert entries[start..end][i] == entries[start + i];
    }
  }

  lemma EntryFragmentsRefine(
    fragments: seq<seq<Core.Entry>>,
    combined: seq<Core.Entry>,
    cuts: seq<nat>
  )
    requires Core.FragmentsConcatenate(fragments, combined, cuts)
    ensures Spec.FragmentsConcatenate(
              ToSpecEntryFragments(fragments),
              Core.ToSpecEntries(combined),
              cuts
            )
  {
    reveal Core.FragmentsConcatenate();
    reveal Spec.FragmentsConcatenate();
    ToSpecEntriesLength(combined);
    forall i: nat {:trigger cuts[i]} | i < |fragments|
      ensures cuts[i] <= cuts[i + 1] &&
              cuts[i + 1] <= |Core.ToSpecEntries(combined)| &&
              cuts[i + 1] == cuts[i] +
              |ToSpecEntryFragments(fragments)[i]| &&
              Core.ToSpecEntries(combined)[cuts[i]..cuts[i + 1]] ==
              ToSpecEntryFragments(fragments)[i]
    {
      ToSpecEntriesLength(fragments[i]);
      ToSpecEntriesSlice(combined, cuts[i], cuts[i + 1]);
    }
  }

  lemma FragmentsRefine<T>(
    fragments: seq<seq<T>>,
    combined: seq<T>,
    cuts: seq<nat>
  )
    requires Core.FragmentsConcatenate(fragments, combined, cuts)
    ensures Spec.FragmentsConcatenate(fragments, combined, cuts)
  {
    reveal Core.FragmentsConcatenate();
    reveal Spec.FragmentsConcatenate();
  }

  lemma ObservationEntryFragmentsEq(
    observations: seq<Core.InputObservation>
  )
    ensures Spec.ObservationEntryFragments(
              ToSpecObservations(observations)
            ) ==
            ToSpecEntryFragments(Core.ObservationEntryFragments(observations))
  {
    assert |Spec.ObservationEntryFragments(
        ToSpecObservations(observations)
      )| == |observations|;
    assert |ToSpecEntryFragments(
        Core.ObservationEntryFragments(observations)
      )| == |observations|;
    forall i: nat | i < |observations|
      ensures Spec.ObservationEntryFragments(
                ToSpecObservations(observations)
              )[i] ==
              ToSpecEntryFragments(
                Core.ObservationEntryFragments(observations)
              )[i]
    {
    }
  }

  lemma ObservationErrorFragmentsEq(
    observations: seq<Core.InputObservation>
  )
    ensures Spec.ObservationErrorFragments(
              ToSpecObservations(observations)
            ) == Core.ObservationErrorFragments(observations)
  {
    assert |Spec.ObservationErrorFragments(
        ToSpecObservations(observations)
      )| == |observations|;
    assert |Core.ObservationErrorFragments(observations)| ==
           |observations|;
    forall i: nat | i < |observations|
      ensures Spec.ObservationErrorFragments(
                ToSpecObservations(observations)
              )[i] == Core.ObservationErrorFragments(observations)[i]
    {
    }
  }

  lemma FailedObservationsEq(
    observations: seq<Core.InputObservation>
  )
    ensures Spec.HasFailedObservation(ToSpecObservations(observations)) ==
            Core.HasFailedObservation(observations)
  {
    reveal Spec.HasFailedObservation();
    reveal Core.HasFailedObservation();
    if exists i: nat ::
        i < |ToSpecObservations(observations)| &&
        ToSpecObservations(observations)[i].failed {
      var i: nat :|
        i < |ToSpecObservations(observations)| &&
        ToSpecObservations(observations)[i].failed;
      assert i < |observations|;
      assert ToSpecObservations(observations)[i].failed ==
             observations[i].failed;
    }
    if exists i: nat ::
        i < |observations| && observations[i].failed {
      var i: nat :| i < |observations| && observations[i].failed;
      assert i < |ToSpecObservations(observations)|;
      assert ToSpecObservations(observations)[i].failed ==
             observations[i].failed;
    }
  }

  lemma InputTraceWitnessRefines(
    cmd: Schema.WcCmd,
    preFs: BW.FileSystem,
    preStdin: BW.Bytes,
    postStdin: BW.Bytes,
    observations: seq<Core.InputObservation>,
    entries: seq<Core.Entry>,
    entryCuts: seq<nat>,
    errorOutput: BW.Bytes,
    errorCuts: seq<nat>,
    hadError: bool
  )
    requires Core.InputTraceWitnessRelation(
               cmd,
               preFs,
               preStdin,
               |cmd.inputs|,
               postStdin,
               observations,
               entries,
               entryCuts,
               errorOutput,
               errorCuts,
               hadError
             )
    ensures Spec.OrderedTraceWitnessRelation(
              cmd,
              preFs,
              preStdin,
              postStdin,
              Core.ToSpecEntries(entries),
              errorOutput,
              hadError,
              ToSpecObservations(observations),
              entryCuts,
              errorCuts
            )
  {
    reveal Core.InputTraceWitnessRelation();
    reveal Spec.OrderedTraceWitnessRelation();
    assert |ToSpecObservations(observations)| == |cmd.inputs|;
    assert forall i: nat | i < |ToSpecObservations(observations)| ::
        Spec.InputObservationRelation(
          cmd,
          preFs,
          preStdin,
          i,
          ToSpecObservations(observations)[i]
        ) by {
      forall i: nat | i < |ToSpecObservations(observations)|
        ensures Spec.InputObservationRelation(
                  cmd,
                  preFs,
                  preStdin,
                  i,
                  ToSpecObservations(observations)[i]
                )
      {
        InputObservationRefines(
          cmd, preFs, preStdin, i, observations[i]
        );
      }
    }
    EntryFragmentsRefine(
      Core.ObservationEntryFragments(observations),
      entries,
      entryCuts
    );
    ObservationEntryFragmentsEq(observations);
    FragmentsRefine(
      Core.ObservationErrorFragments(observations),
      errorOutput,
      errorCuts
    );
    ObservationErrorFragmentsEq(observations);
    FailedObservationsEq(observations);
    assert (exists i: nat ::
              i < |cmd.inputs| && Core.IsStdinInput(cmd.inputs[i])) ==
           (exists i: nat ::
              i < |cmd.inputs| && Spec.IsStdinInput(cmd.inputs[i])) by {
      if exists i: nat ::
          i < |cmd.inputs| && Core.IsStdinInput(cmd.inputs[i]) {
        var i: nat :|
          i < |cmd.inputs| && Core.IsStdinInput(cmd.inputs[i]);
        IsStdinInputEq(cmd.inputs[i]);
      }
      if exists i: nat ::
          i < |cmd.inputs| && Spec.IsStdinInput(cmd.inputs[i]) {
        var i: nat :|
          i < |cmd.inputs| && Spec.IsStdinInput(cmd.inputs[i]);
        IsStdinInputEq(cmd.inputs[i]);
      }
    }
  }

  twostate lemma CoreSummaryImpliesSpec(raw: Schema.WcCmdRaw, io: BenchIO.IO, exit: int)
    requires Core.CoreSummary(raw, io, exit)
    ensures Spec.Spec(raw, io, exit)
  {
    reveal Core.CoreSummary();
    reveal Spec.Spec();
    CommandEq(raw);
    var cmd := Core.Command(raw);
    if cmd.mode == Schema.ModeHelp {
    } else if cmd.mode == Schema.ModeVersion {
    } else {
      var
        observations: seq<Core.InputObservation>,
        coreEntries: seq<Core.Entry>,
        entryCuts: seq<nat>,
        errorOutput: BW.Bytes,
        errorCuts: seq<nat>,
        hadError: bool
        :|
        Core.InputTraceWitnessRelation(
          cmd,
          old(io.fs()),
          old(io.stdin()),
          |cmd.inputs|,
          io.stdin(),
          observations,
          coreEntries,
          entryCuts,
          errorOutput,
          errorCuts,
          hadError
        ) &&
        io.stdout() ==
        old(io.stdout()) +
        Core.RunOutputFromEntriesCore(cmd, coreEntries) &&
        io.stderr() == old(io.stderr()) + errorOutput &&
        exit == (if hadError then 1 else 0);
      InputTraceWitnessRefines(
        cmd,
        old(io.fs()),
        old(io.stdin()),
        io.stdin(),
        observations,
        coreEntries,
        entryCuts,
        errorOutput,
        errorCuts,
        hadError
      );
      reveal Spec.InputTraceRelation();
      assert Spec.InputTraceRelation(
          cmd,
          old(io.fs()),
          old(io.stdin()),
          io.stdin(),
          Core.ToSpecEntries(coreEntries),
          errorOutput,
          hadError
        );
      assert Core.EntriesNonnegative(coreEntries);
      RunOutputRelationForCore(cmd, coreEntries);
      var entries := Core.ToSpecEntries(coreEntries);
      var outputPart := Core.RunOutputFromEntriesCore(cmd, coreEntries);
      assert exists
          specEntries: seq<Spec.Entry>,
          specOutputPart: BW.Bytes,
          specErrorOutput: BW.Bytes,
          specHadError: bool
          ::
            specEntries == entries &&
            specOutputPart == outputPart &&
            specErrorOutput == errorOutput &&
            specHadError == hadError &&
            Spec.InputTraceRelation(
              cmd,
              old(io.fs()),
              old(io.stdin()),
              io.stdin(),
              specEntries,
              specErrorOutput,
              specHadError
            ) &&
            Spec.OutputRelation(cmd, specEntries, specOutputPart) &&
            io.stdout() ==
            old(io.stdout()) + specOutputPart &&
            io.stderr() == old(io.stderr()) + specErrorOutput &&
            exit == (if specHadError then 1 else 0);
    }
  }
}
