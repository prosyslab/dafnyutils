include "../../core/World.dfy"
include "CsplitSchema.dfy"
include "CsplitCore.dfy"
include "CsplitSpec.dfy"

module CsplitProof {
  import BenchIO
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

  lemma DigitCharEq(d: nat)
    requires d < 10
    ensures Core.DigitChar(d) == Schema.DigitChar(d)
  {
  }

  lemma DigitsNatEq(n: nat)
    ensures Core.DigitsNat(n) == Schema.DigitsNat(n)
    decreases n
  {
    if n < 10 {
      DigitCharEq(n);
    } else {
      DigitsNatEq(n / 10);
      DigitCharEq(n % 10);
    }
  }

  lemma CountLineEq(n: nat)
    ensures Core.CountLine(n) == Spec.CountLine(n)
  {
    DigitsNatEq(n);
  }

  lemma OutputNameEq(index: nat)
    ensures Core.OutputName(index) == Spec.OutputName(index)
  {
    DigitsNatEq(index);
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

  ghost predicate SplitFromRelation(
    data: BenchWorld.Bytes,
    lines: seq<nat>,
    start: nat,
    plan: Spec.SplitPlan
  )
  {
    match plan
    case SplitComplete(pieces) =>
      exists cuts: seq<nat> ::
        |cuts| == |lines| + 2 &&
        |pieces| == |lines| + 1 &&
        cuts[0] == start &&
        cuts[|cuts| - 1] == |data| &&
        (forall i :: 0 <= i < |lines| ==>
                       Spec.LineCutRelation(data, lines[i], cuts[i + 1]) &&
                       cuts[i + 1] < |data|) &&
        (forall i {:trigger cuts[i]} :: 0 <= i < |pieces| ==>
                                          cuts[i] <= cuts[i + 1] <= |data| &&
                                          pieces[i] == data[cuts[i]..cuts[i + 1]])
    case SplitOutOfRange(pieces, line) =>
      exists failed: nat, cuts: seq<nat> ::
        failed < |lines| &&
        line == lines[failed] &&
        |cuts| == failed + 2 &&
        |pieces| == failed + 1 &&
        cuts[0] == start &&
        cuts[|cuts| - 1] == |data| &&
        (forall i :: 0 <= i <= failed ==>
                       Spec.LineCutRelation(data, lines[i], cuts[i + 1])) &&
        (forall i {:trigger cuts[i + 1]} ::
           0 <= i < failed ==> cuts[i + 1] < |data|) &&
        (forall i {:trigger cuts[i]} :: 0 <= i < |pieces| ==>
                                          cuts[i] <= cuts[i + 1] <= |data| &&
                                          pieces[i] == data[cuts[i]..cuts[i + 1]])
  }

  lemma TailIndex<T>(values: seq<T>, index: nat)
    requires index + 1 < |values|
    ensures values[1..][index] == values[index + 1]
  {
  }

  ghost predicate PiecesFromCuts(
    data: BenchWorld.Bytes,
    pieces: seq<BenchWorld.Bytes>,
    cuts: seq<nat>
  )
  {
    |cuts| == |pieces| + 1 &&
    (forall i {:trigger cuts[i]} :: 0 <= i < |pieces| ==>
       cuts[i] <= cuts[i + 1] <= |data| &&
       pieces[i] == data[cuts[i]..cuts[i + 1]])
  }

  lemma SplitOutOfRangeWitness(
    data: BenchWorld.Bytes,
    lines: seq<nat>,
    start: nat,
    pieces: seq<BenchWorld.Bytes>,
    line: nat,
    failed: nat,
    cuts: seq<nat>
  )
    requires failed < |lines|
    requires line == lines[failed]
    requires |cuts| == failed + 2
    requires |pieces| == failed + 1
    requires cuts[0] == start
    requires cuts[|cuts| - 1] == |data|
    requires forall i :: 0 <= i <= failed ==>
                           Spec.LineCutRelation(data, lines[i], cuts[i + 1])
    requires forall i {:trigger cuts[i + 1]} ::
               0 <= i < failed ==> cuts[i + 1] < |data|
    requires PiecesFromCuts(data, pieces, cuts)
    ensures SplitFromRelation(
              data,
              lines,
              start,
              Spec.SplitOutOfRange(pieces, line)
            )
  {
    reveal SplitFromRelation();
    reveal PiecesFromCuts();
  }

  lemma PrependCutBounds(
    start: nat,
    tailCuts: seq<nat>,
    failed: nat,
    dataLength: nat
  )
    requires |tailCuts| == failed + 2
    requires tailCuts[0] < dataLength
    requires forall i {:trigger tailCuts[i + 1]} ::
               0 <= i < failed ==> tailCuts[i + 1] < dataLength
    ensures forall i {:trigger ([start] + tailCuts)[i + 1]} ::
              0 <= i < failed + 1 ==>
                ([start] + tailCuts)[i + 1] < dataLength
  {
    forall i {:trigger ([start] + tailCuts)[i + 1]} |
      0 <= i < failed + 1
      ensures ([start] + tailCuts)[i + 1] < dataLength
    {
      if i == 0 {
      } else {
        var j := i - 1;
        assert ([start] + tailCuts)[i + 1] == tailCuts[i];
        assert 0 <= j < failed;
        assert tailCuts[j + 1] < dataLength;
        assert j + 1 == i;
      }
    }
  }

  lemma {:isolate_assertions} SplitPlanFromRefines(
    data: BenchWorld.Bytes,
    lines: seq<nat>,
    start: nat
  )
    requires start <= |data|
    requires forall i :: 0 <= i < |lines| ==>
                           lines[i] > 0 && (i == 0 || lines[i - 1] <= lines[i])
    requires |lines| > 0 ==> start <= Core.LineStart(data, lines[0])
    ensures SplitFromRelation(
              data,
              lines,
              start,
              SplitPlanView(Core.SplitPlanFrom(data, lines, start))
            )
    decreases |lines|
  {
    if |lines| == 0 {
      var cuts := [start, |data|];
      assert Core.SafeSlice(data, start, |data|) == data[start..|data|];
      assert SplitFromRelation(
          data,
          lines,
          start,
          Spec.SplitComplete([data[start..|data|]])
        );
    } else {
      var next := Core.LineStart(data, lines[0]);
      LineStartRefines(data, lines[0]);
      if !Core.LineExists(data, lines[0]) {
        assert next == |data|;
        var cuts := [start, next];
        assert Core.SafeSlice(data, start, next) == data[start..next];
        assert SplitFromRelation(
            data,
            lines,
            start,
            Spec.SplitOutOfRange([data[start..next]], lines[0])
          );
      } else {
        assert next < |data|;
        if |lines| > 1 {
          LineStartMonotone(data, lines[0], lines[1]);
        }
        assert forall i :: 0 <= i < |lines[1..]| ==>
                             lines[1..][i] > 0 &&
                             (i == 0 || lines[1..][i - 1] <= lines[1..][i]);
        SplitPlanFromRefines(data, lines[1..], next);
        var tail := Core.SplitPlanFrom(data, lines[1..], next);
        match tail
        case SplitComplete(tailPieces) =>
          var tailCuts: seq<nat> :| |tailCuts| == |lines[1..]| + 2 &&
                                    |tailPieces| == |lines[1..]| + 1 &&
                                    tailCuts[0] == next &&
                                    tailCuts[|tailCuts| - 1] == |data| &&
                                    (forall i :: 0 <= i < |lines[1..]| ==>
                                                   Spec.LineCutRelation(data, lines[1..][i], tailCuts[i + 1]) &&
                                                   tailCuts[i + 1] < |data|) &&
                                    (forall i {:trigger tailCuts[i]} :: 0 <= i < |tailPieces| ==>
                                                                          tailCuts[i] <= tailCuts[i + 1] <= |data| &&
                                                                          tailPieces[i] == data[tailCuts[i]..tailCuts[i + 1]]);
          var cuts := [start] + tailCuts;
          assert |cuts| == |lines| + 2;
          assert |[data[start..next]] + tailPieces| == |lines| + 1;
          assert forall i :: 0 <= i < |lines| ==>
                               Spec.LineCutRelation(data, lines[i], cuts[i + 1]) &&
                               cuts[i + 1] < |data| by {
            forall i | 0 <= i < |lines|
              ensures Spec.LineCutRelation(data, lines[i], cuts[i + 1]) &&
                      cuts[i + 1] < |data|
            {
              if i == 0 {
              } else {
                assert lines[i] == lines[1..][i - 1];
                assert cuts[i + 1] == tailCuts[i];
              }
            }
          }
          assert forall i {:trigger cuts[i]} ::
              0 <= i < |[data[start..next]] + tailPieces| ==>
                cuts[i] <= cuts[i + 1] <= |data| &&
                ([data[start..next]] + tailPieces)[i] ==
                data[cuts[i]..cuts[i + 1]] by {
            forall i {:trigger cuts[i]} |
          0 <= i < |[data[start..next]] + tailPieces|
              ensures cuts[i] <= cuts[i + 1] <= |data| &&
                      ([data[start..next]] + tailPieces)[i] ==
                      data[cuts[i]..cuts[i + 1]]
            {
              if i == 0 {
                assert cuts[0] == start;
                assert cuts[1] == tailCuts[0];
                assert tailCuts[0] == next;
                assert ([data[start..next]] + tailPieces)[0] ==
                       data[start..next];
              } else {
                var j := i - 1;
                assert 0 <= j < |tailPieces|;
                assert cuts[i] == tailCuts[j];
                assert cuts[i + 1] == tailCuts[j + 1];
                assert ([data[start..next]] + tailPieces)[i] ==
                       tailPieces[j];
                assert tailPieces[j] ==
                       data[tailCuts[j]..tailCuts[j + 1]];
              }
            }
          }
          assert SplitFromRelation(
              data,
              lines,
              start,
              Spec.SplitComplete([data[start..next]] + tailPieces)
            );
        case SplitOutOfRange(tailPieces, line) =>
          var failed: nat, tailCuts: seq<nat> :| failed < |lines[1..]| &&
                                                 line == lines[1..][failed] &&
                                                 |tailCuts| == failed + 2 &&
                                                 |tailPieces| == failed + 1 &&
                                                 tailCuts[0] == next &&
                                                 tailCuts[|tailCuts| - 1] == |data| &&
                                                 (forall i :: 0 <= i <= failed ==>
                                                                Spec.LineCutRelation(data, lines[1..][i], tailCuts[i + 1])) &&
                                                 (forall i {:trigger tailCuts[i + 1]} ::
                                                    0 <= i < failed ==> tailCuts[i + 1] < |data|) &&
                                                 (forall i {:trigger tailCuts[i]} :: 0 <= i < |tailPieces| ==>
                                                                                       tailCuts[i] <= tailCuts[i + 1] <= |data| &&
                                                                                       tailPieces[i] == data[tailCuts[i]..tailCuts[i + 1]]);
          var cuts := [start] + tailCuts;
          var fullFailed := failed + 1;
          assert fullFailed < |lines|;
          TailIndex(lines, failed);
          assert line == lines[fullFailed];
          assert |cuts| == fullFailed + 2;
          assert |[data[start..next]] + tailPieces| == fullFailed + 1;
          assert forall i :: 0 <= i <= fullFailed ==>
                               Spec.LineCutRelation(data, lines[i], cuts[i + 1]) by {
            forall i | 0 <= i <= fullFailed
              ensures Spec.LineCutRelation(data, lines[i], cuts[i + 1])
            {
              if i == 0 {
              } else {
                assert lines[i] == lines[1..][i - 1];
                assert cuts[i + 1] == tailCuts[i];
              }
            }
          }
          PrependCutBounds(start, tailCuts, failed, |data|);
          assert forall i {:trigger cuts[i]} ::
              0 <= i < |[data[start..next]] + tailPieces| ==>
                cuts[i] <= cuts[i + 1] <= |data| &&
                ([data[start..next]] + tailPieces)[i] ==
                data[cuts[i]..cuts[i + 1]] by {
            forall i {:trigger cuts[i]} |
          0 <= i < |[data[start..next]] + tailPieces|
              ensures cuts[i] <= cuts[i + 1] <= |data| &&
                      ([data[start..next]] + tailPieces)[i] ==
                      data[cuts[i]..cuts[i + 1]]
            {
              if i == 0 {
              } else {
                assert cuts[i] == tailCuts[i - 1];
                assert cuts[i + 1] == tailCuts[i];
              }
            }
          }
          assert PiecesFromCuts(
              data,
              [data[start..next]] + tailPieces,
              cuts
            ) by {
            reveal PiecesFromCuts();
          }
          SplitOutOfRangeWitness(
            data,
            lines,
            start,
            [data[start..next]] + tailPieces,
            line,
            fullFailed,
            cuts
          );
          assert SplitFromRelation(
              data,
              lines,
              start,
              Spec.SplitOutOfRange([data[start..next]] + tailPieces, line)
            );
      }
    }
  }

  lemma SplitPlanRefines(data: BenchWorld.Bytes, lines: seq<nat>)
    requires Spec.ValidNumberPrefix(lines, |lines|)
    ensures Spec.SplitPlanRelation(
              data,
              lines,
              SplitPlanView(Core.SplitPlanFor(data, lines))
            )
  {
    reveal Spec.ValidNumberPrefix();
    SplitPlanFromRefines(data, lines, 0);
    reveal SplitFromRelation();
    reveal Spec.PiecePartitionRelation();
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

  lemma DuplicateWarningsFromRefines(
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
            assert ([head] + tailFragments)[i] == tailFragments[i - 1];
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
      assert WarningsFromWitnessRelation(
          lines,
          previous,
          hasPrevious,
          Core.DuplicateWarningsFrom(lines, previous, hasPrevious),
          [head] + tailFragments,
          cuts
        );
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

  lemma {:isolate_assertions} PrependWriteAttempt(
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
    requires IOContract.WriteFileContractFields(
               preFs,
               preNow,
               Spec.OutputName(index),
               pieces[0],
               headOk,
               headErr,
               afterHeadFs
             )
    requires Spec.WriteAttemptsRelation(
               pieces[1..],
               index + 1,
               count,
               afterHeadFs,
               preNow,
               tailStates,
               tailOks,
               tailErrs
             )
    ensures Spec.WriteAttemptsRelation(
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
    reveal Spec.WriteAttemptsRelation();
    forall i | 0 <= i < count + 1
      ensures IOContract.WriteFileContractFields(
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
      } else {
        var j := i - 1;
        assert 0 <= j < count;
        assert pieces == [pieces[0]] + pieces[1..];
      }
    }
  }

  lemma {:isolate_assertions} AppendCleanup(
    index: nat,
    count: nat,
    preFs: BenchWorld.FileSystem,
    middleFs: BenchWorld.FileSystem,
    fs2: BenchWorld.FileSystem,
    states: seq<BenchWorld.FileSystem>,
    ok: bool,
    err: int
  )
    requires Spec.CleanupRelation(index + 1, count, preFs, middleFs, states)
    requires IOContract.DeletePathContractFields(
               middleFs, Spec.OutputName(index), ok, err, fs2
             )
    ensures Spec.CleanupRelation(
              index, count + 1, preFs, fs2, states + [fs2]
            )
  {
    reveal Spec.CleanupRelation();
    var priorOks, priorErrs :|
      Spec.CleanupWitnessRelation(
        index + 1, count, preFs, middleFs, states, priorOks, priorErrs
      );
    reveal Spec.CleanupWitnessRelation();
    var oks := priorOks + [ok];
    var errs := priorErrs + [err];
    forall i | 0 <= i < count + 1
      ensures
        IOContract.DeletePathContractFields(
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
        assert IOContract.DeletePathContractFields(
            (states + [fs2])[i],
            Spec.OutputName(index + count - i),
            oks[i],
            errs[i],
            (states + [fs2])[i + 1]
          );
      }
    }
    assert Spec.CleanupWitnessRelation(
        index, count + 1, preFs, fs2, states + [fs2], oks, errs
      );
    assert Spec.CleanupRelation(
        index, count + 1, preFs, fs2, states + [fs2]
      );
  }

  lemma EmptyCleanup(
    index: nat,
    fs: BenchWorld.FileSystem,
    states: seq<BenchWorld.FileSystem>
  )
    requires states == [fs]
    ensures Spec.CleanupRelation(index, 0, fs, fs, states)
  {
    var oks: seq<bool> := [];
    var errs: seq<int> := [];
    assert Spec.CleanupWitnessRelation(
        index, 0, fs, fs, states, oks, errs
      );
    assert Spec.CleanupRelation(index, 0, fs, fs, states);
  }

  lemma {:isolate_assertions} SingleWriteFailureRefines(
    pieces: seq<BenchWorld.Bytes>,
    index: nat,
    terminalError: BenchWorld.Bytes,
    hasTerminalError: bool,
    preFs: BenchWorld.FileSystem,
    preNow: int,
    afterWriteFs: BenchWorld.FileSystem,
    err: int
  )
    requires |pieces| > 0
    requires IOContract.WriteFileContractFields(
               preFs,
               preNow,
               Spec.OutputName(index),
               pieces[0],
               false,
               err,
               afterWriteFs
             )
    ensures Spec.WriteTraceRelation(
              pieces,
              index,
              terminalError,
              hasTerminalError,
              preFs,
              preNow,
              afterWriteFs,
              [],
              Spec.WriteErrorMessage(Spec.OutputName(index), err),
              1
            )
  {
    var writeStates := [preFs, afterWriteFs];
    var writeOk := [false];
    var writeErr := [err];
    var cleanupStates := [afterWriteFs];
    assert Spec.WriteAttemptsRelation(
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
    EmptyCleanup(index, afterWriteFs, cleanupStates);
    assert Spec.WriteTraceWitnessRelation(
        pieces,
        index,
        terminalError,
        hasTerminalError,
        preFs,
        preNow,
        afterWriteFs,
        [],
        Spec.WriteErrorMessage(Spec.OutputName(index), err),
        1,
        1,
        writeStates,
        writeOk,
        writeErr,
        cleanupStates
      );
    assert Spec.WriteTraceRelation(
        pieces,
        index,
        terminalError,
        hasTerminalError,
        preFs,
        preNow,
        afterWriteFs,
        [],
        Spec.WriteErrorMessage(Spec.OutputName(index), err),
        1
      ) by {
      reveal Spec.WriteTraceRelation();
    }
  }

  lemma WriteTraceWitnessGivesRelation(
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
    requires Spec.WriteTraceWitnessRelation(
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
    ensures Spec.WriteTraceRelation(
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

  lemma ExtractWriteTraceWitness(
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
    requires Spec.WriteTraceRelation(
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
    ensures Spec.WriteTraceWitnessRelation(
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
    reveal Spec.WriteTraceRelation();
    attempted, writeStates, writeOk, writeErr, cleanupStates :|
      Spec.WriteTraceWitnessRelation(
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

  lemma {:isolate_assertions} PrependSuccessfulWriteWitness(
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
    requires IOContract.WriteFileContractFields(
               preFs,
               preNow,
               Spec.OutputName(index),
               pieces[0],
               true,
               headErr,
               afterWriteFs
             )
    requires Spec.WriteTraceWitnessRelation(
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
               IOContract.DeletePathContractFields(
                 tailFs, Spec.OutputName(index), deleteOk, deleteErr, fs2
               )
             else
               fs2 == tailFs
    ensures Spec.WriteTraceRelation(
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
    reveal Spec.WriteTraceWitnessRelation();
    var writeStates := [preFs] + tailWriteStates;
    var writeOk := [true] + tailWriteOk;
    var writeErr := [headErr] + tailWriteErr;
    PrependWriteAttempt(
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
      PrependCountOutput(pieces[0], pieces[1..], attempted - 1, tailOut);
      AppendCleanup(
        index,
        attempted - 1,
        tailWriteStates[attempted],
        tailFs,
        fs2,
        tailCleanupStates,
        deleteOk,
        deleteErr
      );
      var cleanupStates := tailCleanupStates + [fs2];
      assert Spec.WriteTraceWitnessRelation(
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
      WriteTraceWitnessGivesRelation(
        pieces, index, terminalError, hasTerminalError, preFs, preNow,
        fs2, Spec.CountLine(|pieces[0]|) + tailOut, tailErr, tailExit,
        attempted + 1, writeStates, writeOk, writeErr, cleanupStates
      );
    } else {
      PrependCountOutput(pieces[0], pieces[1..], attempted, tailOut);
      if hasTerminalError {
        AppendCleanup(
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
        assert Spec.WriteTraceWitnessRelation(
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
        WriteTraceWitnessGivesRelation(
          pieces, index, terminalError, hasTerminalError, preFs, preNow,
          fs2, Spec.CountLine(|pieces[0]|) + tailOut, tailErr, tailExit,
          attempted + 1, writeStates, writeOk, writeErr, cleanupStates
        );
      } else {
        var cleanupStates := [fs2];
        assert Spec.WriteTraceWitnessRelation(
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
        WriteTraceWitnessGivesRelation(
          pieces, index, terminalError, hasTerminalError, preFs, preNow,
          fs2, Spec.CountLine(|pieces[0]|) + tailOut, tailErr, tailExit,
          attempted + 1, writeStates, writeOk, writeErr, cleanupStates
        );
      }
    }
  }

  lemma {:isolate_assertions} WriteTraceSummaryRefines(
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
    requires Core.WriteTraceSummaryFields(
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
    ensures Spec.WriteTraceRelation(
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
    OutputNameEq(index);
    if |pieces| == 0 {
      var writeStates := [preFs];
      var writeOk: seq<bool> := [];
      var writeErr: seq<int> := [];
      var cleanupStates := [preFs];
      assert Spec.WriteAttemptsRelation(
          pieces, index, 0, preFs, preNow, writeStates, writeOk, writeErr
        );
      EmptyCountOutput(pieces);
      EmptyCleanup(index, preFs, cleanupStates);
      assert Spec.WriteTraceWitnessRelation(
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
      WriteTraceWitnessGivesRelation(
        pieces, index, terminalError, hasTerminalError, preFs, preNow,
        fs2, stdout, stderr, exit, 0, writeStates, writeOk, writeErr,
        cleanupStates
      );
    } else {
      CountLineEq(|pieces[0]|);
      var afterWriteFs, ok, err :|
        IOContract.WriteFileContractFields(
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
            {:trigger Core.WriteTraceSummaryFields(
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
            Core.WriteTraceSummaryFields(
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
                   tailFs, Spec.OutputName(index), deleteOk, deleteErr, fs2
                 )
             else
               fs2 == tailFs) &&
            stdout == Spec.CountLine(|pieces[0]|) + tailOut &&
            stderr == tailErr &&
            exit == tailExit
        else
          fs2 == afterWriteFs &&
          stdout == [] &&
          stderr == Spec.WriteErrorMessage(Spec.OutputName(index), err) &&
          exit == 1;
      if !ok {
        SingleWriteFailureRefines(
          pieces,
          index,
          terminalError,
          hasTerminalError,
          preFs,
          preNow,
          afterWriteFs,
          err
        );
      } else {
        var tailFs, tailOut, tailErr, tailExit :|
          Core.WriteTraceSummaryFields(
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
                 tailFs, Spec.OutputName(index), deleteOk, deleteErr, fs2
               )
           else
             fs2 == tailFs) &&
          stdout == Spec.CountLine(|pieces[0]|) + tailOut &&
          stderr == tailErr &&
          exit == tailExit;
        WriteTraceSummaryRefines(
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
            tailCleanupStates := ExtractWriteTraceWitness(
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
            IOContract.DeletePathContractFields(
              tailFs, Spec.OutputName(index), deleteOk, deleteErr, fs2
            );
        } else {
          assert fs2 == tailFs;
        }
        PrependSuccessfulWriteWitness(
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

  lemma WritePiecesSummaryRefines(
    pieces: seq<BenchWorld.Bytes>,
    index: nat,
    preFs: BenchWorld.FileSystem,
    preNow: int,
    fs2: BenchWorld.FileSystem,
    stdout: BenchWorld.Bytes,
    stderr: BenchWorld.Bytes,
    exit: int
  )
    requires Core.WritePiecesSummaryFields(
               pieces, index, preFs, preNow, fs2, stdout, stderr, exit
             )
    ensures Spec.WritePiecesSummaryFields(
              pieces, index, preFs, preNow, fs2, stdout, stderr, exit
            )
  {
    WriteTraceSummaryRefines(
      pieces, index, [], false, preFs, preNow, fs2, stdout, stderr, exit
    );
  }

  lemma WritePiecesThenErrorSummaryRefines(
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
    requires Core.WritePiecesThenErrorSummaryFields(
               pieces, index, line, preFs, preNow, fs2, stdout, stderr, exit
             )
    ensures Spec.WritePiecesThenErrorSummaryFields(
              pieces, index, line, preFs, preNow, fs2, stdout, stderr, exit
            )
  {
    WriteTraceSummaryRefines(
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
    );
  }

  twostate lemma CoreSummaryImpliesSpec(raw: Schema.CsplitCmdRaw, io: BenchIO.IO, exit: int)
    requires Core.CoreSummary(raw, io, exit)
    ensures Spec.Spec(raw, io, exit)
  {
    if raw.mode == Schema.ModeHelp {
      assert Spec.Spec(raw, io, exit);
      return;
    }
    if raw.mode == Schema.ModeVersion {
      assert Spec.Spec(raw, io, exit);
      return;
    }

    match Spec.ReadResultFields(raw.input, old(io.fs()), old(io.stdin()))
    case Err(err) =>
      assert Spec.Spec(raw, io, exit);
    case Ok(data) =>
      AnalyzeNumbersRefines(raw.lineNumbers);
      var analysis := Core.AnalyzeNumbers(raw.lineNumbers);
      match analysis.status
      case NumberZero =>
        assert Spec.Spec(raw, io, exit) by {
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
        assert Spec.Spec(raw, io, exit) by {
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
            Core.WritePiecesThenErrorSummaryFields(
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
            io.stderr() == old(io.stderr()) + warnings + writeErr;
          WritePiecesThenErrorSummaryRefines(
            pieces,
            0,
            line,
            old(io.fs()),
            old(io.now()),
            io.fs(),
            writeOut,
            writeErr,
            exit
          );
          assert Spec.Spec(raw, io, exit) by {
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
            Core.WritePiecesSummaryFields(
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
            io.stderr() == old(io.stderr()) + warnings + writeErr;
          WritePiecesSummaryRefines(
            pieces,
            0,
            old(io.fs()),
            old(io.now()),
            io.fs(),
            writeOut,
            writeErr,
            exit
          );
          assert Spec.Spec(raw, io, exit) by {
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
}
