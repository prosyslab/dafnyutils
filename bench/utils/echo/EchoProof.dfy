include "../../core/World.dfy"
include "EchoSchema.dfy"
include "EchoCore.dfy"
include "EchoSpec.dfy"

module EchoProof {
  import BenchIO
  import Utf8 = Utf8Semantics
  import BW = BenchWorld
  import Schema = EchoSchema
  import Core = EchoCore
  import Spec = EchoSpec

  ghost function ShiftCuts(cuts: seq<nat>, delta: nat): seq<nat>
    ensures |ShiftCuts(cuts, delta)| == |cuts|
    decreases |cuts|
  {
    if |cuts| == 0 then
      []
    else
      [delta + cuts[0]] + ShiftCuts(cuts[1..], delta)
  }

  lemma ShiftCutsLength(cuts: seq<nat>, delta: nat)
    ensures |ShiftCuts(cuts, delta)| == |cuts|
    decreases |cuts|
  {
    if |cuts| > 0 {
      ShiftCutsLength(cuts[1..], delta);
    }
  }

  lemma ShiftCutsIndex(cuts: seq<nat>, delta: nat, i: nat)
    requires i < |cuts|
    ensures ShiftCuts(cuts, delta)[i] == delta + cuts[i]
    decreases |cuts|
  {
    if i > 0 {
      ShiftCutsIndex(cuts[1..], delta, i - 1);
    }
  }

  lemma OctalSpanCountFunctional(
    text: string, start: nat, first: nat, second: nat, limit: nat
  )
    requires Spec.OctalSpan(text, start, first, limit)
    requires Spec.OctalSpan(text, start, second, limit)
    ensures first == second
  {
    if first < second {
      assert first < limit;
      assert start + first < |text|;
      assert BW.IsOctalDigit(text[start + first]);
    } else if second < first {
      assert second < limit;
      assert start + second < |text|;
      assert BW.IsOctalDigit(text[start + second]);
    }
  }

  lemma EscapeUnitFunctional(
    text: string,
    lo: nat,
    firstHi: nat,
    firstPiece: BW.Bytes,
    firstStopped: bool,
    secondHi: nat,
    secondPiece: BW.Bytes,
    secondStopped: bool
  )
    requires Spec.EscapeUnitRelation(
               text, lo, firstHi, firstPiece, firstStopped
             )
    requires Spec.EscapeUnitRelation(
               text, lo, secondHi, secondPiece, secondStopped
             )
    ensures firstHi == secondHi
    ensures firstPiece == secondPiece
    ensures firstStopped == secondStopped
  {
    if text[lo] == '\\' && lo + 1 < |text| {
      var e := text[lo + 1];
      if e == '0' {
        var firstCount: nat :|
          Spec.OctalSpan(text, lo + 2, firstCount, 3) &&
          firstHi == lo + 2 + firstCount;
        var secondCount: nat :|
          Spec.OctalSpan(text, lo + 2, secondCount, 3) &&
          secondHi == lo + 2 + secondCount;
        OctalSpanCountFunctional(text, lo + 2, firstCount, secondCount, 3);
      } else if BW.IsOctalDigit(e) {
        var firstCount: nat :|
          1 <= firstCount <= 3 &&
          Spec.OctalSpan(text, lo + 1, firstCount, 3) &&
          firstHi == lo + 1 + firstCount;
        var secondCount: nat :|
          1 <= secondCount <= 3 &&
          Spec.OctalSpan(text, lo + 1, secondCount, 3) &&
          secondHi == lo + 1 + secondCount;
        OctalSpanCountFunctional(text, lo + 1, firstCount, secondCount, 3);
      }
    }
  }

  lemma EscapeUnitBounds(
    text: string, lo: nat, hi: nat, piece: BW.Bytes, stopped: bool
  )
    requires Spec.EscapeUnitRelation(text, lo, hi, piece, stopped)
    ensures lo < hi <= |text|
    ensures stopped ==> piece == []
  {
    reveal Spec.EscapeUnitRelation();
  }

  lemma AppendShiftedSlice(
    left: BW.Bytes, right: BW.Bytes, lo: nat, hi: nat
  )
    requires lo <= hi <= |right|
    ensures (left + right)[|left| + lo..|left| + hi] == right[lo..hi]
  {
  }

  lemma ParseOctalAfterZeroSatisfiesSpan(text: string, start: nat)
    requires start <= |text|
    ensures exists count: nat ::
              Spec.OctalSpan(text, start, count, 3) &&
              Core.ParseOctalAfterZero(text, start).next == start + count &&
              Core.ParseOctalAfterZero(text, start).value ==
              Spec.OctalSpanValue(text, start, count)
  {
    if start >= |text| || !BW.IsOctalDigit(text[start]) {
      assert Spec.OctalSpan(text, start, 0, 3);
    } else if start + 1 >= |text| || !BW.IsOctalDigit(text[start + 1]) {
      assert Spec.OctalSpan(text, start, 1, 3);
    } else if start + 2 >= |text| || !BW.IsOctalDigit(text[start + 2]) {
      assert Spec.OctalSpan(text, start, 2, 3);
    } else {
      assert Spec.OctalSpan(text, start, 3, 3);
    }
  }

  lemma ParseOctalInitialSatisfiesSpan(text: string, start: nat)
    requires start < |text|
    requires BW.IsOctalDigit(text[start])
    ensures exists count: nat ::
              1 <= count <= 3 &&
              Spec.OctalSpan(text, start, count, 3) &&
              Core.ParseOctalDigits(
                text, start + 1, BW.CharToDigit(text[start]), 1
              ).next == start + count &&
              Core.ParseOctalDigits(
                text, start + 1, BW.CharToDigit(text[start]), 1
              ).value == Spec.OctalSpanValue(text, start, count)
  {
    if start + 1 >= |text| || !BW.IsOctalDigit(text[start + 1]) {
      assert Spec.OctalSpan(text, start, 1, 3);
    } else if start + 2 >= |text| || !BW.IsOctalDigit(text[start + 2]) {
      assert Spec.OctalSpan(text, start, 2, 3);
    } else {
      assert Spec.OctalSpan(text, start, 3, 3);
    }
  }

  lemma CoreEscapeStepSatisfiesUnit(text: string, lo: nat)
    requires lo < |text|
    ensures exists hi: nat, piece: BW.Bytes, stopped: bool ::
              Spec.EscapeUnitRelation(text, lo, hi, piece, stopped) &&
              if stopped then
                Core.RenderEscaped(text, lo) == Core.RenderResult(piece, true)
              else
                Core.RenderEscaped(text, lo).out ==
                piece + Core.RenderEscaped(text, hi).out &&
                Core.RenderEscaped(text, lo).stopped ==
                Core.RenderEscaped(text, hi).stopped
  {
    if text[lo] != '\\' || lo + 1 >= |text| {
      assert Spec.EscapeUnitRelation(
          text, lo, lo + 1, Utf8.EncodeChar(text[lo]), false
        );
      assert Core.RenderEscaped(text, lo).out ==
             Utf8.EncodeChar(text[lo]) + Core.RenderEscaped(text, lo + 1).out;
    } else {
      var e := text[lo + 1];
      if e == 'c' {
        assert Spec.EscapeUnitRelation(text, lo, lo + 2, [], true);
        assert Core.RenderEscaped(text, lo) == Core.RenderResult([], true);
      } else if e == 'a' || e == 'b' || e == 'e' || e == 'f' ||
                e == 'n' || e == 'r' || e == 't' || e == 'v' || e == '\\' {
        var piece :=
          if e == 'a' then [(7 as char)]
          else if e == 'b' then [(8 as char)]
          else if e == 'e' then [(27 as char)]
          else if e == 'f' then [(12 as char)]
          else if e == 'n' then [(10 as char)]
          else if e == 'r' then [(13 as char)]
          else if e == 't' then [(9 as char)]
          else if e == 'v' then [(11 as char)]
          else ['\\'];
        assert Spec.EscapeUnitRelation(text, lo, lo + 2, piece, false);
        assert Core.RenderEscaped(text, lo).out ==
               piece + Core.RenderEscaped(text, lo + 2).out;
      } else if e == 'x' {
        if lo + 2 < |text| {
          IsHexDigitEq(text[lo + 2]);
        }
        if lo + 2 < |text| && Core.IsHexDigit(text[lo + 2]) {
          assert Spec.IsHexDigit(text[lo + 2]);
          HexValueEq(text[lo + 2]);
          if lo + 3 < |text| {
            IsHexDigitEq(text[lo + 3]);
            if Core.IsHexDigit(text[lo + 3]) {
              assert Spec.IsHexDigit(text[lo + 3]);
              HexValueEq(text[lo + 3]);
            }
          }
          var parsed := Core.ParseHex(text, lo + 2);
          var count :=
            if lo + 3 < |text| && Spec.IsHexDigit(text[lo + 3]) then 2 else 1;
          assert parsed.next == lo + 2 + count;
          assert Spec.EscapeUnitRelation(
              text, lo, parsed.next, [(parsed.value % 256) as char], false
            );
        } else {
          assert Spec.EscapeUnitRelation(
              text, lo, lo + 2, ['\\', 'x'], false
            );
          assert Core.RenderEscaped(text, lo).out ==
                 ['\\', 'x'] + Core.RenderEscaped(text, lo + 2).out;
        }
      } else if e == '0' {
        ParseOctalAfterZeroSatisfiesSpan(text, lo + 2);
        var count: nat :|
          Spec.OctalSpan(text, lo + 2, count, 3) &&
          Core.ParseOctalAfterZero(text, lo + 2).next == lo + 2 + count &&
          Core.ParseOctalAfterZero(text, lo + 2).value ==
          Spec.OctalSpanValue(text, lo + 2, count);
        var parsed := Core.ParseOctalAfterZero(text, lo + 2);
        assert Spec.EscapeUnitRelation(
            text, lo, parsed.next, [(parsed.value % 256) as char], false
          );
      } else if BW.IsOctalDigit(e) {
        ParseOctalInitialSatisfiesSpan(text, lo + 1);
        var count: nat :|
          1 <= count <= 3 &&
          Spec.OctalSpan(text, lo + 1, count, 3) &&
          Core.ParseOctalDigits(
            text, lo + 2, BW.CharToDigit(e), 1
          ).next == lo + 1 + count &&
          Core.ParseOctalDigits(
            text, lo + 2, BW.CharToDigit(e), 1
          ).value == Spec.OctalSpanValue(text, lo + 1, count);
        var parsed := Core.ParseOctalDigits(
          text, lo + 2, BW.CharToDigit(e), 1
        );
        assert Spec.EscapeUnitRelation(
            text, lo, parsed.next, [(parsed.value % 256) as char], false
          );
      } else {
        assert Spec.EscapeUnitRelation(
            text, lo, lo + 2, ['\\'] + Utf8.EncodeChar(e), false
          );
        assert Core.RenderEscaped(text, lo).out ==
               ['\\'] + Utf8.EncodeChar(e) + Core.RenderEscaped(text, lo + 2).out;
      }
    }
  }

  lemma EscapedPartitionElement(
    text: string,
    start: nat,
    out: BW.Bytes,
    stopped: bool,
    inputCuts: seq<nat>,
    outputCuts: seq<nat>,
    i: nat
  )
    requires Spec.EscapedPartition(
               text, start, out, stopped, inputCuts, outputCuts
             )
    requires i + 1 < |inputCuts|
    ensures inputCuts[i] < inputCuts[i + 1] <= |text|
    ensures outputCuts[i] <= outputCuts[i + 1] <= |out|
    ensures Spec.EscapeUnitRelation(
              text,
              inputCuts[i],
              inputCuts[i + 1],
              out[outputCuts[i]..outputCuts[i + 1]],
              stopped && i + 2 == |inputCuts|
            )
  {
    reveal Spec.EscapedPartition();
  }

  lemma RenderEscapedSatisfiesPartition(text: string, start: nat)
    requires start <= |text|
    ensures exists inputCuts: seq<nat>, outputCuts: seq<nat> ::
              Spec.EscapedPartition(
                text,
                start,
                Core.RenderEscaped(text, start).out,
                Core.RenderEscaped(text, start).stopped,
                inputCuts,
                outputCuts
              )
    decreases |text| - start
  {
    if start == |text| {
      assert Core.RenderEscaped(text, start) == Core.RenderResult([], false);
      var inputCuts: seq<nat> := [start];
      var outputCuts: seq<nat> := [0];
      assert Spec.EscapedPartition(
          text, start, [], false, inputCuts, outputCuts
        );
      assert exists ic: seq<nat>, oc: seq<nat> ::
          Spec.EscapedPartition(text, start, [], false, ic, oc);
      return;
    }

    CoreEscapeStepSatisfiesUnit(text, start);
    var hi: nat, piece: BW.Bytes, unitStopped: bool :|
      Spec.EscapeUnitRelation(text, start, hi, piece, unitStopped) &&
      if unitStopped then
        Core.RenderEscaped(text, start) == Core.RenderResult(piece, true)
      else
        Core.RenderEscaped(text, start).out ==
        piece + Core.RenderEscaped(text, hi).out &&
        Core.RenderEscaped(text, start).stopped ==
        Core.RenderEscaped(text, hi).stopped;
    EscapeUnitBounds(text, start, hi, piece, unitStopped);
    if unitStopped {
      assert piece == [];
      var inputCuts: seq<nat> := [start, hi];
      var outputCuts: seq<nat> := [0, 0];
      assert Spec.EscapedPartition(
          text, start, piece, true, inputCuts, outputCuts
        );
    } else {
      RenderEscapedSatisfiesPartition(text, hi);
      var tailInputCuts: seq<nat>, tailOutputCuts: seq<nat> :|
        Spec.EscapedPartition(
          text,
          hi,
          Core.RenderEscaped(text, hi).out,
          Core.RenderEscaped(text, hi).stopped,
          tailInputCuts,
          tailOutputCuts
        );
      var rest := Core.RenderEscaped(text, hi).out;
      var out := piece + rest;
      var inputCuts := [start] + tailInputCuts;
      var shiftedTailCuts := ShiftCuts(tailOutputCuts, |piece|);
      ShiftCutsLength(tailOutputCuts, |piece|);
      var outputCuts := [0] + shiftedTailCuts;
      reveal Spec.EscapedPartition();
      assert tailInputCuts[0] == hi;
      assert tailOutputCuts[0] == 0;
      assert 0 < |tailOutputCuts|;
      assert start < hi <= |text|;
      assert |piece| <= |out|;
      assert |out| == |piece| + |rest|;
      assert |inputCuts| == |outputCuts|;
      assert inputCuts[0] == start;
      assert outputCuts[0] == 0;
      assert inputCuts[|inputCuts| - 1] ==
             tailInputCuts[|tailInputCuts| - 1];
      ShiftCutsIndex(
        tailOutputCuts, |piece|, |tailOutputCuts| - 1
      );
      assert tailOutputCuts[|tailOutputCuts| - 1] == |rest|;
      assert outputCuts[|outputCuts| - 1] == |out|;
      if !Core.RenderEscaped(text, start).stopped {
        assert !Core.RenderEscaped(text, hi).stopped;
        reveal Spec.EscapedPartition();
        assert tailInputCuts[|tailInputCuts| - 1] == |text|;
        assert inputCuts[|inputCuts| - 1] == |text|;
      } else {
        assert Core.RenderEscaped(text, hi).stopped;
        reveal Spec.EscapedPartition();
        assert 1 < |tailInputCuts|;
        assert 1 < |inputCuts|;
      }
      forall i
        {:trigger inputCuts[i], inputCuts[i + 1]}
        {:trigger out[outputCuts[i]..outputCuts[i + 1]]} |
        0 <= i && i + 1 < |inputCuts|
        ensures inputCuts[i] < inputCuts[i + 1] <= |text| &&
                outputCuts[i] <= outputCuts[i + 1] <= |out| &&
                Spec.EscapeUnitRelation(
                  text,
                  inputCuts[i],
                  inputCuts[i + 1],
                  out[outputCuts[i]..outputCuts[i + 1]],
                  Core.RenderEscaped(text, start).stopped &&
                  i + 2 == |inputCuts|
                )
      {
        if i == 0 {
          ShiftCutsIndex(tailOutputCuts, |piece|, 0);
          assert inputCuts[0] == start;
          assert inputCuts[1] == hi;
          assert outputCuts[0] == 0;
          assert outputCuts[1] == |piece|;
          assert out[0..|piece|] == piece;
          assert inputCuts[0] < inputCuts[1] <= |text|;
          assert outputCuts[0] <= outputCuts[1] <= |out|;
          if i + 2 == |inputCuts| {
            assert |tailInputCuts| == 1;
            assert !Core.RenderEscaped(text, hi).stopped;
            assert !Core.RenderEscaped(text, start).stopped;
          }
          assert !(Core.RenderEscaped(text, start).stopped &&
                   i + 2 == |inputCuts|);
          assert Spec.EscapeUnitRelation(
              text,
              inputCuts[i],
              inputCuts[i + 1],
              out[outputCuts[i]..outputCuts[i + 1]],
              Core.RenderEscaped(text, start).stopped &&
              i + 2 == |inputCuts|
            );
        } else {
          var j := i - 1;
          ShiftCutsIndex(tailOutputCuts, |piece|, j);
          ShiftCutsIndex(tailOutputCuts, |piece|, j + 1);
          EscapedPartitionElement(
            text,
            hi,
            rest,
            Core.RenderEscaped(text, hi).stopped,
            tailInputCuts,
            tailOutputCuts,
            j
          );
          assert inputCuts[i] < inputCuts[i + 1] <= |text|;
          assert inputCuts[i] == tailInputCuts[j];
          assert inputCuts[i + 1] == tailInputCuts[j + 1];
          assert outputCuts[i] == |piece| + tailOutputCuts[j];
          assert outputCuts[i + 1] == |piece| + tailOutputCuts[j + 1];
          assert outputCuts[i] <= outputCuts[i + 1] <= |out|;
          AppendShiftedSlice(
            piece, rest, tailOutputCuts[j], tailOutputCuts[j + 1]
          );
          assert out[outputCuts[i]..outputCuts[i + 1]] ==
                 rest[tailOutputCuts[j]..tailOutputCuts[j + 1]];
          assert (i + 2 == |inputCuts|) ==
                 (j + 2 == |tailInputCuts|);
          assert Core.RenderEscaped(text, start).stopped ==
                 Core.RenderEscaped(text, hi).stopped;
          assert Spec.EscapeUnitRelation(
              text,
              inputCuts[i],
              inputCuts[i + 1],
              out[outputCuts[i]..outputCuts[i + 1]],
              Core.RenderEscaped(text, start).stopped &&
              i + 2 == |inputCuts|
            );
        }
      }
      assert Spec.EscapedPartition(
          text,
          start,
          out,
          Core.RenderEscaped(text, start).stopped,
          inputCuts,
          outputCuts
        );
    }
  }

  lemma RenderEscapedSatisfiesRelation(text: string)
    ensures Spec.EscapedStringRelation(
              text, Core.RenderEscaped(text, 0).out, Core.RenderEscaped(text, 0).stopped
            )
  {
    RenderEscapedSatisfiesPartition(text, 0);
  }

  lemma ArgumentSatisfiesRelation(text: string, escapes: bool)
    ensures Spec.ArgumentRelation(
              text,
              escapes,
              Core.RenderArg(text, escapes).out,
              Core.RenderArg(text, escapes).stopped
            )
  {
    if escapes {
      RenderEscapedSatisfiesRelation(text);
    }
  }

  lemma OperandPartitionElement(
    args: seq<string>,
    escapes: bool,
    out: BW.Bytes,
    stopped: bool,
    count: nat,
    pieces: seq<BW.Bytes>,
    cuts: seq<nat>,
    i: nat
  )
    requires Spec.OperandPartition(
               args, escapes, out, stopped, count, pieces, cuts
             )
    requires i < count
    ensures cuts[i] <= cuts[i + 1] <= |out|
    ensures Spec.ArgumentRelation(
              args[i], escapes, pieces[i], stopped && i + 1 == count
            )
    ensures out[cuts[i]..cuts[i + 1]] ==
            pieces[i] + (if i + 1 < count then [' '] else [])
  {
    reveal Spec.OperandPartition();
  }

  lemma RenderOperandsSatisfiesRelation(args: seq<string>, escapes: bool)
    ensures Spec.OperandRelation(
              args,
              escapes,
              Core.RenderOperands(args, escapes).out,
              Core.RenderOperands(args, escapes).stopped
            )
    decreases |args|
  {
    if |args| == 0 {
      var pieces: seq<BW.Bytes> := [];
      var cuts: seq<nat> := [0];
      assert Spec.OperandPartition(
          args, escapes, [], false, 0, pieces, cuts
        );
      return;
    }

    var first := Core.RenderArg(args[0], escapes);
    ArgumentSatisfiesRelation(args[0], escapes);
    if first.stopped {
      var pieces := [first.out];
      var cuts: seq<nat> := [0, |first.out|];
      assert Spec.OperandPartition(
          args, escapes, first.out, true, 1, pieces, cuts
        );
    } else if |args| == 1 {
      var pieces := [first.out];
      var cuts: seq<nat> := [0, |first.out|];
      assert Core.RenderOperands(args, escapes) ==
             Core.RenderResult(first.out, false);
      assert Spec.OperandPartition(
          args, escapes, first.out, false, 1, pieces, cuts
        );
      assert exists count: nat, ps: seq<BW.Bytes>, cs: seq<nat> ::
          Spec.OperandPartition(
            args, escapes, first.out, false, count, ps, cs
          );
    } else {
      var tail := args[1..];
      RenderOperandsSatisfiesRelation(tail, escapes);
      var rest := Core.RenderOperands(tail, escapes);
      var tailCount: nat, tailPieces: seq<BW.Bytes>, tailCuts: seq<nat> :|
        Spec.OperandPartition(
          tail,
          escapes,
          rest.out,
          rest.stopped,
          tailCount,
          tailPieces,
          tailCuts
        );
      reveal Spec.OperandPartition();
      assert 0 < tailCount;
      var out := first.out + [' '] + rest.out;
      var count := tailCount + 1;
      var pieces := [first.out] + tailPieces;
      var shiftedTailCuts := ShiftCuts(
        tailCuts, |first.out| + 1
      );
      ShiftCutsLength(tailCuts, |first.out| + 1);
      var cuts := [0] + shiftedTailCuts;
      assert |pieces| == count;
      assert |cuts| == count + 1;
      assert cuts[0] == 0;
      ShiftCutsIndex(tailCuts, |first.out| + 1, |tailCuts| - 1);
      assert tailCuts[tailCount] == |rest.out|;
      assert cuts[count] == |out|;
      // Argument facts mention no cuts, so they need their own instantiation terms.
      forall i
        {:trigger cuts[i], cuts[i + 1]}
        {:trigger out[cuts[i]..cuts[i + 1]]}
        {:trigger args[i], pieces[i]} | 0 <= i < count
        ensures cuts[i] <= cuts[i + 1] <= |out| &&
                Spec.ArgumentRelation(
                  args[i], escapes, pieces[i], rest.stopped && i + 1 == count
                ) &&
                out[cuts[i]..cuts[i + 1]] ==
                pieces[i] + (if i + 1 < count then [' '] else [])
      {
        if i == 0 {
          ShiftCutsIndex(tailCuts, |first.out| + 1, 0);
          assert cuts[0] == 0;
          assert cuts[1] == |first.out| + 1;
          assert out[cuts[0]..cuts[1]] == first.out + [' '];
          assert !(rest.stopped && i + 1 == count);
          assert Spec.ArgumentRelation(
              args[i], escapes, pieces[i],
              rest.stopped && i + 1 == count
            );
          assert cuts[i] <= cuts[i + 1] <= |out|;
          assert out[cuts[i]..cuts[i + 1]] ==
                 pieces[i] + (if i + 1 < count then [' '] else []);
        } else {
          var j := i - 1;
          ShiftCutsIndex(tailCuts, |first.out| + 1, j);
          ShiftCutsIndex(tailCuts, |first.out| + 1, j + 1);
          OperandPartitionElement(
            tail,
            escapes,
            rest.out,
            rest.stopped,
            tailCount,
            tailPieces,
            tailCuts,
            j
          );
          assert args[i] == tail[j];
          assert pieces[i] == tailPieces[j];
          assert cuts[i] == |first.out| + 1 + tailCuts[j];
          assert cuts[i + 1] == |first.out| + 1 + tailCuts[j + 1];
          AppendShiftedSlice(
            first.out + [' '],
            rest.out,
            tailCuts[j],
            tailCuts[j + 1]
          );
          assert out[cuts[i]..cuts[i + 1]] ==
                 rest.out[tailCuts[j]..tailCuts[j + 1]];
          assert (i + 1 == count) == (j + 1 == tailCount);
          assert cuts[i] <= cuts[i + 1] <= |out|;
          assert Spec.ArgumentRelation(
              args[i], escapes, pieces[i],
              rest.stopped && i + 1 == count
            );
          assert out[cuts[i]..cuts[i + 1]] ==
                 pieces[i] + (if i + 1 < count then [' '] else []);
        }
      }
      assert Spec.OperandPartition(
          args, escapes, out, rest.stopped, count, pieces, cuts
        );
    }
  }

  ghost predicate ProcessedNoNewline(
    args: seq<string>, argIndex: nat, charIndex: nat, noNewline: bool
  )
    requires argIndex < |args|
    requires 1 <= charIndex <= |args[argIndex]|
  {
    noNewline ==
    (exists i ::
       0 <= i <= argIndex &&
       exists j ::
         1 <= j < |args[i]| &&
         (i < argIndex || j < charIndex) &&
         args[i][j] == 'n')
  }

  ghost predicate ProcessedEscapeState(
    args: seq<string>, argIndex: nat, charIndex: nat, enabled: bool
  )
    requires argIndex < |args|
    requires 1 <= charIndex <= |args[argIndex]|
  {
    enabled ==
    (exists i ::
       0 <= i <= argIndex &&
       exists j ::
         1 <= j < |args[i]| &&
         (i < argIndex || j < charIndex) &&
         args[i][j] == 'e' &&
         forall k ::
           0 <= k <= argIndex ==>
             forall l ::
               1 <= l < |args[k]| &&
               (k < argIndex || l < charIndex) &&
               (i < k || (i == k && j < l)) ==>
                 args[k][l] != 'e' && args[k][l] != 'E')
  }

  lemma {:isolate_assertions} ProcessedEndGivesPrefixState(
    args: seq<string>,
    argIndex: nat,
    noNewline: bool,
    enabled: bool
  )
    requires argIndex < |args|
    requires 1 <= |args[argIndex]|
    requires ProcessedNoNewline(
               args, argIndex, |args[argIndex]|, noNewline
             )
    requires ProcessedEscapeState(
               args, argIndex, |args[argIndex]|, enabled
             )
    ensures Spec.NoNewlineInPrefix(args, argIndex + 1, noNewline)
    ensures Spec.LastEscapeOptionEnables(args, argIndex + 1, enabled)
  {
  }

  lemma ApplyEchoOptionCharsSatisfiesProcessedState(
    args: seq<string>,
    argIndex: nat,
    charIndex: nat,
    noNewline: bool,
    doV9: bool
  )
    requires argIndex < |args|
    requires 1 <= charIndex <= |args[argIndex]|
    requires ProcessedNoNewline(args, argIndex, charIndex, noNewline)
    requires ProcessedEscapeState(args, argIndex, charIndex, doV9)
    ensures ProcessedNoNewline(
              args,
              argIndex,
              |args[argIndex]|,
              Core.ApplyEchoOptionChars(
                args[argIndex], charIndex, noNewline, doV9
              ).0
            )
    ensures ProcessedEscapeState(
              args,
              argIndex,
              |args[argIndex]|,
              Core.ApplyEchoOptionChars(
                args[argIndex], charIndex, noNewline, doV9
              ).1
            )
    decreases |args[argIndex]| - charIndex
  {
    if charIndex < |args[argIndex]| {
      var c := args[argIndex][charIndex];
      var nextNoNewline :=
        if c == 'n' then true else noNewline;
      var nextDoV9 :=
        if c == 'e' then true
        else if c == 'E' then false
        else doV9;
      assert ProcessedNoNewline(
          args, argIndex, charIndex + 1, nextNoNewline
        );
      assert ProcessedEscapeState(
          args, argIndex, charIndex + 1, nextDoV9
        );
      ApplyEchoOptionCharsSatisfiesProcessedState(
        args, argIndex, charIndex + 1, nextNoNewline, nextDoV9
      );
    }
  }

  lemma {:isolate_assertions} {:vcs_split_on_every_assert}
    ScanOptionsSatisfiesRelations(
    args: seq<string>,
    i: nat,
    noNewline: bool,
    doV9: bool
  )
    requires i <= |args|
    requires forall j :: 0 <= j < i ==> Spec.OptionToken(args[j])
    requires Spec.NoNewlineInPrefix(args, i, noNewline)
    requires Spec.LastEscapeOptionEnables(args, i, doV9)
    ensures Spec.MaximalOptionPrefix(
              args, Core.ScanOptions(args, i, noNewline, doV9).next
            )
    ensures Spec.NoNewlineInPrefix(
              args,
              Core.ScanOptions(args, i, noNewline, doV9).next,
              Core.ScanOptions(args, i, noNewline, doV9).noNewline
            )
    ensures Spec.LastEscapeOptionEnables(
              args,
              Core.ScanOptions(args, i, noNewline, doV9).next,
              Core.ScanOptions(args, i, noNewline, doV9).doV9
            )
    decreases |args| - i
  {
    if i == |args| {
    } else {
      OptionTokenEq(args[i]);
      if !Core.IsEchoOptionToken(args[i]) {
      } else {
        assert Spec.OptionToken(args[i]);
        assert 1 < |args[i]|;
        assert ProcessedNoNewline(args, i, 1, noNewline);
        assert ProcessedEscapeState(args, i, 1, doV9);
        ApplyEchoOptionCharsSatisfiesProcessedState(
          args, i, 1, noNewline, doV9
        );
        var next := Core.ApplyEchoOptionChars(
          args[i], 1, noNewline, doV9
        );
        ProcessedEndGivesPrefixState(args, i, next.0, next.1);
        assert forall j :: 0 <= j < i + 1 ==> Spec.OptionToken(args[j]);
        ScanOptionsSatisfiesRelations(args, i + 1, next.0, next.1);
      }
    }
  }

  lemma AllValidEchoOptionCharsQuantified(token: string, i: nat)
    requires i <= |token|
    ensures Core.AllValidEchoOptionChars(token, i) ==
            (forall j :: i <= j < |token| ==> Spec.ValidEchoOptionChar(token[j]))
    decreases |token| - i
  {
    if i < |token| {
      AllValidEchoOptionCharsQuantified(token, i + 1);
      if Core.ValidEchoOptionChar(token[i]) &&
         Core.AllValidEchoOptionChars(token, i + 1) {
        assert forall j :: i <= j < |token| ==>
                             Spec.ValidEchoOptionChar(token[j]) by {
          forall j | i <= j < |token|
            ensures Spec.ValidEchoOptionChar(token[j])
          {
            if j == i {
              assert Core.ValidEchoOptionChar(token[i]);
            } else {
              assert i + 1 <= j < |token|;
              assert Spec.ValidEchoOptionChar(token[j]);
            }
          }
        }
      }
    }
  }

  lemma OptionTokenEq(token: string)
    ensures Core.IsEchoOptionToken(token) == Spec.OptionToken(token)
  {
    if |token| > 1 && token[0] == '-' {
      AllValidEchoOptionCharsQuantified(token, 1);
    }
  }

  lemma MaximalOptionPrefixFunctional(
    args: seq<string>, first: nat, second: nat
  )
    requires Spec.MaximalOptionPrefix(args, first)
    requires Spec.MaximalOptionPrefix(args, second)
    ensures first == second
  {
    if first < second {
      assert Spec.OptionToken(args[first]);
    } else if second < first {
      assert Spec.OptionToken(args[second]);
    }
  }

  lemma CommandSatisfiesRelation(
    raw: Schema.EchoCmdRaw, posixlyCorrect: bool
  )
    ensures Spec.CommandRelation(
              raw,
              posixlyCorrect,
              if Core.Command(raw, posixlyCorrect).mode == Core.ModeHelp then
                Spec.ModeHelp
              else if Core.Command(raw, posixlyCorrect).mode == Core.ModeVersion then
                Spec.ModeVersion
              else
                Spec.ModeRun,
              Core.Command(raw, posixlyCorrect).noNewline,
              Core.Command(raw, posixlyCorrect).escapes,
              Core.Command(raw, posixlyCorrect).operands
            )
  {
    var args := raw.args;
    var allowOptions := !posixlyCorrect || (|args| > 0 && args[0] == "-n");
    if allowOptions && |args| == 1 && args[0] == "--help" {
    } else if allowOptions && |args| == 1 && args[0] == "--version" {
    } else if allowOptions {
      assert Spec.NoNewlineInPrefix(args, 0, false);
      assert Spec.LastEscapeOptionEnables(args, 0, false);
      ScanOptionsSatisfiesRelations(args, 0, false, false);
      var scanned := Core.ScanOptions(args, 0, false, false);
      assert Spec.CommandRelation(
          raw,
          posixlyCorrect,
          Spec.ModeRun,
          scanned.noNewline,
          scanned.doV9 || posixlyCorrect,
          args[scanned.next..]
        );
    }
  }

  lemma OutputSatisfiesRelation(
    raw: Schema.EchoCmdRaw, posixlyCorrect: bool
  )
    ensures Spec.OutputRelation(
              raw, posixlyCorrect, Core.Output(raw, posixlyCorrect)
            )
  {
    CommandSatisfiesRelation(raw, posixlyCorrect);
    var cmd := Core.Command(raw, posixlyCorrect);
    if cmd.mode == Core.ModeRun {
      RenderOperandsSatisfiesRelation(cmd.operands, cmd.escapes);
    }
  }

  twostate lemma CoreSummaryImpliesSpec(
    raw: Schema.EchoCmdRaw, io: BenchIO.IO, exit: int
  )
    requires Core.CoreSummary(raw, io, exit)
    ensures Spec.Spec(raw, io, exit)
  {
    OutputSatisfiesRelation(
      raw, Spec.PosixlyCorrect(old(io.env()))
    );
  }

  lemma IsHexDigitEq(c: char)
    ensures Core.IsHexDigit(c) == Spec.IsHexDigit(c)
  {
  }

  lemma HexValueEq(c: char)
    requires Core.IsHexDigit(c)
    requires Spec.IsHexDigit(c)
    ensures Core.HexValue(c) == Spec.HexValue(c)
  {
  }

}
