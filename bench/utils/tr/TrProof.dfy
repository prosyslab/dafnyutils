include "../../core/World.dfy"
include "TrSchema.dfy"
include "TrCore.dfy"
include "TrSpec.dfy"

module TrProof {
  import BenchIO
  import BW = BenchWorld
  import Schema = TrSchema
  import Core = TrCore
  import Spec = TrSpec

  ghost function ShiftIndices(indices: seq<nat>, delta: nat): seq<nat>
    ensures |ShiftIndices(indices, delta)| == |indices|
    decreases |indices|
  {
    if |indices| == 0 then
      []
    else
      [indices[0] + delta] + ShiftIndices(indices[1..], delta)
  }

  lemma ShiftIndicesIndex(indices: seq<nat>, delta: nat, i: nat)
    requires i < |indices|
    ensures ShiftIndices(indices, delta)[i] == indices[i] + delta
    decreases |indices|
  {
    if i > 0 {
      ShiftIndicesIndex(indices[1..], delta, i - 1);
    }
  }

  lemma AppendShiftedSlice(
    left: BW.Bytes, right: BW.Bytes, lo: nat, hi: nat
  )
    requires lo <= hi <= |right|
    ensures (left + right)[|left| + lo..|left| + hi] == right[lo..hi]
  {
  }

  lemma SplitSlice(bytes: BW.Bytes, lo: nat, mid: nat, hi: nat)
    requires lo <= mid <= hi <= |bytes|
    ensures bytes[lo..hi] == bytes[lo..mid] + bytes[mid..hi]
  {
  }

  function ToSpecMode(mode: Core.TrMode): Spec.TrMode
  {
    match mode
    case ModeRun => Spec.ModeRun
    case ModeHelp => Spec.ModeHelp
    case ModeVersion => Spec.ModeVersion
    case ModeMissingOperand(message) => Spec.ModeMissingOperand(message)
    case ModeExtraOperand(operand) => Spec.ModeExtraOperand(operand)
    case ModeUnsupportedSet(operand) => Spec.ModeUnsupportedSet(operand)
    case ModeEmptySet2 => Spec.ModeEmptySet2
  }

  function ToSpecCmd(cmd: Core.TrCmd): Spec.TrCmd
  {
    Spec.TrCmd(ToSpecMode(cmd.mode), cmd.deleteSet, cmd.squeeze, cmd.set1, cmd.set2, cmd.squeezeSet)
  }

  function ToSpecDecode(decoded: Core.SetDecode): Spec.SetDecode
  {
    match decoded
    case SetOk(bytes) => Spec.SetOk(bytes)
    case SetUnsupported(operand) => Spec.SetUnsupported(operand)
  }

  lemma IsAsciiEq(ch: char)
    ensures Core.IsAscii(ch) == Spec.IsAscii(ch)
  {
  }

  lemma IsSetSyntaxMarkerEq(ch: char)
    ensures Core.IsSetSyntaxMarker(ch) == Spec.IsSetSyntaxMarker(ch)
  {
  }

  // Core keeps its index recursion, so each bridge carries the suffix
  // generalisation the declarative specification needs.
  lemma {:induction false} ContainsPairFromEq(
      text: string, i: nat, first: char, second: char)
    requires i <= |text|
    ensures Core.ContainsPairFrom(text, i, first, second) ==
            Spec.ContainsPair(text[i..], first, second)
    decreases |text| - i
  {
    if i < |text| {
      var suf := text[i..];
      assert suf[1..] == text[i + 1..];
      ContainsPairFromEq(text, i + 1, first, second);
      if Core.ContainsPairFrom(text, i, first, second) {
        if i + 1 < |text| && text[i] == first && text[i + 1] == second {
          assert suf[0] == first && suf[1] == second;
        } else {
          var k :| 0 <= k < |suf[1..]| - 1 &&
                   suf[1..][k] == first && suf[1..][k + 1] == second;
          assert suf[k + 1] == first && suf[k + 2] == second;
        }
      }
      if Spec.ContainsPair(suf, first, second) {
        var k :| 0 <= k < |suf| - 1 && suf[k] == first && suf[k + 1] == second;
        if k != 0 {
          assert suf[1..][k - 1] == suf[k];
          assert suf[1..][k] == suf[k + 1];
        }
      }
    }
  }

  lemma {:induction false} ContainsCharFromEq(text: string, i: nat, target: char)
    requires i <= |text|
    ensures Core.ContainsCharFrom(text, i, target) == (target in text[i..])
    decreases |text| - i
  {
    if i < |text| {
      var suf := text[i..];
      assert suf[0] == text[i];
      assert suf[1..] == text[i + 1..];
      ContainsCharFromEq(text, i + 1, target);
      if target in suf && suf[0] != target {
        var k :| 0 <= k < |suf| && suf[k] == target;
        assert k != 0;
        assert suf[1..][k - 1] == suf[k];
      }
    }
  }

  lemma {:induction false} StartsUnsupportedConstructEq(text: string, i: nat)
    requires i <= |text|
    ensures Core.StartsUnsupportedConstruct(text, i) ==
            Spec.StartsUnsupportedConstruct(text[i..])
  {
    var suf := text[i..];
    if i < |text| {
      assert suf[0] == text[i];
      if i + 1 < |text| {
        assert suf[1] == text[i + 1];
        assert suf[2..] == text[i + 2..];
        ContainsPairFromEq(text, i + 2, ':', ']');
        ContainsPairFromEq(text, i + 2, '=', ']');
      }
      if i + 2 < |text| {
        assert suf[2] == text[i + 2];
        assert suf[3..] == text[i + 3..];
        ContainsCharFromEq(text, i + 3, ']');
      }
    }
  }

  lemma RangeExpansionFunctional(
    lo: char,
    hi: char,
    first: BW.Bytes,
    second: BW.Bytes
  )
    requires Spec.RangeExpansion(lo, hi, first)
    requires Spec.RangeExpansion(lo, hi, second)
    ensures first == second
  {
    assert |first| == |second|;
    assert forall i :: 0 <= i < |first| ==> first[i] == second[i] by {
      forall i | 0 <= i < |first|
        ensures first[i] == second[i]
      {
        assert first[i] as int == second[i] as int;
      }
    }
  }

  lemma RangeCharsSatisfiesExpansion(lo: char, hi: char)
    requires Core.IsAscii(lo)
    requires Core.IsAscii(hi)
    requires lo as int <= hi as int
    ensures Spec.RangeExpansion(lo, hi, Core.RangeChars(lo, hi))
    decreases (hi as int) - (lo as int)
  {
    IsAsciiEq(lo);
    IsAsciiEq(hi);
    if lo != hi {
      var next := ((lo as int) + 1) as char;
      RangeCharsSatisfiesExpansion(next, hi);
      assert forall i :: 0 <= i < |Core.RangeChars(lo, hi)| ==>
                           Core.RangeChars(lo, hi)[i] as int == lo as int + i by {
        forall i | 0 <= i < |Core.RangeChars(lo, hi)|
          ensures Core.RangeChars(lo, hi)[i] as int == lo as int + i
        {
          if i > 0 {
            assert Core.RangeChars(lo, hi)[i] ==
                   Core.RangeChars(next, hi)[i - 1];
          }
        }
      }
    }
  }

  lemma SetUnitMatchesCore(
    text: string, lo: nat, hi: nat, bytes: BW.Bytes
  )
    requires Spec.SetUnitRelation(text, lo, hi, bytes)
    ensures lo < hi <= |text|
    ensures if lo + 2 < |text| && text[lo + 1] == '-' then
              bytes == Core.RangeChars(text[lo], text[lo + 2])
            else
              bytes == [text[lo]]
  {
    reveal Spec.SetUnitRelation();
    if lo + 2 < |text| && text[lo + 1] == '-' {
      RangeCharsSatisfiesExpansion(text[lo], text[lo + 2]);
      RangeExpansionFunctional(
        text[lo], text[lo + 2], bytes,
        Core.RangeChars(text[lo], text[lo + 2])
      );
    }
  }

  lemma SetPartitionFromElement(
    text: string,
    start: nat,
    bytes: BW.Bytes,
    inputCuts: seq<nat>,
    outputCuts: seq<nat>,
    i: nat
  )
    requires Spec.SetPartitionFrom(
               text, start, bytes, inputCuts, outputCuts
             )
    requires i + 1 < |inputCuts|
    ensures inputCuts[i] < inputCuts[i + 1] <= |text|
    ensures outputCuts[i] <= outputCuts[i + 1] <= |bytes|
    ensures Spec.SetUnitRelation(
              text,
              inputCuts[i],
              inputCuts[i + 1],
              bytes[outputCuts[i]..outputCuts[i + 1]]
            )
  {
    reveal Spec.SetPartitionFrom();
  }

  lemma PrependSetUnitPartition(
    text: string,
    start: nat,
    next: nat,
    piece: BW.Bytes,
    rest: BW.Bytes,
    tailInputCuts: seq<nat>,
    tailOutputCuts: seq<nat>
  )
    requires Spec.SetUnitRelation(text, start, next, piece)
    requires Spec.SetPartitionFrom(
               text, next, rest, tailInputCuts, tailOutputCuts
             )
    ensures Spec.SetPartitionFrom(
              text,
              start,
              piece + rest,
              [start] + tailInputCuts,
              [0] + ShiftIndices(tailOutputCuts, |piece|)
            )
  {
    reveal Spec.SetPartitionFrom();
    var inputCuts := [start] + tailInputCuts;
    var outputCuts := [0] + ShiftIndices(tailOutputCuts, |piece|);
    assert tailInputCuts[0] == next;
    assert tailOutputCuts[0] == 0;
    assert |inputCuts| == |outputCuts|;
    ShiftIndicesIndex(
      tailOutputCuts, |piece|, |tailOutputCuts| - 1
    );
    assert outputCuts[|outputCuts| - 1] == |piece + rest|;
    assert forall i
        {:trigger inputCuts[i], inputCuts[i + 1]}
        {:trigger (piece + rest)[outputCuts[i]..outputCuts[i + 1]]} ::
        0 <= i && i + 1 < |inputCuts| ==>
          inputCuts[i] < inputCuts[i + 1] <= |text| &&
          outputCuts[i] <= outputCuts[i + 1] <= |piece + rest| &&
          Spec.SetUnitRelation(
            text,
            inputCuts[i],
            inputCuts[i + 1],
            (piece + rest)[outputCuts[i]..outputCuts[i + 1]]
          ) by {
      forall i {:trigger inputCuts[i]} |
    0 <= i && i + 1 < |inputCuts|
        ensures inputCuts[i] < inputCuts[i + 1] <= |text| &&
                outputCuts[i] <= outputCuts[i + 1] <= |piece + rest| &&
                Spec.SetUnitRelation(
                  text,
                  inputCuts[i],
                  inputCuts[i + 1],
                  (piece + rest)[outputCuts[i]..outputCuts[i + 1]]
                )
      {
        if i == 0 {
          ShiftIndicesIndex(tailOutputCuts, |piece|, 0);
          assert outputCuts[1] == |piece|;
          assert (piece + rest)[0..|piece|] == piece;
        } else {
          var j := i - 1;
          ShiftIndicesIndex(tailOutputCuts, |piece|, j);
          ShiftIndicesIndex(tailOutputCuts, |piece|, j + 1);
          SetPartitionFromElement(
            text, next, rest, tailInputCuts, tailOutputCuts, j
          );
          AppendShiftedSlice(
            piece, rest, tailOutputCuts[j], tailOutputCuts[j + 1]
          );
        }
      }
    }
  }

  lemma SetPartitionFromMatchesCore(
    text: string,
    start: nat,
    bytes: BW.Bytes,
    inputCuts: seq<nat>,
    outputCuts: seq<nat>,
    i: nat
  )
    requires Spec.SetPartitionFrom(
               text, start, bytes, inputCuts, outputCuts
             )
    requires i < |inputCuts|
    requires inputCuts[i] <= |text|
    requires outputCuts[i] <= |bytes|
    ensures Core.DecodeSetFrom(text, inputCuts[i]) ==
            Core.SetOk(bytes[outputCuts[i]..])
    decreases |inputCuts| - i
  {
    reveal Spec.SetPartitionFrom();
    if i + 1 == |inputCuts| {
      assert inputCuts[i] == |text|;
      assert outputCuts[i] == |bytes|;
    } else {
      SetPartitionFromElement(
        text, start, bytes, inputCuts, outputCuts, i
      );
      var lo := inputCuts[i];
      var hi := inputCuts[i + 1];
      var piece := bytes[outputCuts[i]..outputCuts[i + 1]];
      SetUnitMatchesCore(text, lo, hi, piece);
      StartsUnsupportedConstructEq(text, lo);
      IsSetSyntaxMarkerEq(text[lo]);
      SetPartitionFromMatchesCore(
        text, start, bytes, inputCuts, outputCuts, i + 1
      );
      SplitSlice(bytes, outputCuts[i], outputCuts[i + 1], |bytes|);
      assert bytes[outputCuts[i]..] ==
             piece + bytes[outputCuts[i + 1]..];
    }
  }

  lemma DecodeSetFromOkSatisfiesPartition(text: string, start: nat)
    requires start <= |text|
    requires Core.DecodeSetFrom(text, start).SetOk?
    ensures exists inputCuts: seq<nat>, outputCuts: seq<nat> ::
              Spec.SetPartitionFrom(
                text,
                start,
                Core.DecodeSetFrom(text, start).bytes,
                inputCuts,
                outputCuts
              )
    decreases |text| - start
  {
    if start == |text| {
      var inputCuts: seq<nat> := [start];
      var outputCuts: seq<nat> := [0];
      assert Spec.SetPartitionFrom(
          text, start, [], inputCuts, outputCuts
        );
    } else {
      StartsUnsupportedConstructEq(text, start);
      IsSetSyntaxMarkerEq(text[start]);
      if Core.StartsUnsupportedConstruct(text, start) ||
         Core.IsSetSyntaxMarker(text[start]) {
      } else if start + 2 < |text| && text[start + 1] == '-' {
        IsAsciiEq(text[start]);
        IsAsciiEq(text[start + 2]);
        if Core.IsAscii(text[start]) &&
           Core.IsAscii(text[start + 2]) &&
           text[start] as int <= text[start + 2] as int {
          var next := start + 3;
          var tail := Core.DecodeSetFrom(text, next);
          match tail
          case SetOk(rest) =>
            DecodeSetFromOkSatisfiesPartition(text, next);
            var tailInputCuts: seq<nat>, tailOutputCuts: seq<nat> :|
              Spec.SetPartitionFrom(
                text, next, rest, tailInputCuts, tailOutputCuts
              );
            var piece := Core.RangeChars(text[start], text[start + 2]);
            RangeCharsSatisfiesExpansion(text[start], text[start + 2]);
            assert Spec.SetUnitRelation(
                text, start, next, piece
              );
            PrependSetUnitPartition(
              text, start, next, piece, rest,
              tailInputCuts, tailOutputCuts
            );
          case SetUnsupported(_) =>
        }
      } else if !Core.IsAscii(text[start]) {
      } else {
        var next := start + 1;
        var tail := Core.DecodeSetFrom(text, next);
        match tail
        case SetOk(rest) =>
          DecodeSetFromOkSatisfiesPartition(text, next);
          var tailInputCuts: seq<nat>, tailOutputCuts: seq<nat> :|
            Spec.SetPartitionFrom(
              text, next, rest, tailInputCuts, tailOutputCuts
            );
          var piece := [text[start]];
          assert Spec.SetUnitRelation(text, start, next, piece);
          PrependSetUnitPartition(
            text, start, next, piece, rest,
            tailInputCuts, tailOutputCuts
          );
        case SetUnsupported(_) =>
      }
    }
  }

  lemma SetBytesRelationMatchesCore(text: string, bytes: BW.Bytes)
    requires Spec.SetBytesRelation(text, bytes)
    ensures Core.DecodeSet(text) == Core.SetOk(bytes)
  {
    var inputCuts: seq<nat>, outputCuts: seq<nat> :|
      Spec.SetPartition(text, bytes, inputCuts, outputCuts);
    reveal Spec.SetPartition();
    reveal Spec.SetPartitionFrom();
    assert inputCuts[0] == 0;
    assert outputCuts[0] == 0;
    SetPartitionFromMatchesCore(
      text, 0, bytes, inputCuts, outputCuts, 0
    );
  }

  lemma CoreDecodeSatisfiesRelation(text: string)
    ensures Spec.SetDecodeRelation(
              text, ToSpecDecode(Core.DecodeSet(text))
            )
  {
    match Core.DecodeSet(text)
    case SetOk(bytes) =>
      DecodeSetFromOkSatisfiesPartition(text, 0);
      var inputCuts: seq<nat>, outputCuts: seq<nat> :|
        Spec.SetPartitionFrom(
          text, 0, bytes, inputCuts, outputCuts
        );
      assert Spec.SetPartition(text, bytes, inputCuts, outputCuts);
      assert Spec.SetBytesRelation(text, bytes);
    case SetUnsupported(_) =>
      assert forall bytes: BW.Bytes ::
          !Spec.SetBytesRelation(text, bytes) by {
        forall bytes: BW.Bytes
          ensures !Spec.SetBytesRelation(text, bytes)
        {
          if Spec.SetBytesRelation(text, bytes) {
            SetBytesRelationMatchesCore(text, bytes);
          }
        }
      }
  }

  ghost function CoreDecodes(
    operands: seq<string>
  ): seq<Spec.SetDecode>
    ensures |CoreDecodes(operands)| == |operands|
    decreases |operands|
  {
    if |operands| == 0 then
      []
    else
      [ToSpecDecode(Core.DecodeSet(operands[0]))] +
      CoreDecodes(operands[1..])
  }

  lemma CoreDecodesIndex(operands: seq<string>, i: nat)
    requires i < |operands|
    ensures CoreDecodes(operands)[i] ==
            ToSpecDecode(Core.DecodeSet(operands[i]))
    decreases |operands|
  {
    if i > 0 {
      CoreDecodesIndex(operands[1..], i - 1);
    }
  }

  lemma CoreDecodesSatisfyRelation(operands: seq<string>)
    ensures Spec.DecodedOperandsRelation(
              operands, CoreDecodes(operands)
            )
    decreases |operands|
  {
    if |operands| > 0 {
      CoreDecodeSatisfiesRelation(operands[0]);
      CoreDecodesSatisfyRelation(operands[1..]);
      assert forall i :: 0 <= i < |operands| ==>
                           Spec.SetDecodeRelation(
                             operands[i], CoreDecodes(operands)[i]
                           ) by {
        forall i | 0 <= i < |operands|
          ensures Spec.SetDecodeRelation(
                    operands[i], CoreDecodes(operands)[i]
                  )
        {
          CoreDecodesIndex(operands, i);
          if i > 0 {
            assert operands[i] == operands[1..][i - 1];
            assert CoreDecodes(operands)[i] ==
                   CoreDecodes(operands[1..])[i - 1];
          }
        }
      }
    }
  }

  lemma CoreFirstUnsupportedSatisfiesRelation(
    operands: seq<string>
  )
    ensures Core.HasUnsupportedOperand(operands) == "" ==>
              !(exists operand ::
                  Spec.FirstUnsupportedOperandRelation(
                    operands, CoreDecodes(operands), operand
                  ))
    ensures Core.HasUnsupportedOperand(operands) != "" ==>
              Spec.FirstUnsupportedOperandRelation(
                operands,
                CoreDecodes(operands),
                Core.HasUnsupportedOperand(operands)
              )
    decreases |operands|
  {
    if |operands| > 0 {
      match Core.DecodeSet(operands[0])
      case SetOk(_) =>
        CoreFirstUnsupportedSatisfiesRelation(operands[1..]);
        if Core.HasUnsupportedOperand(operands[1..]) == "" {
          if exists operand ::
              Spec.FirstUnsupportedOperandRelation(
                operands, CoreDecodes(operands), operand
              ) {
            var operand: string :|
              Spec.FirstUnsupportedOperandRelation(
                operands, CoreDecodes(operands), operand
              );
            var i: int :|
              0 <= i < |operands| &&
              CoreDecodes(operands)[i] ==
              Spec.SetUnsupported(operands[i]) &&
              operand == operands[i] &&
              forall j :: 0 <= j < i ==>
                            CoreDecodes(operands)[j].SetOk?;
            if i > 0 {
              var tailIndex := i - 1;
              assert Spec.FirstUnsupportedOperandRelation(
                  operands[1..],
                  CoreDecodes(operands[1..]),
                  operand
                );
            }
          }
        } else {
          var operand := Core.HasUnsupportedOperand(operands[1..]);
          var tailIndex: int :|
            0 <= tailIndex < |operands[1..]| &&
            CoreDecodes(operands[1..])[tailIndex] ==
            Spec.SetUnsupported(operands[1..][tailIndex]) &&
            operand == operands[1..][tailIndex] &&
            forall j :: 0 <= j < tailIndex ==>
                          CoreDecodes(operands[1..])[j].SetOk?;
          var i := tailIndex + 1;
          assert forall j :: 0 <= j < i ==>
                               CoreDecodes(operands)[j].SetOk? by {
            forall j | 0 <= j < i
              ensures CoreDecodes(operands)[j].SetOk?
            {
              if j > 0 {
                assert CoreDecodes(operands)[j] ==
                       CoreDecodes(operands[1..])[j - 1];
              }
            }
          }
          assert Spec.FirstUnsupportedOperandRelation(
              operands, CoreDecodes(operands), operand
            );
        }
      case SetUnsupported(_) =>
        if operands[0] == "" {
          assert Core.DecodeSet(operands[0]) == Core.SetOk([]);
        }
        assert Spec.FirstUnsupportedOperandRelation(
            operands, CoreDecodes(operands), operands[0]
          );
    }
  }

  lemma DecodedBytesMatchesCore(text: string)
    ensures Spec.DecodedBytes(
              ToSpecDecode(Core.DecodeSet(text))
            ) == Core.SetBytes(text)
  {
  }

  lemma CoreCommandSatisfiesRelation(raw: Schema.TrCmdRaw)
    ensures Spec.CommandRelation(raw, ToSpecCmd(Core.Command(raw)))
  {
    var decoded := CoreDecodes(raw.operands);
    CoreDecodesSatisfyRelation(raw.operands);
    CoreFirstUnsupportedSatisfiesRelation(raw.operands);
    if |raw.operands| > 0 {
      CoreDecodesIndex(raw.operands, 0);
      DecodedBytesMatchesCore(raw.operands[0]);
    }
    if |raw.operands| > 1 {
      CoreDecodesIndex(raw.operands, 1);
      DecodedBytesMatchesCore(raw.operands[1]);
    }
    assert (exists operand ::
              Spec.FirstUnsupportedOperandRelation(
                raw.operands, decoded, operand
              )) == (Core.HasUnsupportedOperand(raw.operands) != "") by {
      if Core.HasUnsupportedOperand(raw.operands) == "" {
      } else {
        assert Spec.FirstUnsupportedOperandRelation(
            raw.operands,
            decoded,
            Core.HasUnsupportedOperand(raw.operands)
          );
      }
    }
    assert Spec.CommandDecodedRelation(
        raw, decoded, ToSpecCmd(Core.Command(raw))
      );
    assert Spec.CommandRelation(raw, ToSpecCmd(Core.Command(raw)));
  }

  lemma ContainsIffMembership(bytes: BW.Bytes, ch: char)
    ensures Core.Contains(bytes, ch) == (ch in bytes)
    decreases |bytes|
  {
    if |bytes| > 0 {
      ContainsIffMembership(bytes[1..], ch);
    }
  }

  lemma TranslateCandidateCharacterization(
    set1: BW.Bytes,
    set2: BW.Bytes,
    ch: char,
    candidate: char
  )
    requires |set2| > 0
    ensures ch !in set1 ==>
              Core.TranslateWithCandidate(set1, set2, ch, candidate) ==
              candidate
    ensures ch in set1 ==>
              exists i ::
                0 <= i < |set1| &&
                set1[i] == ch &&
                (forall j :: i < j < |set1| ==> set1[j] != ch) &&
                Core.TranslateWithCandidate(set1, set2, ch, candidate) ==
                set2[if i < |set2| then i else |set2| - 1]
    decreases |set1|
  {
    if |set1| > 0 {
      var tail1 := set1[1..];
      var tail2 := if |set2| > 1 then set2[1..] else set2;
      var nextCandidate := if set1[0] == ch then set2[0] else candidate;
      TranslateCandidateCharacterization(
        tail1, tail2, ch, nextCandidate
      );
      if ch in tail1 {
        var j: int :|
          0 <= j < |tail1| &&
          tail1[j] == ch &&
          (forall k :: j < k < |tail1| ==> tail1[k] != ch) &&
          Core.TranslateWithCandidate(
            tail1, tail2, ch, nextCandidate
          ) == tail2[if j < |tail2| then j else |tail2| - 1];
        var i := j + 1;
        assert set1[i] == ch;
        assert forall k :: i < k < |set1| ==> set1[k] != ch by {
          forall k | i < k < |set1|
            ensures set1[k] != ch
          {
            assert tail1[k - 1] != ch;
          }
        }
        if |set2| > 1 {
          if i < |set2| {
            assert j < |tail2|;
            assert tail2[j] == set2[i];
          } else {
            assert j >= |tail2|;
            assert tail2[|tail2| - 1] == set2[|set2| - 1];
          }
        } else {
          assert tail2 == set2;
        }
      } else if set1[0] == ch {
        assert Core.TranslateWithCandidate(
            tail1, tail2, ch, nextCandidate
          ) == set2[0];
        assert forall k :: 0 < k < |set1| ==> set1[k] != ch by {
          forall k | 0 < k < |set1|
            ensures set1[k] != ch
          {
            assert tail1[k - 1] != ch;
          }
        }
      }
    }
  }

  lemma CoreTranslationSatisfiesRelation(
    set1: BW.Bytes, set2: BW.Bytes, ch: char
  )
    requires |set2| > 0
    ensures Spec.TranslationRelation(
              set1, set2, ch, Core.TranslateWith(set1, set2, ch)
            )
  {
    TranslateCandidateCharacterization(set1, set2, ch, ch);
  }

  lemma ShiftIndicesStrictlyIncreasing(
    indices: seq<nat>, delta: nat
  )
    requires Spec.StrictlyIncreasing(indices)
    ensures Spec.StrictlyIncreasing(ShiftIndices(indices, delta))
  {
    reveal Spec.StrictlyIncreasing();
    assert forall i, j ::
        0 <= i < j < |ShiftIndices(indices, delta)| ==>
          ShiftIndices(indices, delta)[i] <
          ShiftIndices(indices, delta)[j] by {
      forall i, j |
        0 <= i < j < |ShiftIndices(indices, delta)|
        ensures ShiftIndices(indices, delta)[i] <
                ShiftIndices(indices, delta)[j]
      {
        ShiftIndicesIndex(indices, delta, i);
        ShiftIndicesIndex(indices, delta, j);
      }
    }
  }

  lemma ShiftIndicesMembership(
    indices: seq<nat>, value: nat
  )
    ensures (value in ShiftIndices(indices, 1)) ==
            (0 < value && value - 1 in indices)
    decreases |indices|
  {
    if |indices| > 0 {
      ShiftIndicesMembership(indices[1..], value);
    }
  }

  ghost function CoreKeptIndices(
    cmd: Core.TrCmd, input: BW.Bytes
  ): seq<nat>
    decreases |input|
  {
    if |input| == 0 then
      []
    else
      var tail := ShiftIndices(
                    CoreKeptIndices(cmd, input[1..]), 1
                  );
      if cmd.deleteSet && Core.Contains(cmd.set1, input[0]) then
        tail
      else
        [0] + tail
  }

  lemma CoreKeptIndicesProperties(
    cmd: Core.TrCmd, input: BW.Bytes
  )
    ensures Spec.StrictlyIncreasing(CoreKeptIndices(cmd, input))
    ensures forall k :: 0 <= k < |CoreKeptIndices(cmd, input)| ==>
                          CoreKeptIndices(cmd, input)[k] < |input|
    ensures forall i :: 0 <= i < |input| ==>
                          (i in CoreKeptIndices(cmd, input)) ==
                          (!cmd.deleteSet || input[i] !in cmd.set1)
    decreases |input|
  {
    if |input| > 0 {
      CoreKeptIndicesProperties(cmd, input[1..]);
      ContainsIffMembership(cmd.set1, input[0]);
      var tailIndices := CoreKeptIndices(cmd, input[1..]);
      var shifted := ShiftIndices(tailIndices, 1);
      ShiftIndicesStrictlyIncreasing(tailIndices, 1);
      assert forall k :: 0 <= k < |shifted| ==>
                           shifted[k] < |input| by {
        forall k | 0 <= k < |shifted|
          ensures shifted[k] < |input|
        {
          ShiftIndicesIndex(tailIndices, 1, k);
        }
      }
      assert forall i :: 0 <= i < |input| ==>
                           (i in shifted) ==
                           (0 < i &&
                            (!cmd.deleteSet || input[i] !in cmd.set1)) by {
        forall i | 0 <= i < |input|
          ensures (i in shifted) ==
                  (0 < i &&
                   (!cmd.deleteSet || input[i] !in cmd.set1))
        {
          ShiftIndicesMembership(tailIndices, i);
          if i > 0 {
            assert input[i] == input[1..][i - 1];
          }
        }
      }
      if cmd.deleteSet && Core.Contains(cmd.set1, input[0]) {
      } else {
        assert Spec.StrictlyIncreasing([0] + shifted);
      }
    }
  }

  lemma CoreDeleteOutputProperties(
    cmd: Core.TrCmd, input: BW.Bytes
  )
    ensures |Core.DeleteAndTranslate(cmd, input)| ==
            |CoreKeptIndices(cmd, input)|
    ensures forall k :: 0 <= k < |CoreKeptIndices(cmd, input)| ==>
                          CoreKeptIndices(cmd, input)[k] < |input|
    ensures forall k ::
              0 <= k < |CoreKeptIndices(cmd, input)| ==>
                (if cmd.deleteSet || |cmd.set2| == 0 then
                   Core.DeleteAndTranslate(cmd, input)[k] ==
                   input[CoreKeptIndices(cmd, input)[k]]
                 else
                   Spec.TranslationRelation(
                     cmd.set1,
                     cmd.set2,
                     input[CoreKeptIndices(cmd, input)[k]],
                     Core.DeleteAndTranslate(cmd, input)[k]
                   ))
    decreases |input|
  {
    CoreKeptIndicesProperties(cmd, input);
    if |input| > 0 {
      ContainsIffMembership(cmd.set1, input[0]);
      CoreDeleteOutputProperties(cmd, input[1..]);
      var tailIndices := CoreKeptIndices(cmd, input[1..]);
      if cmd.deleteSet && Core.Contains(cmd.set1, input[0]) {
        assert forall k ::
            0 <= k < |CoreKeptIndices(cmd, input)| ==>
              Core.DeleteAndTranslate(cmd, input)[k] ==
              input[CoreKeptIndices(cmd, input)[k]] by {
          forall k | 0 <= k < |CoreKeptIndices(cmd, input)|
            ensures Core.DeleteAndTranslate(cmd, input)[k] ==
                    input[CoreKeptIndices(cmd, input)[k]]
          {
            ShiftIndicesIndex(tailIndices, 1, k);
            assert CoreKeptIndices(cmd, input)[k] ==
                   tailIndices[k] + 1;
            assert input[CoreKeptIndices(cmd, input)[k]] ==
                   input[1..][tailIndices[k]];
          }
        }
      } else {
        if !cmd.deleteSet && |cmd.set2| > 0 {
          CoreTranslationSatisfiesRelation(
            cmd.set1, cmd.set2, input[0]
          );
        }
        assert forall k ::
            0 <= k < |CoreKeptIndices(cmd, input)| ==>
              (if cmd.deleteSet || |cmd.set2| == 0 then
                 Core.DeleteAndTranslate(cmd, input)[k] ==
                 input[CoreKeptIndices(cmd, input)[k]]
               else
                 Spec.TranslationRelation(
                   cmd.set1,
                   cmd.set2,
                   input[CoreKeptIndices(cmd, input)[k]],
                   Core.DeleteAndTranslate(cmd, input)[k]
                 )) by {
          forall k | 0 <= k < |CoreKeptIndices(cmd, input)|
            ensures if cmd.deleteSet || |cmd.set2| == 0 then
                      Core.DeleteAndTranslate(cmd, input)[k] ==
                      input[CoreKeptIndices(cmd, input)[k]]
                    else
                      Spec.TranslationRelation(
                        cmd.set1,
                        cmd.set2,
                        input[CoreKeptIndices(cmd, input)[k]],
                        Core.DeleteAndTranslate(cmd, input)[k]
                      )
          {
            if k > 0 {
              ShiftIndicesIndex(tailIndices, 1, k - 1);
              assert CoreKeptIndices(cmd, input)[k] ==
                     tailIndices[k - 1] + 1;
              assert input[CoreKeptIndices(cmd, input)[k]] ==
                     input[1..][tailIndices[k - 1]];
              assert Core.DeleteAndTranslate(cmd, input)[k] ==
                     Core.DeleteAndTranslate(cmd, input[1..])[k - 1];
            }
          }
        }
      }
    }
  }

  lemma CoreDeleteTranslateSatisfiesRelation(
    cmd: Core.TrCmd, input: BW.Bytes
  )
    ensures Spec.DeleteTranslateRelation(
              ToSpecCmd(cmd),
              input,
              Core.DeleteAndTranslate(cmd, input)
            )
  {
    CoreKeptIndicesProperties(cmd, input);
    CoreDeleteOutputProperties(cmd, input);
    assert Spec.DeleteTranslateRelation(
        ToSpecCmd(cmd),
        input,
        Core.DeleteAndTranslate(cmd, input)
      );
  }

  ghost function CoreEmittedIndices(
    input: BW.Bytes,
    squeezeSet: BW.Bytes,
    hasPrevious: bool,
    previous: char
  ): seq<nat>
    decreases |input|
  {
    if |input| == 0 then
      []
    else
      var tail := ShiftIndices(
                    CoreEmittedIndices(
                      input[1..], squeezeSet, true, input[0]
                    ),
                    1
                  );
      if hasPrevious &&
         input[0] == previous &&
         Core.Contains(squeezeSet, input[0]) then
        tail
      else
        [0] + tail
  }

  lemma CoreEmittedIndicesProperties(
    input: BW.Bytes,
    squeezeSet: BW.Bytes,
    hasPrevious: bool,
    previous: char
  )
    ensures Spec.StrictlyIncreasing(
              CoreEmittedIndices(
                input, squeezeSet, hasPrevious, previous
              )
            )
    ensures forall k ::
              0 <= k <
              |CoreEmittedIndices(
                input, squeezeSet, hasPrevious, previous
              )| ==>
                CoreEmittedIndices(
                  input, squeezeSet, hasPrevious, previous
                )[k] < |input|
    ensures forall i :: 0 <= i < |input| ==>
                          (i in CoreEmittedIndices(
                                  input, squeezeSet, hasPrevious, previous
                                )) ==
                          Spec.SqueezeEmittedAt(
                            input, squeezeSet, hasPrevious, previous, i
                          )
    decreases |input|
  {
    if |input| > 0 {
      CoreEmittedIndicesProperties(
        input[1..], squeezeSet, true, input[0]
      );
      ContainsIffMembership(squeezeSet, input[0]);
      var tailIndices := CoreEmittedIndices(
        input[1..], squeezeSet, true, input[0]
      );
      var shifted := ShiftIndices(tailIndices, 1);
      ShiftIndicesStrictlyIncreasing(tailIndices, 1);
      assert forall k :: 0 <= k < |shifted| ==>
                           shifted[k] < |input| by {
        forall k | 0 <= k < |shifted|
          ensures shifted[k] < |input|
        {
          ShiftIndicesIndex(tailIndices, 1, k);
        }
      }
      assert forall i :: 0 <= i < |input| ==>
                           (i in CoreEmittedIndices(
                                   input, squeezeSet, hasPrevious, previous
                                 )) ==
                           Spec.SqueezeEmittedAt(
                             input, squeezeSet, hasPrevious, previous, i
                           ) by {
        forall i | 0 <= i < |input|
          ensures (i in CoreEmittedIndices(
                          input, squeezeSet, hasPrevious, previous
                        )) ==
                  Spec.SqueezeEmittedAt(
                    input, squeezeSet, hasPrevious, previous, i
                  )
        {
          reveal Spec.SqueezeEmittedAt();
          if hasPrevious &&
             input[0] == previous &&
             Core.Contains(squeezeSet, input[0]) {
            assert CoreEmittedIndices(
                input, squeezeSet, hasPrevious, previous
              ) == shifted;
          } else {
            assert CoreEmittedIndices(
                input, squeezeSet, hasPrevious, previous
              ) == [0] + shifted;
          }
          if i > 0 {
            ShiftIndicesMembership(tailIndices, i);
            assert (i in CoreEmittedIndices(
                           input, squeezeSet, hasPrevious, previous
                         )) == (i in shifted);
            assert input[i] == input[1..][i - 1];
            assert (i - 1 in tailIndices) ==
                   (input[1..][i - 1] !in squeezeSet ||
                    (if i - 1 == 0 then
                       !true || input[1..][i - 1] != input[0]
                     else
                       input[1..][i - 1] != input[1..][i - 2]));
            if i > 1 {
              assert input[i - 1] == input[1..][i - 2];
            }
          } else {
            ShiftIndicesMembership(tailIndices, i);
            ContainsIffMembership(squeezeSet, input[0]);
          }
        }
      }
      if hasPrevious &&
         input[0] == previous &&
         Core.Contains(squeezeSet, input[0]) {
      } else {
        reveal Spec.StrictlyIncreasing();
        assert forall i, j ::
            0 <= i < j < |[0] + shifted| ==>
              ([0] + shifted)[i] < ([0] + shifted)[j] by {
          forall i, j | 0 <= i < j < |[0] + shifted|
            ensures ([0] + shifted)[i] < ([0] + shifted)[j]
          {
            if i == 0 {
              ShiftIndicesIndex(tailIndices, 1, j - 1);
            } else {
              assert shifted[i - 1] < shifted[j - 1];
            }
          }
        }
      }
    }
  }

  lemma CoreSqueezeOutputProperties(
    input: BW.Bytes,
    squeezeSet: BW.Bytes,
    hasPrevious: bool,
    previous: char
  )
    ensures |Core.SqueezeFrom(
              input, squeezeSet, hasPrevious, previous
            )| == |CoreEmittedIndices(
                    input, squeezeSet, hasPrevious, previous
                  )|
    ensures forall k ::
              0 <= k <
              |CoreEmittedIndices(
                input, squeezeSet, hasPrevious, previous
              )| ==>
                CoreEmittedIndices(
                  input, squeezeSet, hasPrevious, previous
                )[k] < |input|
    ensures forall k ::
              0 <= k <
              |CoreEmittedIndices(
                input, squeezeSet, hasPrevious, previous
              )| ==>
                Core.SqueezeFrom(
                  input, squeezeSet, hasPrevious, previous
                )[k] ==
                input[
                CoreEmittedIndices(
                  input, squeezeSet, hasPrevious, previous
                )[k]
                ]
    decreases |input|
  {
    CoreEmittedIndicesProperties(
      input, squeezeSet, hasPrevious, previous
    );
    if |input| > 0 {
      ContainsIffMembership(squeezeSet, input[0]);
      CoreSqueezeOutputProperties(
        input[1..], squeezeSet, true, input[0]
      );
      var tailIndices := CoreEmittedIndices(
        input[1..], squeezeSet, true, input[0]
      );
      if hasPrevious &&
         input[0] == previous &&
         Core.Contains(squeezeSet, input[0]) {
        assert Core.SqueezeFrom(
            input[1..], squeezeSet, true, previous
          ) == Core.SqueezeFrom(
                      input[1..], squeezeSet, true, input[0]
                    );
        assert forall k ::
            0 <= k <
            |CoreEmittedIndices(
              input, squeezeSet, hasPrevious, previous
            )| ==>
              Core.SqueezeFrom(
                input, squeezeSet, hasPrevious, previous
              )[k] ==
              input[
              CoreEmittedIndices(
                input, squeezeSet, hasPrevious, previous
              )[k]
              ] by {
          forall k |
            0 <= k <
            |CoreEmittedIndices(
              input, squeezeSet, hasPrevious, previous
            )|
            ensures Core.SqueezeFrom(
                      input, squeezeSet, hasPrevious, previous
                    )[k] ==
                    input[
                    CoreEmittedIndices(
                      input, squeezeSet, hasPrevious, previous
                    )[k]
                    ]
          {
            ShiftIndicesIndex(tailIndices, 1, k);
          }
        }
      } else {
        assert forall k ::
            0 <= k <
            |CoreEmittedIndices(
              input, squeezeSet, hasPrevious, previous
            )| ==>
              Core.SqueezeFrom(
                input, squeezeSet, hasPrevious, previous
              )[k] ==
              input[
              CoreEmittedIndices(
                input, squeezeSet, hasPrevious, previous
              )[k]
              ] by {
          forall k |
            0 <= k <
            |CoreEmittedIndices(
              input, squeezeSet, hasPrevious, previous
            )|
            ensures Core.SqueezeFrom(
                      input, squeezeSet, hasPrevious, previous
                    )[k] ==
                    input[
                    CoreEmittedIndices(
                      input, squeezeSet, hasPrevious, previous
                    )[k]
                    ]
          {
            if k > 0 {
              ShiftIndicesIndex(tailIndices, 1, k - 1);
            }
          }
        }
      }
    }
  }

  lemma CoreSqueezeStateSatisfiesRelation(
    input: BW.Bytes,
    squeezeSet: BW.Bytes,
    hasPrevious: bool,
    previous: char
  )
    ensures Spec.SqueezeStateRelation(
              input,
              squeezeSet,
              hasPrevious,
              previous,
              Core.SqueezeFrom(
                input, squeezeSet, hasPrevious, previous
              )
            )
  {
    CoreEmittedIndicesProperties(
      input, squeezeSet, hasPrevious, previous
    );
    CoreSqueezeOutputProperties(
      input, squeezeSet, hasPrevious, previous
    );
    assert Spec.SqueezeStateRelation(
        input,
        squeezeSet,
        hasPrevious,
        previous,
        Core.SqueezeFrom(
          input, squeezeSet, hasPrevious, previous
        )
      );
  }

  lemma CoreSqueezeSatisfiesRelation(
    input: BW.Bytes, squeezeSet: BW.Bytes
  )
    ensures Spec.SqueezeRelation(
              input,
              squeezeSet,
              Core.SqueezeFrom(input, squeezeSet, false, '\0')
            )
  {
    CoreSqueezeStateSatisfiesRelation(
      input, squeezeSet, false, '\0'
    );
  }

  lemma CoreOutputSatisfiesRelation(
    cmd: Core.TrCmd, input: BW.Bytes
  )
    ensures Spec.OutputRelation(
              ToSpecCmd(cmd), input, Core.RenderData(cmd, input)
            )
  {
    CoreDeleteTranslateSatisfiesRelation(cmd, input);
    var transformed := Core.DeleteAndTranslate(cmd, input);
    if cmd.squeeze {
      CoreSqueezeSatisfiesRelation(transformed, cmd.squeezeSet);
    }
    assert Spec.OutputRelation(
        ToSpecCmd(cmd), input, Core.RenderData(cmd, input)
      );
  }

  twostate lemma CoreSummaryImpliesSpec(raw: Schema.TrCmdRaw, io: BenchIO.IO, exit: int)
    requires Core.CoreSummary(raw, io, exit)
    ensures Spec.Spec(raw, io, exit)
  {
    CoreCommandSatisfiesRelation(raw);
    match Core.Command(raw).mode
    case ModeHelp =>
    case ModeVersion =>
    case ModeMissingOperand(_) =>
    case ModeExtraOperand(_) =>
    case ModeUnsupportedSet(_) =>
    case ModeEmptySet2 =>
    case ModeRun =>
      CoreOutputSatisfiesRelation(
        Core.Command(raw), old(io.stdin())
      );
  }
}
