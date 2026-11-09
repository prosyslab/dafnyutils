include "../../../core/World.dfy"
include "../Spec/TrSchema.dfy"
include "../Impl/TrCore.dfy"
include "../Spec/TrSpec.dfy"

module TrProof {
  import StreamWorld = BenchWorld
  import StreamContract = IOContract

  import Result = Results
  import BenchIO
  import BW = BenchWorld
  import Schema = TrSchema
  import Core = TrCore
  import Spec = TrSpec
  import Utf8 = Utf8Semantics
  import IOContract

  predicate StrictlyIncreasing(indices: seq<nat>)
  {
    forall i, j :: 0 <= i < j < |indices| ==>
                     indices[i] < indices[j]
  }

  ghost predicate DeleteTranslateRelation(
    cmd: Spec.TrCmd,
    input: BW.Bytes,
    transformed: BW.Bytes
  )
  {
    exists kept: seq<nat> ::
      StrictlyIncreasing(kept) &&
      (forall k :: 0 <= k < |kept| ==> kept[k] < |input|) &&
      (forall i :: 0 <= i < |input| ==>
                     (i in kept) ==
                     (!cmd.deleteSet || input[i] !in cmd.set1)) &&
      |transformed| == |kept| &&
      (forall k :: 0 <= k < |kept| ==>
                     (if cmd.deleteSet || |cmd.set2| == 0 then
                        transformed[k] == input[kept[k]]
                      else
                        Spec.TranslationRelation(
                          cmd.set1,
                          cmd.set2,
                          input[kept[k]],
                          transformed[k]
                        )))
  }

  ghost predicate SqueezeStateRelation(
    input: BW.Bytes,
    squeezeSet: BW.Bytes,
    hasPrevious: bool,
    previous: char,
    output: BW.Bytes
  )
  {
    exists emitted: seq<nat> ::
      StrictlyIncreasing(emitted) &&
      (forall k :: 0 <= k < |emitted| ==> emitted[k] < |input|) &&
      (forall i :: 0 <= i < |input| ==>
                     (i in emitted) ==
                     SqueezeEmittedAt(
                       input, squeezeSet, hasPrevious, previous, i
                     )) &&
      |output| == |emitted| &&
      (forall k :: 0 <= k < |emitted| ==>
                     output[k] == input[emitted[k]])
  }

  predicate SqueezeEmittedAt(
    input: BW.Bytes,
    squeezeSet: BW.Bytes,
    hasPrevious: bool,
    previous: char,
    i: nat
  )
    requires i < |input|
  {
    input[i] !in squeezeSet ||
    (if i == 0 then
       !hasPrevious || input[i] != previous
     else
       input[i] != input[i - 1])
  }

  ghost predicate SqueezeRelation(
    input: BW.Bytes,
    squeezeSet: BW.Bytes,
    output: BW.Bytes
  )
  {
    SqueezeStateRelation(input, squeezeSet, false, '\0', output)
  }

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
    Spec.TrCmd(ToSpecMode(cmd.mode), cmd.deleteSet, cmd.squeeze, cmd.set1, cmd.set2, cmd.squeezeSet, cmd.warnings)
  }

  lemma CoreAtomSatisfiesRelation(text: string, lo: nat)
    requires lo < |text|
    ensures Spec.SetAtomRelation(
              text, lo, Core.AtomAt(text, lo).next,
              Core.AtomAt(text, lo).bytes)
  {
    reveal Spec.SetAtomRelation();
    if text[lo] == '\\' && lo + 1 < |text| {
      if Spec.IsOctal(text[lo + 1]) {
        if lo + 2 < |text| && Spec.IsOctal(text[lo + 2]) {
          if lo + 3 < |text| && Spec.IsOctal(text[lo + 3]) {
          }
        }
      }
    }
  }

  lemma WarningPartitionFromElement(
    text: string,
    start: nat,
    warnings: BW.Bytes,
    inputCuts: seq<nat>,
    outputCuts: seq<nat>,
    i: nat
  )
    requires Spec.WarningPartitionFrom(
               text, start, warnings, inputCuts, outputCuts)
    requires i + 1 < |inputCuts|
    ensures inputCuts[i] < inputCuts[i + 1] <= |text|
    ensures inputCuts[i + 1] == Spec.AtomNext(text, inputCuts[i])
    ensures outputCuts[i] <= outputCuts[i + 1] <= |warnings|
    ensures warnings[outputCuts[i]..outputCuts[i + 1]] ==
            Spec.WarningAtSpec(text, inputCuts[i])
  {
    reveal Spec.WarningPartitionFrom();
  }

  lemma PrependWarningPartition(
    text: string,
    start: nat,
    next: nat,
    piece: BW.Bytes,
    rest: BW.Bytes,
    tailInputCuts: seq<nat>,
    tailOutputCuts: seq<nat>
  )
    requires start < next <= |text|
    requires next == Spec.AtomNext(text, start)
    requires piece == Spec.WarningAtSpec(text, start)
    requires Spec.WarningPartitionFrom(
               text, next, rest, tailInputCuts, tailOutputCuts)
    ensures Spec.WarningPartitionFrom(
              text, start, piece + rest,
              [start] + tailInputCuts,
              [0] + ShiftIndices(tailOutputCuts, |piece|))
  {
    hide *;
    reveal Spec.WarningPartitionFrom();
    var inputCuts := [start] + tailInputCuts;
    var outputCuts := [0] + ShiftIndices(tailOutputCuts, |piece|);
    assert tailInputCuts[0] == next;
    assert tailOutputCuts[0] == 0;
    ShiftIndicesIndex(tailOutputCuts, |piece|, |tailOutputCuts| - 1);
    assert forall i
        {:trigger inputCuts[i], inputCuts[i + 1]}
        {:trigger (piece + rest)[outputCuts[i]..outputCuts[i + 1]]} ::
        0 <= i && i + 1 < |inputCuts| ==>
          inputCuts[i] < inputCuts[i + 1] <= |text| &&
          inputCuts[i + 1] == Spec.AtomNext(text, inputCuts[i]) &&
          outputCuts[i] <= outputCuts[i + 1] <= |piece + rest| &&
          (piece + rest)[outputCuts[i]..outputCuts[i + 1]] ==
          Spec.WarningAtSpec(text, inputCuts[i]) by {
      forall i {:trigger inputCuts[i]} |
    0 <= i && i + 1 < |inputCuts|
        ensures inputCuts[i] < inputCuts[i + 1] <= |text| &&
                inputCuts[i + 1] == Spec.AtomNext(text, inputCuts[i]) &&
                outputCuts[i] <= outputCuts[i + 1] <= |piece + rest| &&
                (piece + rest)[outputCuts[i]..outputCuts[i + 1]] ==
                Spec.WarningAtSpec(text, inputCuts[i])
      {
        if i == 0 {
          ShiftIndicesIndex(tailOutputCuts, |piece|, 0);
          assert outputCuts[1] == |piece|;
          assert (piece + rest)[0..|piece|] == piece;
        } else {
          var j := i - 1;
          ShiftIndicesIndex(tailOutputCuts, |piece|, j);
          ShiftIndicesIndex(tailOutputCuts, |piece|, j + 1);
          WarningPartitionFromElement(
            text, next, rest, tailInputCuts, tailOutputCuts, j);
          AppendShiftedSlice(
            piece, rest, tailOutputCuts[j], tailOutputCuts[j + 1]);
          assert outputCuts[i] == |piece| + tailOutputCuts[j];
          assert outputCuts[i + 1] == |piece| + tailOutputCuts[j + 1];
          assert inputCuts[i] == tailInputCuts[j];
          assert (piece + rest)[outputCuts[i]..outputCuts[i + 1]] ==
                 rest[tailOutputCuts[j]..tailOutputCuts[j + 1]];
        }
      }
    }
  }

  lemma CoreWarningSatisfiesRelation(text: string, start: nat)
    requires start <= |text|
    ensures exists inputCuts: seq<nat>, outputCuts: seq<nat> ::
              Spec.WarningPartitionFrom(
                text, start, Core.WarningBytesFrom(text, start),
                inputCuts, outputCuts)
    decreases |text| - start
  {
    if start == |text| {
      assert Core.WarningBytesFrom(text, start) == [];
      assert Spec.WarningPartitionFrom(
          text, start, [], [start], [0]);
    } else {
      var next := Core.AtomAt(text, start).next;
      CoreWarningSatisfiesRelation(text, next);
      var tailInputCuts: seq<nat>, tailOutputCuts: seq<nat> :|
        Spec.WarningPartitionFrom(
          text, next, Core.WarningBytesFrom(text, next),
          tailInputCuts, tailOutputCuts);
      PrependWarningPartition(
        text, start, next, Spec.WarningAtSpec(text, start),
        Core.WarningBytesFrom(text, next),
        tailInputCuts, tailOutputCuts);
      assert Core.WarningBytesFrom(text, start) ==
             Spec.WarningAtSpec(text, start) + Core.WarningBytesFrom(text, next);
      assert Spec.WarningPartitionFrom(
          text, start, Core.WarningBytesFrom(text, start),
          [start] + tailInputCuts,
          [0] + ShiftIndices(tailOutputCuts,
                             |Spec.WarningAtSpec(text, start)|));
    }
  }

  lemma SetAtomRelationFunctional(
    text: string, lo: nat, hi: nat, bytes: BW.Bytes)
    requires Spec.SetAtomRelation(text, lo, hi, bytes)
    ensures hi == Core.AtomAt(text, lo).next
    ensures bytes == Core.AtomAt(text, lo).bytes
  {
    CoreAtomSatisfiesRelation(text, lo);
    reveal Spec.SetAtomRelation();
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
    requires 0 <= lo as int < 256
    requires 0 <= hi as int < 256
    requires lo as int <= hi as int
    ensures Spec.RangeExpansion(lo, hi, Core.RangeChars(lo, hi))
    decreases (hi as int) - (lo as int)
  {
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
    ensures !Spec.StartsUnsupportedConstruct(text[lo..])
    ensures Core.AtomAt(text, lo).next < |text| &&
            text[Core.AtomAt(text, lo).next] == '-' &&
            Core.AtomAt(text, lo).next + 1 < |text| ==>
              |Core.AtomAt(text, lo).bytes| == 1 &&
              |Core.AtomAt(text, Core.AtomAt(text, lo).next + 1).bytes| == 1 &&
              Core.AtomAt(text, lo).bytes[0] as int <=
              Core.AtomAt(text, Core.AtomAt(text, lo).next + 1).bytes[0] as int &&
              Core.AtomAt(text, Core.AtomAt(text, lo).next + 1).bytes[0] as int < 256
    ensures if Core.AtomAt(text, lo).next < |text| &&
               text[Core.AtomAt(text, lo).next] == '-' &&
               Core.AtomAt(text, lo).next + 1 < |text| then
              hi == Core.AtomAt(text, Core.AtomAt(text, lo).next + 1).next &&
              bytes == Core.RangeChars(
                Core.AtomAt(text, lo).bytes[0],
                Core.AtomAt(text, Core.AtomAt(text, lo).next + 1).bytes[0])
            else
              hi == Core.AtomAt(text, lo).next &&
              bytes == Core.AtomAt(text, lo).bytes
  {
    reveal Spec.SetUnitRelation();
    var atomEnd := Spec.AtomNext(text, lo);
    var atomBytes := Spec.AtomBytes(text, lo);
    SetAtomRelationFunctional(text, lo, atomEnd, atomBytes);
    if atomEnd < |text| && text[atomEnd] == '-' &&
       atomEnd + 1 < |text| {
      var endEnd := Spec.AtomNext(text, atomEnd + 1);
      var endBytes := Spec.AtomBytes(text, atomEnd + 1);
      SetAtomRelationFunctional(text, atomEnd + 1, endEnd, endBytes);
      reveal Spec.RangeExpansion();
      RangeCharsSatisfiesExpansion(atomBytes[0], endBytes[0]);
      RangeExpansionFunctional(
        atomBytes[0], endBytes[0], bytes,
        Core.RangeChars(atomBytes[0], endBytes[0])
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
    requires start < next <= |text|
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
    hide *;
    reveal Spec.SetPartitionFrom(), ShiftIndices();
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
      forall i
        {:trigger inputCuts[i], inputCuts[i + 1]}
    {:trigger (piece + rest)[outputCuts[i]..outputCuts[i + 1]]} |
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
    assert Spec.SetPartitionFrom(text, start, piece + rest, inputCuts, outputCuts);
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
            Result.Ok(bytes[outputCuts[i]..])
    decreases |inputCuts| - i
  {
    reveal Spec.SetPartitionFrom();
    if i + 1 == |inputCuts| {
      assert inputCuts[i] == |text|;
      assert outputCuts[i] == |bytes|;
      assert bytes[outputCuts[i]..] == [];
      assert Core.DecodeSetFrom(text, inputCuts[i]) == Result.Ok([]) by {
        reveal Core.DecodeSetFrom();
      }
    } else {
      SetPartitionFromElement(
        text, start, bytes, inputCuts, outputCuts, i
      );
      var lo := inputCuts[i];
      var hi := inputCuts[i + 1];
      var piece := bytes[outputCuts[i]..outputCuts[i + 1]];
      SetUnitMatchesCore(text, lo, hi, piece);
      SetPartitionFromMatchesCore(
        text, start, bytes, inputCuts, outputCuts, i + 1
      );
      SplitSlice(bytes, outputCuts[i], outputCuts[i + 1], |bytes|);
      assert bytes[outputCuts[i]..] ==
             piece + bytes[outputCuts[i + 1]..];
      var atom := Core.AtomAt(text, lo);
      if atom.next < |text| && text[atom.next] == '-' &&
         atom.next + 1 < |text| {
        var end := Core.AtomAt(text, atom.next + 1);
        assert hi == end.next;
        assert piece == Core.RangeChars(atom.bytes[0], end.bytes[0]);
      } else {
        assert hi == atom.next;
        assert piece == atom.bytes;
      }
    }
  }

  lemma DecodeSetFromOkSatisfiesPartition(text: string, start: nat)
    requires start <= |text|
    requires Core.DecodeSetFrom(text, start).Ok?
    ensures exists inputCuts: seq<nat>, outputCuts: seq<nat> ::
              Spec.SetPartitionFrom(
                text,
                start,
                Core.DecodeSetFrom(text, start).v,
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
      if Spec.StartsUnsupportedConstruct(text[start..]) {
      } else {
        var atom := Core.AtomAt(text, start);
        CoreAtomSatisfiesRelation(text, start);
        if atom.next < |text| && text[atom.next] == '-' &&
           atom.next + 1 < |text| {
          var end := Core.AtomAt(text, atom.next + 1);
          CoreAtomSatisfiesRelation(text, atom.next + 1);
          if |atom.bytes| == 1 && |end.bytes| == 1 &&
             atom.bytes[0] as int < 256 && end.bytes[0] as int < 256 &&
             atom.bytes[0] as int <= end.bytes[0] as int {
            var next := end.next;
            var tail := Core.DecodeSetFrom(text, next);
            match tail
            case Ok(rest) =>
              DecodeSetFromOkSatisfiesPartition(text, next);
              var tailInputCuts: seq<nat>, tailOutputCuts: seq<nat> :|
                Spec.SetPartitionFrom(
                  text, next, rest, tailInputCuts, tailOutputCuts
                );
              var piece := Core.RangeChars(atom.bytes[0], end.bytes[0]);
              RangeCharsSatisfiesExpansion(atom.bytes[0], end.bytes[0]);
              reveal Spec.SetUnitRelation();
                     assert Spec.SetUnitRelation(
                         text, start, next, piece
                       );
                     PrependSetUnitPartition(
                       text, start, next, piece, rest,
                       tailInputCuts, tailOutputCuts
                     );
            case Err(_) =>
          }
        } else {
          var next := atom.next;
          var tail := Core.DecodeSetFrom(text, next);
          match tail
          case Ok(rest) =>
            DecodeSetFromOkSatisfiesPartition(text, next);
            var tailInputCuts: seq<nat>, tailOutputCuts: seq<nat> :|
              Spec.SetPartitionFrom(
                text, next, rest, tailInputCuts, tailOutputCuts
              );
            var piece := atom.bytes;
            reveal Spec.SetUnitRelation();
                   assert Spec.SetUnitRelation(text, start, next, piece);
                   PrependSetUnitPartition(
                     text, start, next, piece, rest,
                     tailInputCuts, tailOutputCuts
                   );
          case Err(_) =>
        }
      }
    }
  }

  lemma SetBytesRelationMatchesCore(text: string, bytes: BW.Bytes)
    requires Spec.SetBytesRelation(text, bytes)
    ensures Core.DecodeSet(text) == Result.Ok(bytes)
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
              text, Core.DecodeSet(text)
            )
  {
    match Core.DecodeSet(text)
    case Ok(bytes) =>
      DecodeSetFromOkSatisfiesPartition(text, 0);
      var inputCuts: seq<nat>, outputCuts: seq<nat> :|
        Spec.SetPartitionFrom(
          text, 0, bytes, inputCuts, outputCuts
        );
      assert Spec.SetPartition(text, bytes, inputCuts, outputCuts);
      assert Spec.SetBytesRelation(text, bytes);
    case Err(_) =>
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
      [Core.DecodeSet(operands[0])] +
      CoreDecodes(operands[1..])
  }

  lemma CoreDecodesIndex(operands: seq<string>, i: nat)
    requires i < |operands|
    ensures CoreDecodes(operands)[i] ==
            Core.DecodeSet(operands[i])
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
      case Ok(_) =>
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
              Result.Err(operands[i]) &&
              operand == operands[i] &&
              forall j :: 0 <= j < i ==>
                            CoreDecodes(operands)[j].Ok?;
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
            Result.Err(operands[1..][tailIndex]) &&
            operand == operands[1..][tailIndex] &&
            forall j :: 0 <= j < tailIndex ==>
                          CoreDecodes(operands[1..])[j].Ok?;
          var i := tailIndex + 1;
          assert forall j :: 0 <= j < i ==>
                               CoreDecodes(operands)[j].Ok? by {
            forall j | 0 <= j < i
              ensures CoreDecodes(operands)[j].Ok?
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
      case Err(_) =>
        if operands[0] == "" {
          assert Core.DecodeSet(operands[0]) == Result.Ok([]);
        }
        assert Spec.FirstUnsupportedOperandRelation(
            operands, CoreDecodes(operands), operands[0]
          );
    }
  }

  lemma DecodedBytesMatchesCore(text: string)
    ensures Spec.DecodedBytes(
              Core.DecodeSet(text)
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
      CoreWarningSatisfiesRelation(raw.operands[0], 0);
      assert Spec.WarningBytesRelation(
          raw.operands[0], Core.WarningBytesFrom(raw.operands[0], 0));
    }
    if |raw.operands| > 1 {
      CoreDecodesIndex(raw.operands, 1);
      DecodedBytesMatchesCore(raw.operands[1]);
      CoreWarningSatisfiesRelation(raw.operands[1], 0);
      assert Spec.WarningBytesRelation(
          raw.operands[1], Core.WarningBytesFrom(raw.operands[1], 0));
    }
    assert Spec.CommandWarningsRelation(
        raw, decoded, Core.Command(raw).warnings);
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
    requires StrictlyIncreasing(indices)
    ensures StrictlyIncreasing(ShiftIndices(indices, delta))
  {
    reveal StrictlyIncreasing();
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
    ensures StrictlyIncreasing(CoreKeptIndices(cmd, input))
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
        assert StrictlyIncreasing([0] + shifted);
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
    ensures DeleteTranslateRelation(
              ToSpecCmd(cmd),
              input,
              Core.DeleteAndTranslate(cmd, input)
            )
  {
    CoreKeptIndicesProperties(cmd, input);
    CoreDeleteOutputProperties(cmd, input);
    assert DeleteTranslateRelation(
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
    ensures StrictlyIncreasing(
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
                          SqueezeEmittedAt(
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
                           SqueezeEmittedAt(
                             input, squeezeSet, hasPrevious, previous, i
                           ) by {
        forall i | 0 <= i < |input|
          ensures (i in CoreEmittedIndices(
                          input, squeezeSet, hasPrevious, previous
                        )) ==
                  SqueezeEmittedAt(
                    input, squeezeSet, hasPrevious, previous, i
                  )
        {
          reveal SqueezeEmittedAt();
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
        reveal StrictlyIncreasing();
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
    ensures SqueezeStateRelation(
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
    assert SqueezeStateRelation(
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
    ensures SqueezeRelation(
              input,
              squeezeSet,
              Core.SqueezeFrom(input, squeezeSet, false, '\0')
            )
  {
    CoreSqueezeStateSatisfiesRelation(
      input, squeezeSet, false, '\0'
    );
  }

  // Connect the retained index witnesses to the canonical ordered image.
  lemma SelectInOrder(input: BW.Bytes, indices: seq<nat>)
    requires StrictlyIncreasing(indices)
    requires forall k | 0 <= k < |indices| :: indices[k] < |input|
    ensures |Spec.Select(input, set i: nat | i in indices :: i)| == |indices|
    ensures forall k | 0 <= k < |indices| ::
              Spec.Select(input, set i: nat | i in indices :: i)[k] == input[indices[k]]
    decreases |indices|
  {
    reveal Spec.Select();
    var positions := set i: nat | i in indices :: i;
    if |indices| > 0 {
      var tail := set i: nat | i in indices[1..] :: i;
      assert indices == [indices[0]] + indices[1..];
      assert positions == tail + {indices[0]} by {
        forall i: nat
          ensures (i in positions) == (i in tail + {indices[0]})
        {
          if i in positions {
            assert i in indices;
            var k :| 0 <= k < |indices| && indices[k] == i;
            if k > 0 {
              assert indices[1..][k - 1] == i;
              assert i in indices[1..];
              assert i in tail;
            } else {
              assert i == indices[0];
            }
          } else if i in tail {
            var k :| 0 <= k < |indices[1..]| && indices[1..][k] == i;
            assert indices[k + 1] == i;
            assert i in indices;
            assert i in positions;
          } else if i == indices[0] {
            assert i in indices;
            assert i in positions;
          }
        }
      }
      assert forall i | i in tail :: indices[0] < i by {
        forall i | i in tail
          ensures indices[0] < i
        {
          var k :| 0 <= k < |indices[1..]| && indices[1..][k] == i;
        }
      }
      assert forall i | i in positions :: indices[0] <= i;
      assert Spec.Least(positions) == indices[0];
      assert positions - {indices[0]} == tail;
      assert Spec.Select(input, positions) == [input[indices[0]]] + Spec.Select(input, tail);
      SelectInOrder(input, indices[1..]);
      hide Spec.Select();
      forall k | 0 <= k < |indices|
        ensures Spec.Select(input, positions)[k] == input[indices[k]]
      {
        if k > 0 {
          assert indices[1..][k - 1] == indices[k];
          assert Spec.Select(input, tail)[k - 1] == input[indices[1..][k - 1]];
          assert Spec.Select(input, positions)[k] == Spec.Select(input, tail)[k - 1];
        }
      }
    }
  }

  lemma TranslationUnique(set1: BW.Bytes, set2: BW.Bytes, ch: char,
                          first: char, second: char)
    requires Spec.TranslationRelation(set1, set2, ch, first)
    requires Spec.TranslationRelation(set1, set2, ch, second)
    ensures first == second
  {
    if ch in set1 {
      var i :| 0 <= i < |set1| && set1[i] == ch &&
               (forall j :: i < j < |set1| ==> set1[j] != ch) &&
               first == set2[if i < |set2| then i else |set2| - 1];
      var j :| 0 <= j < |set1| && set1[j] == ch &&
               (forall k :: j < k < |set1| ==> set1[k] != ch) &&
               second == set2[if j < |set2| then j else |set2| - 1];
      assert i == j;
    }
  }

  lemma ByteSequenceCanonical(cmd: Spec.TrCmd, data: BW.Bytes, output: BW.Bytes)
    requires |data| == |output|
    requires forall k | 0 <= k < |data| ::
               if cmd.deleteSet || |cmd.set2| == 0 then output[k] == data[k]
               else Spec.TranslationRelation(cmd.set1, cmd.set2, data[k], output[k])
    ensures output == (if cmd.deleteSet then data else
                       seq(|data|, k requires 0 <= k < |data| => Spec.TranslateByte(cmd.set1, cmd.set2, data[k])))
  {
    var expected := if cmd.deleteSet then data else
    seq(|data|, k requires 0 <= k < |data| => Spec.TranslateByte(cmd.set1, cmd.set2, data[k]));
    forall k | 0 <= k < |data|
      ensures output[k] == expected[k]
    {
      if !cmd.deleteSet && |cmd.set2| > 0 {
        TranslationUnique(cmd.set1, cmd.set2, data[k], output[k],
                          Spec.TranslateByte(cmd.set1, cmd.set2, data[k]));
      }
    }
  }

  lemma DeleteTranslateCanonical(cmd: Spec.TrCmd, input: BW.Bytes, output: BW.Bytes)
    requires DeleteTranslateRelation(cmd, input, output)
    ensures output == Spec.DeleteTranslate(cmd, input)
  {
    hide *;
    reveal DeleteTranslateRelation(), StrictlyIncreasing();
    var kept: seq<nat> :| StrictlyIncreasing(kept) &&
                          (forall k :: 0 <= k < |kept| ==> kept[k] < |input|) &&
                          (forall i :: 0 <= i < |input| ==>
                                         (i in kept) == (!cmd.deleteSet || input[i] !in cmd.set1)) &&
                          |output| == |kept| &&
                          (forall k :: 0 <= k < |kept| ==>
                                         (if cmd.deleteSet || |cmd.set2| == 0 then output[k] == input[kept[k]]
                                          else Spec.TranslationRelation(cmd.set1, cmd.set2, input[kept[k]], output[k])));
    SelectInOrder(input, kept);
    var positions := set i: nat | i in kept :: i;
    var selected := set i: nat | i < |input| &&
                                 (!cmd.deleteSet || input[i] !in cmd.set1) :: i;
    if positions != selected {
      var i: nat :| (i in positions) != (i in selected);
      assert (i in positions) == (i in kept);
      if i in positions {
        var k :| 0 <= k < |kept| && kept[k] == i;
        assert i < |input|;
        assert !cmd.deleteSet || input[i] !in cmd.set1;
        assert i in selected;
      } else {
        assert i in selected;
        assert i < |input|;
        assert !cmd.deleteSet || input[i] !in cmd.set1;
        assert i in kept;
        assert i in positions;
      }
      assert false;
    }
    var data := Spec.Select(input, selected);
    assert |data| == |kept|;
    forall k | 0 <= k < |data|
      ensures if cmd.deleteSet || |cmd.set2| == 0 then output[k] == data[k]
              else Spec.TranslationRelation(cmd.set1, cmd.set2, data[k], output[k])
    {
      assert data[k] == input[kept[k]];
    }
    ByteSequenceCanonical(cmd, data, output);
    reveal Spec.DeleteTranslate();
  }

  lemma SqueezeCanonical(input: BW.Bytes, squeezeSet: BW.Bytes, output: BW.Bytes)
    requires SqueezeRelation(input, squeezeSet, output)
    ensures output == Spec.Squeezed(input, squeezeSet)
  {
    hide *;
    reveal SqueezeRelation(), SqueezeStateRelation(), SqueezeEmittedAt(), StrictlyIncreasing();
    var emitted: seq<nat> :| StrictlyIncreasing(emitted) &&
                             (forall k :: 0 <= k < |emitted| ==> emitted[k] < |input|) &&
                             (forall i :: 0 <= i < |input| ==>
                                            (i in emitted) == SqueezeEmittedAt(input, squeezeSet, false, '\0', i)) &&
                             |output| == |emitted| &&
                             (forall k :: 0 <= k < |emitted| ==> output[k] == input[emitted[k]]);
    SelectInOrder(input, emitted);
    var positions := set i: nat | i in emitted :: i;
    var selected := set i: nat | i < |input| &&
                                 (i == 0 || input[i] !in squeezeSet || input[i] != input[i - 1]) :: i;
    if positions != selected {
      var i: nat :| (i in positions) != (i in selected);
      assert (i in positions) == (i in emitted);
      if i in positions {
        var k :| 0 <= k < |emitted| && emitted[k] == i;
        assert i < |input|;
        assert SqueezeEmittedAt(input, squeezeSet, false, '\0', i);
        assert i in selected;
      } else {
        assert i in selected;
        assert SqueezeEmittedAt(input, squeezeSet, false, '\0', i);
        assert i in emitted;
      }
      assert false;
    }
    var expected := Spec.Select(input, selected);
    assert |expected| == |output|;
    forall k | 0 <= k < |output|
      ensures output[k] == expected[k]
    {
      assert expected[k] == input[emitted[k]];
    }
    reveal Spec.Squeezed();
  }

  lemma CoreOutputRefines(
    cmd: Core.TrCmd, input: BW.Bytes
  )
    ensures Core.RenderData(cmd, input) == Spec.Transform(ToSpecCmd(cmd), input)
  {
    CoreDeleteTranslateSatisfiesRelation(cmd, input);
    var transformed := Core.DeleteAndTranslate(cmd, input);
    DeleteTranslateCanonical(ToSpecCmd(cmd), input, transformed);
    if cmd.squeeze {
      CoreSqueezeSatisfiesRelation(transformed, cmd.squeezeSet);
      SqueezeCanonical(transformed, cmd.squeezeSet,
                       Core.SqueezeFrom(transformed, cmd.squeezeSet, false, '\0'));
    }
  }

  twostate lemma PreparedSummaryImpliesPreparedSpec(raw: Schema.TrCmdRaw, io: BenchIO.IO, exit: int, resultStdout: StreamWorld.Bytes, resultStderr: StreamWorld.Bytes)
    requires Core.PreparedSummary(raw, io, exit, resultStdout, resultStderr)
    ensures Spec.PreparedSpec(raw, io, exit, resultStdout, resultStderr)
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
      CoreOutputRefines(
        Core.Command(raw), IOContract.ReadResultData(
          IOContract.ObservedReadStdinResultFields(old(io.stdin()), old(io.trustedStreams())))
      );
  }

  twostate lemma CoreSummaryImpliesSpec(raw: Schema.TrCmdRaw, io: BenchIO.IO, exit: int)
    requires Core.CoreSummary(raw, io, exit)
    ensures Spec.Spec(raw, io, exit)
  {
    var output: StreamWorld.Bytes, diagnostics: StreamWorld.Bytes, normalExit: int :|
      Core.PreparedSummary(raw, io, normalExit, old(io.stdout()) + output, old(io.stderr()) + diagnostics) &&
      Spec.EmissionFields(old(io.stdout()), old(io.stderr()), io.stdout(), io.stderr(),
                          io.trustedStreams(), output, diagnostics, normalExit, exit);
    PreparedSummaryImpliesPreparedSpec(raw, io, normalExit,
                                       old(io.stdout()) + output, old(io.stderr()) + diagnostics);
  }
}
