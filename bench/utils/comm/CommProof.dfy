include "../../core/World.dfy"
include "CommSchema.dfy"
include "CommRenderCore.dfy"
include "CommRenderSpec.dfy"
include "CommCore.dfy"
include "CommSpec.dfy"

module CommProof {
  import BenchIO
  import BW = BenchWorld
  import Schema = CommSchema
  import RCore = CommRenderCore
  import RSpec = CommRenderSpec
  import Core = CommCore
  import Spec = CommSpec

  function ShiftNats(values: seq<nat>, amount: nat): seq<nat>
  {
    seq(|values|, i requires 0 <= i < |values| => values[i] + amount)
  }

  lemma ShiftNatsIndex(values: seq<nat>, amount: nat, i: nat)
    requires i < |values|
    ensures ShiftNats(values, amount)[i] == values[i] + amount
  {
  }

  lemma PrependSlice<T>(head: seq<T>, tail: seq<T>, start: nat, end: nat)
    requires start <= end <= |tail|
    ensures (head + tail)[|head| + start..|head| + end] == tail[start..end]
  {
  }

  lemma ByteValueTail(data: BW.Bytes, i: nat)
    requires i + 1 < |data|
    ensures RSpec.ByteValue(data[1..], i) == RSpec.ByteValue(data, i + 1)
  {
  }

  lemma SliceIndex<T>(values: seq<T>, drop: nat, i: nat)
    requires drop <= |values|
    requires i < |values[drop..]|
    ensures values[drop..][i] == values[drop + i]
  {
  }

  function SpecCounts(counts: RCore.ColumnCounts): RSpec.ColumnCounts
  {
    RSpec.ColumnCounts(counts.first, counts.second, counts.both)
  }

  lemma {:isolate_assertions} PrependFragment(
    head: BW.Bytes,
    tailFragments: seq<BW.Bytes>,
    tail: BW.Bytes,
    tailCuts: seq<nat>
  )
    requires RSpec.FragmentsConcatenate(tailFragments, tail, tailCuts)
    ensures RSpec.FragmentsConcatenate(
              [head] + tailFragments, head + tail, [0] + ShiftNats(tailCuts, |head|)
            )
  {
    reveal RSpec.FragmentsConcatenate();
    forall i: nat {:trigger ([0] + ShiftNats(tailCuts, |head|))[i]}
      | i < |[head] + tailFragments|
      ensures
        ([0] + ShiftNats(tailCuts, |head|))[i] <=
        ([0] + ShiftNats(tailCuts, |head|))[i + 1] <= |head + tail| &&
        ([0] + ShiftNats(tailCuts, |head|))[i + 1] ==
        ([0] + ShiftNats(tailCuts, |head|))[i] + |([head] + tailFragments)[i]| &&
        (head + tail)[
        ([0] + ShiftNats(tailCuts, |head|))[i]..
        ([0] + ShiftNats(tailCuts, |head|))[i + 1]
        ] == ([head] + tailFragments)[i]
    {
      ShiftNatsIndex(tailCuts, |head|, i);
      if i == 0 {
        assert (head + tail)[0..|head|] == head;
      } else {
        var k := i - 1;
        ShiftNatsIndex(tailCuts, |head|, k);
        PrependSlice(head, tail, tailCuts[k], tailCuts[k + 1]);
      }
    }
  }

  lemma RecordDelimiterEq(zeroTerminated: bool)
    ensures RCore.RecordDelimiter(zeroTerminated) == RSpec.RecordDelimiter(zeroTerminated)
  {
  }

  lemma DelimiterValuesMatchAll(first: string, rest: seq<string>)
    ensures RCore.DelimiterValuesMatch(first, rest) ==
            (forall i: nat :: i < |rest| ==> rest[i] == first)
    decreases |rest|
  {
    if |rest| > 0 {
      DelimiterValuesMatchAll(first, rest[1..]);
      assert forall i: nat :: i < |rest| ==>
                                (rest[i] == first) ==
                                ((i == 0 && rest[0] == first) ||
                                 (i > 0 && rest[1..][i - 1] == first));
    }
  }

  lemma HasConflictingOutputDelimitersEq(values: seq<string>)
    ensures RCore.HasConflictingOutputDelimiters(values) ==
            RSpec.HasConflictingOutputDelimitersRelation(values)
  {
    if |values| > 0 {
      DelimiterValuesMatchAll(values[0], values[1..]);
      if RCore.HasConflictingOutputDelimiters(values) {
        var i :| 0 <= i < |values[1..]| && values[1..][i] != values[0];
        assert 1 <= i + 1 < |values|;
      } else {
        assert forall i: nat :: 1 <= i < |values| ==> values[i] == values[0] by {
          forall i: nat | 1 <= i < |values|
            ensures values[i] == values[0]
          {
            assert values[1..][i - 1] == values[0];
          }
        }
      }
    }
  }

  lemma OutputDelimiterFromValuesEq(values: seq<string>)
    ensures RCore.OutputDelimiterFromValues(values) == RSpec.OutputDelimiterFromValues(values)
  {
  }

  lemma {:isolate_assertions} RecordsFromWitness(
    data: BW.Bytes,
    current: BW.Bytes,
    delimiter: BW.RawByte
  ) returns (
      records: seq<BW.Bytes>,
      terminated: seq<bool>,
      fragments: seq<BW.Bytes>,
      cuts: seq<nat>
    )
    requires forall j: nat :: j < |current| ==> current[j] != delimiter
    ensures records == RCore.RecordsFrom(data, current, delimiter)
    ensures RSpec.RecordPartitionWitness(
              current + data, delimiter, records, terminated, fragments, cuts
            )
    decreases |data|
  {
    if |data| == 0 {
      if |current| == 0 {
        records := [];
        terminated := [];
        fragments := [];
        cuts := [0];
      } else {
        records := [current];
        terminated := [false];
        fragments := [current];
        cuts := [0, |current|];
      }
      reveal RSpec.RecordPartitionWitness();
      reveal RSpec.FragmentsConcatenate();
    } else if data[0] == delimiter {
      var tailRecords, tailTerminated, tailFragments, tailCuts :=
        RecordsFromWitness(data[1..], [], delimiter);
      var head := current + [delimiter];
      records := [current] + tailRecords;
      terminated := [true] + tailTerminated;
      fragments := [head] + tailFragments;
      cuts := [0] + ShiftNats(tailCuts, |head|);
      PrependFragment(head, tailFragments, data[1..], tailCuts);
      reveal RSpec.RecordPartitionWitness();
      assert current + data == head + data[1..];
      assert forall i: nat :: i < |records| ==>
                                |fragments[i]| > 0 &&
                                fragments[i] ==
                                records[i] + (if terminated[i] then [delimiter] else []) &&
                                (forall j: nat :: j < |records[i]| ==> records[i][j] != delimiter) &&
                                (i + 1 < |records| ==> terminated[i]) by {
        forall i: nat | i < |records|
          ensures
            |fragments[i]| > 0 &&
            fragments[i] ==
            records[i] + (if terminated[i] then [delimiter] else []) &&
            (forall j: nat :: j < |records[i]| ==> records[i][j] != delimiter) &&
            (i + 1 < |records| ==> terminated[i])
        {
        }
      }
    } else {
      records, terminated, fragments, cuts :=
        RecordsFromWitness(data[1..], current + [data[0]], delimiter);
      assert current + data == (current + [data[0]]) + data[1..];
    }
  }

  lemma RecordsWitness(data: BW.Bytes, delimiter: BW.RawByte) returns (
      records: seq<BW.Bytes>,
      terminated: seq<bool>,
      fragments: seq<BW.Bytes>,
      cuts: seq<nat>
    )
    ensures records == RCore.Records(data, delimiter)
    ensures RSpec.RecordPartitionWitness(
              data, delimiter, records, terminated, fragments, cuts
            )
    ensures RSpec.RecordPartition(data, delimiter, records)
  {
    records, terminated, fragments, cuts := RecordsFromWitness(data, [], delimiter);
    reveal RSpec.RecordPartition();
    assert exists ts: seq<bool>, fs: seq<BW.Bytes>, cs: seq<nat> ::
        RSpec.RecordPartitionWitness(data, delimiter, records, ts, fs, cs) by {
      assert RSpec.RecordPartitionWitness(
          data, delimiter, records, terminated, fragments, cuts
        );
    }
  }

  lemma CompareLessImpliesBytesLess(left: BW.Bytes, right: BW.Bytes)
    requires RCore.CompareRecords(left, right) == RCore.LineLess
    ensures RSpec.BytesLess(left, right)
    decreases |left| + |right|
  {
    reveal RSpec.BytesLess();
    if |left| == 0 {
      assert |right| > 0;
      assert RSpec.BytesLess(left, right) by {
        reveal RSpec.BytesLess();
        assert RSpec.BytesLessAt(left, right, 0) by {
          reveal RSpec.BytesLessAt();
        }
      }
    } else if |right| == 0 {
      assert false;
    } else if (left[0] as int) < (right[0] as int) {
      assert RSpec.ByteValue(left, 0) < RSpec.ByteValue(right, 0);
      assert RSpec.BytesLess(left, right) by {
        reveal RSpec.BytesLess();
        assert RSpec.BytesLessAt(left, right, 0) by {
          reveal RSpec.BytesLessAt();
        }
      }
    } else {
      assert left[0] == right[0];
      CompareLessImpliesBytesLess(left[1..], right[1..]);
      reveal RSpec.BytesLess();
      var i: nat :| RSpec.BytesLessAt(left[1..], right[1..], i);
      reveal RSpec.BytesLessAt();
      assert forall j: nat :: j < i + 1 ==> left[j] == right[j] by {
        forall j: nat | j < i + 1
          ensures left[j] == right[j]
        {
        }
      }
      if i == |left[1..]| {
        assert i + 1 == |left|;
        assert i + 1 < |right|;
      } else {
        assert i < |left[1..]| && i < |right[1..]|;
        ByteValueTail(left, i);
        ByteValueTail(right, i);
      }
      var k := i + 1;
      assert k <= |left| && k <= |right|;
      assert forall j: nat :: j < k ==> left[j] == right[j];
      assert k == |left| < |right| ||
             (k < |left| && k < |right| &&
              RSpec.ByteValue(left, k) < RSpec.ByteValue(right, k));
      assert RSpec.BytesLessAt(left, right, k) by {
        reveal RSpec.BytesLessAt();
      }
    }
  }

  lemma BytesLessImpliesCompareLess(left: BW.Bytes, right: BW.Bytes)
    requires RSpec.BytesLess(left, right)
    ensures RCore.CompareRecords(left, right) == RCore.LineLess
    decreases |left| + |right|
  {
    reveal RSpec.BytesLess();
    var i: nat :| RSpec.BytesLessAt(left, right, i);
    reveal RSpec.BytesLessAt();
    if i > 0 {
      assert left[0] == right[0];
      assert RSpec.BytesLess(left[1..], right[1..]) by {
        reveal RSpec.BytesLess();
        assert forall j: nat :: j < i - 1 ==>
                                  left[1..][j] == right[1..][j] by {
          forall j: nat | j < i - 1
            ensures left[1..][j] == right[1..][j]
          {
            assert j + 1 < i;
          }
        }
        if i == |left| {
          assert i - 1 == |left[1..]|;
          assert i - 1 < |right[1..]|;
        } else {
          assert i < |left| && i < |right|;
          ByteValueTail(left, i - 1);
          ByteValueTail(right, i - 1);
        }
        var k := i - 1;
        assert k <= |left[1..]| && k <= |right[1..]|;
        assert forall j: nat :: j < k ==> left[1..][j] == right[1..][j];
        assert k == |left[1..]| < |right[1..]| ||
               (k < |left[1..]| && k < |right[1..]| &&
                RSpec.ByteValue(left[1..], k) < RSpec.ByteValue(right[1..], k));
        assert RSpec.BytesLessAt(left[1..], right[1..], k) by {
          reveal RSpec.BytesLessAt();
        }
      }
      BytesLessImpliesCompareLess(left[1..], right[1..]);
    } else {
      if |left| == 0 {
        assert |right| > 0;
      } else {
        assert |right| > 0;
        assert RSpec.ByteValue(left, 0) == left[0] as int;
        assert RSpec.ByteValue(right, 0) == right[0] as int;
      }
    }
  }

  lemma CompareLessReverseGreater(left: BW.Bytes, right: BW.Bytes)
    requires RCore.CompareRecords(left, right) == RCore.LineLess
    ensures RCore.CompareRecords(right, left) == RCore.LineGreater
    decreases |left| + |right|
  {
    if |left| > 0 && |right| > 0 &&
       !((left[0] as int) < (right[0] as int)) {
      assert left[0] == right[0];
      CompareLessReverseGreater(left[1..], right[1..]);
    }
  }

  lemma CompareGreaterReverseLess(left: BW.Bytes, right: BW.Bytes)
    requires RCore.CompareRecords(left, right) == RCore.LineGreater
    ensures RCore.CompareRecords(right, left) == RCore.LineLess
    decreases |left| + |right|
  {
    if |left| > 0 && |right| > 0 &&
       !((right[0] as int) < (left[0] as int)) {
      assert left[0] == right[0];
      CompareGreaterReverseLess(left[1..], right[1..]);
    }
  }

  lemma CompareEqualImpliesEqual(left: BW.Bytes, right: BW.Bytes)
    requires RCore.CompareRecords(left, right) == RCore.LineEqual
    ensures left == right
    decreases |left| + |right|
  {
    if |left| > 0 {
      assert |right| > 0;
      assert left[0] == right[0];
      CompareEqualImpliesEqual(left[1..], right[1..]);
    }
  }

  lemma RecordsSortedRelation(records: seq<BW.Bytes>)
    requires RCore.RecordsSorted(records)
    ensures RSpec.RecordsSortedRelation(records)
    decreases |records|
  {
    reveal RSpec.RecordsSortedRelation();
    if |records| >= 2 {
      RecordsSortedRelation(records[1..]);
      assert !RSpec.BytesLess(records[1], records[0]) by {
        if RSpec.BytesLess(records[1], records[0]) {
          BytesLessImpliesCompareLess(records[1], records[0]);
          CompareLessReverseGreater(records[1], records[0]);
        }
      }
      assert forall i: nat :: i + 1 < |records| ==>
                                !RSpec.BytesLess(records[i + 1], records[i]) by {
        forall i: nat | i + 1 < |records|
          ensures !RSpec.BytesLess(records[i + 1], records[i])
        {
          if i > 0 {
            assert records[1..][i - 1] == records[i];
            assert records[1..][i] == records[i + 1];
          }
        }
      }
    }
  }

  lemma DataSortedRelation(data: BW.Bytes, zeroTerminated: bool)
    requires RCore.DataSorted(data, zeroTerminated)
    ensures RSpec.DataSortedRelation(data, zeroTerminated)
  {
    var delimiter := RCore.RecordDelimiter(zeroTerminated);
    RecordDelimiterEq(zeroTerminated);
    var records, terminated, fragments, cuts := RecordsWitness(data, delimiter);
    RecordsSortedRelation(records);
    reveal RSpec.DataSortedRelation();
  }

  lemma RecordsUnsortedRelation(records: seq<BW.Bytes>)
    requires !RCore.RecordsSorted(records)
    ensures RSpec.RecordsUnsorted(records)
    decreases |records|
  {
    reveal RSpec.RecordsUnsorted();
    assert |records| >= 2;
    if RCore.CompareRecords(records[0], records[1]) == RCore.LineGreater {
      CompareGreaterReverseLess(records[0], records[1]);
      CompareLessImpliesBytesLess(records[1], records[0]);
      assert RSpec.UnsortedAt(records, 0) by {
        reveal RSpec.UnsortedAt();
      }
    } else {
      RecordsUnsortedRelation(records[1..]);
      var i: nat :| RSpec.UnsortedAt(records[1..], i);
      reveal RSpec.UnsortedAt();
      assert RSpec.UnsortedAt(records, i + 1) by {
        reveal RSpec.UnsortedAt();
      }
    }
  }

  lemma DataUnsortedRelation(data: BW.Bytes, zeroTerminated: bool)
    requires !RCore.DataSorted(data, zeroTerminated)
    ensures RSpec.DataUnsorted(data, zeroTerminated)
  {
    var delimiter := RCore.RecordDelimiter(zeroTerminated);
    RecordDelimiterEq(zeroTerminated);
    var records, terminated, fragments, cuts := RecordsWitness(data, delimiter);
    RecordsUnsortedRelation(records);
    reveal RSpec.DataUnsorted();
  }

  lemma {:isolate_assertions} PrependMergeWitness(
    cmd: Schema.CommCmd,
    left: seq<BW.Bytes>,
    right: seq<BW.Bytes>,
    leftAfter: seq<BW.Bytes>,
    rightAfter: seq<BW.Bytes>,
    kind: RSpec.MergeKind,
    head: BW.Bytes,
    body: BW.Bytes,
    counts: RSpec.ColumnCounts,
    kinds: seq<RSpec.MergeKind>,
    leftStates: seq<seq<BW.Bytes>>,
    rightStates: seq<seq<BW.Bytes>>,
    suffixCounts: seq<RSpec.ColumnCounts>,
    fragments: seq<BW.Bytes>,
    cuts: seq<nat>
  )
    requires RSpec.MergeWitness(
               cmd, leftAfter, rightAfter, body, counts, kinds,
               leftStates, rightStates, suffixCounts, fragments, cuts
             )
    requires RSpec.MergeStepRelation(
               cmd, kind, left, leftAfter, right, rightAfter, head
             )
    ensures RSpec.MergeWitness(
              cmd, left, right, head + body, RSpec.AddKind(kind, counts),
              [kind] + kinds, [left] + leftStates, [right] + rightStates,
              [RSpec.AddKind(kind, counts)] + suffixCounts,
              [head] + fragments, [0] + ShiftNats(cuts, |head|)
            )
  {
    PrependFragment(head, fragments, body, cuts);
    reveal RSpec.MergeWitness();
    assert forall i: nat {:trigger ([kind] + kinds)[i]} ::
        i < |[kind] + kinds| ==>
          ([RSpec.AddKind(kind, counts)] + suffixCounts)[i] ==
          RSpec.AddKind(
            ([kind] + kinds)[i],
            ([RSpec.AddKind(kind, counts)] + suffixCounts)[i + 1]
          ) &&
          RSpec.MergeStepRelation(
            cmd, ([kind] + kinds)[i],
            ([left] + leftStates)[i], ([left] + leftStates)[i + 1],
            ([right] + rightStates)[i], ([right] + rightStates)[i + 1],
            ([head] + fragments)[i]
          ) by {
      forall i: nat | i < |[kind] + kinds|
        ensures
          ([RSpec.AddKind(kind, counts)] + suffixCounts)[i] ==
          RSpec.AddKind(
            ([kind] + kinds)[i],
            ([RSpec.AddKind(kind, counts)] + suffixCounts)[i + 1]
          ) &&
          RSpec.MergeStepRelation(
            cmd, ([kind] + kinds)[i],
            ([left] + leftStates)[i], ([left] + leftStates)[i + 1],
            ([right] + rightStates)[i], ([right] + rightStates)[i + 1],
            ([head] + fragments)[i]
          )
      {
        if i > 0 {
          var k := i - 1;
          assert k < |kinds|;
          assert leftStates[k] == leftStates[k];
          assert rightStates[k] == rightStates[k];
          assert suffixCounts[k] == RSpec.AddKind(kinds[k], suffixCounts[k + 1]);
          assert RSpec.MergeStepRelation(
              cmd, kinds[k],
              leftStates[k], leftStates[k + 1],
              rightStates[k], rightStates[k + 1],
              fragments[k]
            );
        }
      }
    }
    assert RSpec.MergeWitness(
        cmd, left, right, head + body, RSpec.AddKind(kind, counts),
        [kind] + kinds, [left] + leftStates, [right] + rightStates,
        [RSpec.AddKind(kind, counts)] + suffixCounts,
        [head] + fragments, [0] + ShiftNats(cuts, |head|)
      );
  }

  lemma MergeWitnessForCore(
    cmd: Schema.CommCmd,
    left: seq<BW.Bytes>,
    right: seq<BW.Bytes>
  ) returns (
      body: BW.Bytes,
      coreCounts: RCore.ColumnCounts,
      counts: RSpec.ColumnCounts,
      kinds: seq<RSpec.MergeKind>,
      leftStates: seq<seq<BW.Bytes>>,
      rightStates: seq<seq<BW.Bytes>>,
      suffixCounts: seq<RSpec.ColumnCounts>,
      fragments: seq<BW.Bytes>,
      cuts: seq<nat>
    )
    ensures body == RCore.RenderRecords(cmd, left, right)
    ensures coreCounts == RCore.CountRecords(left, right)
    ensures counts == SpecCounts(coreCounts)
    ensures RSpec.MergeWitness(
              cmd, left, right, body, counts, kinds, leftStates, rightStates,
              suffixCounts, fragments, cuts
            )
    decreases |left| + |right|
  {
    if |left| == 0 && |right| == 0 {
      body := [];
      coreCounts := RCore.ColumnCounts(0, 0, 0);
      counts := RSpec.ColumnCounts(0, 0, 0);
      kinds := [];
      leftStates := [left];
      rightStates := [right];
      suffixCounts := [counts];
      fragments := [];
      cuts := [0];
      reveal RSpec.MergeWitness();
      reveal RSpec.FragmentsConcatenate();
    } else if |left| == 0 {
      var tailBody, tailCoreCounts, tailCounts, tailKinds, tailLeftStates,
          tailRightStates, tailSuffixCounts, tailFragments, tailCuts :=
        MergeWitnessForCore(cmd, left, right[1..]);
      var head := RCore.RenderOnlySecond(cmd, right[0]);
      body := head + tailBody;
      coreCounts := RCore.AddSecond(tailCoreCounts);
      counts := RSpec.AddKind(RSpec.OnlySecond, tailCounts);
      kinds := [RSpec.OnlySecond] + tailKinds;
      leftStates := [left] + tailLeftStates;
      rightStates := [right] + tailRightStates;
      suffixCounts := [counts] + tailSuffixCounts;
      fragments := [head] + tailFragments;
      cuts := [0] + ShiftNats(tailCuts, |head|);
      reveal RSpec.MergeStepRelation();
      assert RSpec.MergeStepRelation(
          cmd, RSpec.OnlySecond, left, left, right, right[1..], head
        );
      PrependMergeWitness(
        cmd, left, right, left, right[1..], RSpec.OnlySecond, head, tailBody,
        tailCounts, tailKinds, tailLeftStates, tailRightStates,
        tailSuffixCounts, tailFragments, tailCuts
      );
    } else if |right| == 0 {
      var tailBody, tailCoreCounts, tailCounts, tailKinds, tailLeftStates,
          tailRightStates, tailSuffixCounts, tailFragments, tailCuts :=
        MergeWitnessForCore(cmd, left[1..], right);
      var head := RCore.RenderOnlyFirst(cmd, left[0]);
      body := head + tailBody;
      coreCounts := RCore.AddFirst(tailCoreCounts);
      counts := RSpec.AddKind(RSpec.OnlyFirst, tailCounts);
      kinds := [RSpec.OnlyFirst] + tailKinds;
      leftStates := [left] + tailLeftStates;
      rightStates := [right] + tailRightStates;
      suffixCounts := [counts] + tailSuffixCounts;
      fragments := [head] + tailFragments;
      cuts := [0] + ShiftNats(tailCuts, |head|);
      reveal RSpec.MergeStepRelation();
      assert RSpec.MergeStepRelation(
          cmd, RSpec.OnlyFirst, left, left[1..], right, right, head
        );
      PrependMergeWitness(
        cmd, left, right, left[1..], right, RSpec.OnlyFirst, head, tailBody,
        tailCounts, tailKinds, tailLeftStates, tailRightStates,
        tailSuffixCounts, tailFragments, tailCuts
      );
    } else {
      match RCore.CompareRecords(left[0], right[0])
      case LineLess =>
        CompareLessImpliesBytesLess(left[0], right[0]);
        var tailBody, tailCoreCounts, tailCounts, tailKinds, tailLeftStates,
            tailRightStates, tailSuffixCounts, tailFragments, tailCuts :=
          MergeWitnessForCore(cmd, left[1..], right);
        var head := RCore.RenderOnlyFirst(cmd, left[0]);
        body := head + tailBody;
        coreCounts := RCore.AddFirst(tailCoreCounts);
        counts := RSpec.AddKind(RSpec.OnlyFirst, tailCounts);
        kinds := [RSpec.OnlyFirst] + tailKinds;
        leftStates := [left] + tailLeftStates;
        rightStates := [right] + tailRightStates;
        suffixCounts := [counts] + tailSuffixCounts;
        fragments := [head] + tailFragments;
        cuts := [0] + ShiftNats(tailCuts, |head|);
        reveal RSpec.MergeStepRelation();
               PrependMergeWitness(
                 cmd, left, right, left[1..], right, RSpec.OnlyFirst, head, tailBody,
                 tailCounts, tailKinds, tailLeftStates, tailRightStates,
                 tailSuffixCounts, tailFragments, tailCuts
               );
      case LineGreater =>
        CompareGreaterReverseLess(left[0], right[0]);
        CompareLessImpliesBytesLess(right[0], left[0]);
        var tailBody, tailCoreCounts, tailCounts, tailKinds, tailLeftStates,
            tailRightStates, tailSuffixCounts, tailFragments, tailCuts :=
          MergeWitnessForCore(cmd, left, right[1..]);
        var head := RCore.RenderOnlySecond(cmd, right[0]);
        body := head + tailBody;
        coreCounts := RCore.AddSecond(tailCoreCounts);
        counts := RSpec.AddKind(RSpec.OnlySecond, tailCounts);
        kinds := [RSpec.OnlySecond] + tailKinds;
        leftStates := [left] + tailLeftStates;
        rightStates := [right] + tailRightStates;
        suffixCounts := [counts] + tailSuffixCounts;
        fragments := [head] + tailFragments;
        cuts := [0] + ShiftNats(tailCuts, |head|);
        reveal RSpec.MergeStepRelation();
               PrependMergeWitness(
                 cmd, left, right, left, right[1..], RSpec.OnlySecond, head, tailBody,
                 tailCounts, tailKinds, tailLeftStates, tailRightStates,
                 tailSuffixCounts, tailFragments, tailCuts
               );
      case LineEqual =>
        CompareEqualImpliesEqual(left[0], right[0]);
        var tailBody, tailCoreCounts, tailCounts, tailKinds, tailLeftStates,
            tailRightStates, tailSuffixCounts, tailFragments, tailCuts :=
          MergeWitnessForCore(cmd, left[1..], right[1..]);
        var head := RCore.RenderBoth(cmd, left[0]);
        body := head + tailBody;
        coreCounts := RCore.AddBoth(tailCoreCounts);
        counts := RSpec.AddKind(RSpec.Both, tailCounts);
        kinds := [RSpec.Both] + tailKinds;
        leftStates := [left] + tailLeftStates;
        rightStates := [right] + tailRightStates;
        suffixCounts := [counts] + tailSuffixCounts;
        fragments := [head] + tailFragments;
        cuts := [0] + ShiftNats(tailCuts, |head|);
        reveal RSpec.MergeStepRelation();
               PrependMergeWitness(
                 cmd, left, right, left[1..], right[1..], RSpec.Both, head, tailBody,
                 tailCounts, tailKinds, tailLeftStates, tailRightStates,
                 tailSuffixCounts, tailFragments, tailCuts
               );
    }
  }

  lemma DecimalTextForCore(n: nat) returns (
      text: BW.Bytes,
      digits: seq<nat>,
      values: seq<nat>
    )
    ensures text == RCore.NatText(n)
    ensures RSpec.DecimalTextWitness(n, text, digits, values)
    ensures RSpec.DecimalText(n, text)
    decreases n
  {
    if n < 10 {
      text := [RCore.DigitChar(n)];
      digits := [n];
      values := [0, n];
      reveal RSpec.DecimalTextWitness();
    } else {
      var prefix, prefixDigits, prefixValues := DecimalTextForCore(n / 10);
      var digit := n % 10;
      text := prefix + [RCore.DigitChar(digit)];
      digits := prefixDigits + [digit];
      values := prefixValues + [n];
      reveal RSpec.DecimalTextWitness();
      assert forall i: nat :: i < |digits| ==>
                                digits[i] < 10 &&
                                text[i] == (('0' as int) + digits[i]) as char &&
                                values[i + 1] == values[i] * 10 + digits[i] by {
        forall i: nat | i < |digits|
          ensures
            digits[i] < 10 &&
            text[i] == (('0' as int) + digits[i]) as char &&
            values[i + 1] == values[i] * 10 + digits[i]
        {
          assert |text| == |digits|;
          assert |values| == |digits| + 1;
          assert i < |text|;
          assert i + 1 < |values|;
          if i + 1 == |digits| {
            assert values[i] == n / 10;
            assert n == (n / 10) * 10 + n % 10;
          }
        }
      }
    }
    reveal RSpec.DecimalText();
    assert exists ds: seq<nat>, vs: seq<nat> ::
        RSpec.DecimalTextWitness(n, text, ds, vs) by {
      assert RSpec.DecimalTextWitness(n, text, digits, values);
    }
  }

  lemma AppendSlice<T>(prefix: seq<T>, suffix: seq<T>, start: nat)
    requires start <= |suffix|
    ensures (prefix + suffix)[|prefix|..|prefix| + start] == suffix[..start]
  {
  }

  lemma {:isolate_assertions} AppendFragment(
    fragments: seq<BW.Bytes>,
    body: BW.Bytes,
    cuts: seq<nat>,
    last: BW.Bytes
  )
    requires RSpec.FragmentsConcatenate(fragments, body, cuts)
    ensures RSpec.FragmentsConcatenate(
              fragments + [last], body + last, cuts + [|body + last|]
            )
  {
    reveal RSpec.FragmentsConcatenate();
    assert forall i: nat {:trigger (cuts + [|body + last|])[i]} ::
        i < |fragments + [last]| ==>
          (cuts + [|body + last|])[i] <=
          (cuts + [|body + last|])[i + 1] <= |body + last| &&
          (cuts + [|body + last|])[i + 1] ==
          (cuts + [|body + last|])[i] + |(fragments + [last])[i]| &&
          (body + last)[
          (cuts + [|body + last|])[i]..
          (cuts + [|body + last|])[i + 1]
          ] == (fragments + [last])[i] by {
      forall i: nat {:trigger (cuts + [|body + last|])[i]}
    | i < |fragments + [last]|
        ensures
          (cuts + [|body + last|])[i] <=
          (cuts + [|body + last|])[i + 1] <= |body + last| &&
          (cuts + [|body + last|])[i + 1] ==
          (cuts + [|body + last|])[i] + |(fragments + [last])[i]| &&
          (body + last)[
          (cuts + [|body + last|])[i]..
          (cuts + [|body + last|])[i + 1]
          ] == (fragments + [last])[i]
      {
        if i < |fragments| {
          assert cuts[i + 1] <= |body|;
          assert (body + last)[cuts[i]..cuts[i + 1]] ==
                 body[cuts[i]..cuts[i + 1]];
        } else {
          assert i == |fragments|;
          assert cuts[i] == |body|;
          AppendSlice(body, last, |last|);
        }
      }
    }
  }

  lemma OutputRelationForCore(
    cmd: Schema.CommCmd,
    leftData: BW.Bytes,
    rightData: BW.Bytes
  )
    requires RCore.DataSorted(leftData, cmd.zeroTerminated)
    requires RCore.DataSorted(rightData, cmd.zeroTerminated)
    ensures RSpec.OutputRelation(
              cmd, leftData, rightData, RCore.RenderData(cmd, leftData, rightData)
            )
  {
    var delimiter := RCore.RecordDelimiter(cmd.zeroTerminated);
    RecordDelimiterEq(cmd.zeroTerminated);
    var left, leftTerminated, leftFragments, leftCuts :=
      RecordsWitness(leftData, delimiter);
    var right, rightTerminated, rightFragments, rightCuts :=
      RecordsWitness(rightData, delimiter);
    RecordsSortedRelation(left);
    RecordsSortedRelation(right);
    var body, coreCounts, counts, kinds, leftStates, rightStates,
        suffixCounts, bodyFragments, bodyCuts :=
      MergeWitnessForCore(cmd, left, right);
    var output := RCore.RenderData(cmd, leftData, rightData);
    var outputFragments: seq<BW.Bytes>;
    var outputCuts: seq<nat>;
    if cmd.total {
      var firstText, firstDigits, firstValues := DecimalTextForCore(coreCounts.first);
      var secondText, secondDigits, secondValues := DecimalTextForCore(coreCounts.second);
      var bothText, bothDigits, bothValues := DecimalTextForCore(coreCounts.both);
      var total := RCore.TotalRow(cmd, left, right);
      assert RSpec.TotalFragment(cmd, counts, total) by {
        reveal RSpec.TotalFragment();
      }
      assert output == body + total;
      outputFragments := bodyFragments + [total];
      outputCuts := bodyCuts + [|output|];
      AppendFragment(bodyFragments, body, bodyCuts, total);
    } else {
      assert RCore.TotalRow(cmd, left, right) == [];
      assert output == body;
      outputFragments := bodyFragments;
      outputCuts := bodyCuts;
    }
    reveal RSpec.OutputRelation();
    reveal RSpec.OutputWitness();
    assert RSpec.OutputWitness(
        cmd, leftData, rightData, output, left, right, counts, kinds,
        leftStates, rightStates, suffixCounts, bodyFragments, bodyCuts, body,
        outputFragments, outputCuts
      );
  }

  lemma FirstOperandEq(operands: seq<string>)
    ensures Core.FirstOperand(operands) == Spec.FirstOperand(operands)
  {
  }

  lemma SecondOperandEq(operands: seq<string>)
    ensures Core.SecondOperand(operands) == Spec.SecondOperand(operands)
  {
  }

  lemma InputFromOperandEq(operand: string)
    ensures Core.InputFromOperand(operand) == Spec.InputFromOperand(operand)
  {
  }

  lemma CommandEq(raw: Schema.CommCmdRaw)
    ensures Core.Command(raw) == Spec.CommandRelation(raw)
  {
    FirstOperandEq(raw.operands);
    SecondOperandEq(raw.operands);
    HasConflictingOutputDelimitersEq(raw.outputDelimiters);
    OutputDelimiterFromValuesEq(raw.outputDelimiters);
    InputFromOperandEq(Core.FirstOperand(raw.operands));
    InputFromOperandEq(Core.SecondOperand(raw.operands));
  }

  lemma InputResultEq(preFs: BW.FileSystem, preStdin: BW.Bytes, input: Schema.CommInput)
    ensures Core.InputResult(preFs, preStdin, input) == Spec.InputResult(preFs, preStdin, input)
  {
  }

  lemma AfterInputReadEq(preStdin: BW.Bytes, input: Schema.CommInput)
    ensures Core.AfterInputRead(preStdin, input) == Spec.AfterInputRead(preStdin, input)
  {
  }

  lemma ReadFirstResultEq(cmd: Schema.CommCmd, preFs: BW.FileSystem, preStdin: BW.Bytes)
    ensures Core.ReadFirstResult(cmd, preFs, preStdin) == Spec.ReadFirstResult(cmd, preFs, preStdin)
  {
    InputResultEq(preFs, preStdin, cmd.input1);
  }

  lemma AfterFirstReadEq(cmd: Schema.CommCmd, preStdin: BW.Bytes)
    ensures Core.AfterFirstRead(cmd, preStdin) == Spec.AfterFirstRead(cmd, preStdin)
  {
    AfterInputReadEq(preStdin, cmd.input1);
  }

  lemma ReadSecondResultEq(cmd: Schema.CommCmd, preFs: BW.FileSystem, preStdin: BW.Bytes)
    ensures Core.ReadSecondResult(cmd, preFs, preStdin) == Spec.ReadSecondResult(cmd, preFs, preStdin)
  {
    AfterFirstReadEq(cmd, preStdin);
    InputResultEq(preFs, Core.AfterFirstRead(cmd, preStdin), cmd.input2);
  }

  lemma AfterSecondReadEq(cmd: Schema.CommCmd, preStdin: BW.Bytes)
    ensures Core.AfterSecondRead(cmd, preStdin) == Spec.AfterSecondRead(cmd, preStdin)
  {
    AfterFirstReadEq(cmd, preStdin);
    AfterInputReadEq(Core.AfterFirstRead(cmd, preStdin), cmd.input2);
  }

  twostate lemma CoreSummaryImpliesSpec(
    raw: Schema.CommCmdRaw,
    io: BenchIO.IO,
    exit: int
  )
    requires Core.CoreSummary(raw, io, exit)
    ensures Spec.Spec(raw, io, exit)
  {
    CommandEq(raw);
    var cmd := Core.Command(raw);
    match cmd.mode
    case ModeHelp =>
    case ModeVersion =>
    case ModeMissingOperand =>
    case ModeMissingOperandAfter(_) =>
    case ModeExtraOperand(_) =>
    case ModeMultipleOutputDelimiters =>
    case ModeRepeatedStdinOperand =>
    case ModeRun =>
      ReadFirstResultEq(cmd, old(io.fs()), old(io.stdin()));
      AfterFirstReadEq(cmd, old(io.stdin()));
      var first := Core.ReadFirstResult(cmd, old(io.fs()), old(io.stdin()));
      match first
      case Err(_) =>
      case Ok(leftData) =>
        ReadSecondResultEq(cmd, old(io.fs()), old(io.stdin()));
        AfterSecondReadEq(cmd, old(io.stdin()));
        var second := Core.ReadSecondResult(cmd, old(io.fs()), old(io.stdin()));
        match second
        case Err(_) =>
        case Ok(rightData) =>
          if RCore.DataSorted(leftData, cmd.zeroTerminated) &&
             RCore.DataSorted(rightData, cmd.zeroTerminated) {
            DataSortedRelation(leftData, cmd.zeroTerminated);
            DataSortedRelation(rightData, cmd.zeroTerminated);
            OutputRelationForCore(cmd, leftData, rightData);
            assert Core.OutputForReads(cmd, first, second) ==
                   RCore.RenderData(cmd, leftData, rightData);
            assert exists stdoutPart: BW.Bytes ::
                stdoutPart == RCore.RenderData(cmd, leftData, rightData) &&
                RSpec.OutputRelation(cmd, leftData, rightData, stdoutPart) &&
                io.stdout() == old(io.stdout()) + stdoutPart;
          } else {
            if !RCore.DataSorted(leftData, cmd.zeroTerminated) {
              DataUnsortedRelation(leftData, cmd.zeroTerminated);
            } else {
              DataUnsortedRelation(rightData, cmd.zeroTerminated);
            }
          }
  }
}
