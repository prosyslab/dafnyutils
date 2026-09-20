include "../../core/World.dfy"
include "CommSchema.dfy"

module CommRenderSpec {
  import BenchWorld
  import Utf8 = Utf8Semantics
  import Schema = CommSchema

  datatype MergeKind = OnlyFirst | OnlySecond | Both
  datatype ColumnCounts = ColumnCounts(first: nat, second: nat, both: nat)

  function RecordDelimiter(zeroTerminated: bool): BenchWorld.RawByte
  {
    if zeroTerminated then '\0' else '\n'
  }

  function OutputDelimiterFromValues(values: seq<string>): BenchWorld.Bytes
  {
    if |values| == 0 then ['\t'] else if values[0] == "" then ['\0'] else Utf8.Encode(values[0])
  }

  ghost predicate HasConflictingOutputDelimitersRelation(values: seq<string>)
  {
    |values| > 0 &&
    exists i: nat :: 1 <= i < |values| && values[i] != values[0]
  }

  function ByteValue(data: BenchWorld.Bytes, i: nat): int
  {
    if i < |data| then data[i] as int else -1
  }

  ghost predicate BytesLessAt(
    left: BenchWorld.Bytes,
    right: BenchWorld.Bytes,
    i: nat
  )
  {
    i <= |left| && i <= |right| &&
    left[..i] == right[..i] &&
    (i == |left| < |right| ||
     (i < |left| && i < |right| && ByteValue(left, i) < ByteValue(right, i)))
  }

  ghost predicate BytesLess(left: BenchWorld.Bytes, right: BenchWorld.Bytes)
  {
    exists i: nat :: BytesLessAt(left, right, i)
  }

  ghost predicate FragmentsConcatenate(
    fragments: seq<BenchWorld.Bytes>,
    combined: BenchWorld.Bytes,
    cuts: seq<nat>
  )
  {
    |cuts| == |fragments| + 1 &&
    cuts[0] == 0 &&
    cuts[|cuts| - 1] == |combined| &&
    forall i: nat {:trigger cuts[i]} :: i < |fragments| ==>
                                          cuts[i] <= cuts[i + 1] <= |combined| &&
                                          cuts[i + 1] == cuts[i] + |fragments[i]| &&
                                          combined[cuts[i]..cuts[i + 1]] == fragments[i]
  }

  ghost predicate RecordPartitionWitness(
    data: BenchWorld.Bytes,
    delimiter: BenchWorld.RawByte,
    records: seq<BenchWorld.Bytes>,
    terminated: seq<bool>,
    fragments: seq<BenchWorld.Bytes>,
    cuts: seq<nat>
  )
  {
    |records| == |terminated| == |fragments| &&
    (|data| == 0) == (|records| == 0) &&
    (forall i: nat :: i < |records| ==>
                        |fragments[i]| > 0 &&
                        fragments[i] == records[i] + (if terminated[i] then [delimiter] else []) &&
                        delimiter !in records[i] &&
                        (i + 1 < |records| ==> terminated[i])) &&
    FragmentsConcatenate(fragments, data, cuts)
  }

  ghost predicate RecordPartition(
    data: BenchWorld.Bytes,
    delimiter: BenchWorld.RawByte,
    records: seq<BenchWorld.Bytes>
  )
  {
    exists terminated: seq<bool>, fragments: seq<BenchWorld.Bytes>, cuts: seq<nat> ::
      RecordPartitionWitness(data, delimiter, records, terminated, fragments, cuts)
  }

  ghost predicate RecordsSortedRelation(records: seq<BenchWorld.Bytes>)
  {
    forall i: nat :: i + 1 < |records| ==> !BytesLess(records[i + 1], records[i])
  }

  ghost predicate DataSortedRelation(data: BenchWorld.Bytes, zeroTerminated: bool)
  {
    exists records: seq<BenchWorld.Bytes> ::
      RecordPartition(data, RecordDelimiter(zeroTerminated), records) &&
      RecordsSortedRelation(records)
  }

  ghost predicate UnsortedAt(records: seq<BenchWorld.Bytes>, i: nat)
  {
    i + 1 < |records| && BytesLess(records[i + 1], records[i])
  }

  ghost predicate RecordsUnsorted(records: seq<BenchWorld.Bytes>)
  {
    exists i: nat :: UnsortedAt(records, i)
  }

  ghost predicate DataUnsorted(data: BenchWorld.Bytes, zeroTerminated: bool)
  {
    exists records: seq<BenchWorld.Bytes> ::
      RecordPartition(data, RecordDelimiter(zeroTerminated), records) &&
      RecordsUnsorted(records)
  }

  function RenderFragment(
    cmd: Schema.CommCmd,
    kind: MergeKind,
    record: BenchWorld.Bytes
  ): BenchWorld.Bytes
  {
    var terminator := [RecordDelimiter(cmd.zeroTerminated)];
    match kind
    case OnlyFirst =>
      if cmd.suppress1 then [] else record + terminator
    case OnlySecond =>
      if cmd.suppress2 then [] else
      (if cmd.suppress1 then [] else cmd.outputDelimiter) + record + terminator
    case Both =>
      if cmd.suppress3 then [] else
      (if cmd.suppress1 then [] else cmd.outputDelimiter) +
      (if cmd.suppress2 then [] else cmd.outputDelimiter) +
      record + terminator
  }

  function AddKind(kind: MergeKind, counts: ColumnCounts): ColumnCounts
  {
    match kind
    case OnlyFirst => ColumnCounts(counts.first + 1, counts.second, counts.both)
    case OnlySecond => ColumnCounts(counts.first, counts.second + 1, counts.both)
    case Both => ColumnCounts(counts.first, counts.second, counts.both + 1)
  }

  ghost predicate MergeStepRelation(
    cmd: Schema.CommCmd,
    kind: MergeKind,
    leftBefore: seq<BenchWorld.Bytes>,
    leftAfter: seq<BenchWorld.Bytes>,
    rightBefore: seq<BenchWorld.Bytes>,
    rightAfter: seq<BenchWorld.Bytes>,
    fragment: BenchWorld.Bytes
  )
  {
    match kind
    case OnlyFirst =>
      |leftBefore| > 0 &&
      (|rightBefore| == 0 || BytesLess(leftBefore[0], rightBefore[0])) &&
      leftAfter == leftBefore[1..] &&
      rightAfter == rightBefore &&
      fragment == RenderFragment(cmd, OnlyFirst, leftBefore[0])
    case OnlySecond =>
      |rightBefore| > 0 &&
      (|leftBefore| == 0 || BytesLess(rightBefore[0], leftBefore[0])) &&
      leftAfter == leftBefore &&
      rightAfter == rightBefore[1..] &&
      fragment == RenderFragment(cmd, OnlySecond, rightBefore[0])
    case Both =>
      |leftBefore| > 0 && |rightBefore| > 0 &&
      leftBefore[0] == rightBefore[0] &&
      leftAfter == leftBefore[1..] &&
      rightAfter == rightBefore[1..] &&
      fragment == RenderFragment(cmd, Both, leftBefore[0])
  }

  ghost predicate MergeWitness(
    cmd: Schema.CommCmd,
    left: seq<BenchWorld.Bytes>,
    right: seq<BenchWorld.Bytes>,
    body: BenchWorld.Bytes,
    counts: ColumnCounts,
    kinds: seq<MergeKind>,
    leftStates: seq<seq<BenchWorld.Bytes>>,
    rightStates: seq<seq<BenchWorld.Bytes>>,
    suffixCounts: seq<ColumnCounts>,
    fragments: seq<BenchWorld.Bytes>,
    cuts: seq<nat>
  )
  {
    |leftStates| == |rightStates| == |suffixCounts| == |kinds| + 1 &&
    |fragments| == |kinds| &&
    leftStates[0] == left && rightStates[0] == right &&
    leftStates[|kinds|] == [] &&
    rightStates[|kinds|] == [] &&
    suffixCounts[0] == counts &&
    suffixCounts[|kinds|] == ColumnCounts(0, 0, 0) &&
    (forall i: nat {:trigger kinds[i]} :: i < |kinds| ==>
                                            suffixCounts[i] == AddKind(kinds[i], suffixCounts[i + 1]) &&
                                            MergeStepRelation(
                                              cmd, kinds[i], leftStates[i], leftStates[i + 1],
                                              rightStates[i], rightStates[i + 1], fragments[i]
                                            )) &&
    FragmentsConcatenate(fragments, body, cuts)
  }

  ghost predicate DecimalTextWitness(
    n: nat,
    text: BenchWorld.Bytes,
    digits: seq<nat>,
    values: seq<nat>
  )
  {
    |digits| > 0 &&
    |text| == |digits| &&
    |values| == |digits| + 1 &&
    values[0] == 0 &&
    values[|digits|] == n &&
    (|digits| == 1 || digits[0] != 0) &&
    forall i: nat :: i < |digits| ==>
                       digits[i] < 10 &&
                       text[i] == (('0' as int) + digits[i]) as char &&
                       values[i + 1] == values[i] * 10 + digits[i]
  }

  ghost predicate DecimalText(n: nat, text: BenchWorld.Bytes)
  {
    exists digits: seq<nat>, values: seq<nat> ::
      DecimalTextWitness(n, text, digits, values)
  }

  ghost predicate TotalFragment(
    cmd: Schema.CommCmd,
    counts: ColumnCounts,
    fragment: BenchWorld.Bytes
  )
  {
    exists firstText: BenchWorld.Bytes,
      secondText: BenchWorld.Bytes,
      bothText: BenchWorld.Bytes ::
      DecimalText(counts.first, firstText) &&
      DecimalText(counts.second, secondText) &&
      DecimalText(counts.both, bothText) &&
      fragment ==
      firstText + cmd.outputDelimiter +
      secondText + cmd.outputDelimiter +
      bothText + cmd.outputDelimiter +
      "total" + [RecordDelimiter(cmd.zeroTerminated)]
  }

  ghost predicate OutputWitness(
    cmd: Schema.CommCmd,
    leftData: BenchWorld.Bytes,
    rightData: BenchWorld.Bytes,
    output: BenchWorld.Bytes,
    left: seq<BenchWorld.Bytes>,
    right: seq<BenchWorld.Bytes>,
    counts: ColumnCounts,
    kinds: seq<MergeKind>,
    leftStates: seq<seq<BenchWorld.Bytes>>,
    rightStates: seq<seq<BenchWorld.Bytes>>,
    suffixCounts: seq<ColumnCounts>,
    bodyFragments: seq<BenchWorld.Bytes>,
    bodyCuts: seq<nat>,
    body: BenchWorld.Bytes,
    outputFragments: seq<BenchWorld.Bytes>,
    outputCuts: seq<nat>
  )
  {
    RecordPartition(leftData, RecordDelimiter(cmd.zeroTerminated), left) &&
    RecordPartition(rightData, RecordDelimiter(cmd.zeroTerminated), right) &&
    RecordsSortedRelation(left) &&
    RecordsSortedRelation(right) &&
    MergeWitness(
      cmd, left, right, body, counts, kinds, leftStates, rightStates,
      suffixCounts, bodyFragments, bodyCuts
    ) &&
    (if cmd.total then
       |body| <= |output| &&
       output[..|body|] == body &&
       TotalFragment(cmd, counts, output[|body|..]) &&
       outputFragments == bodyFragments + [output[|body|..]]
     else
       output == body &&
       outputFragments == bodyFragments) &&
    FragmentsConcatenate(outputFragments, output, outputCuts)
  }

  ghost predicate OutputRelation(
    cmd: Schema.CommCmd,
    leftData: BenchWorld.Bytes,
    rightData: BenchWorld.Bytes,
    output: BenchWorld.Bytes
  )
  {
    exists left: seq<BenchWorld.Bytes>,
      right: seq<BenchWorld.Bytes>,
      counts: ColumnCounts,
      kinds: seq<MergeKind>,
      leftStates: seq<seq<BenchWorld.Bytes>>,
      rightStates: seq<seq<BenchWorld.Bytes>>,
      suffixCounts: seq<ColumnCounts>,
      bodyFragments: seq<BenchWorld.Bytes>,
      bodyCuts: seq<nat>,
      body: BenchWorld.Bytes,
      outputFragments: seq<BenchWorld.Bytes>,
      outputCuts: seq<nat> ::
      OutputWitness(
        cmd, leftData, rightData, output, left, right, counts, kinds,
        leftStates, rightStates, suffixCounts, bodyFragments, bodyCuts,
        body, outputFragments, outputCuts
      )
  }
}
