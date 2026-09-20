include "../../core/World.dfy"
include "CommSchema.dfy"

module CommRenderCore {
  import BenchWorld
  import Utf8 = Utf8Semantics
  import Schema = CommSchema

  datatype LineOrder = LineLess | LineEqual | LineGreater
  datatype ColumnCounts = ColumnCounts(first: nat, second: nat, both: nat)

  function AddFirst(counts: ColumnCounts): ColumnCounts
  {
    ColumnCounts(counts.first + 1, counts.second, counts.both)
  }

  function AddSecond(counts: ColumnCounts): ColumnCounts
  {
    ColumnCounts(counts.first, counts.second + 1, counts.both)
  }

  function AddBoth(counts: ColumnCounts): ColumnCounts
  {
    ColumnCounts(counts.first, counts.second, counts.both + 1)
  }

  function RecordDelimiter(zeroTerminated: bool): BenchWorld.RawByte
  {
    if zeroTerminated then '\0' else '\n'
  }

  function RecordTerminator(cmd: Schema.CommCmd): BenchWorld.Bytes
  {
    [RecordDelimiter(cmd.zeroTerminated)]
  }

  function DelimiterValuesMatch(first: string, rest: seq<string>): bool
    decreases |rest|
  {
    if |rest| == 0 then true else rest[0] == first && DelimiterValuesMatch(first, rest[1..])
  }

  function HasConflictingOutputDelimiters(values: seq<string>): bool
  {
    |values| > 0 && !DelimiterValuesMatch(values[0], values[1..])
  }

  function OutputDelimiterFromValues(values: seq<string>): BenchWorld.Bytes
  {
    if |values| == 0 then ['\t'] else if values[0] == "" then ['\0'] else Utf8.Encode(values[0])
  }

  function RecordsFrom(data: BenchWorld.Bytes, current: BenchWorld.Bytes, delimiter: char): seq<BenchWorld.Bytes>
    decreases |data|
  {
    if |data| == 0 then
      if |current| == 0 then [] else [current]
    else if data[0] == delimiter then
      [current] + RecordsFrom(data[1..], [], delimiter)
    else
      RecordsFrom(data[1..], current + [data[0]], delimiter)
  }

  function Records(data: BenchWorld.Bytes, delimiter: char): seq<BenchWorld.Bytes>
  {
    RecordsFrom(data, [], delimiter)
  }

  function CompareRecords(left: BenchWorld.Bytes, right: BenchWorld.Bytes): LineOrder
    decreases |left| + |right|
  {
    if |left| == 0 && |right| == 0 then
      LineEqual
    else if |left| == 0 then
      LineLess
    else if |right| == 0 then
      LineGreater
    else if (left[0] as int) < (right[0] as int) then
      LineLess
    else if (right[0] as int) < (left[0] as int) then
      LineGreater
    else
      CompareRecords(left[1..], right[1..])
  }

  function Column2Prefix(cmd: Schema.CommCmd): BenchWorld.Bytes
  {
    if cmd.suppress1 then [] else cmd.outputDelimiter
  }

  function Column3Prefix(cmd: Schema.CommCmd): BenchWorld.Bytes
  {
    (if cmd.suppress1 then [] else cmd.outputDelimiter) +
    (if cmd.suppress2 then [] else cmd.outputDelimiter)
  }

  function RenderOnlyFirst(cmd: Schema.CommCmd, record: BenchWorld.Bytes): BenchWorld.Bytes
  {
    if cmd.suppress1 then [] else record + RecordTerminator(cmd)
  }

  function RenderOnlySecond(cmd: Schema.CommCmd, record: BenchWorld.Bytes): BenchWorld.Bytes
  {
    if cmd.suppress2 then [] else Column2Prefix(cmd) + record + RecordTerminator(cmd)
  }

  function RenderBoth(cmd: Schema.CommCmd, record: BenchWorld.Bytes): BenchWorld.Bytes
  {
    if cmd.suppress3 then [] else Column3Prefix(cmd) + record + RecordTerminator(cmd)
  }

  function RenderRecords(
    cmd: Schema.CommCmd,
    left: seq<BenchWorld.Bytes>,
    right: seq<BenchWorld.Bytes>
  ): BenchWorld.Bytes
    decreases |left| + |right|
  {
    if |left| == 0 then
      if |right| == 0 then
        []
      else
        RenderOnlySecond(cmd, right[0]) + RenderRecords(cmd, left, right[1..])
    else if |right| == 0 then
      RenderOnlyFirst(cmd, left[0]) + RenderRecords(cmd, left[1..], right)
    else
      match CompareRecords(left[0], right[0])
      case LineLess =>
        RenderOnlyFirst(cmd, left[0]) + RenderRecords(cmd, left[1..], right)
      case LineGreater =>
        RenderOnlySecond(cmd, right[0]) + RenderRecords(cmd, left, right[1..])
      case LineEqual =>
        RenderBoth(cmd, left[0]) + RenderRecords(cmd, left[1..], right[1..])
  }

  function CountRecords(left: seq<BenchWorld.Bytes>, right: seq<BenchWorld.Bytes>): ColumnCounts
    decreases |left| + |right|
  {
    if |left| == 0 then
      if |right| == 0 then
        ColumnCounts(0, 0, 0)
      else
        AddSecond(CountRecords(left, right[1..]))
    else if |right| == 0 then
      AddFirst(CountRecords(left[1..], right))
    else
      match CompareRecords(left[0], right[0])
      case LineLess =>
        AddFirst(CountRecords(left[1..], right))
      case LineGreater =>
        AddSecond(CountRecords(left, right[1..]))
      case LineEqual =>
        AddBoth(CountRecords(left[1..], right[1..]))
  }

  function DigitChar(n: nat): char
    requires n < 10
  {
    (('0' as int) + n) as char
  }

  function NatText(n: nat): BenchWorld.Bytes
    decreases n
  {
    if n < 10 then [DigitChar(n)] else NatText(n / 10) + [DigitChar(n % 10)]
  }

  function TotalRow(cmd: Schema.CommCmd, left: seq<BenchWorld.Bytes>, right: seq<BenchWorld.Bytes>): BenchWorld.Bytes
  {
    if !cmd.total then
      []
    else
      var counts := CountRecords(left, right);
      NatText(counts.first) + cmd.outputDelimiter +
      NatText(counts.second) + cmd.outputDelimiter +
      NatText(counts.both) + cmd.outputDelimiter +
      "total" + RecordTerminator(cmd)
  }

  function RenderData(
    cmd: Schema.CommCmd,
    leftData: BenchWorld.Bytes,
    rightData: BenchWorld.Bytes
  ): BenchWorld.Bytes
  {
    var delimiter := RecordDelimiter(cmd.zeroTerminated);
    var left := Records(leftData, delimiter);
    var right := Records(rightData, delimiter);
    RenderRecords(cmd, left, right) + TotalRow(cmd, left, right)
  }

  function RecordsSorted(records: seq<BenchWorld.Bytes>): bool
    decreases |records|
  {
    if |records| < 2 then
      true
    else
      CompareRecords(records[0], records[1]) != LineGreater && RecordsSorted(records[1..])
  }

  function DataSorted(data: BenchWorld.Bytes, zeroTerminated: bool): bool
  {
    RecordsSorted(Records(data, RecordDelimiter(zeroTerminated)))
  }

}
