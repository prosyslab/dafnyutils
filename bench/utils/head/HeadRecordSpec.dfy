
module HeadRecordSpec {
  import BenchWorld

  function RecordDelimiter(zeroTerminated: bool): char
  {
    if zeroTerminated then '\0' else '\n'
  }

  ghost predicate RecordCountRelation(
    data: BenchWorld.Bytes,
    delimiter: char,
    count: nat
  )
  {
    count ==
    multiset(data)[delimiter] +
    (if |data| > 0 && data[|data| - 1] != delimiter then 1 else 0)
  }

  ghost predicate RecordCutPointRelation(
    data: BenchWorld.Bytes,
    delimiter: char,
    cut: nat,
    recordsBefore: nat
  )
  {
    cut <= |data| &&
    (cut == 0 || cut == |data| || data[cut - 1] == delimiter) &&
    RecordCountRelation(data[..cut], delimiter, recordsBefore)
  }

  ghost predicate RecordSelectionRelation(
    data: BenchWorld.Bytes,
    count: nat,
    delimiter: char,
    fromEnd: bool,
    output: BenchWorld.Bytes
  )
  {
    exists total: nat, cut: nat ::
      RecordCountRelation(data, delimiter, total) &&
      var keep :=
      (if fromEnd
       then if total <= count then 0 else total - count
       else if total <= count then total else count);
      RecordCutPointRelation(data, delimiter, cut, keep) &&
      output == data[..cut]
  }
}
