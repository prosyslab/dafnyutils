
module HeadRecordCore {
  import BenchWorld

  function RecordDelimiter(zeroTerminated: bool): char
  {
    if zeroTerminated then '\0' else '\n'
  }

  function RecordCount(data: BenchWorld.Bytes, delimiter: char): nat
    decreases |data|
  {
    if |data| == 0 then 0
    else if data[0] == delimiter then 1 + RecordCount(data[1..], delimiter)
    else if |data| == 1 then 1
    else RecordCount(data[1..], delimiter)
  } by method {
    if |data| == 0 {
      return 0;
    } else if data[0] == delimiter {
      return 1 + RecordCount(data[1..], delimiter);
    } else if |data| == 1 {
      return 1;
    } else {
      return RecordCount(data[1..], delimiter);
    }
  }

  function TakeFirstRecords(data: BenchWorld.Bytes, count: int, delimiter: char): BenchWorld.Bytes
    decreases |data|
  {
    if |data| == 0 || count <= 0 then []
    else if data[0] == delimiter then [data[0]] + TakeFirstRecords(data[1..], count - 1, delimiter)
    else [data[0]] + TakeFirstRecords(data[1..], count, delimiter)
  } by method {
    if |data| == 0 || count <= 0 {
      return [];
    } else if data[0] == delimiter {
      return [data[0]] +
        TakeFirstRecords(data[1..], count - 1, delimiter);
    } else {
      return [data[0]] + TakeFirstRecords(data[1..], count, delimiter);
    }
  }

  function TakeAllButLastRecords(data: BenchWorld.Bytes, count: nat, delimiter: char): BenchWorld.Bytes
  {
    var total := RecordCount(data, delimiter);
    var keep := if total <= count then 0 else total - count;
    TakeFirstRecords(data, keep, delimiter)
  } by method {
    var total := RecordCount(data, delimiter);
    var keep := if total <= count then 0 else total - count;
    return TakeFirstRecords(data, keep, delimiter);
  }
}
