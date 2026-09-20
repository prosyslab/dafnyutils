
module TailRecordCore {
  import BenchWorld

  function RecordDelimiter(zeroTerminated: bool): char
  {
    if zeroTerminated then '\0' else '\n'
  }

  function ShiftCuts(cuts: seq<nat>, delta: nat): seq<nat>
  {
    seq(
    |cuts|,
    i requires 0 <= i < |cuts| => cuts[i] + delta
      )
  } by method {
    var shifted := [];
    var i := 0;
    while i < |cuts|
      invariant 0 <= i <= |cuts|
      invariant shifted == seq(
                           i,
                           j requires 0 <= j < i => cuts[j] + delta
                             )
      decreases |cuts| - i
    {
      shifted := shifted + [cuts[i] + delta];
      i := i + 1;
    }
    return shifted;
  }

  function RecordCuts(data: BenchWorld.Bytes, delimiter: char): seq<nat>
    ensures 0 < |RecordCuts(data, delimiter)|
    decreases |data|
  {
    if |data| == 0 then
      [0]
    else if |data| == 1 then
      [0, 1]
    else
      var tailCuts := ShiftCuts(RecordCuts(data[1..], delimiter), 1);
      if data[0] == delimiter then
        [0] + tailCuts
      else
        [0] + tailCuts[1..]
  } by method {
    if |data| == 0 {
      return [0];
    } else if |data| == 1 {
      return [0, 1];
    } else {
      var tailCuts := RecordCuts(data[1..], delimiter);
      var shifted := ShiftCuts(tailCuts, 1);
      return if data[0] == delimiter then [0] + shifted else [0] + shifted[1..];
    }
  }

  function RecordCount(data: BenchWorld.Bytes, delimiter: char): int
  {
    |RecordCuts(data, delimiter)| - 1
  } by method {
    var cuts := RecordCuts(data, delimiter);
    return |cuts| - 1;
  }

  function DropFirstRecords(
    data: BenchWorld.Bytes,
    count: int,
    delimiter: char
  ): BenchWorld.Bytes
  {
    var cuts := RecordCuts(data, delimiter);
    var drop :=
      if count <= 0 then 0
      else if |cuts| - 1 <= count then |cuts| - 1
      else count;
    if 0 <= drop < |cuts| && cuts[drop] <= |data| then data[cuts[drop]..] else []
  } by method {
    var cuts := RecordCuts(data, delimiter);
    var drop :=
      if count <= 0 then 0
      else if |cuts| - 1 <= count then |cuts| - 1
      else count;
    if 0 <= drop < |cuts| && cuts[drop] <= |data| {
      return data[cuts[drop]..];
    } else {
      return [];
    }
  }

  function TakeLastRecords(
    data: BenchWorld.Bytes,
    count: int,
    delimiter: char
  ): BenchWorld.Bytes
  {
    var cuts := RecordCuts(data, delimiter);
    var recordCount := |cuts| - 1;
    var drop :=
      if count <= 0 then recordCount
      else if recordCount <= count then 0
      else recordCount - count;
    if 0 <= drop < |cuts| && cuts[drop] <= |data| then data[cuts[drop]..] else []
  } by method {
    var cuts := RecordCuts(data, delimiter);
    var recordCount := |cuts| - 1;
    var drop :=
      if count <= 0 then recordCount
      else if recordCount <= count then 0
      else recordCount - count;
    if 0 <= drop < |cuts| && cuts[drop] <= |data| {
      return data[cuts[drop]..];
    } else {
      return [];
    }
  }
}
