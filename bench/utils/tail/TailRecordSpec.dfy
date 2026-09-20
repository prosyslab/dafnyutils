include "../../core/World.dfy"

module TailRecordSpec {
  import BenchWorld

  function RecordDelimiter(zeroTerminated: bool): char
  {
    if zeroTerminated then '\0' else '\n'
  }

  ghost predicate RecordInterval(
    data: BenchWorld.Bytes,
    delimiter: char,
    lo: nat,
    hi: nat
  )
  {
    lo < hi <= |data| &&
    delimiter !in data[lo..hi - 1] &&
    (data[hi - 1] == delimiter || hi == |data|)
  }

  ghost predicate RecordCutColumn(
    data: BenchWorld.Bytes,
    delimiter: char,
    cuts: seq<nat>
  )
  {
    0 < |cuts| &&
    cuts[0] == 0 &&
    cuts[|cuts| - 1] == |data| &&
    (forall i: nat {:trigger cuts[i]} | i + 1 < |cuts| ::
       RecordInterval(data, delimiter, cuts[i], cuts[i + 1]))
  }

  ghost predicate DropFirstRecordsRelation(
    data: BenchWorld.Bytes,
    count: nat,
    delimiter: char,
    out: BenchWorld.Bytes
  )
  {
    exists cuts: seq<nat> ::
      RecordCutColumn(data, delimiter, cuts) &&
      var recordCount := |cuts| - 1;
      var drop := if count < recordCount then count else recordCount;
      drop < |cuts| &&
      cuts[drop] <= |data| &&
      out == data[cuts[drop]..]
  }

  ghost predicate TakeLastRecordsRelation(
    data: BenchWorld.Bytes,
    count: nat,
    delimiter: char,
    out: BenchWorld.Bytes
  )
  {
    exists cuts: seq<nat> ::
      RecordCutColumn(data, delimiter, cuts) &&
      var recordCount := |cuts| - 1;
      var drop := if recordCount <= count then 0 else recordCount - count;
      drop < |cuts| &&
      cuts[drop] <= |data| &&
      out == data[cuts[drop]..]
  }

}
