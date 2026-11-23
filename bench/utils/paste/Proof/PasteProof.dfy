include "../../../core/World.dfy"
include "../Spec/PasteSchema.dfy"
include "../Impl/PasteCore.dfy"
include "../Spec/PasteSpec.dfy"

module PasteProof {
  import BenchWorld

  import Result = Results
  import BenchIO
  import Utf8 = Utf8Semantics
  import BW = BenchWorld
  import Schema = PasteSchema
  import Core = PasteCore
  import Spec = PasteSpec
  import C = IOContract

  ghost predicate FragmentsConcatenate<T>(
    fragments: seq<seq<T>>,
    combined: seq<T>,
    cuts: seq<nat>
  )
  {
    |cuts| == |fragments| + 1 &&
    cuts[0] == 0 &&
    cuts[|cuts| - 1] == |combined| &&
    forall i: nat {:trigger cuts[i]} | i < |fragments| ::
      cuts[i] <= cuts[i + 1] <= |combined| &&
      cuts[i + 1] == cuts[i] + |fragments[i]| &&
      combined[cuts[i]..cuts[i + 1]] == fragments[i]
  }

  ghost predicate LinePartitionRelation(
    data: BW.Bytes,
    recordDelimiter: BW.RawByte,
    lines: seq<BW.Bytes>,
    terminated: seq<bool>,
    fragments: seq<BW.Bytes>,
    cuts: seq<nat>
  )
  {
    |lines| == |terminated| == |fragments| &&
    FragmentsConcatenate(fragments, data, cuts) &&
    (forall i: nat | i < |lines| ::
       |fragments[i]| > 0 &&
       fragments[i] ==
       lines[i] + (if terminated[i] then [recordDelimiter] else []) &&
       recordDelimiter !in lines[i] &&
       (i + 1 < |lines| ==> terminated[i]))
  }

  datatype DelimiterAssembly =
    DelimiterDone |
    DelimiterFailure |
    DelimiterStep(
      index: nat,
      nextIndex: nat,
      delimiter: BW.Bytes,
      rest: DelimiterAssembly)

  ghost predicate DelimiterParseRelation(
    text: BW.Bytes,
    i: nat,
    result: Spec.DelimiterResult,
    assembly: DelimiterAssembly
  )
    decreases assembly
  {
    i <= |text| &&
    match assembly
    case DelimiterDone =>
      i == |text| && result == Result.Ok([])
    case DelimiterFailure =>
      i < |text| &&
      text[i] == '\\' &&
      i + 1 == |text| &&
      result == Result.Err(Spec.DelimiterBackslashError(text))
    case DelimiterStep(index, nextIndex, delimiter, rest) =>
      index == i &&
      i < |text| &&
      (if text[i] == '\\' then
         nextIndex == i + 2 &&
         i + 1 < |text| &&
         delimiter == Spec.EscapedDelimiter(text[i + 1])
       else
         nextIndex == i + 1 &&
         delimiter == [text[i]]) &&
      exists restResult: Spec.DelimiterResult ::
        DelimiterParseRelation(text, nextIndex, restResult, rest) &&
        result ==
        match restResult
        case Err(stderr) => Result.Err(stderr)
        case Ok(delims) => Result.Ok([delimiter] + delims)
  }

  ghost function ShiftCuts(cuts: seq<nat>, offset: nat): seq<nat>
  {
    seq(|cuts|, i requires 0 <= i < |cuts| => cuts[i] + offset)
  }

  lemma SliceAfterPrefix<T>(
    head: seq<T>,
    tail: seq<T>,
    start: nat,
    end: nat
  )
    requires start <= end <= |tail|
    ensures (head + tail)[|head| + start..|head| + end] ==
            tail[start..end]
  {
  }

  lemma PrependFragment<T>(
    head: seq<T>,
    tailFragments: seq<seq<T>>,
    tail: seq<T>,
    tailCuts: seq<nat>
  )
    requires FragmentsConcatenate(
               tailFragments, tail, tailCuts)
    ensures FragmentsConcatenate(
              [head] + tailFragments,
              head + tail,
              [0] + ShiftCuts(tailCuts, |head|))
  {
    reveal FragmentsConcatenate();
    forall i: nat {:trigger ([0] + ShiftCuts(
      tailCuts, |head|))[i]} | i < |[head] + tailFragments|
      ensures ([0] + ShiftCuts(tailCuts, |head|))[i] <=
              ([0] + ShiftCuts(tailCuts, |head|))[i + 1] <=
              |head + tail| &&
              ([0] + ShiftCuts(tailCuts, |head|))[i + 1] ==
              ([0] + ShiftCuts(tailCuts, |head|))[i] +
              |([head] + tailFragments)[i]| &&
              (head + tail)[
              ([0] + ShiftCuts(tailCuts, |head|))[i]..
              ([0] + ShiftCuts(tailCuts, |head|))[i + 1]
              ] == ([head] + tailFragments)[i]
    {
      if i > 0 {
        SliceAfterPrefix(
          head, tail, tailCuts[i - 1], tailCuts[i]);
      }
    }
  }

  lemma ReadLineShape(data: BW.Bytes, recordDelimiter: BW.RawByte)
    ensures
      match Core.ReadLine(data, recordDelimiter)
      case NoLine => data == []
      case SomeLine(line, rest) =>
        (forall j: nat :: j < |line| ==> line[j] != recordDelimiter) &&
        (data == line + [recordDelimiter] + rest ||
         (data == line && rest == []))
    decreases |data|
  {
    if |data| > 0 && data[0] != recordDelimiter {
      ReadLineShape(data[1..], recordDelimiter);
      match Core.ReadLine(data[1..], recordDelimiter)
      case NoLine =>
      case SomeLine(line, rest) =>
        assert forall j: nat :: j < |[data[0]] + line| ==>
                                  ([data[0]] + line)[j] != recordDelimiter by {
          forall j: nat | j < |[data[0]] + line|
            ensures ([data[0]] + line)[j] != recordDelimiter
          {
          }
        }
    }
  }

  lemma BuildLinePartition(
    data: BW.Bytes,
    recordDelimiter: BW.RawByte
  ) returns (
      terminated: seq<bool>,
      fragments: seq<BW.Bytes>,
      cuts: seq<nat>
    )
    ensures LinePartitionRelation(
              data,
              recordDelimiter,
              Core.Lines(data, recordDelimiter),
              terminated,
              fragments,
              cuts)
    decreases |data|
  {
    ReadLineShape(data, recordDelimiter);
    match Core.ReadLine(data, recordDelimiter)
    case NoLine =>
      terminated := [];
      fragments := [];
      cuts := [0];
      reveal LinePartitionRelation();
             reveal FragmentsConcatenate();
    case SomeLine(line, rest) =>
      if data == line + [recordDelimiter] + rest {
        var tailTerminated, tailFragments, tailCuts :=
          BuildLinePartition(rest, recordDelimiter);
        var head := line + [recordDelimiter];
        terminated := [true] + tailTerminated;
        fragments := [head] + tailFragments;
        cuts := [0] + ShiftCuts(tailCuts, |head|);
        PrependFragment(head, tailFragments, rest, tailCuts);
        reveal LinePartitionRelation();
        assert Core.Lines(data, recordDelimiter) ==
               [line] + Core.Lines(rest, recordDelimiter);
        assert forall i: nat :: i < |Core.Lines(data, recordDelimiter)| ==>
                                  |fragments[i]| > 0 &&
                                  fragments[i] ==
                                  Core.Lines(data, recordDelimiter)[i] +
                                  (if terminated[i] then [recordDelimiter] else []) &&
                                  (forall j: nat ::
                                     j < |Core.Lines(data, recordDelimiter)[i]| ==>
                                       Core.Lines(data, recordDelimiter)[i][j] !=
                                       recordDelimiter) &&
                                  (i + 1 < |Core.Lines(data, recordDelimiter)| ==>
                                     terminated[i]) by {
          forall i: nat | i < |Core.Lines(data, recordDelimiter)|
            ensures |fragments[i]| > 0 &&
                    fragments[i] ==
                    Core.Lines(data, recordDelimiter)[i] +
                    (if terminated[i] then [recordDelimiter] else []) &&
                    (forall j: nat ::
                       j < |Core.Lines(data, recordDelimiter)[i]| ==>
                         Core.Lines(data, recordDelimiter)[i][j] !=
                         recordDelimiter) &&
                    (i + 1 < |Core.Lines(data, recordDelimiter)| ==>
                       terminated[i])
          {
          }
        }
      } else {
        assert data == line && rest == [];
        terminated := [false];
        fragments := [line];
        cuts := [0, |line|];
        reveal LinePartitionRelation();
        reveal FragmentsConcatenate();
      }
  }

  lemma LinePartitionDenote(data: BW.Bytes, delimiter: BW.RawByte,
                            lines: seq<BW.Bytes>, terminated: seq<bool>,
                            fragments: seq<BW.Bytes>, cuts: seq<nat>)
    requires LinePartitionRelation(data, delimiter, lines, terminated, fragments, cuts)
    ensures Spec.LinesRelation(data, delimiter, lines)
  {
    FragmentsDenote(fragments, data, cuts, |fragments|);
    assert fragments[..|fragments|] == fragments;
    assert data[..cuts[|fragments|]] == data;
    if |lines| == 0 {
      assert data == [];
    } else {
      var last := |lines| - 1;
      assert data[cuts[last]..] == fragments[last];
      assert |data| > 0;
      assert data[|data| - 1] == fragments[last][|fragments[last]| - 1];
      assert terminated[last] == (data[|data| - 1] == delimiter);
      var joined := JoinedFragments(lines, [[delimiter]]);
      JoinedFragmentsEq(lines, [[delimiter]]);
      assert |joined| == |lines|;
      assert joined[last] == lines[last];
      assert fragments[..last] == joined[..last];
      assert fragments == fragments[..last] + [fragments[last]];
      assert joined == joined[..last] + [lines[last]];
      ConcatSnoc(fragments[..last], fragments[last]);
      ConcatSnoc(joined[..last], lines[last]);
      assert Spec.Concat<BW.RawByte>(joined) == Spec.Join(lines, [[delimiter]]);
    }
  }

  lemma JoinConstantHead(lines: seq<BW.Bytes>, delimiter: BW.RawByte)
    requires |lines| > 0
    ensures Spec.Join(lines, [[delimiter]]) == lines[0] +
                                               (if |lines| > 1 then [delimiter] + Spec.Join(lines[1..], [[delimiter]]) else [])
  {
    var pieces := JoinedFragments(lines, [[delimiter]]);
    JoinedFragmentsEq(lines, [[delimiter]]);
    JoinedFragmentsEq(lines[1..], [[delimiter]]);
    assert pieces[1..] == JoinedFragments(lines[1..], [[delimiter]]);
    assert pieces[0] == lines[0] + (if |lines| > 1 then [delimiter] else []);
  }

  lemma ReadRecordCons(head: BW.RawByte, data: BW.Bytes, delimiter: BW.RawByte,
                       line: BW.Bytes, rest: BW.Bytes)
    requires head != delimiter
    requires Core.ReadLine(data, delimiter) == Core.SomeLine(line, rest)
    ensures Core.ReadLine([head] + data, delimiter) == Core.SomeLine([head] + line, rest)
  {
    hide *;
    reveal Core.ReadLine();
  }

  lemma ReadRecord(line: BW.Bytes, delimiter: BW.RawByte, terminated: bool, rest: BW.Bytes)
    requires delimiter !in line
    requires terminated || (|line| > 0 && rest == [])
    ensures Core.ReadLine(line + (if terminated then [delimiter] else []) + rest, delimiter) ==
            Core.SomeLine(line, rest)
    decreases |line|
  {
    hide *;
    if |line| > 0 && (terminated || |line| > 1) {
      var ending: BW.Bytes := if terminated then [delimiter] else [];
      var tail: BW.Bytes := line[1..] + ending + rest;
      ReadRecord(line[1..], delimiter, terminated, rest);
      ReadRecordCons(line[0], tail, delimiter, line[1..], rest);
      assert line == [line[0]] + line[1..];
      assert line + ending + rest == [line[0]] + tail;
      assert Core.ReadLine(line + ending + rest, delimiter) == Core.SomeLine(line, rest);
    } else {
      reveal Core.ReadLine();
      if |line| == 0 {
        assert terminated;
        assert line + [delimiter] + rest == [delimiter] + rest;
      } else {
        assert |line| == 1 && !terminated && rest == [];
        assert line == [line[0]];
      }
    }
  }

  lemma LinesRelationMatchesCore(data: BW.Bytes, delimiter: BW.RawByte,
                                 lines: seq<BW.Bytes>)
    requires Spec.LinesRelation(data, delimiter, lines)
    ensures lines == Core.Lines(data, delimiter)
    decreases |lines|
  {
    if |data| > 0 {
      var ended := data[|data| - 1] == delimiter;
      JoinConstantHead(lines, delimiter);
      if |lines| == 1 {
        assert data == lines[0] + (if ended then [delimiter] else []);
        var empty: BW.Bytes := [];
        if ended {
          ReadRecord(lines[0], delimiter, true, empty);
          assert data == lines[0] + [delimiter] + empty;
        } else {
          ReadRecord(lines[0], delimiter, false, empty);
          assert data == lines[0] + empty + empty;
        }
        assert Core.ReadLine(data, delimiter) == Core.SomeLine(lines[0], []);
        assert lines == [lines[0]];
        assert Core.Lines([], delimiter) == [];
      } else {
        var rest := Spec.Join(lines[1..], [[delimiter]]) + (if ended then [delimiter] else []);
        assert data == lines[0] + [delimiter] + rest;
        assert |rest| > 0 by {
          if |rest| == 0 {
            assert data[|data| - 1] == delimiter;
          }
        }
        assert rest[|rest| - 1] == data[|data| - 1];
        assert Spec.LinesRelation(rest, delimiter, lines[1..]);
        ReadRecord(lines[0], delimiter, true, rest);
        LinesRelationMatchesCore(rest, delimiter, lines[1..]);
      }
    }
  }

  lemma LinesRelationEquivalent(data: BW.Bytes, delimiter: BW.RawByte, lines: seq<BW.Bytes>)
    ensures Spec.LinesRelation(data, delimiter, lines) <==>
            (exists terminated: seq<bool>, fragments: seq<BW.Bytes>, cuts: seq<nat> ::
               LinePartitionRelation(data, delimiter, lines, terminated, fragments, cuts))
  {
    if Spec.LinesRelation(data, delimiter, lines) {
      LinesRelationMatchesCore(data, delimiter, lines);
      var terminated, fragments, cuts := BuildLinePartition(data, delimiter);
    } else if exists terminated: seq<bool>, fragments: seq<BW.Bytes>, cuts: seq<nat> ::
        LinePartitionRelation(data, delimiter, lines, terminated, fragments, cuts) {
      var terminated: seq<bool>, fragments: seq<BW.Bytes>, cuts: seq<nat> :|
        LinePartitionRelation(data, delimiter, lines, terminated, fragments, cuts);
      LinePartitionDenote(data, delimiter, lines, terminated, fragments, cuts);
    }
  }

  lemma EntryRefines(
    result: BW.IOResult<BW.Bytes>,
                        recordDelimiter: BW.RawByte
  )
    ensures Spec.EntryRelation(
              result,
              recordDelimiter,
              Core.EntryForRead(result, recordDelimiter))
  {
    var terminated, fragments, cuts :=
      BuildLinePartition(C.ReadResultData(result), recordDelimiter);
    LinesRelationEquivalent(C.ReadResultData(result), recordDelimiter,
                            Core.EntryForRead(result, recordDelimiter).lines);
  }

  lemma PrefixEntriesIndex(
    cmd: Schema.PasteCmd,
    preFs: BW.FileSystem, preStreams: (BW.TrustedStreamRequest) -> BW.TrustedStreamResult,
    preStdin: BW.Bytes,
    i: nat,
    j: nat
  )
    requires j < i <= |cmd.inputs|
    ensures Core.PrefixEntriesCore(cmd, preFs, preStreams, preStdin, i)[j] ==
            Core.EntryForRead(
              Core.ReadResultCore(cmd, preFs, preStreams, preStdin, j),
              Spec.RecordDelimiter(cmd.zeroTerminated))
    decreases i
  {
    hide *;
    reveal Core.PrefixEntriesCore();
    if j + 1 < i {
      PrefixEntriesIndex(cmd, preFs, preStreams, preStdin, i - 1, j);
    }
  }

  lemma SelectedLinesRefines(
    lines: seq<BW.Bytes>,
    stdinIndex: nat,
    stdinCount: nat
  )
    requires stdinCount > 0
    ensures Spec.SelectedLinesRelation(
              lines,
              stdinIndex,
              stdinCount,
              Core.SelectStdinLines(lines, stdinIndex, stdinCount))
    decreases if stdinIndex <= |lines| then |lines| - stdinIndex else 0
  {
    if stdinIndex < |lines| {
      SelectedLinesRefines(
        lines, stdinIndex + stdinCount, stdinCount);
    }
    reveal Spec.SelectedLinesRelation();
  }

  lemma ParallelEntryAt(
    inputs: seq<Schema.Input>,
    entries: seq<Spec.Entry>,
    stdinLines: seq<BW.Bytes>,
    stdinCount: nat,
    start: nat,
    j: nat
  )
    requires |entries| == |inputs|
    requires start <= j < |inputs|
    ensures Core.ParallelEntriesFrom(
              inputs, entries, stdinLines, stdinCount, start)[j - start] ==
            match inputs[j]
            case Stdin =>
              Spec.Entry(
                Core.SelectStdinLines(
                  stdinLines,
                  Core.CountStdinPrefix(inputs, j),
                  stdinCount),
                true)
            case File(_) => entries[j]
    decreases j - start
  {
    assert |Core.ParallelEntriesFrom(
        inputs, entries, stdinLines, stdinCount, start)| ==
           |inputs| - start;
    if start < j {
      ParallelEntryAt(
        inputs, entries, stdinLines, stdinCount, start + 1, j);
    }
  }

  lemma StdinCountMatchesCore(inputs: seq<Schema.Input>, i: nat)
    requires i <= |inputs|
    ensures Spec.StdinCount(inputs[..i]) == Core.CountStdinPrefix(inputs, i)
    decreases i
  {
    if i > 0 {
      StdinCountMatchesCore(inputs, i - 1);
      StdinCountStep(inputs, i - 1);
    }
  }

  lemma EntriesForOutputRefines(cmd: Schema.PasteCmd, preStdin: BW.Bytes,
                                rawEntries: seq<Spec.Entry>)
    requires |rawEntries| == |cmd.inputs|
    ensures Spec.EntriesForOutputRelation(cmd, preStdin, rawEntries,
                                          Core.EntriesForOutputFromEntries(cmd, rawEntries,
                                                                           if Spec.HasStdinInput(cmd.inputs) then preStdin else []))
  {
    hide *;
    reveal Spec.EntriesForOutputRelation(), Core.EntriesForOutputFromEntries(),
           Core.CountStdinInputs(), Spec.StdinCount();
    if !cmd.serial {
      var data := if Spec.HasStdinInput(cmd.inputs) then preStdin else [];
      var delimiter := Spec.RecordDelimiter(cmd.zeroTerminated);
      var lines := Core.Lines(data, delimiter);
      var terminated, fragments, cuts := BuildLinePartition(data, delimiter);
      LinePartitionDenote(data, delimiter, lines, terminated, fragments, cuts);
      var entries := Core.EntriesForOutputFromEntries(cmd, rawEntries, data);
      StdinCountMatchesCore(cmd.inputs, |cmd.inputs|);
      assert cmd.inputs[..|cmd.inputs|] == cmd.inputs;
      assert Core.CountStdinInputs(cmd.inputs) == Spec.StdinCount(cmd.inputs);
      forall i: nat | i < |cmd.inputs|
        ensures if cmd.inputs[i].Stdin? then entries[i].readOk &&
                                             Spec.SelectedLinesRelation(lines, Spec.StdinCount(cmd.inputs[..i]),
                                                                        Spec.StdinCount(cmd.inputs), entries[i].lines)
                else entries[i] == rawEntries[i]
      {
        ParallelEntryAt(cmd.inputs, rawEntries, lines, Core.CountStdinInputs(cmd.inputs), 0, i);
        if cmd.inputs[i].Stdin? {
          assert Schema.Stdin in cmd.inputs;
          assert Spec.StdinCount(cmd.inputs) > 0;
          StdinCountMatchesCore(cmd.inputs, i);
          assert entries[i] == Spec.Entry(
                                 Core.SelectStdinLines(lines, Core.CountStdinPrefix(cmd.inputs, i),
                                                       Core.CountStdinInputs(cmd.inputs)), true);
          assert entries[i].lines == Core.SelectStdinLines(lines,
                                                           Spec.StdinCount(cmd.inputs[..i]), Spec.StdinCount(cmd.inputs));
          SelectedLinesRefines(lines, Spec.StdinCount(cmd.inputs[..i]), Spec.StdinCount(cmd.inputs));
        }
      }
    }
  }

  lemma ConcatSnoc<T>(parts: seq<seq<T>>, last: seq<T>)
    ensures Spec.Concat<T>(parts + [last]) == Spec.Concat<T>(parts) + last
    decreases |parts|
  {
    if |parts| > 0 {
      ConcatSnoc<T>(parts[1..], last);
      assert (parts + [last])[1..] == parts[1..] + [last];
    }
  }

  lemma NoStdinData(cmd: Schema.PasteCmd,
                    streams: (BW.TrustedStreamRequest) -> BW.TrustedStreamResult, input: BW.Bytes, i: nat)
    requires i <= |cmd.inputs|
    requires Schema.Stdin !in cmd.inputs[..i]
    ensures Core.StdinDataPrefixCore(cmd, streams, input, i) == []
    decreases i
  {
    if i > 0 {
      NoStdinData(cmd, streams, input, i - 1);
    }
  }

  lemma StdinCountStep(inputs: seq<Schema.Input>, i: nat)
    requires i < |inputs|
    ensures Spec.StdinCount(inputs[..i + 1]) == Spec.StdinCount(inputs[..i]) +
                                                (if inputs[i].Stdin? then 1 else 0)
  {
    hide *;
    reveal Spec.StdinCount();
    assert inputs[..i + 1] == inputs[..i] + [inputs[i]];
    assert multiset(inputs[..i + 1]) == multiset(inputs[..i]) + multiset{inputs[i]};
  }

  lemma StdinAfterReadsRefines(
    cmd: Schema.PasteCmd, streams: (BW.TrustedStreamRequest) -> BW.TrustedStreamResult,
    stdin: BW.Bytes, i: nat
  )
    requires i <= |cmd.inputs|
    ensures Core.PrefixStdinCore(cmd, streams, stdin, i) ==
            Spec.StdinAfterReads(stdin, streams, Spec.StdinCount(cmd.inputs[..i]))
    decreases i
  {
    hide *;
    reveal Spec.StdinAfterReads();
    if i == 0 {
      reveal Core.PrefixStdinCore(), Spec.StdinCount();
    } else {
      StdinAfterReadsRefines(cmd, streams, stdin, i - 1);
      StdinCountStep(cmd.inputs, i - 1);
      Core.PrefixStdinCoreStep(cmd, streams, stdin, i - 1);
    }
  }

  lemma ReadResultsRefine(
    cmd: Schema.PasteCmd, fs: BW.FileSystem,
    streams: (BW.TrustedStreamRequest) -> BW.TrustedStreamResult, stdin: BW.Bytes
  )
    ensures forall i: nat | i < |cmd.inputs| ::
              Spec.ReadResults(cmd.inputs, fs, streams, stdin)[i] ==
              Core.ReadResultCore(cmd, fs, streams, stdin, i)
  {
    hide *;
    reveal Spec.ReadResults(), Spec.ReadInput(), Core.ReadResultCore();
    forall i: nat | i < |cmd.inputs|
      ensures Spec.ReadResults(cmd.inputs, fs, streams, stdin)[i] ==
              Core.ReadResultCore(cmd, fs, streams, stdin, i)
    {
      StdinAfterReadsRefines(cmd, streams, stdin, i);
    }
  }

  lemma FragmentsDenote<T>(fragments: seq<seq<T>>, combined: seq<T>, cuts: seq<nat>, i: nat)
    requires FragmentsConcatenate(fragments, combined, cuts)
    requires i <= |fragments|
    ensures combined[..cuts[i]] == Spec.Concat<T>(fragments[..i])
    decreases i
  {
    if i > 0 {
      FragmentsDenote<T>(fragments, combined, cuts, i - 1);
      assert fragments[..i] == fragments[..i - 1] + [fragments[i - 1]];
      ConcatSnoc<T>(fragments[..i - 1], fragments[i - 1]);
      assert combined[..cuts[i]] == combined[..cuts[i - 1]] + combined[cuts[i - 1]..cuts[i]];
    }
  }

  lemma ConcatPrefixStep(parts: seq<BW.Bytes>, i: nat)
    requires i < |parts|
    ensures Spec.Concat<BW.RawByte>(parts[..i + 1]) ==
            Spec.Concat<BW.RawByte>(parts[..i]) + parts[i]
  {
    assert parts[..i + 1] == parts[..i] + [parts[i]];
    ConcatSnoc<BW.RawByte>(parts[..i], parts[i]);
  }

  lemma StdinDataRefines(
    cmd: Schema.PasteCmd, fs: BW.FileSystem,
    streams: (BW.TrustedStreamRequest) -> BW.TrustedStreamResult, stdin: BW.Bytes,
    results: seq<BW.IOResult<BW.Bytes>>, n: nat
  )
    requires n <= |cmd.inputs| == |results|
    requires forall i: nat | i < |results| ::
               results[i] == Core.ReadResultCore(cmd, fs, streams, stdin, i)
    ensures Core.StdinDataPrefixCore(cmd, streams, stdin, n) ==
            Spec.Concat<BW.RawByte>(Spec.StdinPieces(cmd.inputs, results)[..n])
    decreases n
  {
    hide *;
    if n == 0 {
      reveal Core.StdinDataPrefixCore(), Spec.Concat();
    } else {
      var i := n - 1;
      StdinDataRefines(cmd, fs, streams, stdin, results, i);
      Core.StdinDataPrefixCoreStep(cmd, streams, stdin, i);
      var pieces := Spec.StdinPieces(cmd.inputs, results);
      ConcatPrefixStep(pieces, i);
      reveal Core.ReadResultCore(), Spec.StdinPieces();
      assert results[i] == Core.ReadResultCore(cmd, fs, streams, stdin, i);
    }
  }

  lemma InputStatusRefines(
    cmd: Schema.PasteCmd, fs: BW.FileSystem,
    streams: (BW.TrustedStreamRequest) -> BW.TrustedStreamResult, stdin: BW.Bytes,
    results: seq<BW.IOResult<BW.Bytes>>, n: nat
  )
    requires n <= |cmd.inputs| == |results|
    requires forall i: nat | i < |results| ::
               results[i] == Core.ReadResultCore(cmd, fs, streams, stdin, i)
    ensures Core.PrefixHadErrorCore(cmd, fs, streams, stdin, n) ==
            (exists i: nat :: i < n && results[i].Err?)
    ensures Core.PrefixHadBlockingErrorCore(cmd, fs, streams, stdin, n) ==
            (exists i: nat :: i < n && Spec.IsBlockingInput(cmd.inputs[i], results[i]))
    decreases n
  {
    hide *;
    if n == 0 {
      reveal Core.PrefixHadErrorCore(), Core.PrefixHadBlockingErrorCore();
    } else {
      var i := n - 1;
      InputStatusRefines(cmd, fs, streams, stdin, results, i);
      Core.PrefixHadErrorCoreStep(cmd, fs, streams, stdin, i);
      Core.PrefixHadBlockingErrorCoreStep(cmd, fs, streams, stdin, i);
      reveal Core.HadErrorPiece(), Core.HadBlockingErrorPiece();
      assert results[i] == Core.ReadResultCore(cmd, fs, streams, stdin, i);
      assert (exists j: nat :: j < n && results[j].Err?) <==>
             ((exists j: nat :: j < i && results[j].Err?) || results[i].Err?);
      assert (exists j: nat :: j < n && Spec.IsBlockingInput(cmd.inputs[j], results[j])) <==>
             ((exists j: nat :: j < i && Spec.IsBlockingInput(cmd.inputs[j], results[j])) ||
              Spec.IsBlockingInput(cmd.inputs[i], results[i]));
    }
  }

  lemma FirstBlockingDiagnosticRefines(
    cmd: Schema.PasteCmd, fs: BW.FileSystem,
    streams: (BW.TrustedStreamRequest) -> BW.TrustedStreamResult, stdin: BW.Bytes,
    results: seq<BW.IOResult<BW.Bytes>>, first: nat, n: nat
  )
    requires !cmd.serial && first < n <= |cmd.inputs| == |results|
    requires forall i: nat | i < |results| ::
               results[i] == Core.ReadResultCore(cmd, fs, streams, stdin, i)
    requires Spec.IsBlockingInput(cmd.inputs[first], results[first])
    requires forall i: nat | i < first :: !Spec.IsBlockingInput(cmd.inputs[i], results[i])
    ensures Core.PrefixVisibleErrorOutputCore(cmd, fs, streams, stdin, n) ==
            Spec.InputDiagnostic(cmd.inputs[first], results[first])
    decreases n
  {
    hide *;
    var i := n - 1;
    InputStatusRefines(cmd, fs, streams, stdin, results, i);
    Core.PrefixVisibleErrorOutputCoreStep(cmd, fs, streams, stdin, i);
    if first < i {
      assert exists j: nat :: j < i && Spec.IsBlockingInput(cmd.inputs[j], results[j]);
      FirstBlockingDiagnosticRefines(cmd, fs, streams, stdin, results, first, i);
    } else {
      reveal Core.HadBlockingErrorPiece(), Core.ErrorPiece();
      assert results[i] == Core.ReadResultCore(cmd, fs, streams, stdin, i);
    }
  }

  lemma OrderedDiagnosticsRefine(
    cmd: Schema.PasteCmd, fs: BW.FileSystem,
    streams: (BW.TrustedStreamRequest) -> BW.TrustedStreamResult, stdin: BW.Bytes,
    results: seq<BW.IOResult<BW.Bytes>>, n: nat
  )
    requires n <= |cmd.inputs| == |results|
    requires forall i: nat | i < |results| ::
               results[i] == Core.ReadResultCore(cmd, fs, streams, stdin, i)
    requires cmd.serial || (forall i: nat | i < n :: !Spec.IsBlockingInput(cmd.inputs[i], results[i]))
    ensures Core.PrefixVisibleErrorOutputCore(cmd, fs, streams, stdin, n) ==
            Spec.Concat<BW.RawByte>(Spec.InputDiagnostics(cmd.inputs, results)[..n])
    decreases n
  {
    hide *;
    if n == 0 {
      reveal Core.PrefixVisibleErrorOutputCore(), Spec.Concat();
    } else {
      var i := n - 1;
      OrderedDiagnosticsRefine(cmd, fs, streams, stdin, results, i);
      InputStatusRefines(cmd, fs, streams, stdin, results, i);
      Core.PrefixVisibleErrorOutputCoreStep(cmd, fs, streams, stdin, i);
      reveal Core.HadBlockingErrorPiece(), Core.ErrorPiece(), Spec.InputDiagnostics();
      ConcatPrefixStep(Spec.InputDiagnostics(cmd.inputs, results), i);
      assert results[i] == Core.ReadResultCore(cmd, fs, streams, stdin, i);
    }
  }

  lemma VisibleErrorsRefine(
    cmd: Schema.PasteCmd, fs: BW.FileSystem,
    streams: (BW.TrustedStreamRequest) -> BW.TrustedStreamResult, stdin: BW.Bytes,
    results: seq<BW.IOResult<BW.Bytes>>
  )
    requires |cmd.inputs| == |results|
    requires forall i: nat | i < |results| ::
               results[i] == Core.ReadResultCore(cmd, fs, streams, stdin, i)
    ensures Core.PrefixVisibleErrorOutputCore(cmd, fs, streams, stdin, |cmd.inputs|) ==
            Spec.VisibleErrors(cmd.serial, cmd.inputs, results)
  {
    hide *;
    reveal Spec.VisibleErrors();
    if !cmd.serial && (exists i: nat :: i < |results| && Spec.IsBlockingInput(cmd.inputs[i], results[i])) {
      var first := Spec.FirstBlocking(cmd.inputs, results);
      FirstBlockingDiagnosticRefines(cmd, fs, streams, stdin, results, first, |results|);
    } else {
      OrderedDiagnosticsRefine(cmd, fs, streams, stdin, results, |results|);
      var pieces := Spec.InputDiagnostics(cmd.inputs, results);
      assert pieces[..|results|] == pieces;
    }
  }

  twostate lemma {:isolate_assertions} InputRefines(cmd: Schema.PasteCmd, io: BenchIO.IO)
    requires io.stdin() ==
             Core.PrefixStdinCore(cmd, old(io.trustedStreams()), old(io.stdin()), |cmd.inputs|)
    ensures Spec.InputRelation(
              cmd, io,
              Core.EntriesForOutputCore(
                cmd, old(io.fs()), old(io.trustedStreams()), old(io.stdin())),
              Core.PrefixVisibleErrorOutputCore(
                cmd, old(io.fs()), old(io.trustedStreams()), old(io.stdin()), |cmd.inputs|),
              Core.PrefixHadErrorCore(
                cmd, old(io.fs()), old(io.trustedStreams()), old(io.stdin()), |cmd.inputs|),
              Core.PrefixHadBlockingErrorCore(
                cmd, old(io.fs()), old(io.trustedStreams()), old(io.stdin()), |cmd.inputs|))
  {
    hide *;
    var preFs := old(io.fs());
    var preStreams := old(io.trustedStreams());
    var preStdin := old(io.stdin());
    var n := |cmd.inputs|;
    var results := Spec.ReadResults(cmd.inputs, preFs, preStreams, preStdin);
    ReadResultsRefine(cmd, preFs, preStreams, preStdin);
    StdinAfterReadsRefines(cmd, preStreams, preStdin, n);
    assert cmd.inputs[..n] == cmd.inputs;
    InputStatusRefines(cmd, preFs, preStreams, preStdin, results, n);
    VisibleErrorsRefine(cmd, preFs, preStreams, preStdin, results);

    var rawEntries := Core.EntriesCore(cmd, preFs, preStreams, preStdin);
    var delimiter := Spec.RecordDelimiter(cmd.zeroTerminated);
    reveal Core.EntriesCore();
    forall i: nat | i < n
      ensures Spec.EntryRelation(results[i], delimiter, rawEntries[i])
    {
      PrefixEntriesIndex(cmd, preFs, preStreams, preStdin, n, i);
      assert results[i] == Core.ReadResultCore(cmd, preFs, preStreams, preStdin, i);
      EntryRefines(results[i], delimiter);
    }

    StdinDataRefines(cmd, preFs, preStreams, preStdin, results, n);
    var data := Spec.StdinData(cmd.inputs, results);
    assert data == Core.StdinDataForOutputCore(cmd, preStreams, preStdin) by {
      var pieces := Spec.StdinPieces(cmd.inputs, results);
      assert pieces[..n] == pieces;
      reveal Spec.StdinData(), Core.StdinDataForOutputCore();
    }
    if !Spec.HasStdinInput(cmd.inputs) {
      reveal Spec.HasStdinInput(), Core.StdinDataForOutputCore();
      NoStdinData(cmd, preStreams, preStdin, n);
      assert data == [];
    }
    EntriesForOutputRefines(cmd, data, rawEntries);
    reveal Core.EntriesForOutputCore();
    var entries := Core.EntriesForOutputCore(cmd, preFs, preStreams, preStdin);
    assert Spec.EntriesForOutputRelation(cmd, data, rawEntries, entries);
    reveal Spec.InputRelation();
  }

  lemma EscapeDelimiterRefines(ch: BW.RawByte)
    ensures Core.EscapeDelimiter(ch) == Spec.EscapedDelimiter(ch)
  {
  }

  lemma BuildDelimiterParse(
    text: BW.Bytes,
    i: nat
  ) returns (assembly: DelimiterAssembly)
    requires i <= |text|
    ensures DelimiterParseRelation(
              text,
              i,
              Core.CollapseDelimitersFrom(text, i),
              assembly)
    decreases |text| - i
  {
    if i == |text| {
      assembly := DelimiterDone;
    } else if text[i] == '\\' && i + 1 == |text| {
      assembly := DelimiterFailure;
    } else {
      var nextIndex :=
        if text[i] == '\\' then i + 2 else i + 1;
      var delimiter :=
        if text[i] == '\\'
        then Core.EscapeDelimiter(text[i + 1])
        else [text[i]];
      if text[i] == '\\' {
        EscapeDelimiterRefines(text[i + 1]);
      }
      var rest := BuildDelimiterParse(text, nextIndex);
      assembly :=
        DelimiterStep(i, nextIndex, delimiter, rest);
    }
  }

  lemma {:isolate_assertions} DelimiterParseDenote(text: BW.Bytes, i: nat, result: Spec.DelimiterResult,
                                                   assembly: DelimiterAssembly) returns (cuts: seq<nat>)
    requires DelimiterParseRelation(text, i, result, assembly)
    ensures Spec.DelimiterCuts(text, i, cuts)
    ensures result == Spec.DelimiterValue(text, cuts)
    decreases assembly
  {
    hide *;
    reveal DelimiterParseRelation(), Spec.DelimiterCuts(), Spec.DelimiterValue();
    match assembly
    case DelimiterDone =>
      cuts := [i];
      var empty: seq<BW.Bytes> := [];
      assert Spec.DelimiterValue(text, cuts).Ok?;
      assert |Spec.DelimiterValue(text, cuts).v| == 0;
      assert Spec.DelimiterValue(text, cuts).v == empty;
      assert result == Result.Ok(empty);
      assert result == Spec.DelimiterValue(text, cuts);
    case DelimiterFailure =>
      cuts := [i, |text|];
      assert result == Spec.DelimiterValue(text, cuts);
    case DelimiterStep(index, nextIndex, delimiter, rest) =>
      var restResult: Spec.DelimiterResult :|
        DelimiterParseRelation(text, nextIndex, restResult, rest) &&
        result == (match restResult
                   case Err(stderr) => Result.Err(stderr)
                   case Ok(delims) => Result.Ok([delimiter] + delims));
      var tail := DelimiterParseDenote(text, nextIndex, restResult, rest);
      cuts := [i] + tail;
      assert Spec.DelimiterCuts(text, nextIndex, tail);
      assert forall k {:trigger cuts[k]} | 0 <= k < |cuts| - 1 ::
          cuts[k] < cuts[k + 1] <= |text| &&
          cuts[k + 1] == cuts[k] +
          (if text[cuts[k]] == '\\' && cuts[k] + 1 < |text| then 2 else 1) by {
        forall k {:trigger cuts[k]} | 0 <= k < |cuts| - 1
          ensures cuts[k] < cuts[k + 1] <= |text|
          ensures cuts[k + 1] == cuts[k] +
                                 (if text[cuts[k]] == '\\' && cuts[k] + 1 < |text| then 2 else 1)
        {
          if k > 0 {
            assert cuts[k] == tail[k - 1] && cuts[k + 1] == tail[k];
            assert tail[k - 1] < tail[k] <= |text|;
          }
        }
      }
      assert Spec.DelimiterCuts(text, i, cuts);
      assert (exists k | 0 <= k < |cuts| - 1 ::
                text[cuts[k]] == '\\' && cuts[k] + 1 == |text|) == restResult.Err? by {
        if exists k | 0 <= k < |cuts| - 1 ::
            text[cuts[k]] == '\\' && cuts[k] + 1 == |text| {
          var k :| 0 <= k < |cuts| - 1 && text[cuts[k]] == '\\' && cuts[k] + 1 == |text|;
          assert k > 0;
          assert tail[k - 1] == cuts[k];
        } else if restResult.Err? {
          var k :| 0 <= k < |tail| - 1 && text[tail[k]] == '\\' && tail[k] + 1 == |text|;
          assert cuts[k + 1] == tail[k];
        }
      }
      if restResult.Ok? {
        var values: seq<BW.Bytes> := seq(|cuts| - 1, k requires 0 <= k < |cuts| - 1 =>
          if text[cuts[k]] == '\\' then Spec.EscapedDelimiter(text[cuts[k] + 1])
          else [text[cuts[k]]]);
        assert |values| == 1 + |restResult.v|;
        forall k | 0 <= k < |values|
          ensures values[k] == ([delimiter] + restResult.v)[k]
        {
          if k > 0 {
            assert cuts[k] == tail[k - 1];
          }
        }
        assert values == [delimiter] + restResult.v;
        assert result == Result.Ok(values);
        assert Spec.DelimiterValue(text, cuts) == Result.Ok(values);
      } else {
        assert restResult.e == Spec.DelimiterBackslashError(text);
        assert result == Spec.DelimiterValue(text, cuts);
      }
  }

  lemma DelimiterResultRefines(text: string)
    ensures Spec.DelimiterResultRelation(
              text, Core.CollapseDelimiters(text))
  {
    if |text| == 0 {
      reveal Spec.DelimiterResultRelation();
    } else {
      var assembly := BuildDelimiterParse(Utf8.Encode(text), 0);
      var cuts := DelimiterParseDenote(Utf8.Encode(text), 0,
                                       Core.CollapseDelimiters(text), assembly);
      assert Core.CollapseDelimiters(text) ==
             Core.CollapseDelimitersFrom(Utf8.Encode(text), 0);
      reveal Spec.DelimiterResultRelation();
    }
  }

  lemma CollapseDelimitersFromNonEmpty(text: BW.Bytes, i: nat)
    requires i < |text|
    ensures
      match Core.CollapseDelimitersFrom(text, i)
      case Ok(delims) => |delims| > 0
      case Err(_) => true
    decreases |text| - i
  {
    if text[i] == '\\' {
      if i + 1 < |text| {
        if i + 2 < |text| {
          CollapseDelimitersFromNonEmpty(text, i + 2);
        }
      }
    } else if i + 1 < |text| {
      CollapseDelimitersFromNonEmpty(text, i + 1);
    }
  }

  lemma CollapseDelimitersNonEmpty(text: string)
    ensures
      match Core.CollapseDelimiters(text)
      case Ok(delims) => |delims| > 0
      case Err(_) => true
  {
    if |text| > 0 {
      CollapseDelimitersFromNonEmpty(Utf8.Encode(text), 0);
    }
  }

  ghost function JoinedFragments(fields: seq<BW.Bytes>, delims: seq<BW.Bytes>): seq<BW.Bytes>
    requires |delims| > 0
  {
    seq(|fields|, i requires 0 <= i < |fields| =>
      fields[i] + (if i + 1 < |fields| then Spec.DelimAt(delims, i) else []))
  }

  lemma JoinedFragmentsEq(fields: seq<BW.Bytes>, delims: seq<BW.Bytes>)
    requires |delims| > 0
    ensures Spec.Join(fields, delims) == Spec.Concat<BW.RawByte>(JoinedFragments(fields, delims))
  {
    reveal Spec.Join(), JoinedFragments();
  }

  lemma ParallelColumnsRefine(entries: seq<Spec.Entry>, delims: seq<BW.Bytes>, row: nat, i: nat)
    requires |delims| > 0 && |entries| > 0 && i <= |entries|
    ensures Core.RenderParallelRow(entries, delims, row, i, |entries| - 1) ==
            Spec.Concat<BW.RawByte>(JoinedFragments(seq(|entries|, k requires 0 <= k < |entries| =>
                                                      if row < |entries[k].lines| then entries[k].lines[row] else []), delims)[i..])
    decreases |entries| - i
  {
    if i < |entries| {
      ParallelColumnsRefine(entries, delims, row, i + 1);
      var fields := seq(|entries|, k requires 0 <= k < |entries| =>
        if row < |entries[k].lines| then entries[k].lines[row] else []);
      var pieces := JoinedFragments(fields, delims);
      assert pieces[i..][1..] == pieces[i + 1..];
    }
  }

  lemma ParallelRecordsRefine(entries: seq<Spec.Entry>, delims: seq<BW.Bytes>,
                              delimiter: BW.RawByte, row: nat)
    requires |delims| > 0 && row <= Spec.MaxLineCount(entries)
    ensures Core.RenderParallelRows(entries, delims, delimiter, row, Spec.MaxLineCount(entries)) ==
            Spec.Concat<BW.RawByte>(Spec.ParallelRecords(entries, delims, delimiter)[row..])
    decreases Spec.MaxLineCount(entries) - row
  {
    if row < Spec.MaxLineCount(entries) {
      assert |entries| > 0;
      ParallelColumnsRefine(entries, delims, row, 0);
      var fields := seq(|entries|, k requires 0 <= k < |entries| =>
        if row < |entries[k].lines| then entries[k].lines[row] else []);
      JoinedFragmentsEq(fields, delims);
      assert JoinedFragments(fields, delims)[0..] == JoinedFragments(fields, delims);
      ParallelRecordsRefine(entries, delims, delimiter, row + 1);
      assert Spec.ParallelRecords(entries, delims, delimiter)[row..][1..] ==
             Spec.ParallelRecords(entries, delims, delimiter)[row + 1..];
    }
  }

  lemma SerialColumnsRefine(lines: seq<BW.Bytes>, delims: seq<BW.Bytes>, i: nat)
    requires |delims| > 0 && i <= |lines|
    ensures Core.JoinLines(lines, delims, i) == Spec.Concat<BW.RawByte>(JoinedFragments(lines, delims)[i..])
    decreases |lines| - i
  {
    if i < |lines| {
      SerialColumnsRefine(lines, delims, i + 1);
      assert JoinedFragments(lines, delims)[i..][1..] == JoinedFragments(lines, delims)[i + 1..];
    }
  }

  lemma SerialRecordsRefine(entries: seq<Spec.Entry>, delims: seq<BW.Bytes>,
                            delimiter: BW.RawByte, i: nat)
    requires |delims| > 0 && i <= |entries|
    ensures Core.RenderSerial(entries[i..], delims, delimiter) ==
            Spec.Concat<BW.RawByte>(Spec.SerialRecords(entries, delims, delimiter)[i..])
    decreases |entries| - i
  {
    if i < |entries| {
      if entries[i].readOk {
        SerialColumnsRefine(entries[i].lines, delims, 0);
        JoinedFragmentsEq(entries[i].lines, delims);
        assert JoinedFragments(entries[i].lines, delims)[0..] ==
               JoinedFragments(entries[i].lines, delims);
      }
      SerialRecordsRefine(entries, delims, delimiter, i + 1);
      assert entries[i..][1..] == entries[i + 1..];
      assert Spec.SerialRecords(entries, delims, delimiter)[i..][1..] ==
             Spec.SerialRecords(entries, delims, delimiter)[i + 1..];
    }
  }

  lemma OutputRefines(serial: bool, delims: seq<BW.Bytes>, delimiter: BW.RawByte,
                      entries: seq<Spec.Entry>)
    requires |delims| > 0
    ensures Core.RenderOutput(serial, delims, delimiter, entries) ==
            Spec.Output(serial, delims, delimiter, entries)
  {
    if serial {
      SerialRecordsRefine(entries, delims, delimiter, 0);
      assert entries[0..] == entries;
    } else {
      ParallelRecordsRefine(entries, delims, delimiter, 0);
    }
  }

  twostate lemma {:isolate_assertions} PreparedSummaryImpliesPreparedSpec(
    raw: Schema.PasteCmdRaw,
    io: BenchIO.IO,
    exit: int
  , new resultStdout: BenchWorld.Bytes, new resultStderr: BenchWorld.Bytes)
    requires Core.PreparedSummary(raw, io, exit, resultStdout, resultStderr)
    ensures Spec.PreparedSpec(raw, io, exit, resultStdout, resultStderr)
  {
    var cmd := Schema.Command(raw);
    assert cmd == Schema.Command(raw);
    if cmd.mode == Schema.ModeHelp {
    } else if cmd.mode == Schema.ModeVersion {
    } else {
      DelimiterResultRefines(cmd.delimiterText);
      CollapseDelimitersNonEmpty(cmd.delimiterText);
      ghost var result := Core.CollapseDelimiters(cmd.delimiterText);
      assert Spec.DelimiterResultRelation(
          cmd.delimiterText, result);
      match Core.CollapseDelimiters(cmd.delimiterText)
      case Err(stderr) =>
      case Ok(delims) =>
        assert |delims| > 0;
        InputRefines(cmd, io);

        OutputRefines(
          cmd.serial,
          delims,
          Spec.RecordDelimiter(cmd.zeroTerminated),
          Core.EntriesForOutputCore(
            cmd, old(io.fs()), old(io.trustedStreams()), old(io.stdin())));
    }
  }

  twostate lemma CoreSummaryImpliesSpec(raw: Schema.PasteCmdRaw, io: BenchIO.IO, exit: int)
    requires Core.CoreSummary(raw, io, exit)
    ensures Spec.Spec(raw, io, exit)
  {
    var out: BenchWorld.Bytes, diagnostics: BenchWorld.Bytes, normalExit: int :|
      Core.PreparedSummary(raw, io, normalExit,
                           old(io.stdout()) + out, old(io.stderr()) + diagnostics) &&
      Spec.Emission(io, out, diagnostics, normalExit, exit);
    PreparedSummaryImpliesPreparedSpec(raw, io, normalExit,
                                       old(io.stdout()) + out, old(io.stderr()) + diagnostics);
  }
}
