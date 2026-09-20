include "../../core/World.dfy"
include "UniqSchema.dfy"
include "UniqCore.dfy"
include "UniqSpec.dfy"

module UniqProof {
  import BenchIO
  import BW = BenchWorld
  import Schema = UniqSchema
  import Core = UniqCore
  import Spec = UniqSpec

  lemma InputFromOperandsEq(operands: seq<string>)
    ensures Core.InputFromOperands(operands) ==
            Spec.InputFromOperands(operands)
  {
  }

  lemma CommandEq(raw: Schema.UniqCmdRaw)
    ensures Core.Command(raw) == Spec.Command(raw)
  {
    InputFromOperandsEq(raw.operands);
  }

  lemma LowerAsciiEq(ch: BW.RawByte)
    ensures Core.LowerAscii(ch) == Spec.LowerAscii(ch)
  {
  }

  lemma EqualFoldAsciiEq(a: BW.Bytes, b: BW.Bytes)
    ensures Core.EqualFoldAscii(a, b) == Spec.EqualFoldAscii(a, b)
    decreases |a|
  {
    if |a| == |b| && |a| > 0 {
      LowerAsciiEq(a[0]);
      LowerAsciiEq(b[0]);
      EqualFoldAsciiEq(a[1..], b[1..]);
    }
  }

  lemma LinesEqualEq(
    cmd: Schema.UniqCmd,
    a: BW.Bytes,
    b: BW.Bytes
  )
    ensures Core.LinesEqual(cmd, a, b) ==
            Spec.LinesEqual(cmd, a, b)
  {
    if cmd.ignoreCase {
      EqualFoldAsciiEq(a, b);
    }
  }

  lemma EqualFoldAsciiReflexive(line: BW.Bytes)
    ensures Spec.EqualFoldAscii(line, line)
    decreases |line|
  {
    reveal Spec.EqualFoldAscii();
    if |line| > 0 {
      EqualFoldAsciiReflexive(line[1..]);
    }
  }

  lemma LinesEqualReflexive(
    cmd: Schema.UniqCmd,
    line: BW.Bytes
  )
    ensures Spec.LinesEqual(cmd, line, line)
  {
    reveal Spec.LinesEqual();
    if cmd.ignoreCase {
      EqualFoldAsciiReflexive(line);
    }
  }

  ghost function ShiftCuts(cuts: seq<nat>, amount: nat): seq<nat>
  {
    seq(|cuts|, i requires 0 <= i < |cuts| => cuts[i] + amount)
  }

  lemma ShiftCutsIndex(cuts: seq<nat>, amount: nat, i: nat)
    requires i < |cuts|
    ensures ShiftCuts(cuts, amount)[i] == cuts[i] + amount
  {
  }

  lemma PrependSlice<T>(
    head: seq<T>,
    tail: seq<T>,
    start: nat,
    end: nat
  )
    requires start <= end <= |tail|
    ensures (head + tail)[
            |head| + start..|head| + end
            ] == tail[start..end]
  {
  }

  lemma {:isolate_assertions} PrependByteFragment(
    head: BW.Bytes,
    tailFragments: seq<BW.Bytes>,
    tail: BW.Bytes,
    tailCuts: seq<nat>
  )
    requires Spec.FragmentsConcatenate(
               tailFragments, tail, tailCuts
             )
    ensures Spec.FragmentsConcatenate(
              [head] + tailFragments,
              head + tail,
              [0] + ShiftCuts(tailCuts, |head|)
            )
  {
    reveal Spec.FragmentsConcatenate();
    forall i: nat {:trigger ([0] + ShiftCuts(
      tailCuts, |head|
      ))[i]} | i < |[head] + tailFragments|
      ensures ([0] + ShiftCuts(tailCuts, |head|))[i] <=
              ([0] + ShiftCuts(tailCuts, |head|))[i + 1] &&
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
      ShiftCutsIndex(tailCuts, |head|, i);
      if i > 0 {
        ShiftCutsIndex(tailCuts, |head|, i - 1);
        var k := i - 1;
        PrependSlice(head, tail, tailCuts[k], tailCuts[k + 1]);
      }
    }
  }

  lemma {:isolate_assertions} PrependRecordRun(
    head: seq<BW.Bytes>,
    tailRuns: seq<seq<BW.Bytes>>,
    tail: seq<BW.Bytes>,
    tailCuts: seq<nat>
  )
    requires |head| > 0
    requires Spec.RecordsConcatenate(tailRuns, tail, tailCuts)
    ensures Spec.RecordsConcatenate(
              [head] + tailRuns,
              head + tail,
              [0] + ShiftCuts(tailCuts, |head|)
            )
  {
    reveal Spec.RecordsConcatenate();
    forall i: nat {:trigger ([0] + ShiftCuts(
      tailCuts, |head|
      ))[i]} | i < |[head] + tailRuns|
      ensures ([0] + ShiftCuts(tailCuts, |head|))[i] <=
              ([0] + ShiftCuts(tailCuts, |head|))[i + 1] &&
              ([0] + ShiftCuts(tailCuts, |head|))[i + 1] <=
              |head + tail| &&
              ([0] + ShiftCuts(tailCuts, |head|))[i + 1] ==
              ([0] + ShiftCuts(tailCuts, |head|))[i] +
              |([head] + tailRuns)[i]| &&
              (head + tail)[
              ([0] + ShiftCuts(tailCuts, |head|))[i]..
              ([0] + ShiftCuts(tailCuts, |head|))[i + 1]
              ] == ([head] + tailRuns)[i]
    {
      ShiftCutsIndex(tailCuts, |head|, i);
      if i > 0 {
        ShiftCutsIndex(tailCuts, |head|, i - 1);
        var k := i - 1;
        PrependSlice(head, tail, tailCuts[k], tailCuts[k + 1]);
      }
    }
  }

  lemma LinesFromWitness(
    data: BW.Bytes,
    current: BW.Bytes
  ) returns (
      terminated: seq<bool>,
      fragments: seq<BW.Bytes>,
      cuts: seq<nat>
    )
    requires forall j: nat :: j < |current| ==> current[j] != '\n'
    ensures Spec.RecordPartitionWitnessRelation(
              current + data,
              Core.LinesFrom(data, current),
              terminated,
              fragments,
              cuts
            )
    decreases |data|
  {
    var lines := Core.LinesFrom(data, current);
    if |data| == 0 {
      if |current| == 0 {
        terminated := [];
        fragments := [];
        cuts := [0];
      } else {
        terminated := [false];
        fragments := [current];
        cuts := [0, |current|];
      }
      reveal Spec.RecordPartitionWitnessRelation();
      reveal Spec.FragmentsConcatenate();
    } else if data[0] == '\n' {
      var tailTerminated, tailFragments, tailCuts :=
        LinesFromWitness(data[1..], []);
      var head := current + ['\n'];
      terminated := [true] + tailTerminated;
      fragments := [head] + tailFragments;
      cuts := [0] + ShiftCuts(tailCuts, |head|);
      PrependByteFragment(head, tailFragments, data[1..], tailCuts);
      reveal Spec.RecordPartitionWitnessRelation();
      assert forall i: nat | i < |lines| ::
          |fragments[i]| > 0 &&
          fragments[i] ==
          lines[i] + (if terminated[i] then ['\n'] else []) &&
          (forall j: nat :: j < |lines[i]| ==> lines[i][j] != '\n') &&
          (i + 1 < |lines| ==> terminated[i]) by {
        forall i: nat | i < |lines|
          ensures |fragments[i]| > 0 &&
                  fragments[i] ==
                  lines[i] + (if terminated[i] then ['\n'] else []) &&
                  (forall j: nat ::
                     j < |lines[i]| ==> lines[i][j] != '\n') &&
                  (i + 1 < |lines| ==> terminated[i])
        {
        }
      }
    } else {
      terminated, fragments, cuts :=
        LinesFromWitness(data[1..], current + [data[0]]);
    }
  }

  lemma LinesWitness(data: BW.Bytes) returns (
      terminated: seq<bool>,
      fragments: seq<BW.Bytes>,
      cuts: seq<nat>
    )
    ensures Spec.RecordPartitionWitnessRelation(
              data, Core.Lines(data), terminated, fragments, cuts
            )
    ensures Spec.RecordPartitionRelation(
              data, Core.Lines(data), terminated
            )
  {
    terminated, fragments, cuts := LinesFromWitness(data, []);
    reveal Spec.RecordPartitionRelation();
    assert exists fs: seq<BW.Bytes>, cs: seq<nat> ::
        Spec.RecordPartitionWitnessRelation(
          data, Core.Lines(data), terminated, fs, cs
        ) by {
      assert Spec.RecordPartitionWitnessRelation(
          data, Core.Lines(data), terminated, fragments, cuts
        );
    }
  }

  lemma {:isolate_assertions} GroupsFromWitness(
    cmd: Schema.UniqCmd,
    rest: seq<BW.Bytes>,
    current: BW.Bytes,
    count: nat,
    currentRun: seq<BW.Bytes>
  ) returns (
      runs: seq<seq<BW.Bytes>>,
      cuts: seq<nat>
    )
    requires 1 <= count
    requires |currentRun| == count
    requires |currentRun| > 0
    requires currentRun[0] == current
    requires forall j: nat | j < |currentRun| ::
               Spec.LinesEqual(cmd, current, currentRun[j])
    ensures Spec.RunPartitionWitnessRelation(
              cmd,
              currentRun + rest,
              Core.GroupsFrom(cmd, rest, current, count),
              runs,
              cuts
            )
    decreases |rest|
  {
    var groups := Core.GroupsFrom(cmd, rest, current, count);
    if |rest| == 0 {
      runs := [currentRun];
      cuts := [0, |currentRun|];
      reveal Spec.RunPartitionWitnessRelation();
      reveal Spec.RecordsConcatenate();
    } else {
      LinesEqualEq(cmd, current, rest[0]);
      if Core.LinesEqual(cmd, current, rest[0]) {
        assert forall j: nat | j < |currentRun + [rest[0]]| ::
            Spec.LinesEqual(
              cmd, current, (currentRun + [rest[0]])[j]
            ) by {
          forall j: nat | j < |currentRun + [rest[0]]|
            ensures Spec.LinesEqual(
                      cmd, current, (currentRun + [rest[0]])[j]
                    )
          {
          }
        }
        runs, cuts := GroupsFromWitness(
          cmd,
          rest[1..],
          current,
          count + 1,
          currentRun + [rest[0]]
        );
        assert currentRun + rest ==
               (currentRun + [rest[0]]) + rest[1..];
      } else {
        LinesEqualReflexive(cmd, rest[0]);
        var tailRuns, tailCuts := GroupsFromWitness(
          cmd, rest[1..], rest[0], 1, [rest[0]]
        );
        runs := [currentRun] + tailRuns;
        cuts := [0] + ShiftCuts(tailCuts, |currentRun|);
        PrependRecordRun(
          currentRun, tailRuns, [rest[0]] + rest[1..], tailCuts
        );
        reveal Spec.RunPartitionWitnessRelation();
        assert currentRun + rest ==
               currentRun + ([rest[0]] + rest[1..]);
        assert forall i: nat | i < |groups| ::
            |runs[i]| > 0 &&
            groups[i].count == |runs[i]| &&
            groups[i].line == runs[i][0] &&
            (forall j: nat | j < |runs[i]| ::
               Spec.LinesEqual(cmd, groups[i].line, runs[i][j])) &&
            (i + 1 < |groups| ==>
               !Spec.LinesEqual(
                 cmd, groups[i].line, groups[i + 1].line
               )) by {
          forall i: nat | i < |groups|
            ensures |runs[i]| > 0 &&
                    groups[i].count == |runs[i]| &&
                    groups[i].line == runs[i][0] &&
                    (forall j: nat | j < |runs[i]| ::
                       Spec.LinesEqual(
                         cmd, groups[i].line, runs[i][j]
                       )) &&
                    (i + 1 < |groups| ==>
                       !Spec.LinesEqual(
                         cmd, groups[i].line, groups[i + 1].line
                       ))
          {
          }
        }
      }
    }
  }

  lemma GroupsWitness(
    cmd: Schema.UniqCmd,
    lines: seq<BW.Bytes>
  ) returns (
      runs: seq<seq<BW.Bytes>>,
      cuts: seq<nat>
    )
    ensures Spec.RunPartitionWitnessRelation(
              cmd, lines, Core.Groups(cmd, lines), runs, cuts
            )
    ensures Spec.RunPartitionRelation(
              cmd, lines, Core.Groups(cmd, lines)
            )
  {
    if |lines| == 0 {
      runs := [];
      cuts := [0];
      reveal Spec.RunPartitionWitnessRelation();
      reveal Spec.RecordsConcatenate();
    } else {
      LinesEqualReflexive(cmd, lines[0]);
      runs, cuts := GroupsFromWitness(
        cmd, lines[1..], lines[0], 1, [lines[0]]
      );
    }
    reveal Spec.RunPartitionRelation();
    assert exists rs: seq<seq<BW.Bytes>>, cs: seq<nat> ::
        Spec.RunPartitionWitnessRelation(
          cmd, lines, Core.Groups(cmd, lines), rs, cs
        ) by {
      assert Spec.RunPartitionWitnessRelation(
          cmd, lines, Core.Groups(cmd, lines), runs, cuts
        );
    }
  }

  lemma DigitCharEq(d: int)
    ensures Core.DigitChar(d) == Spec.DigitChar(d)
  {
  }

  lemma DigitsEq(n: nat)
    ensures Core.Digits(n) == Spec.Digits(n)
    decreases n
  {
    if n < 10 {
      DigitCharEq(n as int);
    } else {
      DigitsEq(n / 10);
      DigitCharEq((n % 10) as int);
    }
  }

  lemma PadLeftEq(text: BW.Bytes, width: int)
    ensures Core.PadLeft(text, width) == Spec.PadLeft(text, width)
    decreases width - |text|
  {
    if |text| < width {
      PadLeftEq([' '] + text, width);
    }
  }

  lemma CountPrefixEq(count: nat)
    ensures Core.CountPrefix(count) == Spec.CountPrefix(count)
  {
    DigitsEq(count);
    PadLeftEq(Core.Digits(count), 7);
  }

  lemma ShouldOutputGroupEq(
    cmd: Schema.UniqCmd,
    group: Spec.Group
  )
    ensures Core.ShouldOutputGroup(cmd, group) ==
            Spec.ShouldOutputGroup(cmd, group)
  {
  }

  lemma RenderGroupRelation(
    cmd: Schema.UniqCmd,
    group: Spec.Group
  )
    ensures Spec.GroupRenderRelation(
              cmd, group, Core.RenderGroup(cmd, group)
            )
  {
    ShouldOutputGroupEq(cmd, group);
    if Core.ShouldOutputGroup(cmd, group) &&
       cmd.countOccurrences {
      CountPrefixEq(group.count);
    }
    reveal Spec.GroupRenderRelation();
  }

  lemma RenderGroupsWitness(
    cmd: Schema.UniqCmd,
    groups: seq<Spec.Group>
  ) returns (
      fragments: seq<BW.Bytes>,
      cuts: seq<nat>
    )
    ensures |fragments| == |groups|
    ensures forall i: nat | i < |groups| ::
              Spec.GroupRenderRelation(cmd, groups[i], fragments[i])
    ensures Spec.FragmentsConcatenate(
              fragments, Core.RenderGroups(cmd, groups), cuts
            )
    decreases |groups|
  {
    if |groups| == 0 {
      fragments := [];
      cuts := [0];
      reveal Spec.FragmentsConcatenate();
    } else {
      var head := Core.RenderGroup(cmd, groups[0]);
      RenderGroupRelation(cmd, groups[0]);
      var tailFragments, tailCuts :=
        RenderGroupsWitness(cmd, groups[1..]);
      fragments := [head] + tailFragments;
      cuts := [0] + ShiftCuts(tailCuts, |head|);
      PrependByteFragment(
        head,
        tailFragments,
        Core.RenderGroups(cmd, groups[1..]),
        tailCuts
      );
      assert forall i: nat | i < |groups| ::
          Spec.GroupRenderRelation(
            cmd, groups[i], fragments[i]
          ) by {
        forall i: nat | i < |groups|
          ensures Spec.GroupRenderRelation(
                    cmd, groups[i], fragments[i]
                  )
        {
        }
      }
    }
  }

  lemma {:isolate_assertions} OutputRelationForCore(
    cmd: Schema.UniqCmd,
    data: BW.Bytes
  )
    ensures Spec.OutputRelation(
              cmd, data, Core.RenderData(cmd, data)
            )
  {
    var records := Core.Lines(data);
    var terminated, lineFragments, lineCuts := LinesWitness(data);
    var groups := Core.Groups(cmd, records);
    var runs, runCuts := GroupsWitness(cmd, records);
    var outputFragments, outputCuts :=
      RenderGroupsWitness(cmd, groups);
    reveal Spec.OutputWitnessRelation();
    assert Spec.OutputWitnessRelation(
        cmd,
        data,
        Core.RenderData(cmd, data),
        records,
        terminated,
        groups,
        outputFragments,
        outputCuts
      );
    reveal Spec.OutputRelation();
    assert exists rs: seq<BW.Bytes>,
        ts: seq<bool>,
        gs: seq<Spec.Group>,
        fs: seq<BW.Bytes>,
        cs: seq<nat> ::
        Spec.OutputWitnessRelation(
          cmd, data, Core.RenderData(cmd, data), rs, ts, gs, fs, cs
        ) by {
      assert Spec.OutputWitnessRelation(
          cmd,
          data,
          Core.RenderData(cmd, data),
          records,
          terminated,
          groups,
          outputFragments,
          outputCuts
        );
    }
  }

  twostate lemma InputTraceRefines(
    cmd: Schema.UniqCmd,
    io: BenchIO.IO,
    new readResults: seq<BW.Result<BW.Bytes>>,
    new stdoutPart: BW.Bytes,
    new stderrPart: BW.Bytes,
    hadError: bool
  )
    requires Core.InputTraceRelation(
               cmd,
               old(io.fs()),
               old(io.stdin()),
               readResults,
               stdoutPart,
               stderrPart,
               hadError
             )
    ensures Spec.InputTraceRelation(
              cmd, io, readResults, stdoutPart, stderrPart, hadError
            )
  {
    reveal Core.InputTraceRelation();
    reveal Core.OutputRelation();
    reveal Spec.InputTraceRelation();
    match cmd.input {
      case Stdin =>
        OutputRelationForCore(cmd, old(io.stdin()));
      case File(_) =>
        match readResults[0] {
          case Ok(data) =>
            OutputRelationForCore(cmd, data);
          case Err(_) =>
        }
    }
  }

  twostate lemma CoreSummaryImpliesSpec(
    raw: Schema.UniqCmdRaw,
    io: BenchIO.IO,
    exit: int,
    new readResults: seq<BW.Result<BW.Bytes>>,
    new stdoutPart: BW.Bytes,
    new stderrPart: BW.Bytes,
    hadError: bool
  )
    requires Core.CoreSummary(
               raw, io, exit, readResults, stdoutPart, stderrPart, hadError
             )
    ensures Spec.Spec(raw, io, exit)
  {
    reveal Core.CoreSummary();
    reveal Spec.Spec();
    CommandEq(raw);
    var cmd := Core.Command(raw);
    if cmd.mode == Schema.ModeRun {
      InputTraceRefines(
        cmd,
        io,
        readResults,
        stdoutPart,
        stderrPart,
        hadError
      );
    }
  }
}
