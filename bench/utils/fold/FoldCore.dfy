include "../../core/World.dfy"
include "../../core/IO.dfy"
include "../../core/IOContract.dfy"
include "FoldSchema.dfy"
include "FoldSpec.dfy"

module FoldCore {
  import BenchIO
  import Utf8 = Utf8Semantics
  import BenchWorld
  import IOContract
  import Schema = FoldSchema
  import Spec = FoldSpec

  function IsDigit(ch: char): bool
  {
    '0' <= ch <= '9'
  }

  function DigitValue(ch: char): nat
    requires IsDigit(ch)
  {
    ((ch as int) - ('0' as int)) as nat
  }

  function ParseNatFrom(
    text: string,
    i: nat,
    acc: nat
  ): Schema.NatParse
    requires i <= |text|
    decreases |text| - i
  {
    if i == |text| then
      if acc == 0 then Schema.NatErr else Schema.NatOk(acc)
    else if !IsDigit(text[i]) then
      Schema.NatErr
    else
      ParseNatFrom(
        text, i + 1, acc * 10 + DigitValue(text[i])
      )
  } by method {
    if i == |text| {
      return if acc == 0 then Schema.NatErr else Schema.NatOk(acc);
    } else if !IsDigit(text[i]) {
      return Schema.NatErr;
    } else {
      return ParseNatFrom(
          text, i + 1, acc * 10 + DigitValue(text[i])
        );
    }
  }

  function ParsePositiveNat(text: string): Schema.NatParse
  {
    if |text| == 0 then Schema.NatErr else ParseNatFrom(text, 0, 0)
  } by method {
    if |text| == 0 {
      return Schema.NatErr;
    } else {
      return ParseNatFrom(text, 0, 0);
    }
  }

  function ParseWidthArgs(
    args: seq<Schema.WidthArg>,
    width: nat
  ): Schema.WidthParse
    requires width > 0
    ensures !ParseWidthArgs(args, width).hasInvalid ==>
              ParseWidthArgs(args, width).width > 0
    decreases |args|
  {
    if |args| == 0 then
      Schema.WidthParse(false, "", -1, width)
    else
      match ParsePositiveNat(args[0].text)
      case NatErr =>
        Schema.WidthParse(
          true, args[0].text, args[0].tokenIndex, width
        )
      case NatOk(nextWidth) =>
        if nextWidth == 0 then
          Schema.WidthParse(
            true, args[0].text, args[0].tokenIndex, width
          )
        else
          ParseWidthArgs(args[1..], nextWidth)
  } by method {
    if |args| == 0 {
      return Schema.WidthParse(false, "", -1, width);
    }
    match ParsePositiveNat(args[0].text)
    case NatErr =>
      return Schema.WidthParse(
          true, args[0].text, args[0].tokenIndex, width
        );
    case NatOk(nextWidth) =>
      if nextWidth == 0 {
        return Schema.WidthParse(
            true, args[0].text, args[0].tokenIndex, width
          );
      } else {
        return ParseWidthArgs(args[1..], nextWidth);
      }
  }

  function InputsFromOperands(
    operands: seq<string>
  ): seq<Schema.Input>
    ensures |InputsFromOperands(operands)| == |operands|
    decreases |operands|
  {
    if |operands| == 0 then
      []
    else
      [(if operands[0] == "-"
        then Schema.Stdin
        else Schema.File(operands[0]))] +
      InputsFromOperands(operands[1..])
  } by method {
    if |operands| == 0 {
      return [];
    } else {
      var input :=
        if operands[0] == "-"
        then Schema.Stdin
        else Schema.File(operands[0]);
      return [input] + InputsFromOperands(operands[1..]);
    }
  }

  function HelpBeforeOther(raw: Schema.FoldCmdRaw): bool
  {
    var widthPlan := ParseWidthArgs(raw.widthArgs, 80);
    raw.seenHelp &&
    (!raw.seenVersion ||
     raw.helpTokenIndex <= raw.versionTokenIndex) &&
    (!widthPlan.hasInvalid ||
     raw.helpTokenIndex <= widthPlan.invalidTokenIndex)
  }

  function VersionBeforeInvalid(raw: Schema.FoldCmdRaw): bool
  {
    var widthPlan := ParseWidthArgs(raw.widthArgs, 80);
    raw.seenVersion &&
    (!widthPlan.hasInvalid ||
     raw.versionTokenIndex <= widthPlan.invalidTokenIndex)
  }

  function Command(raw: Schema.FoldCmdRaw): Schema.FoldCmd
  {
    var widthPlan := ParseWidthArgs(raw.widthArgs, 80);
    if HelpBeforeOther(raw) then
      Schema.FoldCmd(
        Schema.ModeHelp, 80, "", raw.byteMode, raw.spaceMode, []
      )
    else if VersionBeforeInvalid(raw) then
      Schema.FoldCmd(
        Schema.ModeVersion, 80, "", raw.byteMode, raw.spaceMode, []
      )
    else if widthPlan.hasInvalid then
      Schema.FoldCmd(
        Schema.ModeInvalidWidth,
        80,
        widthPlan.invalidText,
        raw.byteMode,
        raw.spaceMode,
        []
      )
    else
      var inputs := InputsFromOperands(raw.operands);
      Schema.FoldCmd(
        Schema.ModeRun,
        widthPlan.width,
        "",
        raw.byteMode,
        raw.spaceMode,
        if |inputs| == 0 then [Schema.Stdin] else inputs
      )
  } by method {
    var widthPlan := ParseWidthArgs(raw.widthArgs, 80);
    if HelpBeforeOther(raw) {
      return Schema.FoldCmd(
          Schema.ModeHelp, 80, "", raw.byteMode, raw.spaceMode, []
        );
    } else if VersionBeforeInvalid(raw) {
      return Schema.FoldCmd(
          Schema.ModeVersion, 80, "", raw.byteMode, raw.spaceMode, []
        );
    } else if widthPlan.hasInvalid {
      return Schema.FoldCmd(
          Schema.ModeInvalidWidth,
          80,
          widthPlan.invalidText,
          raw.byteMode,
          raw.spaceMode,
          []
        );
    } else {
      var inputs := InputsFromOperands(raw.operands);
      return Schema.FoldCmd(
          Schema.ModeRun,
          widthPlan.width,
          "",
          raw.byteMode,
          raw.spaceMode,
          if |inputs| == 0 then [Schema.Stdin] else inputs
        );
    }
  }

  function StepColumn(byteMode: bool, ch: char, column: nat): nat
  {
    if byteMode then
      column + 1
    else if ch == '\U{0}' then
      column
    else if ch == '\U{8}' then
      if column == 0 then 0 else column - 1
    else if ch == '\r' then
      0
    else if ch == '\t' then
      column + (8 - column % 8)
    else
      column + 1
  } by method {
    if byteMode {
      return column + 1;
    } else if ch == '\U{0}' {
      return column;
    } else if ch == '\U{8}' {
      return if column == 0 then 0 else column - 1;
    } else if ch == '\r' {
      return 0;
    } else if ch == '\t' {
      return column + (8 - column % 8);
    } else {
      return column + 1;
    }
  }

  function IsBlank(ch: char): bool
  {
    ch == ' ' || ch == '\t'
  } by method {
    return ch == ' ' || ch == '\t';
  }

  twostate predicate CoreSummary(raw: Schema.FoldCmdRaw, io: BenchIO.IO, exit: int)
    reads io.Footprint()
  {
    var cmd := Command(raw);
    if cmd.mode == Schema.ModeHelp then
      io.stdin() == old(io.stdin()) &&
      io.stdout() == old(io.stdout()) + Spec.HelpText() &&
      io.stderr() == old(io.stderr()) &&
      exit == 0
    else if cmd.mode == Schema.ModeVersion then
      io.stdin() == old(io.stdin()) &&
      io.stdout() == old(io.stdout()) + Spec.VersionText() &&
      io.stderr() == old(io.stderr()) &&
      exit == 0
    else if cmd.mode == Schema.ModeInvalidWidth then
      io.stdin() == old(io.stdin()) &&
      io.stdout() == old(io.stdout()) &&
      io.stderr() == old(io.stderr()) + Spec.InvalidWidthMessage(cmd.invalidWidthValue) &&
      exit == 1
    else
      exists stdoutPart: BenchWorld.Bytes, stderrPart: BenchWorld.Bytes, hadError: bool ::
        Spec.InputTraceRelation(
          cmd,
          old(io.fs()),
          old(io.stdin()),
          io.stdin(),
          stdoutPart,
          stderrPart,
          hadError
        ) &&
        io.stdout() == old(io.stdout()) + stdoutPart &&
        io.stderr() == old(io.stderr()) + stderrPart &&
        exit == (if hadError then 1 else 0)
  }

  lemma JoinFragmentsSnoc(
    fragments: seq<BenchWorld.Bytes>,
    last: BenchWorld.Bytes
  )
    ensures Spec.JoinFragments(fragments + [last]) ==
            Spec.JoinFragments(fragments) + last
    decreases |fragments|
  {
    if |fragments| > 0 {
      assert (fragments + [last])[0] == fragments[0];
      assert (fragments + [last])[1..] == fragments[1..] + [last];
      JoinFragmentsSnoc(fragments[1..], last);
    }
  }

  lemma {:isolate_assertions} ExtendInputPrefixTrace(
    cmd: Schema.FoldCmd,
    preFs: BenchWorld.FileSystem,
    preStdin: BenchWorld.Bytes,
    count: nat,
    postStdin: BenchWorld.Bytes,
    results: seq<BenchWorld.Result<BenchWorld.Bytes>>,
    stdoutFragments: seq<BenchWorld.Bytes>,
    stderrFragments: seq<BenchWorld.Bytes>,
    hadError: bool,
    result: BenchWorld.Result<BenchWorld.Bytes>,
                              stdoutFragment: BenchWorld.Bytes,
                              stderrFragment: BenchWorld.Bytes,
                              nextPostStdin: BenchWorld.Bytes,
                              nextHadError: bool
  )
    requires count < |cmd.inputs|
    requires Spec.InputPrefixTraceRelation(
               cmd,
               preFs,
               preStdin,
               count,
               postStdin,
               results,
               stdoutFragments,
               stderrFragments,
               hadError
             )
    requires result == Spec.ReadResultAt(cmd, preFs, preStdin, count)
    requires match result
             case Ok(data) =>
               Spec.DataFoldRelation(
                 cmd.width, cmd.byteMode, cmd.spaceMode, data, stdoutFragment
               ) &&
               stderrFragment == []
             case Err(err) =>
               stdoutFragment == [] &&
               match cmd.inputs[count]
               case Stdin => false
               case File(path) => stderrFragment == Spec.ErrorMessage(path, err)
    requires nextPostStdin ==
             (if Spec.HasEarlierStdin(cmd, count + 1) then [] else preStdin)
    requires nextHadError ==
             (hadError ||
              match result
              case Ok(_) => false
              case Err(_) => cmd.inputs[count].File?)
    ensures Spec.InputPrefixTraceRelation(
              cmd,
              preFs,
              preStdin,
              count + 1,
              nextPostStdin,
              results + [result],
              stdoutFragments + [stdoutFragment],
              stderrFragments + [stderrFragment],
              nextHadError
            )
  {
    reveal Spec.InputPrefixTraceRelation();
    assert forall i :: 0 <= i < |results + [result]| ==>
                         (results + [result])[i] ==
                         Spec.ReadResultAt(cmd, preFs, preStdin, i) by {
      forall i | 0 <= i < |results + [result]|
        ensures (results + [result])[i] ==
                Spec.ReadResultAt(cmd, preFs, preStdin, i)
      {
      }
    }
    assert forall i :: 0 <= i < |results + [result]| ==>
                         match (results + [result])[i]
                         case Ok(data) =>
                           Spec.DataFoldRelation(
                             cmd.width,
                             cmd.byteMode,
                             cmd.spaceMode,
                             data,
                             (stdoutFragments + [stdoutFragment])[i]
                           ) &&
                           (stderrFragments + [stderrFragment])[i] == []
                         case Err(err) =>
                           (stdoutFragments + [stdoutFragment])[i] == [] &&
                           match cmd.inputs[i]
                           case Stdin => false
                           case File(path) =>
                             (stderrFragments + [stderrFragment])[i] ==
                             Spec.ErrorMessage(path, err) by {
      forall i | 0 <= i < |results + [result]|
        ensures match (results + [result])[i]
                case Ok(data) =>
                  Spec.DataFoldRelation(
                    cmd.width,
                    cmd.byteMode,
                    cmd.spaceMode,
                    data,
                    (stdoutFragments + [stdoutFragment])[i]
                  ) &&
                  (stderrFragments + [stderrFragment])[i] == []
                case Err(err) =>
                  (stdoutFragments + [stdoutFragment])[i] == [] &&
                  match cmd.inputs[i]
                  case Stdin => false
                  case File(path) =>
                    (stderrFragments + [stderrFragment])[i] ==
                    Spec.ErrorMessage(path, err)
      {
        if i < count {
        } else {
          assert i == count;
        }
      }
    }
  }

  lemma HasEarlierFileStep(cmd: Schema.FoldCmd, i: nat)
    requires i < |cmd.inputs|
    requires cmd.inputs[i].File?
    ensures Spec.HasEarlierStdin(cmd, i + 1) ==
            Spec.HasEarlierStdin(cmd, i)
  {
    reveal Spec.HasEarlierStdin();
    if Spec.HasEarlierStdin(cmd, i + 1) {
      var j :| 0 <= j < i + 1 && cmd.inputs[j] == Schema.Stdin;
      assert j != i;
    }
  }

  method GetHelpText() returns (out: BenchWorld.Bytes)
    ensures out == Spec.HelpText()
  {
    out := Spec.HelpText();
  }

  method GetVersionText() returns (out: BenchWorld.Bytes)
    ensures out == Spec.VersionText()
  {
    out := Spec.VersionText();
  }

  method GetInvalidWidthMessage(value: string) returns (msg: BenchWorld.Bytes)
    ensures msg == Spec.InvalidWidthMessage(value)
  {
    msg := Spec.InvalidWidthMessage(value);
  }

  method ErrorMessageMethod(path: BenchWorld.Path, err: BenchWorld.IOError) returns (msg: BenchWorld.Bytes)
    ensures msg == Spec.ErrorMessage(path, err)
  {
    msg := Spec.ErrorMessage(path, err);
  }

  method FittingPrefixMethod(
    width: nat,
    byteMode: bool,
    line: BenchWorld.Bytes
  ) returns (
      prefix: BenchWorld.Bytes,
      lastBlankEnd: nat,
      ghost columns: seq<nat>
    )
    requires width > 0
    requires |line| > 0
    ensures 0 < |prefix| <= |line|
    ensures prefix == line[..|prefix|]
    ensures Spec.FittingEndRelation(
              width, byteMode, line, 0, |prefix|
            )
    ensures lastBlankEnd <= |prefix|
    ensures lastBlankEnd == 0 ==>
              forall i :: 0 <= i < |prefix| ==> !Spec.IsBlank(prefix[i])
    ensures lastBlankEnd > 0 ==>
              Spec.IsBlank(prefix[lastBlankEnd - 1]) &&
              forall i :: lastBlankEnd <= i < |prefix| ==> !Spec.IsBlank(prefix[i])
  {
    var end: nat := 0;
    var column: nat := 0;
    var scanning := true;
    lastBlankEnd := 0;
    columns := [0];
    reveal Spec.ColumnTraceRelation();
    while scanning && end < |line|
      invariant 0 <= end <= |line|
      invariant |columns| == end + 1
      invariant columns[0] == 0
      invariant forall i :: 0 <= i < end ==>
                              columns[i + 1] ==
                              Spec.StepColumn(byteMode, line[i], columns[i])
      invariant column == columns[end]
      invariant forall i {:trigger columns[i + 1]} ::
                  1 <= i < end ==> columns[i + 1] <= width
      invariant lastBlankEnd <= end
      invariant lastBlankEnd == 0 ==>
                  forall i :: 0 <= i < end ==> !Spec.IsBlank(line[i])
      invariant lastBlankEnd > 0 ==>
                  Spec.IsBlank(line[lastBlankEnd - 1]) &&
                  forall i :: lastBlankEnd <= i < end ==> !Spec.IsBlank(line[i])
      invariant !scanning ==>
                  end > 0 &&
                  end < |line| &&
                  Spec.StepColumn(byteMode, line[end], columns[end]) > width
      decreases |line| - end, if scanning then 1 else 0
    {
      var nextColumn := StepColumn(byteMode, line[end], column);
      if nextColumn > width && end > 0 {
        scanning := false;
      } else {
        ghost var previousColumns := columns;
        var previousEnd := end;
        columns := columns + [nextColumn];
        column := nextColumn;
        end := end + 1;
        assert forall i :: 0 <= i < end ==>
                             columns[i + 1] ==
                             Spec.StepColumn(byteMode, line[i], columns[i]) by {
          forall i | 0 <= i < end
            ensures columns[i + 1] ==
                    Spec.StepColumn(byteMode, line[i], columns[i])
          {
            if i < previousEnd {
              assert columns[i] == previousColumns[i];
              assert columns[i + 1] == previousColumns[i + 1];
            } else {
              assert i == previousEnd;
            }
          }
        }
        if IsBlank(line[previousEnd]) {
          lastBlankEnd := end;
        }
      }
    }
    prefix := line[..end];
    reveal Spec.FittingEndRelation();
    assert Spec.ColumnTraceRelation(byteMode, prefix, 0, columns);
    assert forall i {:trigger columns[i + 1]} ::
        1 <= i < |prefix| ==> columns[i + 1] <= width;
    assert end == |line| ||
           Spec.StepColumn(byteMode, line[end], columns[end]) > width;
  }

  method {:isolate_assertions} BreakPrefixMethod(
    width: nat,
    byteMode: bool,
    spaceMode: bool,
    line: BenchWorld.Bytes
  )
    returns (prefix: BenchWorld.Bytes)
    requires width > 0
    requires |line| > 0
    ensures 0 < |prefix| <= |line|
    ensures prefix == line[..|prefix|]
    ensures Spec.BreakPointRelation(
              width, byteMode, spaceMode, line, 0, |prefix|
            )
  {
    var fit, lastBlankEnd, columns :=
      FittingPrefixMethod(width, byteMode, line);
    if spaceMode && |fit| < |line| && lastBlankEnd > 0 {
      prefix := fit[..lastBlankEnd];
    } else {
      prefix := fit;
    }
    assert prefix == line[..|prefix|];
    reveal Spec.BreakPointRelation();
    if spaceMode && |fit| < |line| && lastBlankEnd > 0 {
      assert Spec.IsBlank(line[lastBlankEnd - 1]);
      assert forall j :: 0 <= j < |fit| && Spec.IsBlank(line[j]) ==>
                           j < lastBlankEnd by {
        forall j | 0 <= j < |fit| && Spec.IsBlank(line[j])
          ensures j < lastBlankEnd
        {
          if lastBlankEnd <= j {
            assert !Spec.IsBlank(fit[j]);
          }
        }
      }
    } else if lastBlankEnd == 0 {
      assert forall j :: 0 <= j < |fit| ==> !Spec.IsBlank(line[j]) by {
        forall j | 0 <= j < |fit|
          ensures !Spec.IsBlank(line[j])
        {
          assert fit[j] == line[j];
        }
      }
    }
  }

  method {:isolate_assertions} FoldLineMethod(
    width: nat,
    byteMode: bool,
    spaceMode: bool,
    line: BenchWorld.Bytes
  )
    returns (out: BenchWorld.Bytes, ghost segments: seq<BenchWorld.Bytes>)
    requires width > 0
    ensures Spec.LinePartitionRelation(width, byteMode, spaceMode, line, segments)
    ensures out == Spec.RenderSegments(segments)
    ensures Spec.LineOutputRelation(width, byteMode, spaceMode, line, out)
    decreases |line|
  {
    if |line| == 0 {
      out := [];
      segments := [];
      reveal Spec.LinePartitionRelation();
      reveal Spec.LineOutputRelation();
    } else {
      var prefix := BreakPrefixMethod(width, byteMode, spaceMode, line);
      if |prefix| == |line| {
        out := prefix;
        segments := [prefix];
        reveal Spec.LinePartitionRelation();
        reveal Spec.LineOutputRelation();
      } else {
        var tail, tailSegments :=
          FoldLineMethod(width, byteMode, spaceMode, line[|prefix|..]);
        out := prefix + ['\n'] + tail;
        segments := [prefix] + tailSegments;
        reveal Spec.LinePartitionRelation();
        assert line == prefix + line[|prefix|..];
        assert line == Spec.JoinFragments(segments);
        assert forall i :: 0 <= i < |segments| ==>
                             |segments[i]| > 0 &&
                             Spec.BreakPointRelation(
                               width,
                               byteMode,
                               spaceMode,
                               Spec.JoinFragments(segments[i..]),
                               0,
                               |segments[i]|
                             ) by {
          forall i | 0 <= i < |segments|
            ensures |segments[i]| > 0 &&
                    Spec.BreakPointRelation(
                      width,
                      byteMode,
                      spaceMode,
                      Spec.JoinFragments(segments[i..]),
                      0,
                      |segments[i]|
                    )
          {
            if i == 0 {
              assert Spec.JoinFragments(segments) == line;
            } else {
              assert segments[i..] == tailSegments[i - 1..];
            }
          }
        }
        reveal Spec.LineOutputRelation();
      }
    }
  }

  method EffectiveInputMethod(data: BenchWorld.Bytes)
    returns (out: BenchWorld.Bytes, ghost end: nat)
    ensures Spec.EffectivePrefixRelation(data, out, end)
    decreases |data|
  {
    if |data| == 0 {
      out := [];
      end := 0;
    } else if data[0] == '\U{FF}' {
      out := [];
      end := 0;
    } else {
      var tail, tailEnd := EffectiveInputMethod(data[1..]);
      out := [data[0]] + tail;
      end := 1 + tailEnd;
    }
    reveal Spec.EffectivePrefixRelation();
  }

  method {:isolate_assertions} LinesFromMethod(
    data: BenchWorld.Bytes,
    current: BenchWorld.Bytes
  ) returns (
      records: seq<BenchWorld.Bytes>,
      terminated: seq<bool>,
      ghost fragments: seq<BenchWorld.Bytes>
    )
    requires forall j :: 0 <= j < |current| ==> current[j] != '\n'
    ensures Spec.RecordPartitionWitnessRelation(
              current + data, records, terminated, fragments
            )
    ensures Spec.RecordPartitionRelation(current + data, records, terminated)
    decreases |data|
  {
    if |data| == 0 {
      if |current| == 0 {
        records := [];
        terminated := [];
        fragments := [];
      } else {
        records := [current];
        terminated := [false];
        fragments := [current];
      }
      reveal Spec.RecordPartitionWitnessRelation();
      reveal Spec.RecordPartitionRelation();
    } else if data[0] == '\n' {
      var tailRecords, tailTerminated, tailFragments :=
        LinesFromMethod(data[1..], []);
      var head := current + ['\n'];
      records := [current] + tailRecords;
      terminated := [true] + tailTerminated;
      fragments := [head] + tailFragments;
      reveal Spec.RecordPartitionWitnessRelation();
      assert current + data == head + data[1..];
      assert Spec.JoinFragments(fragments) ==
             head + Spec.JoinFragments(tailFragments);
      assert forall i :: 0 <= i < |records| ==>
                           fragments[i] ==
                           records[i] + (if terminated[i] then ['\n'] else []) &&
                           (forall j :: 0 <= j < |records[i]| ==> records[i][j] != '\n') &&
                           (i + 1 < |records| ==> terminated[i]) by {
        forall i | 0 <= i < |records|
          ensures fragments[i] ==
                  records[i] + (if terminated[i] then ['\n'] else []) &&
                  (forall j :: 0 <= j < |records[i]| ==> records[i][j] != '\n') &&
                  (i + 1 < |records| ==> terminated[i])
        {
        }
      }
      reveal Spec.RecordPartitionRelation();
    } else {
      records, terminated, fragments :=
        LinesFromMethod(data[1..], current + [data[0]]);
      assert current + data == (current + [data[0]]) + data[1..];
    }
    reveal Spec.RecordPartitionRelation();
    assert exists candidate: seq<BenchWorld.Bytes> ::
        Spec.RecordPartitionWitnessRelation(
          current + data, records, terminated, candidate
        ) by {
      assert Spec.RecordPartitionWitnessRelation(
          current + data, records, terminated, fragments
        );
    }
  }

  method {:isolate_assertions} FoldRecordsMethod(
    width: nat,
    byteMode: bool,
    spaceMode: bool,
    records: seq<BenchWorld.Bytes>,
    terminated: seq<bool>
  ) returns (out: BenchWorld.Bytes, ghost lineOutputs: seq<BenchWorld.Bytes>)
    requires width > 0
    requires |records| == |terminated|
    ensures |lineOutputs| == |records|
    ensures forall i :: 0 <= i < |records| ==>
                          Spec.LineOutputRelation(
                            width, byteMode, spaceMode, records[i], lineOutputs[i]
                          )
    ensures out == Spec.RenderRecords(lineOutputs, terminated)
    decreases |records|
  {
    if |records| == 0 {
      out := [];
      lineOutputs := [];
    } else {
      var head, headSegments :=
        FoldLineMethod(width, byteMode, spaceMode, records[0]);
      var tail, tailOutputs := FoldRecordsMethod(
        width, byteMode, spaceMode, records[1..], terminated[1..]
      );
      lineOutputs := [head] + tailOutputs;
      out := head + (if terminated[0] then ['\n'] else []) + tail;
      assert forall i :: 0 <= i < |records| ==>
                           Spec.LineOutputRelation(
                             width, byteMode, spaceMode, records[i], lineOutputs[i]
                           ) by {
        forall i | 0 <= i < |records|
          ensures Spec.LineOutputRelation(
                    width, byteMode, spaceMode, records[i], lineOutputs[i]
                  )
        {
        }
      }
    }
  }

  method FoldDataMethod(width: nat, byteMode: bool, spaceMode: bool, data: BenchWorld.Bytes)
    returns (out: BenchWorld.Bytes)
    requires width > 0
    ensures Spec.DataFoldRelation(width, byteMode, spaceMode, data, out)
  {
    var effective, effectiveEnd := EffectiveInputMethod(data);
    var records, terminated, fragments := LinesFromMethod(effective, []);
    assert [] + effective == effective;
    assert Spec.RecordPartitionWitnessRelation(
        effective, records, terminated, fragments
      );
    reveal Spec.RecordPartitionRelation();
    assert exists candidate: seq<BenchWorld.Bytes> ::
        Spec.RecordPartitionWitnessRelation(
          effective, records, terminated, candidate
        ) by {
      assert Spec.RecordPartitionWitnessRelation(
          effective, records, terminated, fragments
        );
    }
    var folded, lineOutputs :=
      FoldRecordsMethod(width, byteMode, spaceMode, records, terminated);
    out := folded;
    reveal Spec.DataFoldRelation();
  }

  method OutputPieceMethod(cmd: Schema.FoldCmd, result: BenchWorld.Result<BenchWorld.Bytes>)
    returns (out: BenchWorld.Bytes)
    requires cmd.width > 0
    ensures match result
            case Ok(data) =>
              Spec.DataFoldRelation(cmd.width, cmd.byteMode, cmd.spaceMode, data, out)
            case Err(_) => out == []
  {
    match result
    case Ok(data) =>
      out := FoldDataMethod(cmd.width, cmd.byteMode, cmd.spaceMode, data);
    case Err(_) =>
      out := [];
  }

  method {:isolate_assertions} RunCore(
    raw: Schema.FoldCmdRaw,
    io: BenchIO.IO
  ) returns (exit: int)
    modifies io.stdinRegion, io.stdoutRegion, io.stderrRegion
    ensures CoreSummary(raw, io, exit)
    decreases *
  {
    ghost var preFs := io.fs();
    ghost var preStdin := io.stdin();
    ghost var preStdout := io.stdout();
    ghost var preStderr := io.stderr();
    var cmd := Command(raw);
    if cmd.mode == Schema.ModeHelp {
      var help := GetHelpText();
      io.AppendStdout(help);
      exit := 0;
      assert help == Spec.HelpText();
      assert CoreSummary(raw, io, exit);
      return;
    }
    if cmd.mode == Schema.ModeVersion {
      var version := GetVersionText();
      io.AppendStdout(version);
      exit := 0;
      assert version == Spec.VersionText();
      assert CoreSummary(raw, io, exit);
      return;
    }
    if cmd.mode == Schema.ModeInvalidWidth {
      var msg := GetInvalidWidthMessage(cmd.invalidWidthValue);
      io.AppendStderr(msg);
      exit := 1;
      assert msg == Spec.InvalidWidthMessage(cmd.invalidWidthValue);
      assert CoreSummary(raw, io, exit);
      return;
    }

    assert cmd.width > 0;
    var hadError := false;
    var output: BenchWorld.Bytes := [];
    var errors: BenchWorld.Bytes := [];
    ghost var results: seq<BenchWorld.Result<BenchWorld.Bytes>> := [];
    ghost var stdoutFragments: seq<BenchWorld.Bytes> := [];
    ghost var stderrFragments: seq<BenchWorld.Bytes> := [];
    var i := 0;
    reveal Spec.InputPrefixTraceRelation();
    while i < |cmd.inputs|
      invariant 0 <= i <= |cmd.inputs|
      invariant cmd.width > 0
      invariant io.stdout() == preStdout
      invariant io.stderr() == preStderr
      invariant Spec.InputPrefixTraceRelation(
                  cmd,
                  preFs,
                  preStdin,
                  i,
                  io.stdin(),
                  results,
                  stdoutFragments,
                  stderrFragments,
                  hadError
                )
      invariant output == Spec.JoinFragments(stdoutFragments)
      invariant errors == Spec.JoinFragments(stderrFragments)
      decreases |cmd.inputs| - i
    {
      var input := cmd.inputs[i];
      match input
      case Stdin =>
        ghost var beforeStdin := io.stdin();
        var data := io.ReadStdinAll();
        assert IOContract.ReadStdinAllFields(beforeStdin, io.stdin(), data);
        var piece := OutputPieceMethod(cmd, BenchWorld.Ok(data));
        assert Spec.DataFoldRelation(
            cmd.width, cmd.byteMode, cmd.spaceMode, data, piece
          );
        assert data ==
               (if Spec.HasEarlierStdin(cmd, i) then [] else preStdin);
        JoinFragmentsSnoc(stdoutFragments, piece);
        JoinFragmentsSnoc(stderrFragments, []);
        assert BenchWorld.Ok(data) ==
               Spec.ReadResultAt(cmd, preFs, preStdin, i);
        assert io.stdin() ==
               (if Spec.HasEarlierStdin(cmd, i + 1) then [] else preStdin);
        ExtendInputPrefixTrace(
          cmd,
          preFs,
          preStdin,
          i,
          beforeStdin,
          results,
          stdoutFragments,
          stderrFragments,
          hadError,
          BenchWorld.Ok(data),
          piece,
          [],
          io.stdin(),
          hadError
        );
        results := results + [BenchWorld.Ok(data)];
        stdoutFragments := stdoutFragments + [piece];
        stderrFragments := stderrFragments + [[]];
        output := output + piece;
        i := i + 1;
        reveal Spec.InputPrefixTraceRelation();
      case File(path) =>
        var result := io.ReadFile(path);
        assert result == IOContract.ReadFileResultFields(preFs, path);
        HasEarlierFileStep(cmd, i);
        match result
        case Ok(data) =>
          var piece := OutputPieceMethod(cmd, result);
          JoinFragmentsSnoc(stdoutFragments, piece);
          JoinFragmentsSnoc(stderrFragments, []);
          assert result == Spec.ReadResultAt(cmd, preFs, preStdin, i);
          assert io.stdin() ==
                 (if Spec.HasEarlierStdin(cmd, i + 1) then [] else preStdin);
          ExtendInputPrefixTrace(
            cmd,
            preFs,
            preStdin,
            i,
            io.stdin(),
            results,
            stdoutFragments,
            stderrFragments,
            hadError,
            result,
            piece,
            [],
            io.stdin(),
            hadError
          );
          results := results + [result];
          stdoutFragments := stdoutFragments + [piece];
          stderrFragments := stderrFragments + [[]];
          output := output + piece;
          i := i + 1;
          reveal Spec.InputPrefixTraceRelation();
        case Err(err) =>
          var msg := ErrorMessageMethod(path, err);
          JoinFragmentsSnoc(stdoutFragments, []);
          JoinFragmentsSnoc(stderrFragments, msg);
          assert result == Spec.ReadResultAt(cmd, preFs, preStdin, i);
          assert io.stdin() ==
                 (if Spec.HasEarlierStdin(cmd, i + 1) then [] else preStdin);
          ExtendInputPrefixTrace(
            cmd,
            preFs,
            preStdin,
            i,
            io.stdin(),
            results,
            stdoutFragments,
            stderrFragments,
            hadError,
            result,
            [],
            msg,
            io.stdin(),
            true
          );
          results := results + [result];
          stdoutFragments := stdoutFragments + [[]];
          stderrFragments := stderrFragments + [msg];
          errors := errors + msg;
          hadError := true;
          i := i + 1;
          reveal Spec.InputPrefixTraceRelation();
    }

    reveal Spec.InputTraceRelation();
    assert Spec.InputTraceRelation(
        cmd, preFs, preStdin, io.stdin(), output, errors, hadError
      );
    io.AppendStdout(output);
    io.AppendStderr(errors);
    exit := if hadError then 1 else 0;
    assert exists stdoutPart: BenchWorld.Bytes,
        stderrPart: BenchWorld.Bytes,
        traceHadError: bool ::
        Spec.InputTraceRelation(
          cmd,
          preFs,
          preStdin,
          io.stdin(),
          stdoutPart,
          stderrPart,
          traceHadError
        ) &&
        io.stdout() == preStdout + stdoutPart &&
        io.stderr() == preStderr + stderrPart &&
        exit == (if traceHadError then 1 else 0) by {
      assert Spec.InputTraceRelation(
          cmd, preFs, preStdin, io.stdin(), output, errors, hadError
        );
    }
    assert CoreSummary(raw, io, exit);
  }
}
