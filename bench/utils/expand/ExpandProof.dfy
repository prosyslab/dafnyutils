include "../../core/IO.dfy"
include "ExpandSchema.dfy"
include "ExpandCore.dfy"
include "ExpandSpec.dfy"

module ExpandProof {
  import BenchIO
  import BenchWorld
  import Schema = ExpandSchema
  import Core = ExpandCore
  import Spec = ExpandSpec

  lemma IsDigitEq(ch: char)
    ensures Core.IsDigit(ch) == Spec.IsDigit(ch)
  {
  }

  lemma MaxColumnEq()
    ensures Core.MaxColumn() == Spec.MaxColumn()
  {
  }

  lemma DigitValueEq(ch: char)
    requires Core.IsDigit(ch)
    ensures Core.DigitValue(ch) == Spec.DigitValue(ch)
  {
  }

  lemma IsSeparatorEq(ch: char)
    ensures Core.IsSeparator(ch) == Spec.IsSeparator(ch)
  {
  }

  lemma IsMarkerEq(ch: char)
    ensures Core.IsMarker(ch) == Spec.IsMarker(ch)
  {
  }

  lemma MarkerOfEq(ch: char)
    requires Core.IsMarker(ch)
    ensures Core.MarkerOf(ch) == Spec.MarkerOf(ch)
  {
  }

  lemma LastStopEq(stops: seq<nat>)
    requires |stops| > 0
    ensures Core.LastStop(stops) == Spec.LastStop(stops)
  {
  }

  lemma HelpBeforeOtherEq(raw: Schema.ExpandCmdRaw)
    ensures Core.HelpBeforeOther(raw) == Spec.HelpBeforeOther(raw)
  {
  }

  lemma VersionBeforeInvalidEq(raw: Schema.ExpandCmdRaw)
    ensures Core.VersionBeforeInvalid(raw) == Spec.VersionBeforeInvalid(raw)
  {
  }

  lemma RequestTokenIndexEq(raw: Schema.ExpandCmdRaw)
    ensures Core.RequestTokenIndex(raw) == Spec.RequestTokenIndex(raw)
  {
    HelpBeforeOtherEq(raw);
    VersionBeforeInvalidEq(raw);
  }

  lemma NatParseSatisfies(text: string, i: nat, acc: nat)
    requires i <= |text|
    ensures Spec.NatParseRelation(
              text, i, acc, Core.ParseNatFrom(text, i, acc)
            )
    decreases |text| - i
  {
    if i < |text| {
      IsDigitEq(text[i]);
      if Core.IsDigit(text[i]) {
        DigitValueEq(text[i]);
        MaxColumnEq();
        if acc <= (Core.MaxColumn() - Core.DigitValue(text[i])) / 10 {
          NatParseSatisfies(
            text, i + 1,
            acc * 10 + Core.DigitValue(text[i])
          );
        }
      }
    }
  }

  lemma PositiveNatSatisfies(text: string)
    ensures Spec.PositiveNatRelation(
              text, Core.ParsePositiveNat(text)
            )
  {
    if |text| > 0 {
      NatParseSatisfies(text, 0, 0);
    }
  }

  lemma TokenEndSatisfies(text: string, start: nat)
    requires start <= |text|
    ensures Spec.TokenEndRelation(
              text, start, Core.FindTokenEnd(text, start)
            )
    decreases |text| - start
  {
    if start < |text| {
      IsSeparatorEq(text[start]);
      if !Core.IsSeparator(text[start]) {
        TokenEndSatisfies(text, start + 1);
      }
    }
  }

  lemma DigitsEndSatisfies(text: string, start: nat)
    requires start <= |text|
    ensures Spec.DigitsEndRelation(
              text, start, Core.FindDigitsEnd(text, start)
            )
    decreases |text| - start
  {
    if start < |text| {
      IsDigitEq(text[start]);
      if Core.IsDigit(text[start]) {
        DigitsEndSatisfies(text, start + 1);
      }
    }
  }

  lemma FindDigitsEndEq(text: string, start: nat)
    requires start <= |text|
    ensures Core.FindDigitsEnd(text, start) ==
            Spec.FindDigitsEnd(text, start)
    decreases |text| - start
  {
    if start < |text| {
      IsDigitEq(text[start]);
      if Core.IsDigit(text[start]) {
        FindDigitsEndEq(text, start + 1);
      }
    }
  }

  lemma SyntaxDiagnosticsFromEq(
    text: string,
    i: nat,
    haveValue: bool,
    numberStart: nat,
    value: nat
  )
    requires i <= |text|
    requires !haveValue || numberStart <= i
    ensures Core.SyntaxDiagnosticsFrom(
              text, i, haveValue, numberStart, value
            ) == Spec.SyntaxDiagnosticsFrom(
                   text, i, haveValue, numberStart, value
                 )
    decreases |text| - i
  {
    if i < |text| {
      IsSeparatorEq(text[i]);
      if Core.IsSeparator(text[i]) {
        SyntaxDiagnosticsFromEq(text, i + 1, false, 0, 0);
      } else {
        IsMarkerEq(text[i]);
        if Core.IsMarker(text[i]) {
          MarkerOfEq(text[i]);
          SyntaxDiagnosticsFromEq(
            text, i + 1, haveValue, numberStart, value
          );
        } else {
          IsDigitEq(text[i]);
          if Core.IsDigit(text[i]) {
            DigitValueEq(text[i]);
            MaxColumnEq();
            var start := if haveValue then numberStart else i;
            var accumulated := if haveValue then value else 0;
            if accumulated >
               (Core.MaxColumn() - Core.DigitValue(text[i])) / 10 {
              FindDigitsEndEq(text, i);
              var end := Core.FindDigitsEnd(text, i);
              assert i < end by {
                reveal Core.FindDigitsEnd();
              }
              SyntaxDiagnosticsFromEq(
                text, end, true, start, accumulated
              );
            } else {
              SyntaxDiagnosticsFromEq(
                text, i + 1, true, start,
                accumulated * 10 + Core.DigitValue(text[i])
              );
            }
          }
        }
      }
    }
  }

  lemma SyntaxDiagnosticsEq(text: string)
    ensures Core.SyntaxDiagnostics(text) ==
            Spec.SyntaxDiagnostics(text)
  {
    SyntaxDiagnosticsFromEq(text, 0, false, 0, 0);
  }

  lemma MarkerScanSatisfies(
    part: string,
    i: nat,
    marker: Schema.MarkerKind,
    hasMarker: bool
  )
    requires i <= |part|
    ensures Spec.MarkerScanRelation(
              part, i, marker, hasMarker,
              Core.ScanMarkers(part, i, marker, hasMarker)
            )
    decreases |part| - i
  {
    if i < |part| {
      IsMarkerEq(part[i]);
      if Core.IsMarker(part[i]) {
        MarkerOfEq(part[i]);
        MarkerScanSatisfies(
          part, i + 1, Core.MarkerOf(part[i]), true
        );
      }
    }
  }

  lemma CommitTabValueSatisfies(
    acc: Schema.TabAccum,
    marker: Schema.MarkerKind,
    value: nat
  )
    ensures Spec.CommitTabValueRelation(
              acc, marker, value, Core.CommitTabValue(acc, marker, value)
            )
  {
  }

  lemma TabPartSatisfies(part: string, acc: Schema.TabAccum)
    ensures Spec.TabPartRelation(
              part, acc, Core.ParseTabPart(part, acc)
            )
  {
    if |part| > 0 {
      MarkerScanSatisfies(part, 0, Schema.MarkerNone, false);
      var scan := Core.ScanMarkers(
        part, 0, Schema.MarkerNone, false
      );
      if scan.index < |part| {
        var end := Core.FindDigitsEnd(part, scan.index);
        DigitsEndSatisfies(part, scan.index);
        if end < |part| {
          IsMarkerEq(part[end]);
          if Core.IsMarker(part[end]) {
            MarkerOfEq(part[end]);
          }
        } else {
          PositiveNatSatisfies(part[scan.index..end]);
          match Core.ParsePositiveNat(part[scan.index..end])
          case NatErr =>
          case NatOk(value) =>
            var marker := if scan.hasMarker then
              scan.marker else acc.activeMarker;
            CommitTabValueSatisfies(acc, marker, value);
        }
      }
    }
  }

  lemma TabTextSatisfies(
    text: string, start: nat, acc: Schema.TabAccum
  )
    requires start <= |text|
    ensures Spec.TabTextRelation(
              text, start, acc,
              Core.ParseTabTextFrom(text, start, acc)
            )
    decreases |text| - start
  {
    if start < |text| {
      IsSeparatorEq(text[start]);
      if Core.IsSeparator(text[start]) {
        TabTextSatisfies(text, start + 1, acc);
      } else {
        var end := Core.FindTokenEnd(text, start);
        TokenEndSatisfies(text, start);
        assert start < end <= |text|;
        TabPartSatisfies(text[start..end], acc);
        match Core.ParseTabPart(text[start..end], acc)
        case TabAccumErr(_) =>
        case TabAccumOk(next) =>
          TabTextSatisfies(text, end, next);
      }
    }
  }

  lemma TabArgsFromSatisfies(
    args: seq<Schema.TabArg>,
    i: nat,
    limit: int,
    acc: Schema.TabAccum
  )
    requires i <= |args|
    ensures Spec.TabArgsFromRelation(
              args, i, limit, acc,
              Core.ParseTabArgsFrom(args, i, limit, acc)
            )
    decreases |args| - i
  {
    if i < |args| &&
       !(limit >= 0 && args[i].tokenIndex >= limit) {
      var argAcc := Schema.TabAccum(
        acc.stops, acc.extendSize, acc.incrementSize,
        Schema.MarkerNone
      );
      SyntaxDiagnosticsEq(args[i].text);
      if Core.SyntaxDiagnostics(args[i].text) == "" {
        TabTextSatisfies(args[i].text, 0, argAcc);
        match Core.ParseTabTextFrom(args[i].text, 0, argAcc)
        case TabAccumErr(_) =>
        case TabAccumOk(next) =>
          TabArgsFromSatisfies(args, i + 1, limit, next);
      }
    }
  }

  lemma StopsValidationErrorEq(
    stops: seq<nat>, i: nat, previous: nat
  )
    requires i <= |stops|
    ensures Core.StopsValidationError(stops, i, previous) ==
            Spec.StopsValidationError(stops, i, previous)
    decreases |stops| - i
  {
    if i < |stops| && stops[i] != 0 && stops[i] > previous {
      StopsValidationErrorEq(stops, i + 1, stops[i]);
    }
  }

  lemma FinalizedTabsSatisfies(acc: Schema.TabAccum)
    ensures Spec.FinalizedTabsRelation(
              acc, Core.FinalizeTabAccum(acc)
            )
  {
    StopsValidationErrorEq(acc.stops, 0, 0);
  }

  lemma OptionScanSatisfies(raw: Schema.ExpandCmdRaw)
    ensures Spec.OptionScanRelation(
              raw, Core.ScanCommandOptions(raw)
            )
  {
    RequestTokenIndexEq(raw);
    var initial := Schema.TabAccum([], 0, 0, Schema.MarkerNone);
    TabArgsFromSatisfies(
      raw.tabArgs, 0, Core.RequestTokenIndex(raw), initial
    );
    match Core.ParseTabArgsFrom(
        raw.tabArgs, 0, Core.RequestTokenIndex(raw), initial
      )
    case TabAccumErr(_) =>
    case TabAccumOk(_) =>
      HelpBeforeOtherEq(raw);
      VersionBeforeInvalidEq(raw);
  }

  lemma InputsFromOperandsElement(
    operands: seq<string>, i: nat
  )
    requires i < |operands|
    ensures Core.InputsFromOperands(operands)[i] ==
            (if operands[i] == "-" then
               Schema.Stdin
             else
               Schema.File(operands[i]))
    decreases i
  {
    if i > 0 {
      InputsFromOperandsElement(operands[1..], i - 1);
    }
  }

  lemma InputsSatisfyRelation(operands: seq<string>)
    ensures Spec.InputsRelation(
              operands,
              if |Core.InputsFromOperands(operands)| == 0 then
                [Schema.Stdin]
              else
                Core.InputsFromOperands(operands)
            )
  {
    if |operands| > 0 {
      assert |Core.InputsFromOperands(operands)| == |operands| by {
        calc {
           |Core.InputsFromOperands(operands)|;
        == 1 + |Core.InputsFromOperands(operands[1..])|;
        == 1 + |operands[1..]|;
        == |operands|;
        }
      }
      forall i: nat | i < |operands|
        ensures Core.InputsFromOperands(operands)[i] ==
                (if operands[i] == "-" then
                   Schema.Stdin
                 else
                   Schema.File(operands[i]))
      {
        InputsFromOperandsElement(operands, i);
      }
    }
  }

  lemma CommandSatisfies(raw: Schema.ExpandCmdRaw)
    ensures Spec.CommandRelation(raw, Core.Command(raw))
  {
    OptionScanSatisfies(raw);
    match Core.ScanCommandOptions(raw)
    case ScanInvalidTabs(_) =>
    case ScanHelp =>
    case ScanVersion =>
    case ScanContinue(acc) =>
      FinalizedTabsSatisfies(acc);
      match Core.FinalizeTabAccum(acc)
      case TabErr(_) =>
      case TabOk(_) =>
        InputsSatisfyRelation(raw.operands);
  }

  lemma FixedWidthRelationHolds(width: nat, column: nat)
    ensures Spec.FixedWidthRelation(
              width, column, Core.NextFixedSpaces(width, column)
            )
  {
  }

  lemma IncrementalWidthRelationHolds(
    base: nat, width: nat, column: nat
  )
    ensures Spec.IncrementalWidthRelation(
              base, width, column,
              Core.NextIncrementalSpaces(base, width, column)
            )
  {
  }

  lemma FirstFutureStopRelation(
    stops: seq<nat>, column: nat
  )
    ensures Core.HasFutureStop(stops, column) ==>
              exists j: nat ::
                j < |stops| &&
                (forall k: nat :: k < j ==> stops[k] <= column) &&
                column < stops[j] &&
                Core.NextStopSpaces(stops, column) ==
                stops[j] - column
    ensures !Core.HasFutureStop(stops, column) ==>
              forall j: nat :: j < |stops| ==> stops[j] <= column
    decreases |stops|
  {
    if |stops| > 0 && column >= stops[0] {
      FirstFutureStopRelation(stops[1..], column);
      if Core.HasFutureStop(stops[1..], column) {
        ghost var j: nat :|
          j < |stops[1..]| &&
          (forall k: nat ::
             k < j ==> stops[1..][k] <= column) &&
          column < stops[1..][j] &&
          Core.NextStopSpaces(stops[1..], column) ==
          stops[1..][j] - column;
        assert forall k: nat :: k < j + 1 ==>
                                  stops[k] <= column by {
          forall k: nat | k < j + 1
            ensures stops[k] <= column
          {
            if k > 0 {
              assert stops[k] == stops[1..][k - 1];
            }
          }
        }
      } else {
        assert forall j: nat :: j < |stops| ==>
                                  stops[j] <= column by {
          forall j: nat | j < |stops|
            ensures stops[j] <= column
          {
            if j > 0 {
              assert stops[j] == stops[1..][j - 1];
            }
          }
        }
      }
    }
  }

  lemma TabStopRelationHolds(
    tabs: Schema.TabStops, column: nat
  )
    ensures Spec.TabStopRelation(
              tabs, column, Core.TabSpaces(tabs, column)
            )
  {
    match tabs
    case TabStops(stops, repeat) =>
      FirstFutureStopRelation(stops, column);
      if !Core.HasFutureStop(stops, column) {
        match repeat
        case RepeatNone =>
        case RepeatFixed(width) =>
          FixedWidthRelationHolds(width, column);
        case RepeatIncremental(width) =>
          if |stops| == 0 {
            FixedWidthRelationHolds(width, column);
          } else {
            IncrementalWidthRelationHolds(
              Core.LastStop(stops), width, column
            );
            LastStopEq(stops);
          }
      }
  }

  lemma SpacesRelationHolds(count: nat)
    ensures Spec.SpacePiece(Core.Spaces(count), count)
    decreases count
  {
    if count > 0 {
      SpacesRelationHolds(count - 1);
      assert forall i: nat :: i < |Core.Spaces(count)| ==>
                                Core.Spaces(count)[i] == ' ' by {
        forall i: nat | i < |Core.Spaces(count)|
          ensures Core.Spaces(count)[i] == ' '
        {
          if i > 0 {
            assert Core.Spaces(count)[i] ==
                   Core.Spaces(count - 1)[i - 1];
          }
        }
      }
    }
  }

  lemma JoinPiecesEq(pieces: seq<BenchWorld.Bytes>)
    ensures Core.JoinPieces(pieces) == Spec.JoinPieces(pieces)
    decreases |pieces|
  {
    if |pieces| > 0 {
      JoinPiecesEq(pieces[1..]);
    }
  }

  lemma ByteExpansionSummaryImpliesRelation(
    tabs: Schema.TabStops,
    initialOnly: bool,
    b: BenchWorld.RawByte,
    column: nat,
    leading: bool,
    piece: BenchWorld.Bytes,
    nextColumn: nat,
    nextLeading: bool
  )
    requires Core.ByteExpansionSummary(
               tabs, initialOnly, b, column, leading,
               piece, nextColumn, nextLeading
             )
    ensures Spec.ByteExpansionRelation(
              tabs, initialOnly, b, column, leading,
              piece, nextColumn, nextLeading
            )
  {
    reveal Core.ByteExpansionSummary();
    reveal Spec.ByteExpansionRelation();
    if !(initialOnly && !leading) && b == '\t' {
      var spaces := Core.TabSpaces(tabs, column);
      TabStopRelationHolds(tabs, column);
      SpacesRelationHolds(spaces);
    }
  }

  lemma DataExpansionWitnessSummaryImpliesRelation(
    tabs: Schema.TabStops,
    initialOnly: bool,
    data: BenchWorld.Bytes,
    column: nat,
    leading: bool,
    output: BenchWorld.Bytes,
    nextColumn: nat,
    nextLeading: bool,
    pieces: seq<BenchWorld.Bytes>,
    columns: seq<nat>,
    leadings: seq<bool>
  )
    requires Core.DataExpansionWitnessSummary(
               tabs, initialOnly, data, column, leading,
               output, nextColumn, nextLeading, pieces, columns, leadings
             )
    ensures Spec.DataExpansionWitnessRelation(
              tabs, initialOnly, data, column, leading,
              output, nextColumn, nextLeading, pieces, columns, leadings
            )
  {
    reveal Core.DataExpansionWitnessSummary();
    reveal Spec.DataExpansionWitnessRelation();
    forall i: nat | i < |data|
      ensures Spec.ByteExpansionRelation(
                tabs, initialOnly, data[i], columns[i], leadings[i],
                pieces[i], columns[i + 1], leadings[i + 1]
              )
    {
      ByteExpansionSummaryImpliesRelation(
        tabs, initialOnly, data[i], columns[i], leadings[i],
        pieces[i], columns[i + 1], leadings[i + 1]
      );
    }
    JoinPiecesEq(pieces);
  }

  lemma ReadStepSummaryImpliesRelation(
    input: Schema.Input,
    preFs: BenchWorld.FileSystem,
    stdinBefore: BenchWorld.Bytes,
    stdinAfter: BenchWorld.Bytes,
    result: BenchWorld.Result<BenchWorld.Bytes>
  )
    requires Core.ReadStepSummary(
               input, preFs, stdinBefore, stdinAfter, result
             )
    ensures Spec.ReadStepRelation(
              input, preFs, stdinBefore, stdinAfter, result
            )
  {
  }

  lemma InputPieceSummaryImpliesRelation(
    cmd: Schema.ExpandCmd,
    result: BenchWorld.Result<BenchWorld.Bytes>,
                              column: nat,
                              leading: bool,
                              output: BenchWorld.Bytes,
                              nextColumn: nat,
                              nextLeading: bool
  )
    requires Core.InputPieceSummary(
               cmd, result, column, leading,
               output, nextColumn, nextLeading
             )
    ensures Spec.InputPieceRelation(
              cmd, result, column, leading,
              output, nextColumn, nextLeading
            )
  {
    reveal Core.InputPieceSummary();
    reveal Spec.InputPieceRelation();
    match result
    case Ok(data) =>
      ghost var pieces: seq<BenchWorld.Bytes>,
                columns: seq<nat>, leadings: seq<bool> :|
        Core.DataExpansionWitnessSummary(
          cmd.tabs, cmd.initialOnly, data, column, leading,
          output, nextColumn, nextLeading,
          pieces, columns, leadings
        );
      DataExpansionWitnessSummaryImpliesRelation(
        cmd.tabs, cmd.initialOnly, data, column, leading,
        output, nextColumn, nextLeading,
        pieces, columns, leadings
      );
      reveal Spec.DataExpansionRelation();
    case Err(_) =>
  }

  lemma ErrorPieceSummaryImpliesRelation(
    input: Schema.Input,
    result: BenchWorld.Result<BenchWorld.Bytes>,
                              output: BenchWorld.Bytes,
                              hadError: bool
  )
    requires Core.ErrorPieceSummary(
               input, result, output, hadError
             )
    ensures Spec.ErrorPieceRelation(
              input, result, output, hadError
            )
  {
  }

  lemma InputTracePrefixSummaryImpliesRelation(
    cmd: Schema.ExpandCmd,
    preFs: BenchWorld.FileSystem,
    preStdin: BenchWorld.Bytes,
    count: nat,
    currentStdin: BenchWorld.Bytes,
    output: BenchWorld.Bytes,
    errorOutput: BenchWorld.Bytes,
    hadError: bool,
    results: seq<BenchWorld.Result<BenchWorld.Bytes>>,
    outputPieces: seq<BenchWorld.Bytes>,
    errorPieces: seq<BenchWorld.Bytes>,
    errorFlags: seq<bool>,
    columns: seq<nat>,
    leadings: seq<bool>,
    stdinStates: seq<BenchWorld.Bytes>
  )
    requires Core.InputTracePrefixSummary(
               cmd, preFs, preStdin, count, currentStdin,
               output, errorOutput, hadError, results, outputPieces,
               errorPieces, errorFlags, columns, leadings, stdinStates
             )
    ensures Spec.InputTracePrefixWitnessRelation(
              cmd, preFs, preStdin, count, currentStdin,
              output, errorOutput, hadError, results, outputPieces,
              errorPieces, errorFlags, columns, leadings, stdinStates
            )
  {
    reveal Core.InputTracePrefixSummary();
    reveal Spec.InputTracePrefixWitnessRelation();
    forall i: nat | i < count
      ensures Spec.ReadStepRelation(
                cmd.inputs[i], preFs,
                stdinStates[i], stdinStates[i + 1], results[i]
              ) &&
              Spec.InputPieceRelation(
                cmd, results[i], columns[i], leadings[i],
                outputPieces[i], columns[i + 1], leadings[i + 1]
              ) &&
              Spec.ErrorPieceRelation(
                cmd.inputs[i], results[i],
                errorPieces[i], errorFlags[i]
              )
    {
      ReadStepSummaryImpliesRelation(
        cmd.inputs[i], preFs,
        stdinStates[i], stdinStates[i + 1], results[i]
      );
      InputPieceSummaryImpliesRelation(
        cmd, results[i], columns[i], leadings[i],
        outputPieces[i], columns[i + 1], leadings[i + 1]
      );
      ErrorPieceSummaryImpliesRelation(
        cmd.inputs[i], results[i],
        errorPieces[i], errorFlags[i]
      );
    }
    JoinPiecesEq(outputPieces);
    JoinPiecesEq(errorPieces);
  }

  lemma InputTraceSummaryImpliesRelation(
    cmd: Schema.ExpandCmd,
    preFs: BenchWorld.FileSystem,
    preStdin: BenchWorld.Bytes,
    postStdin: BenchWorld.Bytes,
    output: BenchWorld.Bytes,
    errorOutput: BenchWorld.Bytes,
    hadError: bool
  )
    requires Core.InputTraceSummary(
               cmd, preFs, preStdin, postStdin,
               output, errorOutput, hadError
             )
    ensures Spec.InputTraceRelation(
              cmd, preFs, preStdin, postStdin,
              output, errorOutput, hadError
            )
  {
    reveal Core.InputTraceSummary();
    ghost var
      results: seq<BenchWorld.Result<BenchWorld.Bytes>>,
      outputPieces: seq<BenchWorld.Bytes>,
      errorPieces: seq<BenchWorld.Bytes>,
      errorFlags: seq<bool>,
      columns: seq<nat>,
      leadings: seq<bool>,
      stdinStates: seq<BenchWorld.Bytes> :|
      Core.InputTracePrefixSummary(
        cmd, preFs, preStdin, |cmd.inputs|, postStdin,
        output, errorOutput, hadError, results, outputPieces,
        errorPieces, errorFlags, columns, leadings, stdinStates
      );
    InputTracePrefixSummaryImpliesRelation(
      cmd, preFs, preStdin, |cmd.inputs|, postStdin,
      output, errorOutput, hadError, results, outputPieces,
      errorPieces, errorFlags, columns, leadings, stdinStates
    );
    reveal Spec.InputTraceWitnessRelation();
    assert Spec.InputTraceWitnessRelation(
        cmd, preFs, preStdin, postStdin,
        output, errorOutput, hadError, results, outputPieces,
        errorPieces, errorFlags, columns, leadings, stdinStates
      );
    reveal Spec.InputTraceRelation();
    assert exists
        traceResults: seq<BenchWorld.Result<BenchWorld.Bytes>>,
        traceOutputPieces: seq<BenchWorld.Bytes>,
        traceErrorPieces: seq<BenchWorld.Bytes>,
        traceErrorFlags: seq<bool>,
        traceColumns: seq<nat>,
        traceLeadings: seq<bool>,
        traceStdinStates: seq<BenchWorld.Bytes> ::
        Spec.InputTraceWitnessRelation(
          cmd, preFs, preStdin, postStdin,
          output, errorOutput, hadError, traceResults,
          traceOutputPieces, traceErrorPieces, traceErrorFlags,
          traceColumns, traceLeadings, traceStdinStates
        );
  }

  twostate lemma CoreSummaryImpliesSpec(
    raw: Schema.ExpandCmdRaw, io: BenchIO.IO, exit: int
  )
    requires Core.CoreSummary(raw, io, exit)
    ensures Spec.Spec(raw, io, exit)
  {
    CommandSatisfies(raw);
    reveal Core.CoreSummary();
    reveal Spec.Spec();
    var cmd := Core.Command(raw);
    if cmd.mode != Schema.ModeHelp &&
       cmd.mode != Schema.ModeVersion &&
       cmd.mode != Schema.ModeInvalidTabs {
      ghost var output: BenchWorld.Bytes,
                errorOutput: BenchWorld.Bytes, hadError: bool :|
        Core.InputTraceSummary(
          cmd, old(io.fs()), old(io.stdin()), io.stdin(),
          output, errorOutput, hadError
        ) &&
        io.stdout() == old(io.stdout()) + output &&
        io.stderr() == old(io.stderr()) + errorOutput &&
        exit == (if hadError then 1 else 0);
      InputTraceSummaryImpliesRelation(
        cmd, old(io.fs()), old(io.stdin()), io.stdin(),
        output, errorOutput, hadError
      );
    }
  }
}
