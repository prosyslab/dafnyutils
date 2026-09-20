include "../../core/Utf8.dfy"
include "../../core/World.dfy"
include "../../core/CliTypes.dfy"

module CutSchema {
  import Utf8 = Utf8Semantics
  import BenchWorld
  import CliTypes

  datatype CutMode = ModeRun | ModeHelp | ModeVersion
  datatype SelectionKind = SelectBytes | SelectChars
  datatype Input = Stdin | File(path: BenchWorld.Path)
  datatype Range = Range(first: int, last: int, openEnd: bool)
  datatype Selection = Selection(kind: SelectionKind, ranges: seq<Range>, complement: bool)
  datatype OutputDelimiter = OutputDefault | OutputCustom(text: string)
  datatype CutCmdRaw = CutCmdRaw(
    mode: CutMode,
    selection: Selection,
    outputDelimiter: OutputDelimiter,
    zeroTerminated: bool,
    inputs: seq<Input>
  )

  datatype NumberParseResult = NumberOk(value: int) | NumberErr
  datatype RangeParseError =
    | FromOneError
    | InvalidRangeError
    | InvalidPositionError(text: string)
    | NoEndpointError
    | DecreasingRangeError
  datatype RangeParseResult = RangeOk(range: Range) | RangeErr(error: RangeParseError)
  datatype RangeListParseResult = RangeListOk(ranges: seq<Range>) | RangeListErr(error: RangeParseError)
  datatype PlanError =
    | MissingListError
    | OnlyOneListError
    | SelectionError(error: RangeParseError)
  datatype ParsedPlan = ParsedRun(raw: CutCmdRaw) | ParsedError(error: PlanError)

  method Schema() returns (s: CliTypes.CliSchema)
  {
    s := CliTypes.CliSchema(
      [
        CliTypes.OptionDecl("cut.bytes", ['b'], ["bytes"], CliTypes.ReqArg),
        CliTypes.OptionDecl("cut.characters", ['c'], ["characters"], CliTypes.ReqArg),
        CliTypes.OptionDecl("cut.complement", [], ["complement"], CliTypes.NoArg),
        CliTypes.OptionDecl("cut.no_split", ['n'], [], CliTypes.NoArg),
        CliTypes.OptionDecl("cut.output_delimiter", [], ["output-delimiter"], CliTypes.ReqArg),
        CliTypes.OptionDecl("cut.zero_terminated", ['z'], ["zero-terminated"], CliTypes.NoArg),
        CliTypes.OptionDecl("cut.help", [], ["help"], CliTypes.NoArg),
        CliTypes.OptionDecl("cut.version", [], ["version"], CliTypes.NoArg)
      ],
      true
    );
  }

  method ParserConfig() returns (cfg: CliTypes.ParseConfig)
  {
    cfg := CliTypes.ParseConfig(CliTypes.GNU_Permute, true, true, true);
  }

  function IsDigit(ch: char): bool
  {
    '0' <= ch <= '9'
  }

  function DigitValue(ch: char): int
  {
    (ch as int) - ('0' as int)
  }

  method ParsePositiveInt(text: string) returns (res: NumberParseResult)
  {
    if |text| == 0 {
      res := NumberErr;
      return;
    }

    var value := 0;
    var i := 0;
    while i < |text|
      invariant 0 <= i <= |text|
      invariant 0 <= value
      decreases |text| - i
    {
      if !IsDigit(text[i]) {
        res := NumberErr;
        return;
      }
      value := value * 10 + DigitValue(text[i]);
      i := i + 1;
    }

    if value <= 0 {
      res := NumberErr;
    } else {
      res := NumberOk(value);
    }
  }

  method FindChar(text: string, start: nat, target: char) returns (idx: nat)
    requires start <= |text|
    ensures start <= idx <= |text|
    ensures idx < |text| ==> text[idx] == target
  {
    idx := start;
    while idx < |text| && text[idx] != target
      invariant start <= idx <= |text|
      decreases |text| - idx
    {
      idx := idx + 1;
    }
  }

  method FirstNonDigit(text: string) returns (idx: nat)
    ensures idx <= |text|
    ensures idx < |text| ==> !IsDigit(text[idx])
  {
    idx := 0;
    while idx < |text| && IsDigit(text[idx])
      invariant idx <= |text|
      decreases |text| - idx
    {
      idx := idx + 1;
    }
  }

  method PositionParseError(fragment: string, diagnosticSuffix: string)
    returns (error: RangeParseError)
    requires |fragment| <= |diagnosticSuffix|
  {
    var invalid := FirstNonDigit(fragment);
    if invalid < |fragment| {
      error := InvalidPositionError(diagnosticSuffix[invalid..]);
    } else {
      error := FromOneError;
    }
  }

  method ParseRangeElement(text: string, diagnosticSuffix: string) returns (res: RangeParseResult)
    requires |text| <= |diagnosticSuffix|
  {
    if |text| == 0 {
      res := RangeErr(InvalidRangeError);
      return;
    }

    var dash := FindChar(text, 0, '-');
    assert dash <= |text|;
    if !(dash < |text|) {
      var n := ParsePositiveInt(text);
      match n {
        case NumberOk(value) =>
          res := RangeOk(Range(value, value, false));
        case NumberErr =>
          var error := PositionParseError(text, diagnosticSuffix);
          res := RangeErr(error);
      }
      return;
    }

    assert dash < |text|;
    assert dash + 1 <= |text|;
    var secondDash := FindChar(text, dash + 1, '-');

    if |text| == 1 {
      res := RangeErr(NoEndpointError);
      return;
    }

    if dash == 0 {
      if secondDash < |text| {
        if secondDash == 1 {
          res := RangeErr(InvalidRangeError);
        } else {
          var upperPrefix := text[1..secondDash];
          var upperPrefixNumber := ParsePositiveInt(upperPrefix);
          match upperPrefixNumber
          case NumberOk(_) =>
            res := RangeErr(InvalidRangeError);
          case NumberErr =>
            var error := PositionParseError(upperPrefix, diagnosticSuffix[1..]);
            res := RangeErr(error);
        }
        return;
      }

      var upper := ParsePositiveInt(text[1..]);
      match upper {
        case NumberOk(last) =>
          res := RangeOk(Range(1, last, false));
        case NumberErr =>
          var error := PositionParseError(text[1..], diagnosticSuffix[1..]);
          res := RangeErr(error);
      }
      return;
    }

    var lower := ParsePositiveInt(text[..dash]);
    match lower
    case NumberErr =>
      var error := PositionParseError(text[..dash], diagnosticSuffix);
      res := RangeErr(error);
    case NumberOk(first) =>
      if dash + 1 == |text| {
        res := RangeOk(Range(first, first, true));
      } else if secondDash < |text| {
        if secondDash == dash + 1 {
          res := RangeErr(InvalidRangeError);
        } else {
          var upperPrefix := text[dash + 1..secondDash];
          var upperPrefixNumber := ParsePositiveInt(upperPrefix);
          match upperPrefixNumber
          case NumberOk(_) =>
            res := RangeErr(InvalidRangeError);
          case NumberErr =>
            var error := PositionParseError(
              upperPrefix,
              diagnosticSuffix[dash + 1..]
            );
            res := RangeErr(error);
        }
      } else {
        var upper := ParsePositiveInt(text[dash + 1..]);
        match upper
        case NumberErr =>
          var error := PositionParseError(
            text[dash + 1..],
            diagnosticSuffix[dash + 1..]
          );
          res := RangeErr(error);
        case NumberOk(last) =>
          if last < first {
            res := RangeErr(DecreasingRangeError);
          } else {
            res := RangeOk(Range(first, last, false));
          }
      }
  }

  method ParseRangeListFrom(text: string, start: nat, acc: seq<Range>)
    returns (res: RangeListParseResult)
    requires start <= |text|
    decreases |text| - start
  {
    if start == |text| {
      res := RangeListErr(InvalidRangeError);
      return;
    }

    var comma := FindChar(text, start, ',');
    var parsed := ParseRangeElement(text[start..comma], text[start..]);
    match parsed
    case RangeErr(error) =>
      res := RangeListErr(error);
    case RangeOk(range) =>
      var nextAcc := acc + [range];
      if comma == |text| {
        res := RangeListOk(nextAcc);
      } else {
        res := ParseRangeListFrom(text, comma + 1, nextAcc);
      }
  }

  method ParseRangeList(text: string) returns (res: RangeListParseResult)
  {
    if |text| == 0 {
      res := RangeListErr(FromOneError);
    } else {
      res := ParseRangeListFrom(text, 0, []);
    }
  }

  method InputsFromOperands(operands: seq<string>) returns (inputs: seq<Input>)
    decreases |operands|
  {
    if |operands| == 0 {
      inputs := [];
    } else {
      var head := if operands[0] == "-" then Stdin else File(operands[0]);
      var tail := InputsFromOperands(operands[1..]);
      inputs := [head] + tail;
    }
  }

  method DefaultSelection() returns (selection: Selection)
  {
    selection := Selection(SelectBytes, [Range(1, 1, false)], false);
  }

  method Decode(p: CliTypes.ParsedArgs) returns (raw: CutCmdRaw)
  {
    var selection := DefaultSelection();
    raw := CutCmdRaw(ModeRun, selection, OutputDefault, false, [Stdin]);
  }

  method PlanParsed(p: CliTypes.ParsedArgs) returns (plan: ParsedPlan)
    decreases *
  {
    var seenHelp := false;
    var seenVersion := false;
    var helpTokenIndex := -1;
    var versionTokenIndex := -1;
    var listCount := 0;
    var kind := SelectBytes;
    var listText := "";
    var complement := false;
    var outputDelimiter := OutputDefault;
    var zeroTerminated := false;

    var i := 0;
    while i < |p.options|
      invariant 0 <= i <= |p.options|
      invariant 0 <= listCount
      decreases |p.options| - i
    {
      var occ := p.options[i];
      if occ.key == "cut.help" {
        seenHelp := true;
        if helpTokenIndex == -1 || occ.tokenIndex < helpTokenIndex {
          helpTokenIndex := occ.tokenIndex;
        }
      } else if occ.key == "cut.version" {
        seenVersion := true;
        if versionTokenIndex == -1 || occ.tokenIndex < versionTokenIndex {
          versionTokenIndex := occ.tokenIndex;
        }
      } else if occ.key == "cut.bytes" || occ.key == "cut.characters" {
        listCount := listCount + 1;
        kind := if occ.key == "cut.characters" then SelectChars else SelectBytes;
        match occ.value
        case Some(value) =>
          listText := value;
        case None =>
          listText := "";
      } else if occ.key == "cut.complement" {
        complement := true;
      } else if occ.key == "cut.output_delimiter" {
        match occ.value
        case Some(value) =>
          outputDelimiter := OutputCustom(value);
        case None =>
          outputDelimiter := OutputCustom("");
      } else if occ.key == "cut.zero_terminated" {
        zeroTerminated := true;
      }
      i := i + 1;
    }

    var operands := InputsFromOperands(p.positionals);

    if seenHelp && (!seenVersion || helpTokenIndex <= versionTokenIndex) {
      var selection := DefaultSelection();
      plan := ParsedRun(CutCmdRaw(ModeHelp, selection, OutputDefault, false, operands));
      return;
    }

    if seenVersion {
      var selection := DefaultSelection();
      plan := ParsedRun(CutCmdRaw(ModeVersion, selection, OutputDefault, false, operands));
      return;
    }

    if listCount == 0 {
      plan := ParsedError(MissingListError);
      return;
    }

    if listCount > 1 {
      plan := ParsedError(OnlyOneListError);
      return;
    }

    var parsedRanges := ParseRangeList(listText);
    match parsedRanges
    case RangeListErr(error) =>
      plan := ParsedError(SelectionError(error));
    case RangeListOk(ranges) =>
      var runInputs := if |operands| == 0 then [Stdin] else operands;
      plan := ParsedRun(CutCmdRaw(
                          ModeRun,
                          Selection(kind, ranges, complement),
                          outputDelimiter,
                          zeroTerminated,
                          runInputs
                        ));
  }

  function TryHelpText(): string
  {
    "Try 'cut --help' for more information.\n"
  }

  function ParseErrorText(e: CliTypes.ParseError): string
  {
    if e.kind == CliTypes.UnknownOption || e.kind == CliTypes.UnexpectedValue then
      if |e.rawToken| > 2 && e.rawToken[0] == '-' && e.rawToken[1] == '-' then
        "cut: unrecognized option '" + e.rawToken + "'\n" + TryHelpText()
      else if |e.rawToken| > 1 && e.rawToken[0] == '-' then
        "cut: invalid option -- '" + [e.rawToken[1]] + "'\n" + TryHelpText()
      else
        "cut: invalid option\n" + TryHelpText()
    else if e.kind == CliTypes.MissingValue then
      if |e.rawToken| > 2 && e.rawToken[0] == '-' && e.rawToken[1] == '-' then
        "cut: option '" + e.rawToken + "' requires an argument\n" + TryHelpText()
      else if |e.rawToken| > 1 && e.rawToken[0] == '-' then
        "cut: option requires an argument -- '" + [e.rawToken[1]] + "'\n" + TryHelpText()
      else
        "cut: option requires an argument\n" + TryHelpText()
    else
      "cut: option '" + e.rawToken + "' is ambiguous\n" + TryHelpText()
  }

  function RangeErrorText(error: RangeParseError): string
  {
    match error
    case FromOneError =>
      "cut: byte/character positions are numbered from 1\n" + TryHelpText()
    case InvalidRangeError =>
      "cut: invalid byte or character range\n" + TryHelpText()
    case InvalidPositionError(text) =>
      "cut: invalid byte/character position '" + text + "'\n" + TryHelpText()
    case NoEndpointError =>
      "cut: invalid range with no endpoint: -\n" + TryHelpText()
    case DecreasingRangeError =>
      "cut: invalid decreasing range\n" + TryHelpText()
  }

  function PlanErrorText(error: PlanError): string
  {
    match error
    case MissingListError =>
      "cut: you must specify a list of bytes, characters, or fields\n" + TryHelpText()
    case OnlyOneListError =>
      "cut: only one list may be specified\n" + TryHelpText()
    case SelectionError(rangeError) =>
      RangeErrorText(rangeError)
  }

  method ParseErrorMessage(e: CliTypes.ParseError) returns (message: BenchWorld.Bytes)
  {
    message := Utf8.Encode(ParseErrorText(e));
  }

  method PlanErrorMessage(error: PlanError) returns (message: BenchWorld.Bytes)
  {
    message := Utf8.Encode(PlanErrorText(error));
  }
}
