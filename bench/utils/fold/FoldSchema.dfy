include "../../core/Utf8.dfy"
include "../../core/World.dfy"
include "../../core/CliTypes.dfy"

module FoldSchema {
  import Utf8 = Utf8Semantics
  import BenchWorld
  import CliTypes

  datatype FoldMode = ModeRun | ModeHelp | ModeVersion | ModeInvalidWidth
  datatype Input = Stdin | File(path: BenchWorld.Path)
  datatype WidthArg = WidthArg(text: string, tokenIndex: int)
  datatype NatParse = NatOk(value: nat) | NatErr
  datatype WidthParse = WidthParse(
    hasInvalid: bool,
    invalidText: string,
    invalidTokenIndex: int,
    width: nat
  )

  datatype FoldCmdRaw = FoldCmdRaw(
    widthArgs: seq<WidthArg>,
    byteMode: bool,
    spaceMode: bool,
    seenHelp: bool,
    seenVersion: bool,
    helpTokenIndex: int,
    versionTokenIndex: int,
    operands: seq<string>
  )

  datatype FoldCmd = FoldCmd(
    mode: FoldMode,
    width: nat,
    invalidWidthValue: string,
    byteMode: bool,
    spaceMode: bool,
    inputs: seq<Input>
  )

  datatype FoldParseFailurePlan =
    | FoldRun(raw: FoldCmdRaw)
    | FoldParseError(error: CliTypes.ParseError)

  method Schema() returns (s: CliTypes.CliSchema)
  {
    s := CliTypes.CliSchema(
      [
        CliTypes.OptionDecl("fold.bytes", ['b'], ["bytes"], CliTypes.NoArg),
        CliTypes.OptionDecl("fold.spaces", ['s'], ["spaces"], CliTypes.NoArg),
        CliTypes.OptionDecl("fold.width", ['w'], ["width"], CliTypes.ReqArg),
        CliTypes.OptionDecl("fold.help", [], ["help"], CliTypes.NoArg),
        CliTypes.OptionDecl("fold.version", [], ["version"], CliTypes.NoArg)
      ],
      true
    );
  }

  method ParserConfig() returns (cfg: CliTypes.ParseConfig)
  {
    cfg := CliTypes.ParseConfig(CliTypes.GNU_Permute, true, true, true);
  }

  method PlanParseFailure(
    e: CliTypes.ParseError,
    argv: seq<string>
  ) returns (plan: FoldParseFailurePlan)
    decreases *
  {
    var seenHelp := false;
    var seenVersion := false;
    var helpTokenIndex := -1;
    var versionTokenIndex := -1;
    var widthArgs: seq<WidthArg> := [];

    var i := 0;
    while i < |argv| && i < e.tokenIndex
      decreases |argv| - i
    {
      var token := argv[i];
      var consumedNext := false;
      if token == "--help" {
        seenHelp := true;
        if helpTokenIndex == -1 {
          helpTokenIndex := i;
        }
      } else if token == "--version" {
        seenVersion := true;
        if versionTokenIndex == -1 {
          versionTokenIndex := i;
        }
      } else if token == "-w" || token == "--width" {
        if i + 1 < |argv| && i + 1 < e.tokenIndex {
          widthArgs := widthArgs + [WidthArg(argv[i + 1], i)];
          consumedNext := true;
        }
      } else if 8 <= |token| && token[..8] == "--width=" {
        widthArgs := widthArgs + [WidthArg(token[8..], i)];
      } else if |token| > 2 && token[0] == '-' && token[1] == 'w' {
        widthArgs := widthArgs + [WidthArg(token[2..], i)];
      }

      if consumedNext {
        i := i + 2;
      } else {
        i := i + 1;
      }
    }

    var invalidTokenIndex := -1;
    var j := 0;
    while j < |widthArgs|
      decreases |widthArgs| - j
    {
      if invalidTokenIndex == -1 {
        var ok := WidthTextIsPositiveDecimal(widthArgs[j].text);
        if !ok {
          invalidTokenIndex := widthArgs[j].tokenIndex;
        }
      }
      j := j + 1;
    }

    if seenHelp &&
       (!seenVersion || helpTokenIndex <= versionTokenIndex) &&
       (invalidTokenIndex == -1 || helpTokenIndex <= invalidTokenIndex) {
      plan := FoldRun(FoldCmdRaw(
                        widthArgs, false, false, true, seenVersion,
                        helpTokenIndex, versionTokenIndex, []
                      ));
      return;
    }

    if seenVersion &&
       (invalidTokenIndex == -1 || versionTokenIndex <= invalidTokenIndex) {
      plan := FoldRun(FoldCmdRaw(
                        widthArgs, false, false, seenHelp, true,
                        helpTokenIndex, versionTokenIndex, []
                      ));
      return;
    }

    if invalidTokenIndex != -1 {
      plan := FoldRun(FoldCmdRaw(
                        widthArgs, false, false, false, false, -1, -1, []
                      ));
      return;
    }

    plan := FoldParseError(e);
  }

  method WidthTextIsPositiveDecimal(text: string) returns (ok: bool)
  {
    if |text| == 0 {
      ok := false;
      return;
    }
    ok := true;
    var sawNonZero := false;
    var i := 0;
    while i < |text|
      decreases |text| - i
    {
      if !('0' <= text[i] <= '9') {
        ok := false;
        return;
      }
      if text[i] != '0' {
        sawNonZero := true;
      }
      i := i + 1;
    }
    if !sawNonZero {
      ok := false;
    }
  }

  method Decode(p: CliTypes.ParsedArgs) returns (raw: FoldCmdRaw)
  {
    var widthArgs: seq<WidthArg> := [];
    var byteMode := false;
    var spaceMode := false;
    var seenHelp := false;
    var seenVersion := false;
    var helpTokenIndex := -1;
    var versionTokenIndex := -1;

    var i := 0;
    while i < |p.options|
      decreases |p.options| - i
    {
      var occ := p.options[i];
      if occ.key == "fold.width" {
        match occ.value
        case Some(value) =>
          widthArgs := widthArgs + [WidthArg(value, occ.tokenIndex)];
        case None =>
      }
      if occ.key == "fold.bytes" {
        byteMode := true;
      }
      if occ.key == "fold.spaces" {
        spaceMode := true;
      }
      if occ.key == "fold.help" {
        seenHelp := true;
        if helpTokenIndex == -1 || occ.tokenIndex < helpTokenIndex {
          helpTokenIndex := occ.tokenIndex;
        }
      }
      if occ.key == "fold.version" {
        seenVersion := true;
        if versionTokenIndex == -1 || occ.tokenIndex < versionTokenIndex {
          versionTokenIndex := occ.tokenIndex;
        }
      }
      i := i + 1;
    }

    raw := FoldCmdRaw(widthArgs, byteMode, spaceMode, seenHelp, seenVersion, helpTokenIndex, versionTokenIndex, p.positionals);
  }

  function TryHelpText(): string
  {
    "Try 'fold --help' for more information.\n"
  }

  function ParseErrorText(e: CliTypes.ParseError): string
  {
    if e.kind == CliTypes.UnknownOption || e.kind == CliTypes.UnexpectedValue then
      if |e.rawToken| > 2 && e.rawToken[0] == '-' && e.rawToken[1] == '-' then
        "fold: unrecognized option '" + e.rawToken + "'\n" + TryHelpText()
      else if |e.rawToken| > 1 && e.rawToken[0] == '-' then
        "fold: invalid option -- '" + [e.rawToken[1]] + "'\n" + TryHelpText()
      else
        "fold: invalid option\n" + TryHelpText()
    else if e.kind == CliTypes.MissingValue then
      if |e.rawToken| > 2 && e.rawToken[0] == '-' && e.rawToken[1] == '-' then
        "fold: option '" + e.rawToken + "' requires an argument\n" + TryHelpText()
      else if |e.rawToken| > 1 && e.rawToken[0] == '-' then
        "fold: option requires an argument -- '" + [e.rawToken[1]] + "'\n" + TryHelpText()
      else
        "fold: option requires an argument\n" + TryHelpText()
    else if e.kind == CliTypes.Ambiguous then
      "fold: option '" + e.rawToken + "' is ambiguous\n" + TryHelpText()
    else
      "fold: parse error at token '" + e.rawToken + "'\n"
  }

  method FormatParseError(e: CliTypes.ParseError) returns (b: BenchWorld.Bytes)
  {
    b := Utf8.Encode(ParseErrorText(e));
  }

  method PlanError(
    e: CliTypes.ParseError
  ) returns (plan: CliTypes.CliPlan<FoldCmdRaw>)
  {
    var msg := FormatParseError(e);
    plan := CliTypes.CliEarlyExit(1, [], msg);
  }
}
