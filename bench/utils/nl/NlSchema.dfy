include "../../core/Utf8.dfy"
include "../../core/World.dfy"
include "../../core/CliTypes.dfy"

module NlSchema {
  import Utf8 = Utf8Semantics
  import BenchWorld
  import CliTypes

  datatype NlMode =
    | ModeRun
    | ModeHelp
    | ModeVersion
    | ModeInvalidBodyStyle(value: string)
    | ModeUnsupportedRegexBodyStyle(value: string)
    | ModeInvalidNumberFormat(value: string)

  datatype BodyStyle = NumberAll | NumberNonEmpty | NumberNone
  datatype NumberFormat = FormatLeft | FormatRight | FormatRightZero
  datatype Input = Stdin | File(path: BenchWorld.Path)

  datatype NlCmdRaw = NlCmdRaw(
    bodyStyle: CliTypes.OptionalString,
    numberFormat: CliTypes.OptionalString,
    separator: CliTypes.OptionalString,
    seenHelp: bool,
    seenVersion: bool,
    helpTokenIndex: int,
    versionTokenIndex: int,
    operands: seq<string>
  )

  datatype NlCmd = NlCmd(
    mode: NlMode,
    bodyStyle: BodyStyle,
    numberFormat: NumberFormat,
    separator: string,
    inputs: seq<Input>
  )

  function InputsFromOperands(operands: seq<string>): seq<Input>
    decreases |operands|
  {
    if |operands| == 0 then
      []
    else
      [(if operands[0] == "-" then Stdin else File(operands[0]))] +
      InputsFromOperands(operands[1..])
  }

  function BodyStyleMode(opt: CliTypes.OptionalString): NlMode
  {
    match opt
    case None => ModeRun
    case Some(value) =>
      if |value| == 0 then
        ModeInvalidBodyStyle(value)
      else if value[0] == 'p' then
        ModeUnsupportedRegexBodyStyle(value)
      else if value[0] == 'a' || value[0] == 't' || value[0] == 'n' then
        ModeRun
      else
        ModeInvalidBodyStyle(value)
  }

  function BodyStyleValue(opt: CliTypes.OptionalString): BodyStyle
  {
    match opt
    case Some(value) =>
      if |value| > 0 && value[0] == 'a' then
        NumberAll
      else if |value| > 0 && value[0] == 'n' then
        NumberNone
      else
        NumberNonEmpty
    case None => NumberNonEmpty
  }

  function NumberFormatMode(opt: CliTypes.OptionalString): NlMode
  {
    match opt
    case None => ModeRun
    case Some(value) =>
      if value == "ln" || value == "rn" || value == "rz" then
        ModeRun
      else
        ModeInvalidNumberFormat(value)
  }

  function NumberFormatValue(opt: CliTypes.OptionalString): NumberFormat
  {
    match opt
    case Some(value) =>
      if value == "ln" then
        FormatLeft
      else if value == "rz" then
        FormatRightZero
      else
        FormatRight
    case None => FormatRight
  }

  function SeparatorValue(opt: CliTypes.OptionalString): string
  {
    match opt
    case Some(value) => value
    case None => "\t"
  }

  function Command(raw: NlCmdRaw): NlCmd
  {
    var specialMode :=
      if raw.seenHelp && (!raw.seenVersion || raw.helpTokenIndex <= raw.versionTokenIndex) then
        ModeHelp
      else if raw.seenVersion then
        ModeVersion
      else
        ModeRun;
    var bodyMode := BodyStyleMode(raw.bodyStyle);
    var formatMode := NumberFormatMode(raw.numberFormat);
    var mode :=
      if specialMode != ModeRun then
        specialMode
      else if bodyMode != ModeRun then
        bodyMode
      else if formatMode != ModeRun then
        formatMode
      else
        ModeRun;
    var inputs := InputsFromOperands(raw.operands);
    var runInputs := if mode == ModeRun && |inputs| == 0 then [Stdin] else inputs;
    NlCmd(
      mode,
      BodyStyleValue(raw.bodyStyle),
      NumberFormatValue(raw.numberFormat),
      SeparatorValue(raw.separator),
      runInputs
    )
  }

  method Schema() returns (s: CliTypes.CliSchema)
  {
    s := CliTypes.CliSchema(
      [
        CliTypes.OptionDecl("nl.body_numbering", ['b'], ["body-numbering"], CliTypes.ReqArg),
        CliTypes.OptionDecl("nl.number_format", ['n'], ["number-format"], CliTypes.ReqArg),
        CliTypes.OptionDecl("nl.number_separator", ['s'], ["number-separator"], CliTypes.ReqArg),
        CliTypes.OptionDecl("nl.help", [], ["help"], CliTypes.NoArg),
        CliTypes.OptionDecl("nl.version", [], ["version"], CliTypes.NoArg)
      ],
      true
    );
  }

  method ParserConfig() returns (cfg: CliTypes.ParseConfig)
  {
    cfg := CliTypes.ParseConfig(CliTypes.GNU_Permute, true, true, true);
  }

  method Decode(p: CliTypes.ParsedArgs) returns (raw: NlCmdRaw)
  {
    var bodyStyle: CliTypes.OptionalString := CliTypes.None;
    var numberFormat: CliTypes.OptionalString := CliTypes.None;
    var separator: CliTypes.OptionalString := CliTypes.None;
    var seenHelp := false;
    var seenVersion := false;
    var helpTokenIndex := -1;
    var versionTokenIndex := -1;

    var i := 0;
    while i < |p.options|
      decreases |p.options| - i
    {
      var occ := p.options[i];
      if occ.key == "nl.body_numbering" {
        bodyStyle := occ.value;
      }
      if occ.key == "nl.number_format" {
        numberFormat := occ.value;
      }
      if occ.key == "nl.number_separator" {
        separator := occ.value;
      }
      if occ.key == "nl.help" {
        seenHelp := true;
        if helpTokenIndex == -1 || occ.tokenIndex < helpTokenIndex {
          helpTokenIndex := occ.tokenIndex;
        }
      }
      if occ.key == "nl.version" {
        seenVersion := true;
        if versionTokenIndex == -1 || occ.tokenIndex < versionTokenIndex {
          versionTokenIndex := occ.tokenIndex;
        }
      }
      i := i + 1;
    }

    raw := NlCmdRaw(
      bodyStyle,
      numberFormat,
      separator,
      seenHelp,
      seenVersion,
      helpTokenIndex,
      versionTokenIndex,
      p.positionals
    );
  }

  function ParseErrorText(e: CliTypes.ParseError): string
  {
    if e.kind == CliTypes.UnknownOption then
      if |e.rawToken| > 2 && e.rawToken[0] == '-' && e.rawToken[1] == '-' then
        "nl: unrecognized option '" + e.rawToken + "'\n" + TryHelp()
      else if |e.rawToken| > 1 && e.rawToken[0] == '-' then
        var option: string := [e.rawToken[1]];
        "nl: invalid option -- '" + option + "'\n" + TryHelp()
      else
        "nl: invalid option\n" + TryHelp()
    else if e.kind == CliTypes.MissingValue then
      if |e.rawToken| > 2 && e.rawToken[0] == '-' && e.rawToken[1] == '-' then
        "nl: option '" + e.rawToken + "' requires an argument\n" + TryHelp()
      else if |e.rawToken| > 1 && e.rawToken[0] == '-' then
        var option: string := [e.rawToken[|e.rawToken| - 1]];
        "nl: option requires an argument -- '" + option + "'\n" + TryHelp()
      else
        "nl: option requires an argument\n" + TryHelp()
    else if e.kind == CliTypes.Ambiguous then
      "nl: option '" + e.rawToken + "' is ambiguous\n" + TryHelp()
    else if e.kind == CliTypes.UnexpectedValue then
      "nl: option '" + e.rawToken + "' doesn't allow an argument\n" + TryHelp()
    else
      "nl: parse error at token '" + e.rawToken + "'\n"
  }

  function TryHelp(): BenchWorld.Bytes
  {
    "Try 'nl --help' for more information.\n"
  }

  method FormatParseError(e: CliTypes.ParseError) returns (b: BenchWorld.Bytes)
  {
    b := Utf8.Encode(ParseErrorText(e));
  }

  method PlanParseFailure(
    e: CliTypes.ParseError,
    argv: seq<string>
  ) returns (plan: CliTypes.CliPlan<NlCmdRaw>)
    decreases *
  {
    var msg := FormatParseError(e);
    plan := CliTypes.CliEarlyExit(1, [], msg);
  }
}
