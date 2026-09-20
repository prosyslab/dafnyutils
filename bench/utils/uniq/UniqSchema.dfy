include "../../core/Utf8.dfy"
include "../../core/World.dfy"
include "../../core/CliTypes.dfy"

module UniqSchema {
  import Utf8 = Utf8Semantics
  import BenchWorld
  import CliTypes

  datatype UniqMode =
    | ModeRun
    | ModeHelp
    | ModeVersion
    | ModeUnsupportedOutput(output: string)
    | ModeUnsupportedSkipChars(operand: string)
    | ModeExtraOperand(operand: string)

  datatype Input = Stdin | File(path: BenchWorld.Path)

  datatype UniqCmdRaw = UniqCmdRaw(
    seenCount: bool,
    seenRepeated: bool,
    seenUnique: bool,
    seenIgnoreCase: bool,
    seenHelp: bool,
    seenVersion: bool,
    helpTokenIndex: int,
    versionTokenIndex: int,
    operands: seq<string>
  )

  datatype UniqCmd = UniqCmd(
    mode: UniqMode,
    countOccurrences: bool,
    outputUnique: bool,
    outputRepeated: bool,
    ignoreCase: bool,
    input: Input
  )

  method Schema() returns (s: CliTypes.CliSchema)
  {
    s := CliTypes.CliSchema(
      [
        CliTypes.OptionDecl("uniq.count", ['c'], ["count"], CliTypes.NoArg),
        CliTypes.OptionDecl("uniq.repeated", ['d'], ["repeated"], CliTypes.NoArg),
        CliTypes.OptionDecl("uniq.ignore_case", ['i'], ["ignore-case"], CliTypes.NoArg),
        CliTypes.OptionDecl("uniq.unique", ['u'], ["unique"], CliTypes.NoArg),
        CliTypes.OptionDecl("uniq.help", [], ["help"], CliTypes.NoArg),
        CliTypes.OptionDecl("uniq.version", [], ["version"], CliTypes.NoArg)
      ],
      true
    );
  }

  method ParserConfig() returns (cfg: CliTypes.ParseConfig)
  {
    cfg := CliTypes.ParseConfig(CliTypes.GNU_Permute, true, true, true);
  }

  function AllDigits(text: string): bool
    decreases |text|
  {
    if |text| == 0 then
      true
    else
      '0' <= text[0] <= '9' && AllDigits(text[1..])
  }

  function IsTraditionalSkipCharsOperand(text: string): bool
  {
    |text| > 1 && text[0] == '+' && AllDigits(text[1..])
  }

  function UnsupportedSkipOperand(operands: seq<string>): string
    decreases |operands|
  {
    if |operands| == 0 then
      ""
    else if IsTraditionalSkipCharsOperand(operands[0]) then
      operands[0]
    else
      UnsupportedSkipOperand(operands[1..])
  }

  method Decode(p: CliTypes.ParsedArgs) returns (raw: UniqCmdRaw)
  {
    var seenCount := false;
    var seenRepeated := false;
    var seenUnique := false;
    var seenIgnoreCase := false;
    var seenHelp := false;
    var seenVersion := false;
    var helpTokenIndex := -1;
    var versionTokenIndex := -1;

    var i := 0;
    while i < |p.options|
      decreases |p.options| - i
    {
      var occ := p.options[i];
      if occ.key == "uniq.count" {
        seenCount := true;
      }
      if occ.key == "uniq.repeated" {
        seenRepeated := true;
      }
      if occ.key == "uniq.unique" {
        seenUnique := true;
      }
      if occ.key == "uniq.ignore_case" {
        seenIgnoreCase := true;
      }
      if occ.key == "uniq.help" {
        seenHelp := true;
        if helpTokenIndex == -1 || occ.tokenIndex < helpTokenIndex {
          helpTokenIndex := occ.tokenIndex;
        }
      }
      if occ.key == "uniq.version" {
        seenVersion := true;
        if versionTokenIndex == -1 || occ.tokenIndex < versionTokenIndex {
          versionTokenIndex := occ.tokenIndex;
        }
      }
      i := i + 1;
    }

    raw := UniqCmdRaw(
      seenCount,
      seenRepeated,
      seenUnique,
      seenIgnoreCase,
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
        "uniq: unrecognized option '" + e.rawToken + "'\n" +
        "Try 'uniq --help' for more information.\n"
      else if |e.rawToken| > 1 && e.rawToken[0] == '-' then
        "uniq: invalid option -- '" + [e.rawToken[1]] + "'\n" +
        "Try 'uniq --help' for more information.\n"
      else
        "uniq: invalid option\nTry 'uniq --help' for more information.\n"
    else if e.kind == CliTypes.Ambiguous then
      "uniq: option '" + e.rawToken + "' is ambiguous\n" +
      "Try 'uniq --help' for more information.\n"
    else
      "uniq: parse error at token '" + e.rawToken + "'\n"
  }

  method FormatParseError(e: CliTypes.ParseError) returns (b: BenchWorld.Bytes)
  {
    b := Utf8.Encode(ParseErrorText(e));
  }

  method PlanParseFailure(
    e: CliTypes.ParseError,
    argv: seq<string>
  ) returns (plan: CliTypes.CliPlan<UniqCmdRaw>)
    decreases *
  {
    var msg := FormatParseError(e);
    plan := CliTypes.CliEarlyExit(1, [], msg);
  }
}
