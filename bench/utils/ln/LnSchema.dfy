include "../../core/Utf8.dfy"
include "../../core/World.dfy"
include "../../core/CliTypes.dfy"

module LnSchema {
  import Utf8 = Utf8Semantics
  import BenchWorld
  import CliTypes

  datatype LnMode = ModeRun | ModeHelp | ModeVersion

  datatype LnCmdRaw = LnCmdRaw(
    seenSymbolic: bool,
    seenHelp: bool,
    seenVersion: bool,
    helpTokenIndex: int,
    versionTokenIndex: int,
    operands: seq<string>
  )

  datatype LnCmd = LnCmd(
    mode: LnMode,
    symbolic: bool,
    operands: seq<string>
  )

  function RequestedMode(raw: LnCmdRaw): LnMode
  {
    if raw.seenHelp && (!raw.seenVersion || raw.helpTokenIndex <= raw.versionTokenIndex) then
      ModeHelp
    else if raw.seenVersion then
      ModeVersion
    else
      ModeRun
  }

  function Command(raw: LnCmdRaw): LnCmd
  {
    LnCmd(RequestedMode(raw), raw.seenSymbolic, raw.operands)
  }

  method Schema() returns (s: CliTypes.CliSchema)
  {
    s := CliTypes.CliSchema(
      [
        CliTypes.OptionDecl("ln.symbolic", ['s'], ["symbolic"], CliTypes.NoArg),
        CliTypes.OptionDecl("ln.help", [], ["help"], CliTypes.NoArg),
        CliTypes.OptionDecl("ln.version", [], ["version"], CliTypes.NoArg)
      ],
      true
    );
  }

  method ParserConfig() returns (cfg: CliTypes.ParseConfig)
  {
    cfg := CliTypes.ParseConfig(CliTypes.GNU_Permute, true, true, true);
  }

  method Decode(p: CliTypes.ParsedArgs) returns (raw: LnCmdRaw)
  {
    var seenSymbolic := false;
    var seenHelp := false;
    var seenVersion := false;
    var helpTokenIndex := -1;
    var versionTokenIndex := -1;

    var i := 0;
    while i < |p.options|
      decreases |p.options| - i
    {
      var occ := p.options[i];
      if occ.key == "ln.symbolic" {
        seenSymbolic := true;
      }
      if occ.key == "ln.help" {
        seenHelp := true;
        if helpTokenIndex == -1 || occ.tokenIndex < helpTokenIndex {
          helpTokenIndex := occ.tokenIndex;
        }
      }
      if occ.key == "ln.version" {
        seenVersion := true;
        if versionTokenIndex == -1 || occ.tokenIndex < versionTokenIndex {
          versionTokenIndex := occ.tokenIndex;
        }
      }
      i := i + 1;
    }

    raw := LnCmdRaw(
      seenSymbolic,
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
        "ln: unrecognized option '" + e.rawToken + "'\n" +
        "Try 'ln --help' for more information.\n"
      else if |e.rawToken| > 1 && e.rawToken[0] == '-' then
        "ln: invalid option -- '" + [e.rawToken[1]] + "'\n" +
        "Try 'ln --help' for more information.\n"
      else
        "ln: invalid option\nTry 'ln --help' for more information.\n"
    else if e.kind == CliTypes.Ambiguous then
      "ln: option '" + e.rawToken + "' is ambiguous\n" +
      "Try 'ln --help' for more information.\n"
    else
      "ln: " +
      (if e.kind == CliTypes.MissingValue then
         "missing option value"
       else if e.kind == CliTypes.UnexpectedValue then
         "option does not take a value"
       else
         "parse error") +
      " at token '" + e.rawToken + "'\n"
  }

  method FormatParseError(e: CliTypes.ParseError) returns (b: BenchWorld.Bytes)
  {
    b := Utf8.Encode(ParseErrorText(e));
  }

  method PlanParseFailure(
    e: CliTypes.ParseError,
    argv: seq<string>
  ) returns (plan: CliTypes.CliPlan<LnCmdRaw>)
    decreases *
  {
    var msg := FormatParseError(e);
    plan := CliTypes.CliEarlyExit(1, [], msg);
  }
}
