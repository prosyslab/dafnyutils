include "../../core/Utf8.dfy"
include "../../core/World.dfy"
include "../../core/CliTypes.dfy"

module LognameSchema {
  import Utf8 = Utf8Semantics
  import BenchWorld
  import CliTypes

  datatype LognameMode = ModeRun | ModeHelp | ModeVersion

  datatype LognameCmdRaw = LognameCmdRaw(
    seenHelp: bool,
    seenVersion: bool,
    helpTokenIndex: int,
    versionTokenIndex: int,
    operands: seq<string>
  )

  datatype LognameCmd = LognameCmd(
    mode: LognameMode,
    operands: seq<string>
  )

  function Command(raw: LognameCmdRaw): LognameCmd
  {
    var mode :=
      if raw.seenHelp && (!raw.seenVersion || raw.helpTokenIndex <= raw.versionTokenIndex) then
        ModeHelp
      else if raw.seenVersion then
        ModeVersion
      else
        ModeRun;
    LognameCmd(mode, raw.operands)
  }

  method Schema() returns (s: CliTypes.CliSchema)
  {
    s := CliTypes.CliSchema(
      [
        CliTypes.OptionDecl("logname.help", [], ["help"], CliTypes.NoArg),
        CliTypes.OptionDecl("logname.version", [], ["version"], CliTypes.NoArg)
      ],
      true
    );
  }

  method ParserConfig() returns (cfg: CliTypes.ParseConfig)
  {
    cfg := CliTypes.ParseConfig(CliTypes.GNU_Permute, true, true, true);
  }

  method Decode(p: CliTypes.ParsedArgs) returns (raw: LognameCmdRaw)
  {
    var seenHelp := false;
    var seenVersion := false;
    var helpTokenIndex := -1;
    var versionTokenIndex := -1;

    var i := 0;
    while i < |p.options|
      decreases |p.options| - i
    {
      var occ := p.options[i];
      if occ.key == "logname.help" {
        seenHelp := true;
        if helpTokenIndex == -1 || occ.tokenIndex < helpTokenIndex {
          helpTokenIndex := occ.tokenIndex;
        }
      }
      if occ.key == "logname.version" {
        seenVersion := true;
        if versionTokenIndex == -1 || occ.tokenIndex < versionTokenIndex {
          versionTokenIndex := occ.tokenIndex;
        }
      }
      i := i + 1;
    }

    raw := LognameCmdRaw(seenHelp, seenVersion, helpTokenIndex, versionTokenIndex, p.positionals);
  }

  function ParseErrorText(e: CliTypes.ParseError): string
  {
    if e.kind == CliTypes.UnknownOption then
      if |e.rawToken| > 2 && e.rawToken[0] == '-' && e.rawToken[1] == '-' then
        "logname: unrecognized option '" + e.rawToken + "'\n" +
        "Try 'logname --help' for more information.\n"
      else if |e.rawToken| > 1 && e.rawToken[0] == '-' then
        "logname: invalid option -- '" + [e.rawToken[1]] + "'\n" +
        "Try 'logname --help' for more information.\n"
      else
        "logname: invalid option\nTry 'logname --help' for more information.\n"
    else if e.kind == CliTypes.Ambiguous then
      "logname: option '" + e.rawToken + "' is ambiguous\n" +
      "Try 'logname --help' for more information.\n"
    else
      "logname: " +
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
  ) returns (plan: CliTypes.CliPlan<LognameCmdRaw>)
    decreases *
  {
    var msg := FormatParseError(e);
    plan := CliTypes.CliEarlyExit(1, [], msg);
  }
}
