include "../../core/Utf8.dfy"
include "../../core/World.dfy"
include "../../core/CliTypes.dfy"

module PrintenvSchema {
  import Utf8 = Utf8Semantics
  import BenchWorld
  import CliTypes

  datatype PrintenvCmdRaw = PrintenvCmdRaw(
    seenNull: bool,
    seenHelp: bool,
    seenVersion: bool,
    helpTokenIndex: int,
    versionTokenIndex: int,
    operands: seq<string>
  )

  datatype PrintenvMode = ModeRun | ModeHelp | ModeVersion
  datatype PrintenvCmd = PrintenvCmd(
    mode: PrintenvMode,
    nullTerminated: bool,
    operands: seq<string>
  )

  function Command(raw: PrintenvCmdRaw): PrintenvCmd
  {
    var mode :=
      if raw.seenHelp && (!raw.seenVersion || raw.helpTokenIndex <= raw.versionTokenIndex) then
        ModeHelp
      else if raw.seenVersion then
        ModeVersion
      else
        ModeRun;
    PrintenvCmd(mode, raw.seenNull, raw.operands)
  }

  method Schema() returns (s: CliTypes.CliSchema)
  {
    s := CliTypes.CliSchema(
      [
        CliTypes.OptionDecl("printenv.null", ['0'], ["null"], CliTypes.NoArg),
        CliTypes.OptionDecl("printenv.help", [], ["help"], CliTypes.NoArg),
        CliTypes.OptionDecl("printenv.version", [], ["version"], CliTypes.NoArg)
      ],
      true
    );
  }

  method ParserConfig() returns (cfg: CliTypes.ParseConfig)
  {
    cfg := CliTypes.ParseConfig(CliTypes.POSIX_StopAtFirst, true, true, true);
  }

  method Decode(p: CliTypes.ParsedArgs) returns (raw: PrintenvCmdRaw)
  {
    var seenNull := false;
    var seenHelp := false;
    var seenVersion := false;
    var helpTokenIndex := -1;
    var versionTokenIndex := -1;

    var i := 0;
    while i < |p.options|
      decreases |p.options| - i
    {
      var occ := p.options[i];
      if occ.key == "printenv.null" {
        seenNull := true;
      }
      if occ.key == "printenv.help" {
        seenHelp := true;
        if helpTokenIndex == -1 || occ.tokenIndex < helpTokenIndex {
          helpTokenIndex := occ.tokenIndex;
        }
      }
      if occ.key == "printenv.version" {
        seenVersion := true;
        if versionTokenIndex == -1 || occ.tokenIndex < versionTokenIndex {
          versionTokenIndex := occ.tokenIndex;
        }
      }
      i := i + 1;
    }

    raw := PrintenvCmdRaw(
      seenNull,
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
        "printenv: unrecognized option '" + e.rawToken + "'\n" +
        "Try 'printenv --help' for more information.\n"
      else if |e.rawToken| > 1 && e.rawToken[0] == '-' then
        "printenv: invalid option -- '" + [e.rawToken[1]] + "'\n" +
        "Try 'printenv --help' for more information.\n"
      else
        "printenv: invalid option\nTry 'printenv --help' for more information.\n"
    else if e.kind == CliTypes.Ambiguous then
      "printenv: option '" + e.rawToken + "' is ambiguous\n" +
      "Try 'printenv --help' for more information.\n"
    else if e.kind == CliTypes.UnexpectedValue then
      "printenv: option '" + e.rawToken + "' doesn't allow an argument\n" +
      "Try 'printenv --help' for more information.\n"
    else
      "printenv: parse error at token '" + e.rawToken + "'\n"
  }

  method FormatParseError(e: CliTypes.ParseError) returns (b: BenchWorld.Bytes)
  {
    b := Utf8.Encode(ParseErrorText(e));
  }

  method PlanParseFailure(
    e: CliTypes.ParseError,
    argv: seq<string>
  ) returns (plan: CliTypes.CliPlan<PrintenvCmdRaw>)
    decreases *
  {
    var msg := FormatParseError(e);
    plan := CliTypes.CliEarlyExit(2, [], msg);
  }
}
