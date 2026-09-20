include "../../core/Utf8.dfy"
include "../../core/World.dfy"
include "../../core/CliTypes.dfy"

module TrueSchema {
  import Utf8 = Utf8Semantics
  import BenchWorld
  import CliTypes

  datatype TrueMode = ModeRun | ModeHelp | ModeVersion

  datatype TrueCmdRaw = TrueCmdRaw(
    seenHelp: bool,
    seenVersion: bool,
    helpTokenIndex: int,
    versionTokenIndex: int,
    operands: seq<string>
  )

  datatype TrueCmd = TrueCmd(
    mode: TrueMode,
    operands: seq<string>
  )

  function Command(raw: TrueCmdRaw): TrueCmd
  {
    var mode :=
      if raw.seenHelp && (!raw.seenVersion || raw.helpTokenIndex <= raw.versionTokenIndex) then
        ModeHelp
      else if raw.seenVersion then
        ModeVersion
      else
        ModeRun;
    TrueCmd(mode, raw.operands)
  }

  method Schema() returns (s: CliTypes.CliSchema)
  {
    s := CliTypes.CliSchema(
      [
        CliTypes.OptionDecl("true.help", [], ["help"], CliTypes.NoArg),
        CliTypes.OptionDecl("true.version", [], ["version"], CliTypes.NoArg)
      ],
      true
    );
  }

  method ParserConfig() returns (cfg: CliTypes.ParseConfig)
  {
    cfg := CliTypes.ParseConfig(CliTypes.GNU_Permute, true, false, true);
  }

  method Decode(p: CliTypes.ParsedArgs) returns (raw: TrueCmdRaw)
  {
    var specialOnly := |p.options| == 1 && |p.positionals| == 0;
    var seenHelp := false;
    var seenVersion := false;
    var helpTokenIndex := -1;
    var versionTokenIndex := -1;

    var i := 0;
    while i < |p.options|
      decreases |p.options| - i
    {
      var occ := p.options[i];
      if specialOnly && occ.key == "true.help" {
        seenHelp := true;
        if helpTokenIndex == -1 || occ.tokenIndex < helpTokenIndex {
          helpTokenIndex := occ.tokenIndex;
        }
      }
      if specialOnly && occ.key == "true.version" {
        seenVersion := true;
        if versionTokenIndex == -1 || occ.tokenIndex < versionTokenIndex {
          versionTokenIndex := occ.tokenIndex;
        }
      }
      i := i + 1;
    }

    raw := TrueCmdRaw(seenHelp, seenVersion, helpTokenIndex, versionTokenIndex, p.positionals);
  }

  method FromArgv(argv: seq<string>) returns (raw: TrueCmdRaw)
  {
    var singleUserArgument := |argv| == 2;
    var seenHelp := singleUserArgument && argv[1] == "--help";
    var seenVersion := singleUserArgument && argv[1] == "--version";
    var operands := if |argv| > 0 then argv[1..] else [];
    raw := TrueCmdRaw(
      seenHelp,
      seenVersion,
      if seenHelp then 1 else -1,
      if seenVersion then 1 else -1,
      operands
    );
  }

  function ParseErrorText(e: CliTypes.ParseError): string
  {
    if e.kind == CliTypes.UnknownOption then
      if |e.rawToken| > 2 && e.rawToken[0] == '-' && e.rawToken[1] == '-' then
        "true: unrecognized option '" + e.rawToken + "'\n" +
        "Try 'true --help' for more information.\n"
      else if |e.rawToken| > 1 && e.rawToken[0] == '-' then
        "true: invalid option -- '" + [e.rawToken[1]] + "'\n" +
        "Try 'true --help' for more information.\n"
      else
        "true: invalid option\nTry 'true --help' for more information.\n"
    else if e.kind == CliTypes.Ambiguous then
      "true: option '" + e.rawToken + "' is ambiguous\n" +
      "Try 'true --help' for more information.\n"
    else
      "true: " +
      (if e.kind == CliTypes.MissingValue
       then "missing option value"
       else if e.kind == CliTypes.UnexpectedValue
         then "option does not take a value"
         else "parse error") +
      " at token '" + e.rawToken + "'\n"
  }

  method FormatParseError(e: CliTypes.ParseError) returns (b: BenchWorld.Bytes)
  {
    b := Utf8.Encode(ParseErrorText(e));
  }

  method PlanParseFailure(
    e: CliTypes.ParseError,
    argv: seq<string>
  ) returns (plan: CliTypes.CliPlan<TrueCmdRaw>)
    decreases *
  {
    plan := CliTypes.CliEarlyExit(0, [], []);
  }
}
