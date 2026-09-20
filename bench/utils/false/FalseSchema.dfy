include "../../core/CliTypes.dfy"

module FalseSchema {
  import CliTypes

  datatype FalseMode = ModeRun | ModeHelp | ModeVersion

  datatype FalseCmdRaw = FalseCmdRaw(
    seenHelp: bool,
    seenVersion: bool,
    helpTokenIndex: int,
    versionTokenIndex: int,
    operands: seq<string>
  )

  datatype FalseCmd = FalseCmd(
    mode: FalseMode,
    operands: seq<string>
  )

  function Command(raw: FalseCmdRaw): FalseCmd
  {
    var mode :=
      if raw.seenHelp && (!raw.seenVersion || raw.helpTokenIndex <= raw.versionTokenIndex) then
        ModeHelp
      else if raw.seenVersion then
        ModeVersion
      else
        ModeRun;
    FalseCmd(mode, raw.operands)
  }

  method Schema() returns (s: CliTypes.CliSchema)
  {
    s := CliTypes.CliSchema(
      [
        CliTypes.OptionDecl("false.help", [], ["help"], CliTypes.NoArg),
        CliTypes.OptionDecl("false.version", [], ["version"], CliTypes.NoArg)
      ],
      true
    );
  }

  method ParserConfig() returns (cfg: CliTypes.ParseConfig)
  {
    cfg := CliTypes.ParseConfig(CliTypes.GNU_Permute, true, false, true);
  }

  method Decode(p: CliTypes.ParsedArgs) returns (raw: FalseCmdRaw)
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
      if specialOnly && occ.key == "false.help" {
        seenHelp := true;
        if helpTokenIndex == -1 || occ.tokenIndex < helpTokenIndex {
          helpTokenIndex := occ.tokenIndex;
        }
      }
      if specialOnly && occ.key == "false.version" {
        seenVersion := true;
        if versionTokenIndex == -1 || occ.tokenIndex < versionTokenIndex {
          versionTokenIndex := occ.tokenIndex;
        }
      }
      i := i + 1;
    }

    raw := FalseCmdRaw(seenHelp, seenVersion, helpTokenIndex, versionTokenIndex, p.positionals);
  }

  method FromArgv(argv: seq<string>) returns (raw: FalseCmdRaw)
  {
    var singleUserArgument := |argv| == 2;
    var seenHelp := singleUserArgument && argv[1] == "--help";
    var seenVersion := singleUserArgument && argv[1] == "--version";
    var operands := if |argv| > 0 then argv[1..] else [];
    raw := FalseCmdRaw(
      seenHelp,
      seenVersion,
      if seenHelp then 1 else -1,
      if seenVersion then 1 else -1,
      operands
    );
  }

  method PlanParseFailure(
    e: CliTypes.ParseError,
    argv: seq<string>
  ) returns (plan: CliTypes.CliPlan<FalseCmdRaw>)
    decreases *
  {
    plan := CliTypes.CliEarlyExit(1, [], []);
  }
}
