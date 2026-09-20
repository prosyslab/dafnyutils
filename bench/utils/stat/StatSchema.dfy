include "../../core/Utf8.dfy"
include "../../core/World.dfy"
include "../../core/CliTypes.dfy"

module StatSchema {
  import Utf8 = Utf8Semantics
  import BenchWorld
  import CliTypes

  datatype StatMode = ModeRun | ModeHelp | ModeVersion | ModeMissingFormat | ModeMissingOperand

  datatype StatCmdRaw = StatCmdRaw(
    followSymlink: bool,
    seenFormat: bool,
    format: string,
    seenHelp: bool,
    seenVersion: bool,
    helpTokenIndex: int,
    versionTokenIndex: int,
    operands: seq<string>
  )

  datatype StatCmd = StatCmd(
    mode: StatMode,
    followSymlink: bool,
    format: string,
    files: seq<string>
  )

  function RequestedMode(raw: StatCmdRaw): StatMode
  {
    if raw.seenHelp && (!raw.seenVersion || raw.helpTokenIndex <= raw.versionTokenIndex) then
      ModeHelp
    else if raw.seenVersion then
      ModeVersion
    else if !raw.seenFormat then
      ModeMissingFormat
    else if |raw.operands| == 0 then
      ModeMissingOperand
    else
      ModeRun
  }

  function Command(raw: StatCmdRaw): StatCmd
  {
    StatCmd(RequestedMode(raw), raw.followSymlink, raw.format, raw.operands)
  }

  method Schema() returns (s: CliTypes.CliSchema)
  {
    s := CliTypes.CliSchema(
      [
        CliTypes.OptionDecl("stat.dereference", ['L'], ["dereference"], CliTypes.NoArg),
        CliTypes.OptionDecl("stat.format", ['c'], ["format"], CliTypes.ReqArg),
        CliTypes.OptionDecl("stat.help", [], ["help"], CliTypes.NoArg),
        CliTypes.OptionDecl("stat.version", [], ["version"], CliTypes.NoArg)
      ],
      true
    );
  }

  method ParserConfig() returns (cfg: CliTypes.ParseConfig)
  {
    cfg := CliTypes.ParseConfig(CliTypes.GNU_Permute, true, true, true);
  }

  method Decode(p: CliTypes.ParsedArgs) returns (raw: StatCmdRaw)
  {
    var followSymlink := false;
    var seenFormat := false;
    var format := "";
    var formatTokenIndex := -1;
    var seenHelp := false;
    var seenVersion := false;
    var helpTokenIndex := -1;
    var versionTokenIndex := -1;

    var i := 0;
    while i < |p.options|
      invariant 0 <= i <= |p.options|
      decreases |p.options| - i
    {
      var occurrence := p.options[i];
      if occurrence.key == "stat.dereference" {
        followSymlink := true;
      }
      if occurrence.key == "stat.format" {
        match occurrence.value
        case Some(value) =>
          if formatTokenIndex == -1 || occurrence.tokenIndex >= formatTokenIndex {
            seenFormat := true;
            format := value;
            formatTokenIndex := occurrence.tokenIndex;
          }
        case None =>
      }
      if occurrence.key == "stat.help" {
        seenHelp := true;
        if helpTokenIndex == -1 || occurrence.tokenIndex < helpTokenIndex {
          helpTokenIndex := occurrence.tokenIndex;
        }
      }
      if occurrence.key == "stat.version" {
        seenVersion := true;
        if versionTokenIndex == -1 || occurrence.tokenIndex < versionTokenIndex {
          versionTokenIndex := occurrence.tokenIndex;
        }
      }
      i := i + 1;
    }

    raw := StatCmdRaw(
      followSymlink,
      seenFormat,
      format,
      seenHelp,
      seenVersion,
      helpTokenIndex,
      versionTokenIndex,
      p.positionals
    );
  }

  function ParseErrorText(error: CliTypes.ParseError): string
  {
    if error.kind == CliTypes.UnknownOption ||
       error.kind == CliTypes.UnexpectedValue ||
       error.kind == CliTypes.MissingValue then
      if |error.rawToken| > 2 && error.rawToken[0] == '-' && error.rawToken[1] == '-' then
        "stat: unrecognized option '" + error.rawToken + "'\n" +
        "Try 'stat --help' for more information.\n"
      else if |error.rawToken| > 1 && error.rawToken[0] == '-' then
        "stat: invalid option -- '" + [error.rawToken[1]] + "'\n" +
        "Try 'stat --help' for more information.\n"
      else
        "stat: invalid option\nTry 'stat --help' for more information.\n"
    else if error.kind == CliTypes.Ambiguous then
      "stat: option '" + error.rawToken + "' is ambiguous\n" +
      "Try 'stat --help' for more information.\n"
    else
      "stat: parse error at token '" + error.rawToken + "'\n"
  }

  method FormatParseError(error: CliTypes.ParseError) returns (message: BenchWorld.Bytes)
  {
    message := Utf8.Encode(ParseErrorText(error));
  }

  method PlanParseFailure(
    error: CliTypes.ParseError,
    argv: seq<string>
  ) returns (plan: CliTypes.CliPlan<StatCmdRaw>)
    decreases *
  {
    var message := FormatParseError(error);
    plan := CliTypes.CliEarlyExit(1, [], message);
  }
}
