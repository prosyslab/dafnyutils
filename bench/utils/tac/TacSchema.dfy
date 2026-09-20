include "../../core/Utf8.dfy"
include "../../core/World.dfy"
include "../../core/CliTypes.dfy"

module TacSchema {
  import Utf8 = Utf8Semantics
  import BenchWorld
  import CliTypes

  datatype TacMode = ModeRun | ModeHelp | ModeVersion
  datatype Input = Stdin | File(path: BenchWorld.Path)

  datatype TacCmdRaw = TacCmdRaw(
    seenBefore: bool,
    separator: CliTypes.OptionalString,
    seenHelp: bool,
    seenVersion: bool,
    helpTokenIndex: int,
    versionTokenIndex: int,
    operands: seq<string>
  )

  datatype TacCmd = TacCmd(
    mode: TacMode,
    before: bool,
    separator: BenchWorld.Bytes,
    inputs: seq<Input>
  )

  method Schema() returns (s: CliTypes.CliSchema)
  {
    // Deferred GNU behavior: `-r`/`--regex` remains outside this benchmark
    // schema; literal separators use GNU's default after-record attachment
    // unless `--before` is selected.
    s := CliTypes.CliSchema(
      [
        CliTypes.OptionDecl("tac.before", ['b'], ["before"], CliTypes.NoArg),
        CliTypes.OptionDecl("tac.separator", ['s'], ["separator"], CliTypes.ReqArg),
        CliTypes.OptionDecl("tac.help", [], ["help"], CliTypes.NoArg),
        CliTypes.OptionDecl("tac.version", [], ["version"], CliTypes.NoArg)
      ],
      true
    );
  }

  method ParserConfig() returns (cfg: CliTypes.ParseConfig)
  {
    cfg := CliTypes.ParseConfig(CliTypes.GNU_Permute, true, true, true);
  }

  method Decode(p: CliTypes.ParsedArgs) returns (raw: TacCmdRaw)
  {
    var seenBefore := false;
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
      if occ.key == "tac.before" {
        seenBefore := true;
      }
      if occ.key == "tac.separator" {
        separator := occ.value;
      }
      if occ.key == "tac.help" {
        seenHelp := true;
        if helpTokenIndex == -1 || occ.tokenIndex < helpTokenIndex {
          helpTokenIndex := occ.tokenIndex;
        }
      }
      if occ.key == "tac.version" {
        seenVersion := true;
        if versionTokenIndex == -1 || occ.tokenIndex < versionTokenIndex {
          versionTokenIndex := occ.tokenIndex;
        }
      }
      i := i + 1;
    }

    raw := TacCmdRaw(
      seenBefore,
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
        "tac: unrecognized option '" + e.rawToken + "'\n" +
        "Try 'tac --help' for more information.\n"
      else if |e.rawToken| > 1 && e.rawToken[0] == '-' then
        "tac: invalid option -- '" + [e.rawToken[1]] + "'\n" +
        "Try 'tac --help' for more information.\n"
      else
        "tac: invalid option\nTry 'tac --help' for more information.\n"
    else if e.kind == CliTypes.Ambiguous then
      "tac: option '" + e.rawToken + "' is ambiguous\n" +
      "Try 'tac --help' for more information.\n"
    else if e.kind == CliTypes.MissingValue then
      "tac: option '" + e.rawToken + "' requires an argument\n" +
      "Try 'tac --help' for more information.\n"
    else
      "tac: parse error at token '" + e.rawToken + "'\n"
  }

  method FormatParseError(e: CliTypes.ParseError) returns (b: BenchWorld.Bytes)
  {
    b := Utf8.Encode(ParseErrorText(e));
  }

  method PlanParseFailure(
    e: CliTypes.ParseError,
    argv: seq<string>
  ) returns (plan: CliTypes.CliPlan<TacCmdRaw>)
    decreases *
  {
    match CliTypes.PriorHelpVersionRequest(argv, e.tokenIndex)
    case RequestHelp =>
      plan := CliTypes.CliRun(
        TacCmdRaw(false, CliTypes.None, true, false, 0, -1, [])
      );
    case RequestVersion =>
      plan := CliTypes.CliRun(
        TacCmdRaw(false, CliTypes.None, false, true, -1, 0, [])
      );
    case RequestNone =>
      var msg := FormatParseError(e);
      plan := CliTypes.CliEarlyExit(1, [], msg);
  }
}
