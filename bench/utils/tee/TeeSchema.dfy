include "../../core/Utf8.dfy"
include "../../core/World.dfy"
include "../../core/CliTypes.dfy"

module TeeSchema {
  import Utf8 = Utf8Semantics
  import BenchWorld
  import CliTypes

  datatype TeeMode = ModeRun | ModeHelp | ModeVersion

  datatype TeeCmdRaw = TeeCmdRaw(
    seenAppend: bool,
    seenIgnoreInterrupts: bool,
    seenHelp: bool,
    seenVersion: bool,
    helpTokenIndex: int,
    versionTokenIndex: int,
    operands: seq<string>
  )

  datatype TeeCmd = TeeCmd(
    mode: TeeMode,
    append: bool,
    ignoreInterrupts: bool,
    outputs: seq<BenchWorld.Path>
  )

  method Schema() returns (s: CliTypes.CliSchema)
  {
    s := CliTypes.CliSchema(
      [
        CliTypes.OptionDecl("tee.append", ['a'], ["append"], CliTypes.NoArg),
        CliTypes.OptionDecl("tee.ignore_interrupts", ['i'], ["ignore-interrupts"], CliTypes.NoArg),
        CliTypes.OptionDecl("tee.help", [], ["help"], CliTypes.NoArg),
        CliTypes.OptionDecl("tee.version", [], ["version"], CliTypes.NoArg)
      ],
      true
    );
  }

  method ParserConfig() returns (cfg: CliTypes.ParseConfig)
  {
    cfg := CliTypes.ParseConfig(CliTypes.GNU_Permute, true, true, true);
  }

  method Decode(p: CliTypes.ParsedArgs) returns (raw: TeeCmdRaw)
  {
    var seenAppend := false;
    var seenIgnoreInterrupts := false;
    var seenHelp := false;
    var seenVersion := false;
    var helpTokenIndex := -1;
    var versionTokenIndex := -1;

    var i := 0;
    while i < |p.options|
      decreases |p.options| - i
    {
      var occ := p.options[i];
      if occ.key == "tee.append" {
        seenAppend := true;
      }
      if occ.key == "tee.ignore_interrupts" {
        seenIgnoreInterrupts := true;
      }
      if occ.key == "tee.help" {
        seenHelp := true;
        if helpTokenIndex == -1 || occ.tokenIndex < helpTokenIndex {
          helpTokenIndex := occ.tokenIndex;
        }
      }
      if occ.key == "tee.version" {
        seenVersion := true;
        if versionTokenIndex == -1 || occ.tokenIndex < versionTokenIndex {
          versionTokenIndex := occ.tokenIndex;
        }
      }
      i := i + 1;
    }

    raw := TeeCmdRaw(
      seenAppend,
      seenIgnoreInterrupts,
      seenHelp,
      seenVersion,
      helpTokenIndex,
      versionTokenIndex,
      p.positionals
    );
  }

  function ParseErrorText(e: CliTypes.ParseError): string
  {
    if e.kind == CliTypes.UnknownOption || e.kind == CliTypes.UnexpectedValue then
      if |e.rawToken| > 2 && e.rawToken[0] == '-' && e.rawToken[1] == '-' then
        "tee: unrecognized option '" + e.rawToken + "'\n" +
        "Try 'tee --help' for more information.\n"
      else if |e.rawToken| > 1 && e.rawToken[0] == '-' then
        "tee: invalid option -- '" + [e.rawToken[1]] + "'\n" +
        "Try 'tee --help' for more information.\n"
      else
        "tee: invalid option\nTry 'tee --help' for more information.\n"
    else if e.kind == CliTypes.Ambiguous then
      "tee: option '" + e.rawToken + "' is ambiguous\n" +
      "Try 'tee --help' for more information.\n"
    else
      "tee: parse error at token '" + e.rawToken + "'\n"
  }

  method FormatParseError(e: CliTypes.ParseError) returns (b: BenchWorld.Bytes)
  {
    b := Utf8.Encode(ParseErrorText(e));
  }

  method PlanParseFailure(
    e: CliTypes.ParseError,
    argv: seq<string>
  ) returns (plan: CliTypes.CliPlan<TeeCmdRaw>)
    decreases *
  {
    var msg := FormatParseError(e);
    plan := CliTypes.CliEarlyExit(1, [], msg);
  }
}
