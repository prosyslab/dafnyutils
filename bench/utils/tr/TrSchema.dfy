include "../../core/Utf8.dfy"
include "../../core/World.dfy"
include "../../core/CliTypes.dfy"

module TrSchema {
  import Utf8 = Utf8Semantics
  import BenchWorld
  import CliTypes

  datatype TrCmdRaw = TrCmdRaw(
    seenDelete: bool,
    seenSqueeze: bool,
    seenHelp: bool,
    seenVersion: bool,
    helpTokenIndex: int,
    versionTokenIndex: int,
    operands: seq<string>
  )

  method Schema() returns (s: CliTypes.CliSchema)
  {
    s := CliTypes.CliSchema(
      [
        CliTypes.OptionDecl("tr.delete", ['d'], ["delete"], CliTypes.NoArg),
        CliTypes.OptionDecl("tr.squeeze", ['s'], ["squeeze-repeats"], CliTypes.NoArg),
        CliTypes.OptionDecl("tr.help", [], ["help"], CliTypes.NoArg),
        CliTypes.OptionDecl("tr.version", [], ["version"], CliTypes.NoArg)
      ],
      true
    );
  }

  method ParserConfig() returns (cfg: CliTypes.ParseConfig)
  {
    cfg := CliTypes.ParseConfig(CliTypes.POSIX_StopAtFirst, true, true, true);
  }

  method Decode(p: CliTypes.ParsedArgs) returns (raw: TrCmdRaw)
  {
    var seenDelete := false;
    var seenSqueeze := false;
    var seenHelp := false;
    var seenVersion := false;
    var helpTokenIndex := -1;
    var versionTokenIndex := -1;

    var i := 0;
    while i < |p.options|
      decreases |p.options| - i
    {
      var occ := p.options[i];
      if occ.key == "tr.delete" {
        seenDelete := true;
      }
      if occ.key == "tr.squeeze" {
        seenSqueeze := true;
      }
      if occ.key == "tr.help" {
        seenHelp := true;
        if helpTokenIndex == -1 || occ.tokenIndex < helpTokenIndex {
          helpTokenIndex := occ.tokenIndex;
        }
      }
      if occ.key == "tr.version" {
        seenVersion := true;
        if versionTokenIndex == -1 || occ.tokenIndex < versionTokenIndex {
          versionTokenIndex := occ.tokenIndex;
        }
      }
      i := i + 1;
    }

    raw := TrCmdRaw(
      seenDelete,
      seenSqueeze,
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
        "tr: unrecognized option '" + e.rawToken + "'\n" +
        "Try 'tr --help' for more information.\n"
      else if |e.rawToken| > 1 && e.rawToken[0] == '-' then
        "tr: invalid option -- '" + [e.rawToken[1]] + "'\n" +
        "Try 'tr --help' for more information.\n"
      else
        "tr: invalid option\nTry 'tr --help' for more information.\n"
    else if e.kind == CliTypes.Ambiguous then
      "tr: option '" + e.rawToken + "' is ambiguous\n" +
      "Try 'tr --help' for more information.\n"
    else
      "tr: " +
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
  ) returns (plan: CliTypes.CliPlan<TrCmdRaw>)
    decreases *
  {
    var msg := FormatParseError(e);
    plan := CliTypes.CliEarlyExit(1, [], msg);
  }
}
