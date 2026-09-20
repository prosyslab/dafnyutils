include "../../core/Utf8.dfy"
include "../../core/World.dfy"
include "../../core/CliTypes.dfy"

module PwdSchema {
  import Utf8 = Utf8Semantics
  import BenchWorld
  import CliTypes

  datatype PwdCmdRaw = PwdCmdRaw(
    seenHelp: bool,
    seenVersion: bool,
    helpOccurrenceIndex: int,
    versionOccurrenceIndex: int,
    seenLogical: bool,
    seenPhysical: bool,
    logicalOccurrenceIndex: int,
    physicalOccurrenceIndex: int,
    operands: seq<string>
  )

  method Schema() returns (s: CliTypes.CliSchema)
  {
    s := CliTypes.CliSchema(
      [
        CliTypes.OptionDecl("pwd.logical", ['L'], ["logical"], CliTypes.NoArg),
        CliTypes.OptionDecl("pwd.physical", ['P'], ["physical"], CliTypes.NoArg),
        CliTypes.OptionDecl("pwd.help", [], ["help"], CliTypes.NoArg),
        CliTypes.OptionDecl("pwd.version", [], ["version"], CliTypes.NoArg)
      ],
      true
    );
  }

  method ParserConfig() returns (cfg: CliTypes.ParseConfig)
  {
    cfg := CliTypes.ParseConfig(CliTypes.GNU_Permute, true, true, true);
  }

  method Decode(p: CliTypes.ParsedArgs) returns (raw: PwdCmdRaw)
  {
    var seenHelp := false;
    var seenVersion := false;
    var helpOccurrenceIndex := -1;
    var versionOccurrenceIndex := -1;
    var seenLogical := false;
    var seenPhysical := false;
    var logicalOccurrenceIndex := -1;
    var physicalOccurrenceIndex := -1;

    var i := 0;
    while i < |p.options|
      decreases |p.options| - i
    {
      var occ := p.options[i];
      if occ.key == "pwd.help" {
        seenHelp := true;
        if helpOccurrenceIndex == -1 || i > helpOccurrenceIndex {
          helpOccurrenceIndex := i;
        }
      }
      if occ.key == "pwd.version" {
        seenVersion := true;
        if versionOccurrenceIndex == -1 || i > versionOccurrenceIndex {
          versionOccurrenceIndex := i;
        }
      }
      if occ.key == "pwd.logical" {
        seenLogical := true;
        if logicalOccurrenceIndex == -1 || i > logicalOccurrenceIndex {
          logicalOccurrenceIndex := i;
        }
      }
      if occ.key == "pwd.physical" {
        seenPhysical := true;
        if physicalOccurrenceIndex == -1 || i > physicalOccurrenceIndex {
          physicalOccurrenceIndex := i;
        }
      }
      i := i + 1;
    }

    raw := PwdCmdRaw(
      seenHelp,
      seenVersion,
      helpOccurrenceIndex,
      versionOccurrenceIndex,
      seenLogical,
      seenPhysical,
      logicalOccurrenceIndex,
      physicalOccurrenceIndex,
      p.positionals
    );
  }

  function ParseErrorText(e: CliTypes.ParseError): string
  {
    if e.kind == CliTypes.UnknownOption || e.kind == CliTypes.UnexpectedValue || e.kind == CliTypes.MissingValue then
      if |e.rawToken| > 2 && e.rawToken[0] == '-' && e.rawToken[1] == '-' then
        "pwd: unrecognized option '" + e.rawToken + "'\n" +
        "Try 'pwd --help' for more information.\n"
      else if |e.rawToken| > 1 && e.rawToken[0] == '-' then
        "pwd: invalid option -- '" + [e.rawToken[1]] + "'\n" +
        "Try 'pwd --help' for more information.\n"
      else
        "pwd: invalid option\nTry 'pwd --help' for more information.\n"
    else if e.kind == CliTypes.Ambiguous then
      "pwd: option '" + e.rawToken + "' is ambiguous\n" +
      "Try 'pwd --help' for more information.\n"
    else
      "pwd: parse error at token '" + e.rawToken + "'\n"
  }

  method FormatParseError(e: CliTypes.ParseError) returns (b: BenchWorld.Bytes)
  {
    b := Utf8.Encode(ParseErrorText(e));
  }

  method PlanParseFailure(
    e: CliTypes.ParseError,
    argv: seq<string>
  ) returns (plan: CliTypes.CliPlan<PwdCmdRaw>)
    decreases *
  {
    var msg := FormatParseError(e);
    plan := CliTypes.CliEarlyExit(1, [], msg);
  }
}
