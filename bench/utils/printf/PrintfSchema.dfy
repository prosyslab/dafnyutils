include "../../core/Utf8.dfy"
include "../../core/World.dfy"
include "../../core/CliTypes.dfy"

module PrintfSchema {
  import Utf8 = Utf8Semantics
  import BenchWorld
  import CliTypes

  datatype PrintfCmdRaw = PrintfCmdRaw(
    seenHelp: bool,
    seenVersion: bool,
    helpTokenIndex: int,
    versionTokenIndex: int,
    excessAfterRequest: CliTypes.OptionalString,
    operands: seq<string>
  )

  function HelpSelected(raw: PrintfCmdRaw): bool
  {
    raw.seenHelp &&
    (!raw.seenVersion || raw.helpTokenIndex <= raw.versionTokenIndex)
  }

  function VersionSelected(raw: PrintfCmdRaw): bool
  {
    raw.seenVersion &&
    (!raw.seenHelp || raw.versionTokenIndex < raw.helpTokenIndex)
  }

  method Schema() returns (s: CliTypes.CliSchema)
  {
    s := CliTypes.CliSchema(
      [
        CliTypes.OptionDecl("printf.help", [], ["help"], CliTypes.NoArg),
        CliTypes.OptionDecl("printf.version", [], ["version"], CliTypes.NoArg)
      ],
      true
    );
  }

  method ParserConfig() returns (cfg: CliTypes.ParseConfig)
  {
    cfg := CliTypes.ParseConfig(CliTypes.POSIX_StopAtFirst, false, true, true);
  }

  method Decode(p: CliTypes.ParsedArgs) returns (raw: PrintfCmdRaw)
  {
    var seenHelp := false;
    var seenVersion := false;
    var helpTokenIndex := -1;
    var versionTokenIndex := -1;
    var excessAfterRequest: CliTypes.OptionalString := CliTypes.None;
    var excessTokenIndex := -1;

    var i := 0;
    while i < |p.options|
      decreases |p.options| - i
    {
      var occ := p.options[i];
      if occ.key == "printf.help" {
        seenHelp := true;
        if helpTokenIndex == -1 || occ.tokenIndex < helpTokenIndex {
          helpTokenIndex := occ.tokenIndex;
        }
      }
      if occ.key == "printf.version" {
        seenVersion := true;
        if versionTokenIndex == -1 || occ.tokenIndex < versionTokenIndex {
          versionTokenIndex := occ.tokenIndex;
        }
      }
      i := i + 1;
    }

    var requestTokenIndex :=
      if seenHelp && (!seenVersion || helpTokenIndex <= versionTokenIndex) then
        helpTokenIndex
      else if seenVersion then
        versionTokenIndex
      else
        -1;

    if requestTokenIndex != -1 {
      i := 0;
      while i < |p.options|
        decreases |p.options| - i
      {
        var occ := p.options[i];
        if occ.tokenIndex > requestTokenIndex &&
           (excessTokenIndex == -1 || occ.tokenIndex < excessTokenIndex)
        {
          excessAfterRequest := CliTypes.Some(occ.rawToken);
          excessTokenIndex := occ.tokenIndex;
        }
        i := i + 1;
      }
      if excessAfterRequest.None? && |p.positionals| > 0 {
        excessAfterRequest := CliTypes.Some(p.positionals[0]);
      }
    }

    raw := PrintfCmdRaw(
      seenHelp,
      seenVersion,
      helpTokenIndex,
      versionTokenIndex,
      excessAfterRequest,
      p.positionals
    );
  }

  function ParseErrorText(e: CliTypes.ParseError): string
  {
    if e.kind == CliTypes.UnknownOption ||
       e.kind == CliTypes.UnexpectedValue ||
       e.kind == CliTypes.MissingValue then
      if |e.rawToken| > 2 && e.rawToken[0] == '-' && e.rawToken[1] == '-' then
        "printf: unrecognized option '" + e.rawToken + "'\n" +
        "Try 'printf --help' for more information.\n"
      else if |e.rawToken| > 1 && e.rawToken[0] == '-' then
        "printf: invalid option -- '" + [e.rawToken[1]] + "'\n" +
        "Try 'printf --help' for more information.\n"
      else
        "printf: invalid option\nTry 'printf --help' for more information.\n"
    else if e.kind == CliTypes.Ambiguous then
      "printf: option '" + e.rawToken + "' is ambiguous\n" +
      "Try 'printf --help' for more information.\n"
    else
      "printf: parse error at token '" + e.rawToken + "'\n"
  }

  method FormatParseError(e: CliTypes.ParseError) returns (b: BenchWorld.Bytes)
  {
    b := Utf8.Encode(ParseErrorText(e));
  }

  method PlanParseFailure(
    e: CliTypes.ParseError,
    argv: seq<string>
  ) returns (plan: CliTypes.CliPlan<PrintfCmdRaw>)
    decreases *
  {
    var msg := FormatParseError(e);
    plan := CliTypes.CliEarlyExit(1, [], msg);
  }
}
