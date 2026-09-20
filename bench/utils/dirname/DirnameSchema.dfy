include "../../core/Utf8.dfy"
include "../../core/World.dfy"
include "../../core/CliTypes.dfy"

module DirnameSchema {
  import Utf8 = Utf8Semantics
  import BenchWorld
  import CliTypes

  datatype DirnameCmdRaw = DirnameCmdRaw(
    seenZero: bool,
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
        CliTypes.OptionDecl("dirname.zero", ['z'], ["zero"], CliTypes.NoArg),
        CliTypes.OptionDecl("dirname.help", [], ["help"], CliTypes.NoArg),
        CliTypes.OptionDecl("dirname.version", [], ["version"], CliTypes.NoArg)
      ],
      true
    );
  }

  method ParserConfig() returns (cfg: CliTypes.ParseConfig)
  {
    cfg := CliTypes.ParseConfig(CliTypes.GNU_Permute, true, true, true);
  }

  method Decode(p: CliTypes.ParsedArgs) returns (raw: DirnameCmdRaw)
  {
    var seenZero := false;
    var seenHelp := false;
    var seenVersion := false;
    var helpTokenIndex := -1;
    var versionTokenIndex := -1;

    var i := 0;
    while i < |p.options|
      decreases |p.options| - i
    {
      var occ := p.options[i];
      if occ.key == "dirname.zero" {
        seenZero := true;
      }
      if occ.key == "dirname.help" {
        seenHelp := true;
        if helpTokenIndex == -1 || occ.tokenIndex < helpTokenIndex {
          helpTokenIndex := occ.tokenIndex;
        }
      }
      if occ.key == "dirname.version" {
        seenVersion := true;
        if versionTokenIndex == -1 || occ.tokenIndex < versionTokenIndex {
          versionTokenIndex := occ.tokenIndex;
        }
      }
      i := i + 1;
    }

    raw := DirnameCmdRaw(seenZero, seenHelp, seenVersion, helpTokenIndex, versionTokenIndex, p.positionals);
  }

  function ParseErrorText(e: CliTypes.ParseError): string
  {
    if e.kind == CliTypes.UnknownOption then
      if |e.rawToken| > 2 && e.rawToken[0] == '-' && e.rawToken[1] == '-' then
        "dirname: unrecognized option '" + e.rawToken + "'\n" +
        "Try 'dirname --help' for more information.\n"
      else if |e.rawToken| > 1 && e.rawToken[0] == '-' then
        "dirname: invalid option -- '" + [e.rawToken[1]] + "'\n" +
        "Try 'dirname --help' for more information.\n"
      else
        "dirname: invalid option\nTry 'dirname --help' for more information.\n"
    else if e.kind == CliTypes.Ambiguous then
      "dirname: option '" + e.rawToken + "' is ambiguous\n" +
      "Try 'dirname --help' for more information.\n"
    else
      "dirname: parse error at token '" + e.rawToken + "'\n"
  }

  method DirnameFormatParseError(e: CliTypes.ParseError) returns (b: BenchWorld.Bytes)
  {
    b := Utf8.Encode(ParseErrorText(e));
  }
}
