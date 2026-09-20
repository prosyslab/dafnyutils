include "../../core/Utf8.dfy"
include "../../core/World.dfy"
include "../../core/CliTypes.dfy"

module WcSchema {
  import Utf8 = Utf8Semantics
  import BenchWorld
  import CliTypes

  datatype WcMode = ModeRun | ModeHelp | ModeVersion
  datatype Input = Stdin(displayName: string) | File(path: BenchWorld.Path)

  datatype WcCmdRaw = WcCmdRaw(
    seenLines: bool,
    seenWords: bool,
    seenChars: bool,
    seenBytes: bool,
    seenMaxLineLength: bool,
    seenHelp: bool,
    seenVersion: bool,
    helpTokenIndex: int,
    versionTokenIndex: int,
    operands: seq<string>
  )

  datatype WcCmd = WcCmd(
    mode: WcMode,
    showLines: bool,
    showWords: bool,
    showChars: bool,
    showBytes: bool,
    showMaxLineLength: bool,
    inputs: seq<Input>
  )

  method Schema() returns (s: CliTypes.CliSchema)
  {
    s := CliTypes.CliSchema(
      [
        CliTypes.OptionDecl("wc.lines", ['l'], ["lines"], CliTypes.NoArg),
        CliTypes.OptionDecl("wc.words", ['w'], ["words"], CliTypes.NoArg),
        CliTypes.OptionDecl("wc.chars", ['m'], ["chars"], CliTypes.NoArg),
        CliTypes.OptionDecl("wc.bytes", ['c'], ["bytes"], CliTypes.NoArg),
        CliTypes.OptionDecl("wc.max_line_length", ['L'], ["max-line-length"], CliTypes.NoArg),
        CliTypes.OptionDecl("wc.help", [], ["help"], CliTypes.NoArg),
        CliTypes.OptionDecl("wc.version", [], ["version"], CliTypes.NoArg)
      ],
      true
    );
  }

  method ParserConfig() returns (cfg: CliTypes.ParseConfig)
  {
    cfg := CliTypes.ParseConfig(CliTypes.GNU_Permute, true, true, true);
  }

  method Decode(p: CliTypes.ParsedArgs) returns (raw: WcCmdRaw)
  {
    var seenLines := false;
    var seenWords := false;
    var seenChars := false;
    var seenBytes := false;
    var seenMaxLineLength := false;
    var seenHelp := false;
    var seenVersion := false;
    var helpTokenIndex := -1;
    var versionTokenIndex := -1;

    var i := 0;
    while i < |p.options|
      decreases |p.options| - i
    {
      var occ := p.options[i];
      if occ.key == "wc.lines" {
        seenLines := true;
      }
      if occ.key == "wc.words" {
        seenWords := true;
      }
      if occ.key == "wc.chars" {
        seenChars := true;
      }
      if occ.key == "wc.bytes" {
        seenBytes := true;
      }
      if occ.key == "wc.max_line_length" {
        seenMaxLineLength := true;
      }
      if occ.key == "wc.help" {
        seenHelp := true;
        if helpTokenIndex == -1 || occ.tokenIndex < helpTokenIndex {
          helpTokenIndex := occ.tokenIndex;
        }
      }
      if occ.key == "wc.version" {
        seenVersion := true;
        if versionTokenIndex == -1 || occ.tokenIndex < versionTokenIndex {
          versionTokenIndex := occ.tokenIndex;
        }
      }
      i := i + 1;
    }

    raw := WcCmdRaw(
      seenLines,
      seenWords,
      seenChars,
      seenBytes,
      seenMaxLineLength,
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
        "wc: unrecognized option '" + e.rawToken + "'\n" +
        "Try 'wc --help' for more information.\n"
      else if |e.rawToken| > 1 && e.rawToken[0] == '-' then
        "wc: invalid option -- '" + [e.rawToken[1]] + "'\n" +
        "Try 'wc --help' for more information.\n"
      else
        "wc: invalid option\nTry 'wc --help' for more information.\n"
    else if e.kind == CliTypes.Ambiguous then
      "wc: option '" + e.rawToken + "' is ambiguous\n" +
      "Try 'wc --help' for more information.\n"
    else
      "wc: parse error at token '" + e.rawToken + "'\n"
  }

  method FormatParseError(e: CliTypes.ParseError) returns (b: BenchWorld.Bytes)
  {
    b := Utf8.Encode(ParseErrorText(e));
  }

  method PlanParseFailure(
    e: CliTypes.ParseError,
    argv: seq<string>
  ) returns (plan: CliTypes.CliPlan<WcCmdRaw>)
    decreases *
  {
    var msg := FormatParseError(e);
    plan := CliTypes.CliEarlyExit(1, [], msg);
  }
}
