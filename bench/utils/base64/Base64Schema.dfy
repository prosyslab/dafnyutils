include "../../core/Utf8.dfy"
include "../../core/World.dfy"
include "../../core/CliTypes.dfy"

module Base64Schema {
  import Utf8 = Utf8Semantics
  import BenchWorld
  import CliTypes

  datatype Base64Mode = ModeRun | ModeHelp | ModeVersion | ModeInvalidWrap | ModeExtraOperand(operand: string)
  datatype Input = Stdin | File(path: BenchWorld.Path)
  datatype WidthArg = WidthArg(text: string, tokenIndex: int)

  datatype Base64CmdRaw = Base64CmdRaw(
    seenDecode: bool,
    seenIgnoreGarbage: bool,
    seenHelp: bool,
    seenVersion: bool,
    helpTokenIndex: int,
    versionTokenIndex: int,
    wrapArgs: seq<WidthArg>,
    operands: seq<string>
  )

  datatype Base64Cmd = Base64Cmd(
    mode: Base64Mode,
    decode: bool,
    ignoreGarbage: bool,
    wrapWidth: nat,
    invalidWrapValue: string,
    inputs: seq<Input>
  )

  method Schema() returns (s: CliTypes.CliSchema)
  {
    s := CliTypes.CliSchema(
      [
        CliTypes.OptionDecl("base64.decode", ['d'], ["decode"], CliTypes.NoArg),
        CliTypes.OptionDecl("base64.ignore_garbage", ['i'], ["ignore-garbage"], CliTypes.NoArg),
        CliTypes.OptionDecl("base64.wrap", ['w'], ["wrap"], CliTypes.ReqArg),
        CliTypes.OptionDecl("base64.help", [], ["help"], CliTypes.NoArg),
        CliTypes.OptionDecl("base64.version", [], ["version"], CliTypes.NoArg)
      ],
      true
    );
  }

  method ParserConfig() returns (cfg: CliTypes.ParseConfig)
  {
    cfg := CliTypes.ParseConfig(CliTypes.GNU_Permute, true, true, true);
  }

  method Decode(p: CliTypes.ParsedArgs) returns (raw: Base64CmdRaw)
  {
    var seenDecode := false;
    var seenIgnoreGarbage := false;
    var seenHelp := false;
    var seenVersion := false;
    var helpTokenIndex := -1;
    var versionTokenIndex := -1;
    var wrapArgs: seq<WidthArg> := [];

    var i := 0;
    while i < |p.options|
      decreases |p.options| - i
    {
      var occ := p.options[i];
      if occ.key == "base64.decode" {
        seenDecode := true;
      }
      if occ.key == "base64.ignore_garbage" {
        seenIgnoreGarbage := true;
      }
      if occ.key == "base64.wrap" {
        match occ.value
        case Some(value) =>
          wrapArgs := wrapArgs + [WidthArg(value, occ.tokenIndex)];
        case None =>
      }
      if occ.key == "base64.help" {
        seenHelp := true;
        if helpTokenIndex == -1 || occ.tokenIndex < helpTokenIndex {
          helpTokenIndex := occ.tokenIndex;
        }
      }
      if occ.key == "base64.version" {
        seenVersion := true;
        if versionTokenIndex == -1 || occ.tokenIndex < versionTokenIndex {
          versionTokenIndex := occ.tokenIndex;
        }
      }
      i := i + 1;
    }

    raw := Base64CmdRaw(
      seenDecode,
      seenIgnoreGarbage,
      seenHelp,
      seenVersion,
      helpTokenIndex,
      versionTokenIndex,
      wrapArgs,
      p.positionals
    );
  }

  function TryHelpText(): string
  {
    "Try 'base64 --help' for more information.\n"
  }

  function ParseErrorText(e: CliTypes.ParseError): string
  {
    if e.kind == CliTypes.UnknownOption || e.kind == CliTypes.UnexpectedValue then
      if |e.rawToken| > 2 && e.rawToken[0] == '-' && e.rawToken[1] == '-' then
        "base64: unrecognized option '" + e.rawToken + "'\n" + TryHelpText()
      else if |e.rawToken| > 1 && e.rawToken[0] == '-' then
        "base64: invalid option -- '" + [e.rawToken[1]] + "'\n" + TryHelpText()
      else
        "base64: invalid option\n" + TryHelpText()
    else if e.kind == CliTypes.MissingValue then
      if |e.rawToken| > 2 && e.rawToken[0] == '-' && e.rawToken[1] == '-' then
        "base64: option '" + e.rawToken + "' requires an argument\n" + TryHelpText()
      else if |e.rawToken| > 1 && e.rawToken[0] == '-' then
        "base64: option requires an argument -- '" + [e.rawToken[1]] + "'\n" + TryHelpText()
      else
        "base64: option requires an argument\n" + TryHelpText()
    else if e.kind == CliTypes.Ambiguous then
      "base64: option '" + e.rawToken + "' is ambiguous\n" + TryHelpText()
    else
      "base64: parse error at token '" + e.rawToken + "'\n"
  }

  method Base64FormatParseError(e: CliTypes.ParseError) returns (b: BenchWorld.Bytes)
  {
    b := Utf8.Encode(ParseErrorText(e));
  }
}
