include "../../core/Utf8.dfy"
include "../../core/World.dfy"
include "../../core/CliTypes.dfy"

module PasteSchema {
  import Utf8 = Utf8Semantics
  import BenchWorld
  import CliTypes

  datatype PasteMode = ModeRun | ModeHelp | ModeVersion
  datatype Input = Stdin | File(path: BenchWorld.Path)

  datatype PasteCmdRaw = PasteCmdRaw(
    delimiter: CliTypes.OptionalString,
    serial: bool,
    zeroTerminated: bool,
    seenHelp: bool,
    seenVersion: bool,
    helpTokenIndex: int,
    versionTokenIndex: int,
    operands: seq<string>
  )

  datatype PasteCmd = PasteCmd(
    mode: PasteMode,
    delimiterText: string,
    serial: bool,
    zeroTerminated: bool,
    inputs: seq<Input>
  )

  function InputsFromOperands(operands: seq<string>): seq<Input>
    decreases |operands|
  {
    if |operands| == 0 then
      []
    else
      [(if operands[0] == "-" then Stdin else File(operands[0]))] +
      InputsFromOperands(operands[1..])
  }

  function Command(raw: PasteCmdRaw): PasteCmd
  {
    var mode :=
      if raw.seenHelp && (!raw.seenVersion || raw.helpTokenIndex <= raw.versionTokenIndex) then
        ModeHelp
      else if raw.seenVersion then
        ModeVersion
      else
        ModeRun;
    var delimiterText :=
      match raw.delimiter
      case Some(value) => value
      case None => "\t";
    var inputs := InputsFromOperands(raw.operands);
    var runInputs := if mode == ModeRun && |inputs| == 0 then [Stdin] else inputs;
    PasteCmd(mode, delimiterText, raw.serial, raw.zeroTerminated, runInputs)
  }

  method Schema() returns (s: CliTypes.CliSchema)
  {
    s := CliTypes.CliSchema(
      [
        CliTypes.OptionDecl("paste.delimiters", ['d'], ["delimiters"], CliTypes.ReqArg),
        CliTypes.OptionDecl("paste.serial", ['s'], ["serial"], CliTypes.NoArg),
        CliTypes.OptionDecl("paste.zero_terminated", ['z'], ["zero-terminated"], CliTypes.NoArg),
        CliTypes.OptionDecl("paste.help", [], ["help"], CliTypes.NoArg),
        CliTypes.OptionDecl("paste.version", [], ["version"], CliTypes.NoArg)
      ],
      true
    );
  }

  method ParserConfig() returns (cfg: CliTypes.ParseConfig)
  {
    cfg := CliTypes.ParseConfig(CliTypes.GNU_Permute, true, true, true);
  }

  method Decode(p: CliTypes.ParsedArgs) returns (raw: PasteCmdRaw)
  {
    var delimiter: CliTypes.OptionalString := CliTypes.None;
    var serial := false;
    var zeroTerminated := false;
    var seenHelp := false;
    var seenVersion := false;
    var helpTokenIndex := -1;
    var versionTokenIndex := -1;

    var i := 0;
    while i < |p.options|
      decreases |p.options| - i
    {
      var occ := p.options[i];
      if occ.key == "paste.delimiters" {
        delimiter := occ.value;
      }
      if occ.key == "paste.serial" {
        serial := true;
      }
      if occ.key == "paste.zero_terminated" {
        zeroTerminated := true;
      }
      if occ.key == "paste.help" {
        seenHelp := true;
        if helpTokenIndex == -1 || occ.tokenIndex < helpTokenIndex {
          helpTokenIndex := occ.tokenIndex;
        }
      }
      if occ.key == "paste.version" {
        seenVersion := true;
        if versionTokenIndex == -1 || occ.tokenIndex < versionTokenIndex {
          versionTokenIndex := occ.tokenIndex;
        }
      }
      i := i + 1;
    }

    raw := PasteCmdRaw(
      delimiter,
      serial,
      zeroTerminated,
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
        "paste: unrecognized option '" + e.rawToken + "'\n" +
        "Try 'paste --help' for more information.\n"
      else if |e.rawToken| > 1 && e.rawToken[0] == '-' then
        "paste: invalid option -- '" + [e.rawToken[1]] + "'\n" +
        "Try 'paste --help' for more information.\n"
      else
        "paste: invalid option\nTry 'paste --help' for more information.\n"
    else if e.kind == CliTypes.MissingValue then
      if |e.rawToken| > 2 && e.rawToken[0] == '-' && e.rawToken[1] == '-' then
        "paste: option '" + e.rawToken + "' requires an argument\n" +
        "Try 'paste --help' for more information.\n"
      else if |e.rawToken| > 1 && e.rawToken[0] == '-' then
        "paste: option requires an argument -- '" + [e.rawToken[1]] + "'\n" +
        "Try 'paste --help' for more information.\n"
      else
        "paste: option requires an argument\nTry 'paste --help' for more information.\n"
    else if e.kind == CliTypes.Ambiguous then
      "paste: option '" + e.rawToken + "' is ambiguous\n" +
      "Try 'paste --help' for more information.\n"
    else
      "paste: parse error at token '" + e.rawToken + "'\n"
  }

  method FormatParseError(e: CliTypes.ParseError) returns (b: BenchWorld.Bytes)
  {
    b := Utf8.Encode(ParseErrorText(e));
  }

  method PlanParseFailure(
    e: CliTypes.ParseError,
    argv: seq<string>
  ) returns (plan: CliTypes.CliPlan<PasteCmdRaw>)
    decreases *
  {
    var msg := FormatParseError(e);
    plan := CliTypes.CliEarlyExit(1, [], msg);
  }
}
