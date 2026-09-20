include "../../core/Utf8.dfy"
include "../../core/World.dfy"
include "../../core/CliTypes.dfy"

module CommSchema {
  import Utf8 = Utf8Semantics
  import BenchWorld
  import CliTypes

  datatype CommMode =
    | ModeRun
    | ModeHelp
    | ModeVersion
    | ModeMissingOperand
    | ModeMissingOperandAfter(operand: string)
    | ModeExtraOperand(operand: string)
    | ModeMultipleOutputDelimiters
    | ModeRepeatedStdinOperand

  datatype CommInput = Stdin | File(path: BenchWorld.Path)

  datatype CommCmdRaw = CommCmdRaw(
    suppress1: bool,
    suppress2: bool,
    suppress3: bool,
    total: bool,
    zeroTerminated: bool,
    outputDelimiters: seq<string>,
    seenHelp: bool,
    seenVersion: bool,
    helpTokenIndex: int,
    versionTokenIndex: int,
    operands: seq<string>
  )

  datatype CommCmd = CommCmd(
    mode: CommMode,
    suppress1: bool,
    suppress2: bool,
    suppress3: bool,
    total: bool,
    zeroTerminated: bool,
    outputDelimiter: BenchWorld.Bytes,
    input1: CommInput,
    input2: CommInput
  )

  method Schema() returns (s: CliTypes.CliSchema)
  {
    s := CliTypes.CliSchema(
      [
        CliTypes.OptionDecl("comm.suppress1", ['1'], [], CliTypes.NoArg),
        CliTypes.OptionDecl("comm.suppress2", ['2'], [], CliTypes.NoArg),
        CliTypes.OptionDecl("comm.suppress3", ['3'], [], CliTypes.NoArg),
        CliTypes.OptionDecl("comm.total", [], ["total"], CliTypes.NoArg),
        CliTypes.OptionDecl("comm.zero_terminated", ['z'], ["zero-terminated"], CliTypes.NoArg),
        CliTypes.OptionDecl("comm.output_delimiter", [], ["output-delimiter"], CliTypes.ReqArg),
        CliTypes.OptionDecl("comm.help", [], ["help"], CliTypes.NoArg),
        CliTypes.OptionDecl("comm.version", [], ["version"], CliTypes.NoArg)
      ],
      true
    );
  }

  method ParserConfig() returns (cfg: CliTypes.ParseConfig)
  {
    cfg := CliTypes.ParseConfig(CliTypes.GNU_Permute, true, true, true);
  }

  method Decode(p: CliTypes.ParsedArgs) returns (raw: CommCmdRaw)
  {
    var suppress1 := false;
    var suppress2 := false;
    var suppress3 := false;
    var total := false;
    var zeroTerminated := false;
    var outputDelimiters: seq<string> := [];
    var seenHelp := false;
    var seenVersion := false;
    var helpTokenIndex := -1;
    var versionTokenIndex := -1;

    var i := 0;
    while i < |p.options|
      decreases |p.options| - i
    {
      var occ := p.options[i];
      if occ.key == "comm.suppress1" {
        suppress1 := true;
      }
      if occ.key == "comm.suppress2" {
        suppress2 := true;
      }
      if occ.key == "comm.suppress3" {
        suppress3 := true;
      }
      if occ.key == "comm.total" {
        total := true;
      }
      if occ.key == "comm.zero_terminated" {
        zeroTerminated := true;
      }
      if occ.key == "comm.output_delimiter" {
        match occ.value
        case Some(value) =>
          outputDelimiters := outputDelimiters + [value];
        case None =>
          outputDelimiters := outputDelimiters + [""];
      }
      if occ.key == "comm.help" {
        seenHelp := true;
        if helpTokenIndex == -1 || occ.tokenIndex < helpTokenIndex {
          helpTokenIndex := occ.tokenIndex;
        }
      }
      if occ.key == "comm.version" {
        seenVersion := true;
        if versionTokenIndex == -1 || occ.tokenIndex < versionTokenIndex {
          versionTokenIndex := occ.tokenIndex;
        }
      }
      i := i + 1;
    }

    raw := CommCmdRaw(
      suppress1,
      suppress2,
      suppress3,
      total,
      zeroTerminated,
      outputDelimiters,
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
        "comm: unrecognized option '" + e.rawToken + "'\n" +
        "Try 'comm --help' for more information.\n"
      else if |e.rawToken| > 1 && e.rawToken[0] == '-' then
        "comm: invalid option -- '" + [e.rawToken[1]] + "'\n" +
        "Try 'comm --help' for more information.\n"
      else
        "comm: invalid option\nTry 'comm --help' for more information.\n"
    else if e.kind == CliTypes.MissingValue then
      "comm: option '" + e.rawToken + "' requires an argument\n" +
      "Try 'comm --help' for more information.\n"
    else if e.kind == CliTypes.Ambiguous then
      "comm: option '" + e.rawToken + "' is ambiguous\n" +
      "Try 'comm --help' for more information.\n"
    else
      "comm: parse error at token '" + e.rawToken + "'\n"
  }

  method CommFormatParseError(e: CliTypes.ParseError) returns (b: BenchWorld.Bytes)
  {
    b := Utf8.Encode(ParseErrorText(e));
  }

  method PlanParseFailure(
    e: CliTypes.ParseError,
    argv: seq<string>
  ) returns (plan: CliTypes.CliPlan<CommCmdRaw>)
    decreases *
  {
    var msg := CommFormatParseError(e);
    plan := CliTypes.CliEarlyExit(1, [], msg);
  }
}
