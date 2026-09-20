include "../../core/Utf8.dfy"
include "../../core/World.dfy"
include "../../core/CliTypes.dfy"

module DuSchema {
  import Utf8 = Utf8Semantics
  import BenchWorld
  import CliTypes

  datatype DuMode = ModeRun | ModeHelp | ModeVersion | ModeUnsupportedAccounting

  datatype DuCmdRaw = DuCmdRaw(
    seenApparentSize: bool,
    seenBytes: bool,
    seenBlockSize: bool,
    blockSize: string,
    seenSummarize: bool,
    seenHelp: bool,
    seenVersion: bool,
    helpTokenIndex: int,
    versionTokenIndex: int,
    operands: seq<string>
  )

  datatype DuCmd = DuCmd(
    mode: DuMode,
    byteCounts: bool,
    summarize: bool,
    operands: seq<string>
  )

  function RequestedByteCounts(raw: DuCmdRaw): bool
  {
    raw.seenBytes ||
    (raw.seenApparentSize && raw.seenBlockSize && raw.blockSize == "1")
  }

  function RequestedMode(raw: DuCmdRaw): DuMode
  {
    if raw.seenHelp && (!raw.seenVersion || raw.helpTokenIndex <= raw.versionTokenIndex) then
      ModeHelp
    else if raw.seenVersion then
      ModeVersion
    else if !RequestedByteCounts(raw) then
      ModeUnsupportedAccounting
    else
      ModeRun
  }

  function EffectiveOperands(raw: DuCmdRaw): seq<string>
  {
    if |raw.operands| == 0 then ["."] else raw.operands
  }

  function Command(raw: DuCmdRaw): DuCmd
  {
    DuCmd(RequestedMode(raw), RequestedByteCounts(raw), raw.seenSummarize, EffectiveOperands(raw))
  }

  method Schema() returns (s: CliTypes.CliSchema)
  {
    s := CliTypes.CliSchema(
      [
        CliTypes.OptionDecl("du.apparent_size", ['A'], ["apparent-size"], CliTypes.NoArg),
        CliTypes.OptionDecl("du.block_size", ['B'], ["block-size"], CliTypes.ReqArg),
        CliTypes.OptionDecl("du.bytes", ['b'], ["bytes"], CliTypes.NoArg),
        CliTypes.OptionDecl("du.summarize", ['s'], ["summarize"], CliTypes.NoArg),
        CliTypes.OptionDecl("du.help", [], ["help"], CliTypes.NoArg),
        CliTypes.OptionDecl("du.version", [], ["version"], CliTypes.NoArg)
      ],
      true
    );
  }

  method ParserConfig() returns (cfg: CliTypes.ParseConfig)
  {
    cfg := CliTypes.ParseConfig(CliTypes.GNU_Permute, true, true, true);
  }

  method Decode(p: CliTypes.ParsedArgs) returns (raw: DuCmdRaw)
  {
    var seenApparentSize := false;
    var seenBytes := false;
    var seenBlockSize := false;
    var blockSize := "";
    var seenSummarize := false;
    var seenHelp := false;
    var seenVersion := false;
    var helpTokenIndex := -1;
    var versionTokenIndex := -1;

    var i := 0;
    while i < |p.options|
      decreases |p.options| - i
    {
      var occ := p.options[i];
      if occ.key == "du.apparent_size" {
        seenApparentSize := true;
      }
      if occ.key == "du.block_size" {
        match occ.value
        case Some(value) =>
          seenBlockSize := true;
          blockSize := value;
        case None =>
      }
      if occ.key == "du.bytes" {
        seenBytes := true;
        seenApparentSize := true;
        seenBlockSize := true;
        blockSize := "1";
      }
      if occ.key == "du.summarize" {
        seenSummarize := true;
      }
      if occ.key == "du.help" {
        seenHelp := true;
        if helpTokenIndex == -1 || occ.tokenIndex < helpTokenIndex {
          helpTokenIndex := occ.tokenIndex;
        }
      }
      if occ.key == "du.version" {
        seenVersion := true;
        if versionTokenIndex == -1 || occ.tokenIndex < versionTokenIndex {
          versionTokenIndex := occ.tokenIndex;
        }
      }
      i := i + 1;
    }

    raw := DuCmdRaw(
      seenApparentSize,
      seenBytes,
      seenBlockSize,
      blockSize,
      seenSummarize,
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
        "du: unrecognized option '" + e.rawToken + "'\n" +
        "Try 'du --help' for more information.\n"
      else if |e.rawToken| > 1 && e.rawToken[0] == '-' then
        "du: invalid option -- '" + [e.rawToken[1]] + "'\n" +
        "Try 'du --help' for more information.\n"
      else
        "du: invalid option\nTry 'du --help' for more information.\n"
    else if e.kind == CliTypes.MissingValue then
      if |e.rawToken| > 2 && e.rawToken[0] == '-' && e.rawToken[1] == '-' then
        "du: option '" + e.rawToken + "' requires an argument\n" +
        "Try 'du --help' for more information.\n"
      else if |e.rawToken| > 1 && e.rawToken[0] == '-' then
        "du: option requires an argument -- '" + [e.rawToken[1]] + "'\n" +
        "Try 'du --help' for more information.\n"
      else
        "du: option requires an argument\nTry 'du --help' for more information.\n"
    else
      "du: option '" + e.rawToken + "' is ambiguous\n" +
      "Try 'du --help' for more information.\n"
  }

  method ParseErrorMessage(e: CliTypes.ParseError) returns (message: BenchWorld.Bytes)
  {
    message := Utf8.Encode(ParseErrorText(e));
  }
}
