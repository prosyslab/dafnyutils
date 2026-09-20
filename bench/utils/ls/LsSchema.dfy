include "../../core/Utf8.dfy"
include "../../core/World.dfy"
include "../../core/CliTypes.dfy"

module LsSchema {
  import Utf8 = Utf8Semantics
  import BenchWorld
  import CliTypes

  datatype LsMode =
    ModeRun | ModeHelp | ModeVersion |
    ModeInvalidBlockSize(value: string) | ModeInvalidTime(value: string) |
    ModeInvalidTimeStyle(value: string)
  datatype HiddenMode = HideDotFiles | AlmostAll | All
  datatype SortMode = SortName | SortSize | SortTime
  datatype TimeField = ModificationTime | AccessTime | ChangeTime
  datatype FollowMode = FollowNever | FollowCommandLine | FollowAlways
  datatype TimeStyle = DefaultC | FullIso | LongIso | Iso | EpochSeconds
  datatype PositiveNatParse = PositiveNat(value: nat) | InvalidPositiveNat

  datatype LsCmdRaw = LsCmdRaw(
    hiddenMode: HiddenMode,
    listDirectories: bool,
    numericLong: bool,
    showBlocks: bool,
    seenBlockSize: bool,
    blockSizeText: string,
    seenTimeStyle: bool,
    timeStyleText: string,
    sortMode: SortMode,
    reverse: bool,
    timeField: TimeField,
    immediateMode: LsMode,
    followMode: FollowMode,
    recursive: bool,
    operands: seq<string>
  )

  datatype LsCmd = LsCmd(
    mode: LsMode,
    hiddenMode: HiddenMode,
    listDirectories: bool,
    numericLong: bool,
    showBlocks: bool,
    cliBlockSize: nat,
    fileSizeBlockSize: nat,
    timeStyle: TimeStyle,
    referenceNow: int,
    sortMode: SortMode,
    reverse: bool,
    timeField: TimeField,
    followMode: FollowMode,
    recursive: bool,
    operands: seq<string>
  )

  function DecimalDigitValue(ch: char): nat
    requires '0' <= ch <= '9'
  {
    ((ch as int) - ('0' as int)) as nat
  }

  function ParsePositiveFrom(text: string, i: nat, value: nat): PositiveNatParse
    requires i <= |text|
    decreases |text| - i
  {
    if i == |text| then
      if value == 0 then InvalidPositiveNat else PositiveNat(value)
    else if !('0' <= text[i] <= '9') then
      InvalidPositiveNat
    else
      ParsePositiveFrom(text, i + 1, value * 10 + DecimalDigitValue(text[i]))
  }

  function ParsePositive(text: string): PositiveNatParse
  {
    if |text| == 0 then InvalidPositiveNat else ParsePositiveFrom(text, 0, 0)
  }

  function ParsedBlockSize(raw: LsCmdRaw): nat
  {
    if !raw.seenBlockSize then 0
    else
      match ParsePositive(raw.blockSizeText)
      case PositiveNat(value) => value
      case InvalidPositiveNat => 0
  }

  function RequestedMode(raw: LsCmdRaw): LsMode
  {
    if !raw.immediateMode.ModeRun? then
      raw.immediateMode
    else if raw.numericLong && raw.seenTimeStyle &&
            raw.timeStyleText != "+%s" && raw.timeStyleText != "full-iso" &&
            raw.timeStyleText != "long-iso" && raw.timeStyleText != "iso" &&
            raw.timeStyleText != "locale" && raw.timeStyleText != "posix-full-iso" &&
            raw.timeStyleText != "posix-long-iso" && raw.timeStyleText != "posix-iso" &&
            raw.timeStyleText != "posix-locale" then
      ModeInvalidTimeStyle(raw.timeStyleText)
    else
      ModeRun
  }

  function EffectiveOperands(raw: LsCmdRaw): seq<string>
  {
    if |raw.operands| == 0 then ["."] else raw.operands
  }

  function Command(raw: LsCmdRaw): LsCmd
  {
    LsCmd(
      RequestedMode(raw),
      raw.hiddenMode,
      raw.listDirectories,
      raw.numericLong,
      raw.showBlocks,
      ParsedBlockSize(raw),
      if ParsedBlockSize(raw) > 0 then ParsedBlockSize(raw) else 1,
      if !raw.seenTimeStyle then DefaultC
      else if raw.timeStyleText == "+%s" then EpochSeconds
      else if raw.timeStyleText == "full-iso" then FullIso
      else if raw.timeStyleText == "long-iso" then LongIso
      else if raw.timeStyleText == "iso" then Iso
      else DefaultC,
      0,
      raw.sortMode,
      raw.reverse,
      raw.timeField,
      raw.followMode,
      raw.recursive,
      EffectiveOperands(raw)
    )
  }

  function WithBlockSize(
    cmd: LsCmd, blockSize: nat, fileSizeBlockSize: nat
  ): LsCmd
    requires blockSize > 0
    requires fileSizeBlockSize > 0
  {
    LsCmd(
      cmd.mode,
      cmd.hiddenMode,
      cmd.listDirectories,
      cmd.numericLong,
      cmd.showBlocks,
      blockSize,
      fileSizeBlockSize,
      cmd.timeStyle,
      cmd.referenceNow,
      cmd.sortMode,
      cmd.reverse,
      cmd.timeField,
      cmd.followMode,
      cmd.recursive,
      cmd.operands
    )
  }

  function WithReferenceNow(cmd: LsCmd, referenceNow: int): LsCmd
  {
    LsCmd(
      cmd.mode, cmd.hiddenMode, cmd.listDirectories, cmd.numericLong,
      cmd.showBlocks, cmd.cliBlockSize, cmd.fileSizeBlockSize,
      cmd.timeStyle, referenceNow,
      cmd.sortMode, cmd.reverse, cmd.timeField, cmd.followMode,
      cmd.recursive, cmd.operands)
  }

  method Schema() returns (s: CliTypes.CliSchema)
  {
    s := CliTypes.CliSchema(
      [
        CliTypes.OptionDecl("ls.all", ['a'], ["all"], CliTypes.NoArg),
        CliTypes.OptionDecl("ls.almost_all", ['A'], ["almost-all"], CliTypes.NoArg),
        CliTypes.OptionDecl("ls.directory", ['d'], ["directory"], CliTypes.NoArg),
        CliTypes.OptionDecl("ls.numeric_long", ['n'], ["numeric-uid-gid"], CliTypes.NoArg),
        CliTypes.OptionDecl("ls.blocks", ['s'], ["size"], CliTypes.NoArg),
        CliTypes.OptionDecl("ls.block_size", [], ["block-size"], CliTypes.ReqArg),
        CliTypes.OptionDecl("ls.time_style", [], ["time-style"], CliTypes.ReqArg),
        CliTypes.OptionDecl("ls.sort_size", ['S'], [], CliTypes.NoArg),
        CliTypes.OptionDecl("ls.sort_time", ['t'], [], CliTypes.NoArg),
        CliTypes.OptionDecl("ls.reverse", ['r'], ["reverse"], CliTypes.NoArg),
        CliTypes.OptionDecl("ls.access_time", ['u'], [], CliTypes.NoArg),
        CliTypes.OptionDecl("ls.change_time", ['c'], [], CliTypes.NoArg),
        CliTypes.OptionDecl("ls.time", [], ["time"], CliTypes.ReqArg),
        CliTypes.OptionDecl("ls.follow_command", ['H'], ["dereference-command-line"], CliTypes.NoArg),
        CliTypes.OptionDecl("ls.follow_all", ['L'], ["dereference"], CliTypes.NoArg),
        CliTypes.OptionDecl("ls.recursive", ['R'], ["recursive"], CliTypes.NoArg),
        CliTypes.OptionDecl("ls.help", [], ["help"], CliTypes.NoArg),
        CliTypes.OptionDecl("ls.version", [], ["version"], CliTypes.NoArg)
      ],
      true
    );
  }

  method ParserConfig() returns (cfg: CliTypes.ParseConfig)
  {
    cfg := CliTypes.ParseConfig(CliTypes.GNU_Permute, true, true, true);
  }

  method Decode(p: CliTypes.ParsedArgs) returns (raw: LsCmdRaw)
  {
    var hiddenMode := HideDotFiles;
    var listDirectories := false;
    var numericLong := false;
    var showBlocks := false;
    var seenBlockSize := false;
    var blockSizeText := "";
    var seenTimeStyle := false;
    var timeStyleText := "";
    var sortMode := SortName;
    var reverse := false;
    var timeField := ModificationTime;
    var immediateMode := ModeRun;
    var followMode := FollowNever;
    var recursive := false;
    var i := 0;
    while i < |p.options|
      invariant 0 <= i <= |p.options|
      decreases |p.options| - i
    {
      var occ := p.options[i];
      if occ.key == "ls.all" {
        hiddenMode := All;
      }
      if occ.key == "ls.almost_all" {
        hiddenMode := AlmostAll;
      }
      if occ.key == "ls.directory" {
        listDirectories := true;
      }
      if occ.key == "ls.numeric_long" {
        numericLong := true;
      }
      if occ.key == "ls.blocks" {
        showBlocks := true;
      }
      if occ.key == "ls.block_size" {
        match occ.value
        case Some(value) =>
          seenBlockSize := true;
          blockSizeText := value;
          if immediateMode.ModeRun? && ParsePositive(value).InvalidPositiveNat? {
            immediateMode := ModeInvalidBlockSize(value);
          }
        case None =>
      }
      if occ.key == "ls.time_style" {
        match occ.value
        case Some(value) =>
          seenTimeStyle := true;
          timeStyleText := value;
        case None =>
      }
      if occ.key == "ls.sort_size" {
        sortMode := SortSize;
      }
      if occ.key == "ls.sort_time" {
        sortMode := SortTime;
      }
      if occ.key == "ls.reverse" {
        reverse := true;
      }
      if occ.key == "ls.access_time" {
        timeField := AccessTime;
      }
      if occ.key == "ls.change_time" {
        timeField := ChangeTime;
      }
      if occ.key == "ls.time" {
        match occ.value
        case Some(value) =>
          if value == "atime" || value == "access" || value == "use" {
            timeField := AccessTime;
          } else if value == "ctime" || value == "status" {
            timeField := ChangeTime;
          } else if value == "mtime" || value == "modification" {
            timeField := ModificationTime;
          } else {
            if immediateMode.ModeRun? {
              immediateMode := ModeInvalidTime(value);
            }
          }
        case None =>
      }
      if occ.key == "ls.follow_command" {
        followMode := FollowCommandLine;
      }
      if occ.key == "ls.follow_all" {
        followMode := FollowAlways;
      }
      if occ.key == "ls.recursive" {
        recursive := true;
      }
      if occ.key == "ls.help" {
        if immediateMode.ModeRun? {
          immediateMode := ModeHelp;
        }
      }
      if occ.key == "ls.version" {
        if immediateMode.ModeRun? {
          immediateMode := ModeVersion;
        }
      }
      i := i + 1;
    }
    raw := LsCmdRaw(
      hiddenMode,
      listDirectories,
      numericLong,
      showBlocks,
      seenBlockSize,
      blockSizeText,
      seenTimeStyle,
      timeStyleText,
      sortMode,
      reverse,
      timeField,
      immediateMode,
      followMode,
      recursive,
      p.positionals
    );
  }

  function ParseErrorText(e: CliTypes.ParseError): string
  {
    if e.kind == CliTypes.UnknownOption || e.kind == CliTypes.UnexpectedValue then
      if |e.rawToken| > 2 && e.rawToken[0] == '-' && e.rawToken[1] == '-' then
        "ls: unrecognized option '" + e.rawToken + "'\n" +
        "Try 'ls --help' for more information.\n"
      else if |e.rawToken| > 1 && e.rawToken[0] == '-' then
        "ls: invalid option -- '" + [e.rawToken[1]] + "'\n" +
        "Try 'ls --help' for more information.\n"
      else
        "ls: invalid option\nTry 'ls --help' for more information.\n"
    else if e.kind == CliTypes.MissingValue then
      "ls: option requires an argument\nTry 'ls --help' for more information.\n"
    else
      "ls: option '" + e.rawToken + "' is ambiguous\n" +
      "Try 'ls --help' for more information.\n"
  }

  method FormatParseError(e: CliTypes.ParseError) returns (message: BenchWorld.Bytes)
  {
    message := Utf8.Encode(ParseErrorText(e));
  }

  method PlanParseFailure(
    e: CliTypes.ParseError,
    argv: seq<string>
  ) returns (plan: CliTypes.CliPlan<LsCmdRaw>)
    decreases *
  {
    var message := FormatParseError(e);
    plan := CliTypes.CliEarlyExit(1, [], message);
  }
}
