include "../../core/World.dfy"
include "../../core/CliTypes.dfy"
include "../../core/Utf8.dfy"

module TouchSchema {
  import Utf8 = Utf8Semantics
  import BenchWorld
  import CliTypes

  datatype TouchMode = ModeRun | ModeInvalidTime | ModeAmbiguousTime | ModeHelp | ModeVersion

  datatype TouchCmdRaw = TouchCmdRaw(
    seenNoCreate: bool,
    seenNoDereference: bool,
    seenAtime: bool,
    seenMtime: bool,
    seenHelp: bool,
    seenVersion: bool,
    helpTokenIndex: int,
    versionTokenIndex: int,
    hasDate: bool,
    hasReference: bool,
    hasTimestamp: bool,
    dateArg: string,
    referenceArg: string,
    timestampArg: string,
    timeArg: string,
    timeTokenIndex: int,
    timeErrorArg: string,
    timeErrorTokenIndex: int,
    timeErrorAmbiguous: bool,
    operands: seq<string>
  )

  datatype TouchCmd = TouchCmd(
    mode: TouchMode,
    noCreate: bool,
    followSymlink: bool,
    touchAtime: bool,
    touchMtime: bool,
    hasDate: bool,
    hasReference: bool,
    hasTimestamp: bool,
    dateArg: string,
    referenceArg: string,
    timestampArg: string,
    timeArg: string,
    files: seq<string>
  )

  datatype TimeWord = TimeWordAccess | TimeWordModify | TimeWordInvalid | TimeWordAmbiguous
  datatype TimeSelection = TimeBoth | TimeAccess | TimeModify
  datatype TimeSource =
    | TimeSourceCurrent
    | TimeSourceFixed(atimeSec: int, atimeNsec: int, mtimeSec: int, mtimeNsec: int)

  function HasPrefix(text: string, prefix: string): bool
  {
    |prefix| <= |text| && text[..|prefix|] == prefix
  }

  function MatchesAccessTimeWord(value: string): bool
  {
    value != "" &&
    (HasPrefix("access", value) || HasPrefix("atime", value) || HasPrefix("use", value))
  }

  function MatchesModifyTimeWord(value: string): bool
  {
    value != "" &&
    (HasPrefix("modify", value) || HasPrefix("mtime", value))
  }

  function ClassifyTimeWord(value: string): TimeWord
  {
    if MatchesAccessTimeWord(value) && !MatchesModifyTimeWord(value) then
      TimeWordAccess
    else if MatchesModifyTimeWord(value) && !MatchesAccessTimeWord(value) then
      TimeWordModify
    else if MatchesAccessTimeWord(value) || MatchesModifyTimeWord(value) || value == "" then
      TimeWordAmbiguous
    else
      TimeWordInvalid
  }

  function RequestedMode(raw: TouchCmdRaw): TouchMode
  {
    if raw.seenHelp && (!raw.seenVersion || raw.helpTokenIndex <= raw.versionTokenIndex) then
      ModeHelp
    else if raw.seenVersion then
      ModeVersion
    else
      ModeRun
  }

  function RequestedModeTokenIndex(raw: TouchCmdRaw): int
  {
    if RequestedMode(raw) == ModeHelp then
      raw.helpTokenIndex
    else if RequestedMode(raw) == ModeVersion then
      raw.versionTokenIndex
    else
      -1
  }

  function TimeErrorTakesPrecedence(raw: TouchCmdRaw): bool
  {
    raw.timeErrorTokenIndex >= 0 &&
    (RequestedModeTokenIndex(raw) == -1 || raw.timeErrorTokenIndex < RequestedModeTokenIndex(raw))
  }

  function Command(raw: TouchCmdRaw): TouchCmd
  {
    var mode :=
      if TimeErrorTakesPrecedence(raw) then
        if raw.timeErrorAmbiguous then ModeAmbiguousTime else ModeInvalidTime
      else
        RequestedMode(raw);
    var timeArg :=
      if TimeErrorTakesPrecedence(raw) then
        raw.timeErrorArg
      else
        raw.timeArg;
    TouchCmd(
      mode,
      raw.seenNoCreate,
      !raw.seenNoDereference,
      raw.seenAtime,
      raw.seenMtime,
      raw.hasDate,
      raw.hasReference,
      raw.hasTimestamp,
      raw.dateArg,
      raw.referenceArg,
      raw.timestampArg,
      timeArg,
      raw.operands
    )
  }

  method Schema() returns (s: CliTypes.CliSchema)
  {
    s := CliTypes.CliSchema(
      [
        CliTypes.OptionDecl("touch.atime", ['a'], [], CliTypes.NoArg),
        CliTypes.OptionDecl("touch.no_create", ['c'], ["no-create"], CliTypes.NoArg),
        CliTypes.OptionDecl("touch.date", ['d'], ["date"], CliTypes.ReqArg),
        CliTypes.OptionDecl("touch.ignored_f", ['f'], [], CliTypes.NoArg),
        CliTypes.OptionDecl("touch.no_dereference", ['h'], ["no-dereference"], CliTypes.NoArg),
        CliTypes.OptionDecl("touch.mtime", ['m'], [], CliTypes.NoArg),
        CliTypes.OptionDecl("touch.reference", ['r'], ["reference"], CliTypes.ReqArg),
        CliTypes.OptionDecl("touch.timestamp", ['t'], [], CliTypes.ReqArg),
        CliTypes.OptionDecl("touch.time", [], ["time"], CliTypes.ReqArg),
        CliTypes.OptionDecl("touch.help", [], ["help"], CliTypes.NoArg),
        CliTypes.OptionDecl("touch.version", [], ["version"], CliTypes.NoArg)
      ],
      true
    );
  }

  method ParserConfig() returns (cfg: CliTypes.ParseConfig)
  {
    cfg := CliTypes.ParseConfig(CliTypes.GNU_Permute, true, true, true);
  }

  method Decode(p: CliTypes.ParsedArgs) returns (raw: TouchCmdRaw)
  {
    var seenNoCreate := false;
    var seenNoDereference := false;
    var seenAtime := false;
    var seenMtime := false;
    var seenHelp := false;
    var seenVersion := false;
    var helpTokenIndex := -1;
    var versionTokenIndex := -1;
    var hasDate := false;
    var hasReference := false;
    var hasTimestamp := false;
    var dateArg := "";
    var referenceArg := "";
    var timestampArg := "";
    var timeArg := "";
    var timeTokenIndex := -1;
    var timeErrorArg := "";
    var timeErrorTokenIndex := -1;
    var timeErrorAmbiguous := false;

    var i := 0;
    while i < |p.options|
      decreases |p.options| - i
    {
      var occ := p.options[i];
      if occ.key == "touch.atime" {
        seenAtime := true;
      }
      if occ.key == "touch.no_create" {
        seenNoCreate := true;
      }
      if occ.key == "touch.date" {
        match occ.value
        case Some(value) =>
          hasDate := true;
          dateArg := value;
        case None =>
      }
      if occ.key == "touch.no_dereference" {
        seenNoDereference := true;
      }
      if occ.key == "touch.mtime" {
        seenMtime := true;
      }
      if occ.key == "touch.reference" {
        match occ.value
        case Some(value) =>
          hasReference := true;
          referenceArg := value;
        case None =>
      }
      if occ.key == "touch.timestamp" {
        match occ.value
        case Some(value) =>
          hasTimestamp := true;
          timestampArg := value;
        case None =>
      }
      if occ.key == "touch.time" {
        match occ.value
        case Some(value) =>
          var timeWord := ClassifyTimeWord(value);
          if timeWord == TimeWordAccess || timeWord == TimeWordModify {
            seenAtime := seenAtime || timeWord == TimeWordAccess;
            seenMtime := seenMtime || timeWord == TimeWordModify;
            if timeTokenIndex == -1 || occ.tokenIndex >= timeTokenIndex {
              timeArg := value;
              timeTokenIndex := occ.tokenIndex;
            }
          } else if timeErrorTokenIndex == -1 || occ.tokenIndex < timeErrorTokenIndex {
            timeErrorArg := value;
            timeErrorTokenIndex := occ.tokenIndex;
            timeErrorAmbiguous := timeWord == TimeWordAmbiguous;
          }
        case None =>
      }
      if occ.key == "touch.help" {
        seenHelp := true;
        if helpTokenIndex == -1 || occ.tokenIndex < helpTokenIndex {
          helpTokenIndex := occ.tokenIndex;
        }
      }
      if occ.key == "touch.version" {
        seenVersion := true;
        if versionTokenIndex == -1 || occ.tokenIndex < versionTokenIndex {
          versionTokenIndex := occ.tokenIndex;
        }
      }
      i := i + 1;
    }

    raw := TouchCmdRaw(
      seenNoCreate,
      seenNoDereference,
      seenAtime,
      seenMtime,
      seenHelp,
      seenVersion,
      helpTokenIndex,
      versionTokenIndex,
      hasDate,
      hasReference,
      hasTimestamp,
      dateArg,
      referenceArg,
      timestampArg,
      timeArg,
      timeTokenIndex,
      timeErrorArg,
      timeErrorTokenIndex,
      timeErrorAmbiguous,
      p.positionals
    );
  }

  function IsMissingShortRequiredArgument(e: CliTypes.ParseError): bool
  {
    e.kind == CliTypes.MissingValue &&
    |e.rawToken| > 1 &&
    e.rawToken[0] == '-' &&
    e.rawToken[1] != '-' &&
    e.rawToken[|e.rawToken| - 1] in {'d', 'r', 't'}
  }

  function MissingLongRequiredOption(e: CliTypes.ParseError): string
  {
    if |e.rawToken| <= 2 then "" else
    var option := e.rawToken[2..];
    if HasPrefix("date", option) then
      "date"
    else if HasPrefix("reference", option) then
      "reference"
    else if HasPrefix("time", option) then
      "time"
    else
      ""
  }

  function IsMissingLongRequiredArgument(e: CliTypes.ParseError): bool
  {
    e.kind == CliTypes.MissingValue &&
    |e.rawToken| > 2 &&
    e.rawToken[0] == '-' &&
    e.rawToken[1] == '-' &&
    MissingLongRequiredOption(e) != ""
  }

  function ParseErrorText(e: CliTypes.ParseError): string
  {
    if IsMissingShortRequiredArgument(e) then
      "touch: option requires an argument -- '" + [e.rawToken[|e.rawToken| - 1]] + "'\n" +
      "Try 'touch --help' for more information.\n"
    else if IsMissingLongRequiredArgument(e) then
      "touch: option '--" + MissingLongRequiredOption(e) + "' requires an argument\n" +
      "Try 'touch --help' for more information.\n"
    else if e.kind == CliTypes.UnknownOption then
      if |e.rawToken| > 2 && e.rawToken[0] == '-' && e.rawToken[1] == '-' then
        "touch: unrecognized option '" + e.rawToken + "'\n" +
        "Try 'touch --help' for more information.\n"
      else if |e.rawToken| > 1 && e.rawToken[0] == '-' then
        "touch: invalid option -- '" + [e.rawToken[1]] + "'\n" +
        "Try 'touch --help' for more information.\n"
      else
        "touch: invalid option\nTry 'touch --help' for more information.\n"
    else if e.kind == CliTypes.Ambiguous then
      "touch: option '" + e.rawToken + "' is ambiguous\n" +
      "Try 'touch --help' for more information.\n"
    else
      "touch: " +
      (if e.kind == CliTypes.MissingValue
       then (if |e.rawToken| > 2 && e.rawToken[0] == '-' && e.rawToken[1] == '-'
             then "missing option value"
             else "missing short option value")
       else if e.kind == CliTypes.UnexpectedValue
         then "option does not take a value"
         else "parse error") +
      " at token '" + e.rawToken + "'\n"
  }

  method FormatParseError(e: CliTypes.ParseError) returns (b: BenchWorld.Bytes)
    ensures b == Utf8.Encode(ParseErrorText(e))
  {
    b := Utf8.Encode(ParseErrorText(e));
  }

  method PlanParseFailure(
    e: CliTypes.ParseError,
    argv: seq<string>
  ) returns (plan: CliTypes.CliPlan<TouchCmdRaw>)
    ensures plan == CliTypes.CliEarlyExit(1, [], Utf8.Encode(ParseErrorText(e)))
    decreases *
  {
    var msg := FormatParseError(e);
    plan := CliTypes.CliEarlyExit(1, [], msg);
  }
}
