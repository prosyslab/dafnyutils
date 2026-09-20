include "../../core/Utf8.dfy"
include "../../core/World.dfy"
include "../../core/CliTypes.dfy"

module MvSchema {
  import Utf8 = Utf8Semantics
  import BenchWorld
  import CliTypes

  datatype MvMode = ModeRun | ModeInvalidBackup | ModeInvalidUpdate | ModeHelp | ModeVersion
  datatype OverwriteMode = OverwriteDefault | OverwriteInteractive | OverwriteSkip
  datatype BackupMode = BackupOff | BackupSimple | BackupNumbered | BackupExisting
  datatype UpdateMode = UpdateAll | UpdateOlder | UpdateNone | UpdateNoneFail

  datatype MvCmdRaw = MvCmdRaw(
    noTargetDirectory: bool,
    overwriteMode: OverwriteMode,
    verbose: bool,
    debug: bool,
    exchange: bool,
    stripTrailingSlashes: bool,
    targetDirectory: string,
    backupMode: BackupMode,
    backupSuffix: string,
    updateMode: UpdateMode,
    seenHelp: bool,
    seenVersion: bool,
    helpTokenIndex: int,
    versionTokenIndex: int,
    invalidBackupArg: string,
    invalidBackupTokenIndex: int,
    invalidUpdateArg: string,
    invalidUpdateTokenIndex: int,
    operands: seq<string>
  )

  datatype MvCmd = MvCmd(
    mode: MvMode,
    noTargetDirectory: bool,
    overwriteMode: OverwriteMode,
    verbose: bool,
    debug: bool,
    exchange: bool,
    stripTrailingSlashes: bool,
    targetDirectory: string,
    backupMode: BackupMode,
    backupSuffix: string,
    updateMode: UpdateMode,
    invalidBackupArg: string,
    invalidUpdateArg: string,
    operands: seq<string>
  )

  function HasPrefix(text: string, prefix: string): bool
  {
    |prefix| <= |text| && text[..|prefix|] == prefix
  }

  function IsBackupOffWord(value: string): bool
  {
    value == "none" || value == "off"
  }

  function IsBackupSimpleWord(value: string): bool
  {
    value == "simple" || value == "never"
  }

  function IsBackupExistingWord(value: string): bool
  {
    value == "existing" || value == "nil"
  }

  function IsBackupNumberedWord(value: string): bool
  {
    value == "numbered" || value == "t"
  }

  function IsValidBackupControl(value: string): bool
  {
    IsBackupOffWord(value) || IsBackupSimpleWord(value) ||
    IsBackupExistingWord(value) || IsBackupNumberedWord(value)
  }

  function DecodeBackupControl(value: string): BackupMode
    requires IsValidBackupControl(value)
  {
    if IsBackupOffWord(value) then
      BackupOff
    else if IsBackupSimpleWord(value) then
      BackupSimple
    else if IsBackupExistingWord(value) then
      BackupExisting
    else
      BackupNumbered
  }

  function IsUpdateAllWord(value: string): bool
  {
    value == "all"
  }

  function IsUpdateOlderWord(value: string): bool
  {
    value == "older"
  }

  function IsUpdateNoneWord(value: string): bool
  {
    value == "none"
  }

  function IsUpdateNoneFailWord(value: string): bool
  {
    value == "none-fail"
  }

  function IsValidUpdateControl(value: string): bool
  {
    IsUpdateAllWord(value) || IsUpdateOlderWord(value) ||
    IsUpdateNoneWord(value) || IsUpdateNoneFailWord(value)
  }

  function DecodeUpdateControl(value: string): UpdateMode
    requires IsValidUpdateControl(value)
  {
    if IsUpdateAllWord(value) then
      UpdateAll
    else if IsUpdateNoneWord(value) then
      UpdateNone
    else if IsUpdateNoneFailWord(value) then
      UpdateNoneFail
    else
      UpdateOlder
  }

  function RequestedMode(raw: MvCmdRaw): MvMode
  {
    if raw.seenHelp && (!raw.seenVersion || raw.helpTokenIndex <= raw.versionTokenIndex) then
      ModeHelp
    else if raw.seenVersion then
      ModeVersion
    else
      ModeRun
  }

  function RequestedModeTokenIndex(raw: MvCmdRaw): int
  {
    if RequestedMode(raw) == ModeHelp then
      raw.helpTokenIndex
    else if RequestedMode(raw) == ModeVersion then
      raw.versionTokenIndex
    else
      -1
  }

  function BackupErrorTakesPrecedence(raw: MvCmdRaw): bool
  {
    raw.invalidBackupTokenIndex >= 0 &&
    (RequestedModeTokenIndex(raw) == -1 || raw.invalidBackupTokenIndex < RequestedModeTokenIndex(raw)) &&
    (raw.invalidUpdateTokenIndex == -1 || raw.invalidBackupTokenIndex <= raw.invalidUpdateTokenIndex)
  }

  function UpdateErrorTakesPrecedence(raw: MvCmdRaw): bool
  {
    raw.invalidUpdateTokenIndex >= 0 &&
    (RequestedModeTokenIndex(raw) == -1 || raw.invalidUpdateTokenIndex < RequestedModeTokenIndex(raw)) &&
    (raw.invalidBackupTokenIndex == -1 || raw.invalidUpdateTokenIndex < raw.invalidBackupTokenIndex)
  }

  function Command(raw: MvCmdRaw): MvCmd
  {
    var mode :=
      if BackupErrorTakesPrecedence(raw) then
        ModeInvalidBackup
      else if UpdateErrorTakesPrecedence(raw) then
        ModeInvalidUpdate
      else
        RequestedMode(raw);
    var verbose := raw.verbose || raw.debug;
    var suffix := if raw.backupSuffix == "" then "~" else raw.backupSuffix;
    MvCmd(
      mode,
      raw.noTargetDirectory,
      raw.overwriteMode,
      verbose,
      raw.debug,
      raw.exchange,
      raw.stripTrailingSlashes,
      raw.targetDirectory,
      raw.backupMode,
      suffix,
      raw.updateMode,
      raw.invalidBackupArg,
      raw.invalidUpdateArg,
      raw.operands
    )
  }

  method Schema() returns (s: CliTypes.CliSchema)
  {
    s := CliTypes.CliSchema(
      [
        CliTypes.OptionDecl("mv.force", ['f'], ["force"], CliTypes.NoArg),
        CliTypes.OptionDecl("mv.backup_short", ['b'], [], CliTypes.NoArg),
        CliTypes.OptionDecl("mv.backup_long", [], ["backup"], CliTypes.OptArg),
        CliTypes.OptionDecl("mv.debug", [], ["debug"], CliTypes.NoArg),
        CliTypes.OptionDecl("mv.no_clobber", ['n'], ["no-clobber"], CliTypes.NoArg),
        CliTypes.OptionDecl("mv.no_copy", [], ["no-copy"], CliTypes.NoArg),
        CliTypes.OptionDecl("mv.strip_trailing_slashes", [], ["strip-trailing-slashes"], CliTypes.NoArg),
        CliTypes.OptionDecl("mv.suffix", ['S'], ["suffix"], CliTypes.ReqArg),
        CliTypes.OptionDecl("mv.target_directory", ['t'], ["target-directory"], CliTypes.ReqArg),
        CliTypes.OptionDecl("mv.no_target_directory", ['T'], ["no-target-directory"], CliTypes.NoArg),
        CliTypes.OptionDecl("mv.update_short", ['u'], [], CliTypes.NoArg),
        CliTypes.OptionDecl("mv.update_long", [], ["update"], CliTypes.OptArg),
        CliTypes.OptionDecl("mv.verbose", ['v'], ["verbose"], CliTypes.NoArg),
        CliTypes.OptionDecl("mv.help", [], ["help"], CliTypes.NoArg),
        CliTypes.OptionDecl("mv.version", [], ["version"], CliTypes.NoArg)
      ],
      true
    );
  }

  method ParserConfig() returns (cfg: CliTypes.ParseConfig)
  {
    cfg := CliTypes.ParseConfig(CliTypes.GNU_Permute, true, true, true);
  }

  method Decode(p: CliTypes.ParsedArgs) returns (raw: MvCmdRaw)
  {
    var noTargetDirectory := false;
    var overwriteMode := OverwriteDefault;
    var verbose := false;
    var debug := false;
    var exchange := false;
    var stripTrailingSlashes := false;
    var targetDirectory := "";
    var backupMode := BackupOff;
    var backupSuffix := "";
    var updateMode := UpdateAll;
    var seenHelp := false;
    var seenVersion := false;
    var helpTokenIndex := -1;
    var versionTokenIndex := -1;
    var invalidBackupArg := "";
    var invalidBackupTokenIndex := -1;
    var invalidUpdateArg := "";
    var invalidUpdateTokenIndex := -1;

    var i := 0;
    while i < |p.options|
      decreases |p.options| - i
    {
      var occ := p.options[i];
      if occ.key == "mv.force" {
        overwriteMode := OverwriteDefault;
      }
      if occ.key == "mv.backup_short" {
        backupMode := BackupExisting;
      }
      if occ.key == "mv.backup_long" {
        match occ.value
        case Some(value) =>
          if IsValidBackupControl(value) {
            backupMode := DecodeBackupControl(value);
          } else if invalidBackupTokenIndex == -1 || occ.tokenIndex < invalidBackupTokenIndex {
            invalidBackupArg := value;
            invalidBackupTokenIndex := occ.tokenIndex;
          }
        case None =>
          backupMode := BackupExisting;
      }
      if occ.key == "mv.debug" {
        debug := true;
        verbose := true;
      }
      if occ.key == "mv.no_clobber" {
        overwriteMode := OverwriteSkip;
      }
      if occ.key == "mv.strip_trailing_slashes" {
        stripTrailingSlashes := true;
      }
      if occ.key == "mv.suffix" {
        match occ.value
        case Some(value) =>
          backupSuffix := value;
        case None =>
      }
      if occ.key == "mv.target_directory" {
        match occ.value
        case Some(value) =>
          targetDirectory := value;
        case None =>
      }
      if occ.key == "mv.no_target_directory" {
        noTargetDirectory := true;
      }
      if occ.key == "mv.update_short" {
        updateMode := UpdateOlder;
      }
      if occ.key == "mv.update_long" {
        match occ.value
        case Some(value) =>
          if IsValidUpdateControl(value) {
            updateMode := DecodeUpdateControl(value);
          } else if invalidUpdateTokenIndex == -1 || occ.tokenIndex < invalidUpdateTokenIndex {
            invalidUpdateArg := value;
            invalidUpdateTokenIndex := occ.tokenIndex;
          }
        case None =>
          updateMode := UpdateOlder;
      }
      if occ.key == "mv.verbose" {
        verbose := true;
      }
      if occ.key == "mv.help" {
        seenHelp := true;
        if helpTokenIndex == -1 || occ.tokenIndex < helpTokenIndex {
          helpTokenIndex := occ.tokenIndex;
        }
      }
      if occ.key == "mv.version" {
        seenVersion := true;
        if versionTokenIndex == -1 || occ.tokenIndex < versionTokenIndex {
          versionTokenIndex := occ.tokenIndex;
        }
      }
      i := i + 1;
    }

    raw := MvCmdRaw(
      noTargetDirectory,
      overwriteMode,
      verbose,
      debug,
      exchange,
      stripTrailingSlashes,
      targetDirectory,
      backupMode,
      backupSuffix,
      updateMode,
      seenHelp,
      seenVersion,
      helpTokenIndex,
      versionTokenIndex,
      invalidBackupArg,
      invalidBackupTokenIndex,
      invalidUpdateArg,
      invalidUpdateTokenIndex,
      p.positionals
    );
  }

  function ParseErrorText(e: CliTypes.ParseError): string
  {
    if e.kind == CliTypes.UnknownOption then
      if |e.rawToken| > 2 && e.rawToken[0] == '-' && e.rawToken[1] == '-' then
        "mv: unrecognized option '" + e.rawToken + "'\n" +
        "Try 'mv --help' for more information.\n"
      else if |e.rawToken| > 1 && e.rawToken[0] == '-' then
        "mv: invalid option -- '" + [e.rawToken[1]] + "'\n" +
        "Try 'mv --help' for more information.\n"
      else
        "mv: invalid option\nTry 'mv --help' for more information.\n"
    else if e.kind == CliTypes.Ambiguous then
      "mv: option '" + e.rawToken + "' is ambiguous\n" +
      "Try 'mv --help' for more information.\n"
    else if e.kind == CliTypes.MissingValue then
      if |e.rawToken| > 1 && e.rawToken[0] == '-' then
        "mv: option requires an argument -- '" +
        [e.rawToken[|e.rawToken| - 1]] + "'\n" +
        "Try 'mv --help' for more information.\n"
      else
        "mv: missing option value\nTry 'mv --help' for more information.\n"
    else
      "mv: " +
      (if e.kind == CliTypes.UnexpectedValue then
         "option does not take a value"
       else
         "parse error") +
      " at token '" + e.rawToken + "'\n"
  }

  method FormatParseError(e: CliTypes.ParseError) returns (b: BenchWorld.Bytes)
  {
    b := Utf8.Encode(ParseErrorText(e));
  }

  method PlanParseFailure(
    e: CliTypes.ParseError,
    argv: seq<string>
  ) returns (plan: CliTypes.CliPlan<MvCmdRaw>)
    decreases *
  {
    var msg := FormatParseError(e);
    plan := CliTypes.CliEarlyExit(1, [], msg);
  }
}
