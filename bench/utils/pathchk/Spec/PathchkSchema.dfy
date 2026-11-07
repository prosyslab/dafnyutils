include "../../../core/CliTypes.dfy"

module PathchkSchema {
  import CliTypes

  datatype PathchkMode = ModeRun | ModeHelp | ModeVersion | ModeMissingOperand

  datatype PathchkCmdRaw = PathchkCmdRaw(
    mode: PathchkMode,
    checkBasicPortability: bool,
    checkExtraPortability: bool,
    operands: seq<string>
  )

  method Schema() returns (schema: CliTypes.CliSchema)
  {
    schema := CliTypes.CliSchema([
                                   CliTypes.OptionDecl("pathchk.basic_portability", ['p'], [], CliTypes.NoArg),
                                   CliTypes.OptionDecl("pathchk.extra_portability", ['P'], [], CliTypes.NoArg),
                                   CliTypes.OptionDecl("pathchk.portability", [], ["portability"], CliTypes.NoArg),
                                   CliTypes.OptionDecl("pathchk.help", [], ["help"], CliTypes.NoArg),
                                   CliTypes.OptionDecl("pathchk.version", [], ["version"], CliTypes.NoArg)
                                 ], true);
  }

  method ParserConfig() returns (cfg: CliTypes.ParseConfig)
  {
    cfg := CliTypes.ParseConfig(CliTypes.POSIX_StopAtFirst, true, true, true);
  }

  method Decode(parsed: CliTypes.ParsedArgs) returns (raw: PathchkCmdRaw)
  {
    var checkBasicPortability := false;
    var checkExtraPortability := false;
    var seenHelp := false;
    var seenVersion := false;
    var helpTokenIndex := -1;
    var versionTokenIndex := -1;
    var i := 0;
    while i < |parsed.options|
      decreases |parsed.options| - i
    {
      var option := parsed.options[i];

      if option.key == "pathchk.basic_portability" || option.key == "pathchk.portability" {
        checkBasicPortability := true;
      }
      if option.key == "pathchk.extra_portability" || option.key == "pathchk.portability" {
        checkExtraPortability := true;
      }
      if option.key == "pathchk.help" {
        seenHelp := true;
        if helpTokenIndex == -1 || option.tokenIndex < helpTokenIndex {
          helpTokenIndex := option.tokenIndex;
        }
      }
      if option.key == "pathchk.version" {
        seenVersion := true;
        if versionTokenIndex == -1 || option.tokenIndex < versionTokenIndex {
          versionTokenIndex := option.tokenIndex;
        }
      }

      i := i + 1;
    }
    var mode := if seenHelp && (!seenVersion || helpTokenIndex <= versionTokenIndex) then
      ModeHelp
    else if seenVersion then
      ModeVersion
    else if |parsed.positionals| == 0 then
      ModeMissingOperand
    else
      ModeRun;

    raw := PathchkCmdRaw(mode, checkBasicPortability, checkExtraPortability, parsed.positionals);
  }
}
