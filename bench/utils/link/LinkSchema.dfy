include "../../core/CliTypes.dfy"

module LinkSchema {
  import CliTypes

  datatype LinkMode = ModeRun | ModeHelp | ModeVersion | ModeExtraOperand(operand: string)
  
  datatype LinkCmdRaw = LinkCmdRaw(
    mode: LinkMode,
    operands: seq<string>
  )

  method Schema() returns (schema: CliTypes.CliSchema)
  {
    schema := CliTypes.CliSchema([
      CliTypes.OptionDecl("link.help", [], ["help"], CliTypes.NoArg),
      CliTypes.OptionDecl("link.version", [], ["version"], CliTypes.NoArg)
    ], true);
  }

  method ParserConfig() returns (cfg: CliTypes.ParseConfig)
  {
    cfg := CliTypes.ParseConfig(CliTypes.GNU_Permute, false, true, true);
  }

  method Decode(parsed: CliTypes.ParsedArgs) returns (raw: LinkCmdRaw)
  {
    var seenHelp := false;
    var seenVersion := false;
    var helpTokenIndex := -1;
    var versionTokenIndex := -1;
    var i := 0;
    while i < |parsed.options|
      decreases |parsed.options| - i
    {
      var option := parsed.options[i];

      if option.key == "link.help" {
        seenHelp := true;
        if helpTokenIndex == -1 || option.tokenIndex < helpTokenIndex {
          helpTokenIndex := option.tokenIndex;
        }
      }
      if option.key == "link.version" {
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
      else if |parsed.positionals| > 2 then
        ModeExtraOperand(parsed.positionals[2])
      else
        ModeRun;

    raw := LinkCmdRaw(mode, parsed.positionals);
  }
}
