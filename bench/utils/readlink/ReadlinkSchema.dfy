include "../../core/Utf8.dfy"
include "../../core/World.dfy"
include "../../core/CliTypes.dfy"

module ReadlinkSchema {
  import Utf8 = Utf8Semantics
  import BenchWorld
  import CliTypes

  datatype ReadlinkMode = ModeRun | ModeHelp | ModeVersion | ModeUnsupportedCanonicalize

  datatype ReadlinkCmdRaw = ReadlinkCmdRaw(
    seenCanonicalize: bool,
    seenCanonicalizeExisting: bool,
    seenCanonicalizeMissing: bool,
    seenNoNewline: bool,
    seenZero: bool,
    diagnosticMode: int,
    seenHelp: bool,
    seenVersion: bool,
    helpTokenIndex: int,
    versionTokenIndex: int,
    operands: seq<string>
  )

  datatype ReadlinkCmd = ReadlinkCmd(
    mode: ReadlinkMode,
    noNewline: bool,
    zeroTerminated: bool,
    verbose: bool,
    operands: seq<string>
  )

  function RequestedMode(raw: ReadlinkCmdRaw): ReadlinkMode
  {
    if raw.seenHelp && (!raw.seenVersion || raw.helpTokenIndex <= raw.versionTokenIndex) then
      ModeHelp
    else if raw.seenVersion then
      ModeVersion
    else if raw.seenCanonicalize || raw.seenCanonicalizeExisting || raw.seenCanonicalizeMissing then
      ModeUnsupportedCanonicalize
    else
      ModeRun
  }

  function Command(raw: ReadlinkCmdRaw): ReadlinkCmd
  {
    ReadlinkCmd(
      RequestedMode(raw),
      raw.seenNoNewline,
      raw.seenZero,
      raw.diagnosticMode == 1,
      raw.operands
    )
  }

  method Schema() returns (s: CliTypes.CliSchema)
  {
    s := CliTypes.CliSchema(
      [
        CliTypes.OptionDecl("readlink.canonicalize", ['f'], ["canonicalize"], CliTypes.NoArg),
        CliTypes.OptionDecl("readlink.canonicalize_existing", ['e'], ["canonicalize-existing"], CliTypes.NoArg),
        CliTypes.OptionDecl("readlink.canonicalize_missing", ['m'], ["canonicalize-missing"], CliTypes.NoArg),
        CliTypes.OptionDecl("readlink.no_newline", ['n'], ["no-newline"], CliTypes.NoArg),
        CliTypes.OptionDecl("readlink.quiet", ['q'], ["quiet"], CliTypes.NoArg),
        CliTypes.OptionDecl("readlink.silent", ['s'], ["silent"], CliTypes.NoArg),
        CliTypes.OptionDecl("readlink.verbose", ['v'], ["verbose"], CliTypes.NoArg),
        CliTypes.OptionDecl("readlink.zero", ['z'], ["zero"], CliTypes.NoArg),
        CliTypes.OptionDecl("readlink.help", [], ["help"], CliTypes.NoArg),
        CliTypes.OptionDecl("readlink.version", [], ["version"], CliTypes.NoArg)
      ],
      true
    );
  }

  method ParserConfig() returns (cfg: CliTypes.ParseConfig)
  {
    cfg := CliTypes.ParseConfig(CliTypes.GNU_Permute, true, true, true);
  }

  method Decode(p: CliTypes.ParsedArgs) returns (raw: ReadlinkCmdRaw)
  {
    var seenCanonicalize := false;
    var seenCanonicalizeExisting := false;
    var seenCanonicalizeMissing := false;
    var seenNoNewline := false;
    var seenZero := false;
    var diagnosticMode := 0;
    var seenHelp := false;
    var seenVersion := false;
    var helpTokenIndex := -1;
    var versionTokenIndex := -1;

    var i := 0;
    while i < |p.options|
      decreases |p.options| - i
    {
      var occ := p.options[i];
      if occ.key == "readlink.canonicalize" {
        seenCanonicalize := true;
      }
      if occ.key == "readlink.canonicalize_existing" {
        seenCanonicalizeExisting := true;
      }
      if occ.key == "readlink.canonicalize_missing" {
        seenCanonicalizeMissing := true;
      }
      if occ.key == "readlink.no_newline" {
        seenNoNewline := true;
      }
      if occ.key == "readlink.zero" {
        seenZero := true;
      }
      if occ.key == "readlink.quiet" || occ.key == "readlink.silent" {
        diagnosticMode := 0;
      }
      if occ.key == "readlink.verbose" {
        diagnosticMode := 1;
      }
      if occ.key == "readlink.help" {
        seenHelp := true;
        if helpTokenIndex == -1 || occ.tokenIndex < helpTokenIndex {
          helpTokenIndex := occ.tokenIndex;
        }
      }
      if occ.key == "readlink.version" {
        seenVersion := true;
        if versionTokenIndex == -1 || occ.tokenIndex < versionTokenIndex {
          versionTokenIndex := occ.tokenIndex;
        }
      }
      i := i + 1;
    }

    raw := ReadlinkCmdRaw(
      seenCanonicalize,
      seenCanonicalizeExisting,
      seenCanonicalizeMissing,
      seenNoNewline,
      seenZero,
      diagnosticMode,
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
        "readlink: unrecognized option '" + e.rawToken + "'\n" +
        "Try 'readlink --help' for more information.\n"
      else if |e.rawToken| > 1 && e.rawToken[0] == '-' then
        "readlink: invalid option -- '" + [e.rawToken[1]] + "'\n" +
        "Try 'readlink --help' for more information.\n"
      else
        "readlink: invalid option\nTry 'readlink --help' for more information.\n"
    else if e.kind == CliTypes.Ambiguous then
      "readlink: option '" + e.rawToken + "' is ambiguous\n" +
      "Try 'readlink --help' for more information.\n"
    else
      "readlink: parse error at token '" + e.rawToken + "'\n"
  }

  method FormatParseError(e: CliTypes.ParseError) returns (b: BenchWorld.Bytes)
  {
    b := Utf8.Encode(ParseErrorText(e));
  }

  method PlanParseFailure(
    e: CliTypes.ParseError,
    argv: seq<string>
  ) returns (plan: CliTypes.CliPlan<ReadlinkCmdRaw>)
    decreases *
  {
    var msg := FormatParseError(e);
    plan := CliTypes.CliEarlyExit(1, [], msg);
  }
}
