include "../../core/Utf8.dfy"
include "../../core/World.dfy"
include "../../core/CliTypes.dfy"

module CatSchema {
  import Utf8 = Utf8Semantics
  import BenchWorld
  import CliTypes

  datatype CatMode = ModeRun | ModeHelp | ModeVersion
  datatype NumberMode = NoNumber | NumberAll | NumberNonBlank
  datatype Input = Stdin | File(path: BenchWorld.Path)

  datatype CatCmdRaw = CatCmdRaw(
    seenN: bool,
    seenB: bool,
    seenS: bool,
    seenA: bool,
    seenE: bool,
    seenShowEnds: bool,
    seenT: bool,
    seenShowTabs: bool,
    seenV: bool,
    seenHelp: bool,
    seenVersion: bool,
    helpTokenIndex: int,
    versionTokenIndex: int,
    operands: seq<string>
  )

  datatype CatCmd = CatCmd(
    mode: CatMode,
    number: NumberMode,
    squeezeBlank: bool,
    showEnds: bool,
    showTabs: bool,
    showNonPrinting: bool,
    inputs: seq<Input>
  )

  method Schema() returns (s: CliTypes.CliSchema)
  {
    s := CliTypes.CliSchema(
      [
        CliTypes.OptionDecl("cat.show_all", ['A'], ["show-all"], CliTypes.NoArg),
        CliTypes.OptionDecl("cat.number_nonblank", ['b'], ["number-nonblank"], CliTypes.NoArg),
        CliTypes.OptionDecl("cat.show_nonprinting_ends", ['e'], [], CliTypes.NoArg),
        CliTypes.OptionDecl("cat.show_ends", ['E'], ["show-ends"], CliTypes.NoArg),
        CliTypes.OptionDecl("cat.number_all", ['n'], ["number"], CliTypes.NoArg),
        CliTypes.OptionDecl("cat.squeeze_blank", ['s'], ["squeeze-blank"], CliTypes.NoArg),
        CliTypes.OptionDecl("cat.show_nonprinting_tabs", ['t'], [], CliTypes.NoArg),
        CliTypes.OptionDecl("cat.show_tabs", ['T'], ["show-tabs"], CliTypes.NoArg),
        CliTypes.OptionDecl("cat.unbuffered", ['u'], [], CliTypes.NoArg),
        CliTypes.OptionDecl("cat.show_nonprinting", ['v'], ["show-nonprinting"], CliTypes.NoArg),
        CliTypes.OptionDecl("cat.help", [], ["help"], CliTypes.NoArg),
        CliTypes.OptionDecl("cat.version", [], ["version"], CliTypes.NoArg)
      ],
      true
    );
  }

  method ParserConfig() returns (cfg: CliTypes.ParseConfig)
  {
    cfg := CliTypes.ParseConfig(CliTypes.GNU_Permute, true, true, true);
  }

  method Decode(p: CliTypes.ParsedArgs) returns (raw: CatCmdRaw)
  {
    var seenN := false;
    var seenB := false;
    var seenS := false;
    var seenA := false;
    var seenE := false;
    var seenShowEnds := false;
    var seenT := false;
    var seenShowTabs := false;
    var seenV := false;
    var seenHelp := false;
    var seenVersion := false;
    var helpTokenIndex := -1;
    var versionTokenIndex := -1;

    var i := 0;
    while i < |p.options|
      decreases |p.options| - i
    {
      var occ := p.options[i];
      var key := occ.key;
      if key == "cat.number_all" {
        seenN := true;
      }
      if key == "cat.number_nonblank" {
        seenB := true;
      }
      if key == "cat.squeeze_blank" {
        seenS := true;
      }
      if key == "cat.show_all" {
        seenA := true;
      }
      if key == "cat.show_nonprinting_ends" {
        seenE := true;
      }
      if key == "cat.show_ends" {
        seenShowEnds := true;
      }
      if key == "cat.show_nonprinting_tabs" {
        seenT := true;
      }
      if key == "cat.show_tabs" {
        seenShowTabs := true;
      }
      if key == "cat.show_nonprinting" {
        seenV := true;
      }
      if key == "cat.help" {
        seenHelp := true;
        if helpTokenIndex == -1 || occ.tokenIndex < helpTokenIndex {
          helpTokenIndex := occ.tokenIndex;
        }
      }
      if key == "cat.version" {
        seenVersion := true;
        if versionTokenIndex == -1 || occ.tokenIndex < versionTokenIndex {
          versionTokenIndex := occ.tokenIndex;
        }
      }
      i := i + 1;
    }

    raw := CatCmdRaw(
      seenN,
      seenB,
      seenS,
      seenA,
      seenE,
      seenShowEnds,
      seenT,
      seenShowTabs,
      seenV,
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
        "cat: unrecognized option '" + e.rawToken + "'\n" +
        "Try 'cat --help' for more information.\n"
      else if |e.rawToken| > 1 && e.rawToken[0] == '-' then
        "cat: invalid option -- '" + [e.rawToken[1]] + "'\n" +
        "Try 'cat --help' for more information.\n"
      else
        "cat: invalid option\nTry 'cat --help' for more information.\n"
    else if e.kind == CliTypes.Ambiguous then
      "cat: option '" + e.rawToken + "' is ambiguous\n" +
      "Try 'cat --help' for more information.\n"
    else
      "cat: " +
      (if e.kind == CliTypes.MissingValue
       then (if |e.rawToken| > 2
             then "missing option value"
             else "missing short option value")
       else if e.kind == CliTypes.UnexpectedValue
         then "option does not take a value"
         else "parse error") +
      " at token '" + e.rawToken + "'\n"
  }

  method CatFormatParseError(e: CliTypes.ParseError) returns (b: BenchWorld.Bytes)
  {
    b := Utf8.Encode(ParseErrorText(e));
  }

  method PlanParseFailure(
    e: CliTypes.ParseError,
    argv: seq<string>
  ) returns (plan: CliTypes.CliPlan<CatCmdRaw>)
    decreases *
  {
    var msg := CatFormatParseError(e);
    plan := CliTypes.CliEarlyExit(1, [], msg);
  }
}
