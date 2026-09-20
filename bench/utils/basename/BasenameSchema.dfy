include "../../core/Utf8.dfy"
include "../../core/World.dfy"
include "../../core/CliTypes.dfy"

module BasenameSchema {
  import Utf8 = Utf8Semantics
  import BenchWorld
  import CliTypes

  datatype BasenameMode = ModeRun | ModeHelp | ModeVersion

  datatype BasenameCmdRaw = BasenameCmdRaw(
    seenMultiple: bool,
    suffix: CliTypes.OptionalString,
    seenZero: bool,
    seenHelp: bool,
    seenVersion: bool,
    helpTokenIndex: int,
    versionTokenIndex: int,
    operands: seq<string>
  )

  datatype BasenameCmd = BasenameCmd(
    mode: BasenameMode,
    multiple: bool,
    suffix: CliTypes.OptionalString,
    zeroTerminated: bool,
    operands: seq<string>
  )

  function Command(raw: BasenameCmdRaw): BasenameCmd
  {
    var mode :=
      if raw.seenHelp && (!raw.seenVersion || raw.helpTokenIndex <= raw.versionTokenIndex) then
        ModeHelp
      else if raw.seenVersion then
        ModeVersion
      else
        ModeRun;
    BasenameCmd(mode, raw.seenMultiple, raw.suffix, raw.seenZero, raw.operands)
  }

  method Schema() returns (s: CliTypes.CliSchema)
  {
    s := CliTypes.CliSchema(
      [
        CliTypes.OptionDecl("basename.multiple", ['a'], ["multiple"], CliTypes.NoArg),
        CliTypes.OptionDecl("basename.suffix", ['s'], ["suffix"], CliTypes.ReqArg),
        CliTypes.OptionDecl("basename.zero", ['z'], ["zero"], CliTypes.NoArg),
        CliTypes.OptionDecl("basename.help", [], ["help"], CliTypes.NoArg),
        CliTypes.OptionDecl("basename.version", [], ["version"], CliTypes.NoArg)
      ],
      true
    );
  }

  method ParserConfig() returns (cfg: CliTypes.ParseConfig)
  {
    cfg := CliTypes.ParseConfig(CliTypes.POSIX_StopAtFirst, true, true, true);
  }

  function HasPrefix(text: string, prefix: string): bool
  {
    |prefix| <= |text| && text[..|prefix|] == prefix
  }

  function IsSuffixLongOptionNeedingValue(token: string): bool
  {
    |token| > 2 &&
    token[0] == '-' &&
    token[1] == '-' &&
    var name := token[2..];
    0 < |name| && HasPrefix("suffix", name)
  }

  method DecodeEarlySpecial(argv: seq<string>, stopTokenIndex: int) returns (found: bool, raw: BasenameCmdRaw)
    requires 0 <= stopTokenIndex <= |argv|
  {
    var seenHelp := false;
    var seenVersion := false;
    var helpTokenIndex := -1;
    var versionTokenIndex := -1;

    var i := if stopTokenIndex == 0 then 0 else 1;
    while i < stopTokenIndex
      invariant 0 <= i <= stopTokenIndex
      invariant stopTokenIndex > 0 ==> 1 <= i
      decreases stopTokenIndex - i
    {
      var token := argv[i];
      if token == "--" || token == "-" {
        i := i + 1;
        break;
      }

      if token == "--help" {
        seenHelp := true;
        if helpTokenIndex == -1 {
          helpTokenIndex := i;
        }
      }
      if token == "--version" {
        seenVersion := true;
        if versionTokenIndex == -1 {
          versionTokenIndex := i;
        }
      }

      if IsSuffixLongOptionNeedingValue(token) {
        if i + 1 < stopTokenIndex {
          assert i + 2 <= stopTokenIndex;
          i := i + 2;
        } else {
          i := i + 1;
        }
        continue;
      }

      if |token| > 1 && token[0] == '-' && !(|token| > 2 && token[1] == '-') {
        var consumesNext := false;
        var j := 1;
        while j < |token|
          invariant 1 <= j <= |token|
          invariant consumesNext ==> i + 1 < stopTokenIndex
          decreases |token| - j
        {
          if token[j] == 's' {
            if j + 1 == |token| && i + 1 < stopTokenIndex {
              consumesNext := true;
            }
            j := |token|;
          } else {
            j := j + 1;
          }
        }
        if consumesNext {
          assert i + 2 <= stopTokenIndex;
          i := i + 2;
        } else {
          i := i + 1;
        }
      } else {
        i := i + 1;
      }
    }

    found := seenHelp || seenVersion;
    raw := BasenameCmdRaw(false, CliTypes.None, false, seenHelp, seenVersion, helpTokenIndex, versionTokenIndex, []);
  }

  method Decode(p: CliTypes.ParsedArgs) returns (raw: BasenameCmdRaw)
  {
    var seenMultiple := false;
    var suffix: CliTypes.OptionalString := CliTypes.None;
    var seenZero := false;
    var seenHelp := false;
    var seenVersion := false;
    var helpTokenIndex := -1;
    var versionTokenIndex := -1;

    var i := 0;
    while i < |p.options|
      decreases |p.options| - i
    {
      var occ := p.options[i];
      if occ.key == "basename.multiple" {
        seenMultiple := true;
      }
      if occ.key == "basename.suffix" {
        suffix := occ.value;
        seenMultiple := true;
      }
      if occ.key == "basename.zero" {
        seenZero := true;
      }
      if occ.key == "basename.help" {
        seenHelp := true;
        if helpTokenIndex == -1 || occ.tokenIndex < helpTokenIndex {
          helpTokenIndex := occ.tokenIndex;
        }
      }
      if occ.key == "basename.version" {
        seenVersion := true;
        if versionTokenIndex == -1 || occ.tokenIndex < versionTokenIndex {
          versionTokenIndex := occ.tokenIndex;
        }
      }
      i := i + 1;
    }

    raw := BasenameCmdRaw(
      seenMultiple,
      suffix,
      seenZero,
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
        "basename: unrecognized option '" + e.rawToken + "'\n" +
        "Try 'basename --help' for more information.\n"
      else if |e.rawToken| > 1 && e.rawToken[0] == '-' then
        "basename: invalid option -- '" + [e.rawToken[1]] + "'\n" +
        "Try 'basename --help' for more information.\n"
      else
        "basename: invalid option\nTry 'basename --help' for more information.\n"
    else if e.kind == CliTypes.Ambiguous then
      "basename: option '" + e.rawToken + "' is ambiguous\n" +
      "Try 'basename --help' for more information.\n"
    else if e.kind == CliTypes.MissingValue then
      if IsSuffixLongOptionNeedingValue(e.rawToken) then
        "basename: option '--suffix' requires an argument\n" +
        "Try 'basename --help' for more information.\n"
      else if |e.rawToken| > 1 && e.rawToken[0] == '-' then
        "basename: option requires an argument -- '" +
        [e.rawToken[|e.rawToken| - 1]] + "'\n" +
        "Try 'basename --help' for more information.\n"
      else
        "basename: missing option value\n" +
        "Try 'basename --help' for more information.\n"
    else
      "basename: " +
      (if e.kind == CliTypes.UnexpectedValue
       then "option does not take a value"
       else "parse error") +
      " at token '" + e.rawToken + "'\n"
  }

  method FormatParseError(e: CliTypes.ParseError) returns (b: BenchWorld.Bytes)
  {
    b := Utf8.Encode(ParseErrorText(e));
  }

  method PlanParseFailure(
    e: CliTypes.ParseError,
    argv: seq<string>
  ) returns (plan: CliTypes.CliPlan<BasenameCmdRaw>)
    decreases *
  {
    if 0 <= e.tokenIndex <= |argv| {
      var handled, raw := DecodeEarlySpecial(argv, e.tokenIndex);
      if handled {
        plan := CliTypes.CliRun(raw);
        return;
      }
    }

    var msg := FormatParseError(e);
    plan := CliTypes.CliEarlyExit(1, [], msg);
  }
}
