include "../../core/Utf8.dfy"
include "../../core/World.dfy"
include "../../core/CliTypes.dfy"

module SeqSchema {
  import Utf8 = Utf8Semantics
  import BenchWorld
  import CliTypes

  datatype SeqCmdRaw = SeqCmdRaw(
    separator: CliTypes.OptionalString,
    equalWidth: bool,
    seenHelp: bool,
    seenVersion: bool,
    helpTokenIndex: int,
    versionTokenIndex: int,
    operands: seq<string>
  )

  method Schema() returns (s: CliTypes.CliSchema)
  {
    s := CliTypes.CliSchema(
      [
        CliTypes.OptionDecl("seq.separator", ['s'], ["separator"], CliTypes.ReqArg),
        CliTypes.OptionDecl("seq.equal_width", ['w'], ["equal-width"], CliTypes.NoArg),
        CliTypes.OptionDecl("seq.help", [], ["help"], CliTypes.NoArg),
        CliTypes.OptionDecl("seq.version", [], ["version"], CliTypes.NoArg)
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

  method DecodeEarlySpecial(argv: seq<string>, stopTokenIndex: int) returns (found: bool, raw: SeqCmdRaw)
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
        i := i + 1;
        continue;
      }
      if token == "--version" {
        seenVersion := true;
        if versionTokenIndex == -1 {
          versionTokenIndex := i;
        }
        i := i + 1;
        continue;
      }

      if token == "--separator" {
        if i + 1 < stopTokenIndex {
          assert i + 2 <= stopTokenIndex;
          i := i + 2;
        } else {
          i := i + 1;
        }
        continue;
      }
      if HasPrefix(token, "--separator=") {
        i := i + 1;
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
        continue;
      }

      i := i + 1;
    }

    found := seenHelp || seenVersion;
    raw := SeqCmdRaw(CliTypes.None, false, seenHelp, seenVersion, helpTokenIndex, versionTokenIndex, []);
  }

  method Decode(p: CliTypes.ParsedArgs) returns (raw: SeqCmdRaw)
  {
    var separator: CliTypes.OptionalString := CliTypes.None;
    var equalWidth := false;
    var seenHelp := false;
    var seenVersion := false;
    var helpTokenIndex := -1;
    var versionTokenIndex := -1;

    var i := 0;
    while i < |p.options|
      decreases |p.options| - i
    {
      var occ := p.options[i];
      if occ.key == "seq.separator" {
        separator := occ.value;
      }
      if occ.key == "seq.equal_width" {
        equalWidth := true;
      }
      if occ.key == "seq.help" {
        seenHelp := true;
        if helpTokenIndex == -1 || occ.tokenIndex < helpTokenIndex {
          helpTokenIndex := occ.tokenIndex;
        }
      }
      if occ.key == "seq.version" {
        seenVersion := true;
        if versionTokenIndex == -1 || occ.tokenIndex < versionTokenIndex {
          versionTokenIndex := occ.tokenIndex;
        }
      }
      i := i + 1;
    }

    raw := SeqCmdRaw(
      separator,
      equalWidth,
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
        "seq: unrecognized option '" + e.rawToken + "'\n" +
        "Try 'seq --help' for more information.\n"
      else if |e.rawToken| > 1 && e.rawToken[0] == '-' then
        "seq: invalid option -- '" + [e.rawToken[1]] + "'\n" +
        "Try 'seq --help' for more information.\n"
      else
        "seq: invalid option\nTry 'seq --help' for more information.\n"
    else if e.kind == CliTypes.MissingValue then
      if |e.rawToken| > 2 && e.rawToken[0] == '-' && e.rawToken[1] == '-' then
        "seq: option '" + e.rawToken + "' requires an argument\n" +
        "Try 'seq --help' for more information.\n"
      else if |e.rawToken| > 1 && e.rawToken[0] == '-' then
        "seq: option requires an argument -- '" + [e.rawToken[1]] + "'\n" +
        "Try 'seq --help' for more information.\n"
      else
        "seq: option requires an argument\nTry 'seq --help' for more information.\n"
    else if e.kind == CliTypes.Ambiguous then
      "seq: option '" + e.rawToken + "' is ambiguous\n" +
      "Try 'seq --help' for more information.\n"
    else
      "seq: parse error at token '" + e.rawToken + "'\n"
  }

  method FormatParseError(e: CliTypes.ParseError) returns (b: BenchWorld.Bytes)
  {
    b := Utf8.Encode(ParseErrorText(e));
  }

  method PlanParseFailure(
    e: CliTypes.ParseError,
    argv: seq<string>
  ) returns (plan: CliTypes.CliPlan<SeqCmdRaw>)
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
