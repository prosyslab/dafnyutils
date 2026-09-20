include "../../core/Utf8.dfy"
include "../../core/World.dfy"
include "../../core/CliTypes.dfy"
include "../../core/CliExtern.dfy"

module HeadSchema {
  import Utf8 = Utf8Semantics
  import BenchWorld
  import CliTypes
  import CliExtern

  datatype HeadMode = ModeRun | ModeHelp | ModeVersion | ModeInvalidCount
  datatype CountUnit = CountLines | CountBytes
  datatype HeaderMode = HeadersMultiple | HeadersNever | HeadersAlways
  datatype Input = Stdin(displayName: string) | File(path: BenchWorld.Path)

  datatype CountSelection = CountSelection(unit: CountUnit, fromEnd: bool, amount: nat)

  datatype HeadCmdRaw = HeadCmdRaw(
    selection: CountSelection,
    headerMode: HeaderMode,
    zeroTerminated: bool,
    seenHelp: bool,
    seenVersion: bool,
    helpTokenIndex: int,
    versionTokenIndex: int,
    invalidCountUnit: CountUnit,
    invalidCountValue: string,
    invalidCountTokenIndex: int,
    operands: seq<string>
  )

  datatype HeadCmd = HeadCmd(
    mode: HeadMode,
    selection: CountSelection,
    headerMode: HeaderMode,
    zeroTerminated: bool,
    invalidCountUnit: CountUnit,
    invalidCountValue: string,
    inputs: seq<Input>
  )

  datatype HeadParseFailurePlan =
    | HeadRun(raw: HeadCmdRaw)
    | HeadParseError(error: CliTypes.ParseError)
    | HeadLegacyError(option: string)

  method Schema() returns (s: CliTypes.CliSchema)
  {
    s := CliTypes.CliSchema(
      [
        CliTypes.OptionDecl("head.bytes", ['c'], ["bytes"], CliTypes.ReqArg),
        CliTypes.OptionDecl("head.lines", ['n'], ["lines"], CliTypes.ReqArg),
        CliTypes.OptionDecl("head.zero_terminated", ['z'], ["zero-terminated"], CliTypes.NoArg),
        CliTypes.OptionDecl("head.quiet", ['q'], ["quiet", "silent"], CliTypes.NoArg),
        CliTypes.OptionDecl("head.verbose", ['v'], ["verbose"], CliTypes.NoArg),
        CliTypes.OptionDecl("head.help", [], ["help"], CliTypes.NoArg),
        CliTypes.OptionDecl("head.version", [], ["version"], CliTypes.NoArg)
      ],
      true
    );
  }

  method ParserConfig() returns (cfg: CliTypes.ParseConfig)
  {
    cfg := CliTypes.ParseConfig(CliTypes.GNU_Permute, true, true, true);
  }

  method PlanParseFailure(
    e: CliTypes.ParseError,
    argv: seq<string>
  ) returns (plan: HeadParseFailurePlan)
    decreases *
  {
    var handled, ok, normalized, badOption := NormalizeLegacyArgv(argv);
    if handled {
      if !ok {
        plan := HeadLegacyError(badOption);
        return;
      }

      var schema := Schema();
      var cfg := ParserConfig();
      var res := CliExtern.Cli.Parse(normalized, schema, cfg);
      match res {
        case ParseSuccess(parsed) =>
          var raw := Decode(parsed);
          plan := HeadRun(raw);
        case ParseFailure(err) =>
          plan := PlanStandardParseFailure(err, normalized);
      }
      return;
    }

    plan := PlanStandardParseFailure(e, argv);
  }

  method PlanStandardParseFailure(
    e: CliTypes.ParseError,
    argv: seq<string>
  ) returns (plan: HeadParseFailurePlan)
    decreases *
  {
    var seenHelp := false;
    var seenVersion := false;
    var helpTokenIndex := -1;
    var versionTokenIndex := -1;
    var invalidUnit := CountLines;
    var invalidValue := "";
    var invalidTokenIndex := -1;

    var i := 0;
    while i < |argv| && i < e.tokenIndex
      decreases |argv| - i
    {
      var token := argv[i];
      if token == "--help" {
        seenHelp := true;
        if helpTokenIndex == -1 {
          helpTokenIndex := i;
        }
      } else if token == "--version" {
        seenVersion := true;
        if versionTokenIndex == -1 {
          versionTokenIndex := i;
        }
      }

      var countUnit := CountLines;
      var countValue := "";
      var hasCountValue := false;
      var consumedNext := false;

      if token == "-n" || token == "--lines" {
        countUnit := CountLines;
        if i + 1 < |argv| && i + 1 < e.tokenIndex {
          countValue := argv[i + 1];
          hasCountValue := true;
          consumedNext := true;
        }
      } else if token == "-c" || token == "--bytes" {
        countUnit := CountBytes;
        if i + 1 < |argv| && i + 1 < e.tokenIndex {
          countValue := argv[i + 1];
          hasCountValue := true;
          consumedNext := true;
        }
      } else if 8 <= |token| && token[..8] == "--lines=" {
        countUnit := CountLines;
        countValue := token[8..];
        hasCountValue := true;
      } else if 8 <= |token| && token[..8] == "--bytes=" {
        countUnit := CountBytes;
        countValue := token[8..];
        hasCountValue := true;
      } else if |token| > 2 && token[0] == '-' && token[1] == 'n' {
        countUnit := CountLines;
        countValue := token[2..];
        hasCountValue := true;
      } else if |token| > 2 && token[0] == '-' && token[1] == 'c' {
        countUnit := CountBytes;
        countValue := token[2..];
        hasCountValue := true;
      }

      if hasCountValue && invalidTokenIndex == -1 {
        var ok, fromEnd, amount := ParseCountArg(countValue);
        if !ok {
          invalidUnit := countUnit;
          invalidValue := countValue;
          invalidTokenIndex := i;
        }
      }

      if consumedNext {
        i := i + 2;
      } else {
        i := i + 1;
      }
    }

    if seenHelp &&
       (!seenVersion || helpTokenIndex <= versionTokenIndex) &&
       (invalidTokenIndex == -1 || helpTokenIndex <= invalidTokenIndex) {
      plan := HeadRun(HeadCmdRaw(
                        CountSelection(CountLines, false, 10),
                        HeadersMultiple,
                        false,
                        true,
                        false,
                        0,
                        -1,
                        CountLines,
                        "",
                        -1,
                        []
                      ));
      return;
    }

    if seenVersion &&
       (invalidTokenIndex == -1 || versionTokenIndex <= invalidTokenIndex) {
      plan := HeadRun(HeadCmdRaw(
                        CountSelection(CountLines, false, 10),
                        HeadersMultiple,
                        false,
                        false,
                        true,
                        -1,
                        0,
                        CountLines,
                        "",
                        -1,
                        []
                      ));
      return;
    }

    if invalidTokenIndex != -1 {
      plan := HeadRun(HeadCmdRaw(
                        CountSelection(CountLines, false, 10),
                        HeadersMultiple,
                        false,
                        false,
                        false,
                        -1,
                        -1,
                        invalidUnit,
                        invalidValue,
                        invalidTokenIndex,
                        []
                      ));
      return;
    }

    plan := HeadParseError(e);
  }

  function IsDigit(ch: char): bool
  {
    '0' <= ch <= '9'
  }

  function Pow(base: nat, exp: nat): nat
    decreases exp
  {
    if exp == 0 then 1 else base * Pow(base, exp - 1)
  }

  function CountSuffixMultiplier(suffix: string): nat
  {
    if suffix == "" then
      1
    else if suffix == "b" then
      512
    else if suffix == "k" || suffix == "K" || suffix == "KiB" then
      Pow(1024, 1)
    else if suffix == "kB" || suffix == "KB" then
      Pow(1000, 1)
    else if suffix == "m" || suffix == "M" || suffix == "MiB" then
      Pow(1024, 2)
    else if suffix == "MB" then
      Pow(1000, 2)
    else if suffix == "G" || suffix == "GiB" then
      Pow(1024, 3)
    else if suffix == "GB" then
      Pow(1000, 3)
    else if suffix == "T" || suffix == "TiB" then
      Pow(1024, 4)
    else if suffix == "TB" then
      Pow(1000, 4)
    else if suffix == "P" || suffix == "PiB" then
      Pow(1024, 5)
    else if suffix == "PB" then
      Pow(1000, 5)
    else if suffix == "E" || suffix == "EiB" then
      Pow(1024, 6)
    else if suffix == "EB" then
      Pow(1000, 6)
    else if suffix == "Z" || suffix == "ZiB" then
      Pow(1024, 7)
    else if suffix == "ZB" then
      Pow(1000, 7)
    else if suffix == "Y" || suffix == "YiB" then
      Pow(1024, 8)
    else if suffix == "YB" then
      Pow(1000, 8)
    else if suffix == "R" || suffix == "RiB" then
      Pow(1024, 9)
    else if suffix == "RB" then
      Pow(1000, 9)
    else if suffix == "Q" || suffix == "QiB" then
      Pow(1024, 10)
    else if suffix == "QB" then
      Pow(1000, 10)
    else
      0
  }

  method ParseCountArg(text: string) returns (ok: bool, fromEnd: bool, amount: nat)
  {
    ok := false;
    fromEnd := false;
    amount := 0;

    var i := 0;
    if |text| > 0 && text[0] == '-' {
      fromEnd := true;
      i := 1;
    } else if |text| > 0 && text[0] == '+' {
      i := 1;
    }

    if i >= |text| {
      return;
    }

    var sawDigits := false;
    while i < |text| && IsDigit(text[i])
      invariant 0 <= i <= |text|
      decreases |text| - i
    {
      sawDigits := true;
      var digit := ((text[i] as int) - ('0' as int)) as nat;
      amount := amount * 10 + digit;
      i := i + 1;
    }

    var multiplier := CountSuffixMultiplier(text[i..]);
    if multiplier == 0 || (!sawDigits && multiplier == 1) {
      amount := 0;
      return;
    }
    if !sawDigits {
      amount := 1;
    }
    amount := amount * multiplier;
    ok := true;
  }

  method NormalizeLegacyArgv(argv: seq<string>) returns (
      handled: bool,
      ok: bool,
      normalized: seq<string>,
      badOption: string
    )
  {
    handled := false;
    ok := false;
    normalized := argv;
    badOption := "";

    if |argv| <= 1 {
      return;
    }

    var token := argv[1];
    if |token| <= 1 || token[0] != '-' || !IsDigit(token[1]) {
      return;
    }

    handled := true;

    var i := 2;
    while i < |token| && IsDigit(token[i])
      invariant 2 <= i <= |token|
      decreases |token| - i
    {
      i := i + 1;
    }

    var countText := token[1..i];
    var unit := CountLines;
    var multiplierSuffix := "";
    var legacyOptions: seq<string> := [];

    while i < |token|
      invariant 2 <= i <= |token|
      decreases |token| - i
    {
      var ch := token[i];
      if ch == 'c' {
        unit := CountBytes;
        multiplierSuffix := "";
      } else if ch == 'b' || ch == 'k' || ch == 'm' {
        unit := CountBytes;
        multiplierSuffix := [ch];
      } else if ch == 'l' {
        unit := CountLines;
      } else if ch == 'q' {
        legacyOptions := legacyOptions + ["-q"];
      } else if ch == 'v' {
        legacyOptions := legacyOptions + ["-v"];
      } else if ch == 'z' {
        legacyOptions := legacyOptions + ["-z"];
      } else {
        badOption := [ch];
        return;
      }
      i := i + 1;
    }

    var countOption := if unit == CountBytes then "-c" else "-n";
    normalized := [argv[0], countOption, countText + multiplierSuffix] + legacyOptions + argv[2..];
    ok := true;
  }

  method DecodeCountOption(
    occ: CliTypes.OptOccurrence,
    unit: CountUnit,
    current: CountSelection,
    invalidUnit: CountUnit,
    invalidValue: string,
    invalidTokenIndex: int
  ) returns (
      next: CountSelection,
      nextInvalidUnit: CountUnit,
      nextInvalidValue: string,
      nextInvalidTokenIndex: int
    )
  {
    next := current;
    nextInvalidUnit := invalidUnit;
    nextInvalidValue := invalidValue;
    nextInvalidTokenIndex := invalidTokenIndex;

    match occ.value
    case Some(value) =>
      var ok, fromEnd, amount := ParseCountArg(value);
      if ok {
        next := CountSelection(unit, fromEnd, amount);
      } else if nextInvalidTokenIndex == -1 || occ.tokenIndex < nextInvalidTokenIndex {
        nextInvalidUnit := unit;
        nextInvalidValue := value;
        nextInvalidTokenIndex := occ.tokenIndex;
      }
    case None =>
      if nextInvalidTokenIndex == -1 || occ.tokenIndex < nextInvalidTokenIndex {
        nextInvalidUnit := unit;
        nextInvalidValue := "";
        nextInvalidTokenIndex := occ.tokenIndex;
      }
  }

  method Decode(p: CliTypes.ParsedArgs) returns (raw: HeadCmdRaw)
  {
    var selection := CountSelection(CountLines, false, 10);
    var headerMode := HeadersMultiple;
    var zeroTerminated := false;
    var seenHelp := false;
    var seenVersion := false;
    var helpTokenIndex := -1;
    var versionTokenIndex := -1;
    var invalidCountUnit := CountLines;
    var invalidCountValue := "";
    var invalidCountTokenIndex := -1;

    var i := 0;
    while i < |p.options|
      decreases |p.options| - i
    {
      var occ := p.options[i];
      if occ.key == "head.lines" {
        selection, invalidCountUnit, invalidCountValue, invalidCountTokenIndex :=
          DecodeCountOption(
            occ,
            CountLines,
            selection,
            invalidCountUnit,
            invalidCountValue,
            invalidCountTokenIndex
          );
      }
      if occ.key == "head.bytes" {
        selection, invalidCountUnit, invalidCountValue, invalidCountTokenIndex :=
          DecodeCountOption(
            occ,
            CountBytes,
            selection,
            invalidCountUnit,
            invalidCountValue,
            invalidCountTokenIndex
          );
      }
      if occ.key == "head.quiet" {
        headerMode := HeadersNever;
      }
      if occ.key == "head.verbose" {
        headerMode := HeadersAlways;
      }
      if occ.key == "head.zero_terminated" {
        zeroTerminated := true;
      }
      if occ.key == "head.help" {
        seenHelp := true;
        if helpTokenIndex == -1 || occ.tokenIndex < helpTokenIndex {
          helpTokenIndex := occ.tokenIndex;
        }
      }
      if occ.key == "head.version" {
        seenVersion := true;
        if versionTokenIndex == -1 || occ.tokenIndex < versionTokenIndex {
          versionTokenIndex := occ.tokenIndex;
        }
      }
      i := i + 1;
    }

    raw := HeadCmdRaw(
      selection,
      headerMode,
      zeroTerminated,
      seenHelp,
      seenVersion,
      helpTokenIndex,
      versionTokenIndex,
      invalidCountUnit,
      invalidCountValue,
      invalidCountTokenIndex,
      p.positionals
    );
  }

  function ParseErrorText(e: CliTypes.ParseError): string
  {
    if e.kind == CliTypes.UnknownOption || e.kind == CliTypes.UnexpectedValue then
      if |e.rawToken| > 2 && e.rawToken[0] == '-' && e.rawToken[1] == '-' then
        "head: unrecognized option '" + e.rawToken + "'\n" +
        "Try 'head --help' for more information.\n"
      else if |e.rawToken| > 1 && e.rawToken[0] == '-' then
        "head: invalid option -- '" + [e.rawToken[1]] + "'\n" +
        "Try 'head --help' for more information.\n"
      else
        "head: invalid option\nTry 'head --help' for more information.\n"
    else if e.kind == CliTypes.MissingValue then
      if |e.rawToken| > 2 && e.rawToken[0] == '-' && e.rawToken[1] == '-' then
        "head: option '" + e.rawToken + "' requires an argument\n" +
        "Try 'head --help' for more information.\n"
      else if |e.rawToken| > 1 && e.rawToken[0] == '-' then
        "head: option requires an argument -- '" + [e.rawToken[|e.rawToken| - 1]] + "'\n" +
        "Try 'head --help' for more information.\n"
      else
        "head: option requires an argument\nTry 'head --help' for more information.\n"
    else if e.kind == CliTypes.Ambiguous then
      "head: option '" + e.rawToken + "' is ambiguous\n" +
      "Try 'head --help' for more information.\n"
    else
      "head: parse error at token '" + e.rawToken + "'\n"
  }

  function LegacyTrailingOptionText(option: string): string
  {
    "head: invalid trailing option -- " + option + "\n" +
    "Try 'head --help' for more information.\n"
  }

  method FormatParseError(e: CliTypes.ParseError) returns (b: BenchWorld.Bytes)
  {
    b := Utf8.Encode(ParseErrorText(e));
  }

  method FormatLegacyTrailingOption(option: string) returns (b: BenchWorld.Bytes)
  {
    b := Utf8.Encode(LegacyTrailingOptionText(option));
  }
}
