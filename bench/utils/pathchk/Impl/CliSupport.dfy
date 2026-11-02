// Task-local CLI protocol scaffolding; not a library of utility algorithms.
include "../../../core/IO.dfy"
include "../../../core/CliTypes.dfy"
include "../../../core/Utf8.dfy"

module CliModel {
  import opened CliTypes

  datatype OptionLookup = OptionMissing | OptionFound(decl: OptionDecl)
  datatype LongOptionLookup = LongMissing | LongFound(decl: OptionDecl) | LongAmbiguous
  datatype ShortParse = ShortParsed(options: seq<OptOccurrence>, consumesNext: bool) |
                        ShortFailed(error: ParseError)

  function HasPrefix(text: string, prefix: string): bool
  {
    |prefix| <= |text| && text[..|prefix|] == prefix
  }

  function FindCharFrom(text: string, target: char, i: nat): int
    requires i <= |text|
    ensures -1 <= FindCharFrom(text, target, i) < |text|
    decreases |text| - i
  {
    if i == |text| then -1
    else if text[i] == target then i as int
    else FindCharFrom(text, target, i + 1)
  }

  function FindChar(text: string, target: char): int
  {
    FindCharFrom(text, target, 0)
  }

  function {:fuel 20} ContainsChar(chars: seq<char>, target: char): bool
    decreases |chars|
  {
    |chars| > 0 && (chars[0] == target || ContainsChar(chars[1..], target))
  }

  function {:fuel 20} FindShortInDecls(options: seq<OptionDecl>, short: char): OptionLookup
    decreases |options|
  {
    if |options| == 0 then OptionMissing
    else if ContainsChar(options[0].shorts, short) then OptionFound(options[0])
    else FindShortInDecls(options[1..], short)
  }

  function {:fuel 20} FindExactLongInNames(
    decl: OptionDecl,
    names: seq<string>,
    name: string
  ): OptionLookup
    decreases |names|
  {
    if |names| == 0 then OptionMissing
    else if names[0] == name then OptionFound(decl)
    else FindExactLongInNames(decl, names[1..], name)
  }

  function {:fuel 20} FindExactLong(options: seq<OptionDecl>, name: string): OptionLookup
    decreases |options|
  {
    if |options| == 0 then OptionMissing
    else
      match FindExactLongInNames(options[0], options[0].longs, name)
      case OptionFound(decl) => OptionFound(decl)
      case OptionMissing => FindExactLong(options[1..], name)
  }

  function {:fuel 20} PrefixLongDecls(
    options: seq<OptionDecl>,
    name: string
  ): seq<OptionDecl>
    decreases |options|
  {
    if |options| == 0 then []
    else (PrefixLongNames(options[0], options[0].longs, name) +
          PrefixLongDecls(options[1..], name))
  }

  function {:fuel 20} PrefixLongNames(
    decl: OptionDecl,
    names: seq<string>,
    name: string
  ): seq<OptionDecl>
    decreases |names|
  {
    if |names| == 0 then []
    else ((if HasPrefix(names[0], name) then [decl] else []) +
          PrefixLongNames(decl, names[1..], name))
  }

  function FindLongOption(
    options: seq<OptionDecl>,
    name: string,
    allowAbbrev: bool
  ): LongOptionLookup
  {
    match FindExactLong(options, name)
    case OptionFound(decl) => LongFound(decl)
    case OptionMissing =>
      if !allowAbbrev then LongMissing
      else
        var matches := PrefixLongDecls(options, name);
        if |matches| == 0 then LongMissing
        else if |matches| == 1 then LongFound(matches[0])
        else LongAmbiguous
  }

  function LooksLikeOption(token: string): bool
  {
    |token| > 1 && token[0] == '-'
  }

  function ParseShortFrom(
    argv: seq<string>,
    options: seq<OptionDecl>,
    tokenIndex: nat,
    token: string,
    j: nat,
    parsed: seq<OptOccurrence>
  ): ShortParse
    requires tokenIndex < |argv|
    requires 1 <= j <= |token|
    ensures (ParseShortFrom(argv, options, tokenIndex, token, j, parsed).ShortParsed? &&
             ParseShortFrom(argv, options, tokenIndex, token, j, parsed).consumesNext) ==>
              tokenIndex + 1 < |argv|
    decreases |token| - j
  {
    if j == |token| then ShortParsed(parsed, false)
    else
      var c := token[j];
      match FindShortInDecls(options, c)
      case OptionMissing =>
        ShortFailed(ParseError(UnknownOption, tokenIndex as int, token))
      case OptionFound(decl) =>
        if decl.arity == NoArg then
          ParseShortFrom(
            argv, options, tokenIndex, token, j + 1,
            parsed + [OptOccurrence(decl.key, Short(c), None, tokenIndex as int, token)]
          )
        else if decl.arity == ReqArg then
          if j + 1 < |token| then
            ShortParsed(
              parsed + [OptOccurrence(
                          decl.key, Short(c), Some(token[j + 1..]), tokenIndex as int, token
                        )],
              false
            )
          else if tokenIndex + 1 < |argv| then
            ShortParsed(
              parsed + [OptOccurrence(
                          decl.key, Short(c), Some(argv[tokenIndex + 1]), tokenIndex as int, token
                        )],
              true
            )
          else
            ShortFailed(ParseError(MissingValue, tokenIndex as int, token))
        else if j + 1 < |token| then
          ShortParsed(
            parsed + [OptOccurrence(
                        decl.key, Short(c), Some(token[j + 1..]), tokenIndex as int, token
                      )],
            false
          )
        else
          ShortParsed(
            parsed + [OptOccurrence(decl.key, Short(c), None, tokenIndex as int, token)],
            false
          )
  }

  function ParseFrom(
    argv: seq<string>,
    schema: CliSchema,
    cfg: ParseConfig,
    prog: string,
    i: nat,
    options: seq<OptOccurrence>,
    positionals: seq<string>,
    sawDoubleDash: bool,
    parsingOptions: bool
  ): ParseResult
    requires i <= |argv|
    decreases |argv| - i
  {
    if i == |argv| then
      ParseSuccess(ParsedArgs(prog, options, positionals, sawDoubleDash))
    else
      var token := argv[i];
      if parsingOptions && schema.supportsDoubleDash && token == "--" then
        ParseFrom(argv, schema, cfg, prog, i + 1, options, positionals, true, false)
      else if parsingOptions && cfg.treatDashAsOperand && token == "-" then
        ParseFrom(
          argv, schema, cfg, prog, i + 1, options, positionals + [token],
          sawDoubleDash, cfg.order != POSIX_StopAtFirst
        )
      else if parsingOptions && |token| > 2 && token[0] == '-' && token[1] == '-' then
        var longToken := token[2..];
        var eq := FindChar(longToken, '=');
        var longName := if eq >= 0 then longToken[..eq] else longToken;
        var inlineValue := if eq >= 0 then longToken[eq + 1..] else "";
        var hasInlineValue := eq >= 0;
        match FindLongOption(schema.options, longName, cfg.allowLongAbbrev)
        case LongAmbiguous =>
          ParseFailure(ParseError(Ambiguous, i as int, token))
        case LongMissing =>
          ParseFailure(ParseError(UnknownOption, i as int, token))
        case LongFound(decl) =>
          if decl.arity == NoArg then
            if hasInlineValue then
              ParseFailure(ParseError(UnexpectedValue, i as int, token))
            else
              ParseFrom(
                argv, schema, cfg, prog, i + 1,
                options + [OptOccurrence(decl.key, Long(longName), None, i as int, token)],
                positionals, sawDoubleDash, parsingOptions
              )
          else if decl.arity == ReqArg then
            if hasInlineValue then
              ParseFrom(
                argv, schema, cfg, prog, i + 1,
                options + [OptOccurrence(
                             decl.key, Long(longName), Some(inlineValue), i as int, token
                           )],
                positionals, sawDoubleDash, parsingOptions
              )
            else if i + 1 < |argv| then
              ParseFrom(
                argv, schema, cfg, prog, i + 2,
                options + [OptOccurrence(
                             decl.key, Long(longName), Some(argv[i + 1]), i as int, token
                           )],
                positionals, sawDoubleDash, parsingOptions
              )
            else
              ParseFailure(ParseError(MissingValue, i as int, token))
          else if hasInlineValue then
            ParseFrom(
              argv, schema, cfg, prog, i + 1,
              options + [OptOccurrence(
                           decl.key, Long(longName), Some(inlineValue), i as int, token
                         )],
              positionals, sawDoubleDash, parsingOptions
            )
          else if i + 1 < |argv| && !LooksLikeOption(argv[i + 1]) then
            ParseFrom(
              argv, schema, cfg, prog, i + 2,
              options + [OptOccurrence(
                           decl.key, Long(longName), Some(argv[i + 1]), i as int, token
                         )],
              positionals, sawDoubleDash, parsingOptions
            )
          else
            ParseFrom(
              argv, schema, cfg, prog, i + 1,
              options + [OptOccurrence(decl.key, Long(longName), None, i as int, token)],
              positionals, sawDoubleDash, parsingOptions
            )
      else if parsingOptions && |token| > 1 && token[0] == '-' then
        if !cfg.allowBundling && |token| > 2 then
          ParseFailure(ParseError(UnknownOption, i as int, token))
        else
          match ParseShortFrom(argv, schema.options, i, token, 1, options)
          case ShortFailed(error) => ParseFailure(error)
          case ShortParsed(parsed, consumesNext) =>
            ParseFrom(
              argv, schema, cfg, prog, if consumesNext then i + 2 else i + 1,
              parsed, positionals, sawDoubleDash, parsingOptions
            )
      else
        ParseFrom(
          argv, schema, cfg, prog, i + 1, options, positionals + [token],
          sawDoubleDash, if cfg.order == POSIX_StopAtFirst then false else parsingOptions
        )
  }

  function ParseValue(
    argv: seq<string>,
    schema: CliSchema,
    cfg: ParseConfig
  ): ParseResult
  {
    var hasProg := |argv| > 0 && |argv[0]| > 0 && argv[0][0] != '-';
    ParseFrom(
      argv, schema, cfg,
      if hasProg then argv[0] else "",
      if hasProg then 1 else 0,
      [], [], false, true
    )
  }
}

module CliExtern {
  import opened CliTypes
  import CliModel

  class Cli {
    static method Parse(
      argv: seq<string>,
      schema: CliSchema,
      cfg: ParseConfig
    ) returns (res: ParseResult)
      ensures res == CliModel.ParseValue(argv, schema, cfg)
    {
      res := CliModel.ParseValue(argv, schema, cfg);
    }

    static method ParsePortable(
      argv: seq<string>,
      schema: CliSchema,
      cfg: ParseConfig
    ) returns (res: ParseResult)
      ensures res == CliModel.ParseValue(argv, schema, cfg)
    {
      res := CliModel.ParseValue(argv, schema, cfg);
    }
  }
}

module BenchItem {
  import opened BenchWorld
  import BenchIO
  import opened CliTypes
  import opened CliExtern
  import C = IOContract
  import Utf8Semantics

  // CLI protocol code is fixed scaffolding.
  export
    provides BenchWorld, BenchIO, CliTypes
    reveals BenchmarkItemTwostate
    provides BenchmarkItemTwostate.Name, BenchmarkItemTwostate.Schema
    provides BenchmarkItemTwostate.ParseConfig, BenchmarkItemTwostate.Decode
    provides BenchmarkItemTwostate.FormatParseError, BenchmarkItemTwostate.PlanParsed
    provides BenchmarkItemTwostate.PlanParseFailure, BenchmarkItemTwostate.PlanArgv
    provides BenchmarkItemTwostate.RunCore, RunMain

  trait {:termination false} BenchmarkItemTwostate<CmdRaw> {
    method Name() returns (name: string)
    method Schema() returns (schema: CliSchema)
    method ParseConfig() returns (cfg: ParseConfig)
    method Decode(parsed: ParsedArgs) returns (raw: CmdRaw)
    method FormatParseError(err: ParseError) returns (msg: Bytes)
    method PlanParsed(parsed: ParsedArgs) returns (plan: CliPlan<CmdRaw>)
      decreases *
    {
      var raw := Decode(parsed);
      plan := CliRun(raw);
    }

    method PlanArgv(argv: seq<string>) returns (plan: CliPlan<CmdRaw>)
      decreases *
    {
      var schema := Schema();
      var cfg := ParseConfig();
      var parseRes := Cli.Parse(argv, schema, cfg);

      match parseRes {
        case ParseFailure(err) =>
          plan := PlanParseFailure(err, argv);
        case ParseSuccess(parsed) =>
          plan := PlanParsed(parsed);
      }
    }

    method RunCore(raw: CmdRaw, io: BenchIO.IO) returns (exit: int)
      modifies io.Footprint()
      decreases *

    method PlanParseFailure(err: ParseError, argv: seq<string>) returns (plan: CliPlan<CmdRaw>)
      decreases *
    {
      var msg := FormatParseError(err);
      plan := CliEarlyExit(1, [], msg);
    }
  }

  method RunMain<CmdRaw>(item: BenchmarkItemTwostate<CmdRaw>, argv: seq<string>, io: BenchIO.IO) returns (exit: int)
    modifies io.Footprint()
    decreases *
  {
    var plan := item.PlanArgv(argv);

    match plan {
      case CliRun(raw) =>
        exit := item.RunCore(raw, io);
      case CliEarlyExit(code, stdout, stderr) =>
        var stdoutResult := io.WriteStdout(stdout);
        var diagnostic := stderr;
        if stdoutResult.Err? {
          var name := item.Name();
          var reason := io.GetCLocaleErrnoText(C.ResultErrno(stdoutResult));
          diagnostic := diagnostic + Utf8Semantics.Encode(name + ": write error: " + reason + "\n");
        }
        var stderrResult := io.WriteStderr(diagnostic);
        exit := if stdoutResult.Err? || stderrResult.Err? then 1 else code;
    }
  }
}
