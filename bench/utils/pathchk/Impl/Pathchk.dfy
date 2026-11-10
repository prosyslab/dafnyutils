include "CliSupport.dfy"
include "../Spec/PathchkSpec.dfy"
include "../Impl/PathchkCore.dfy"

module Pathchk {
  import BenchIO
  import BenchWorld
  import BenchItem
  import CliTypes
  import S = PathchkSchema
  import Core = PathchkCore
  import Spec = PathchkSpec
  import opened CliExtern

  class PathchkBenchmarkItem extends BenchItem.BenchmarkItemTwostate<S.PathchkCmdRaw> {
    constructor() {}

    method Name() returns (name: string) {
      name := "pathchk";
    }

    method Schema() returns (schema: CliTypes.CliSchema) {
      schema := S.Schema();
    }

    method ParseConfig() returns (cfg: CliTypes.ParseConfig) {
      cfg := S.ParserConfig();
    }

    method Decode(parsed: CliTypes.ParsedArgs) returns (raw: S.PathchkCmdRaw) {
      raw := S.Decode(parsed);
    }

    method FormatParseError(err: CliTypes.ParseError) returns (msg: BenchWorld.Bytes)
      ensures msg == Spec.ParseErrorText(err)
    {
      var token := Core.Encode(err.rawToken);
      msg := Spec.ParseErrorMessage(err, token);
    }

    method PlanParseFailure(
      err: CliTypes.ParseError, argv: seq<string>
    ) returns (plan: CliTypes.CliPlan<S.PathchkCmdRaw>)
      decreases *
    {
      if 0 < err.tokenIndex < |argv| {
        var schema := S.Schema();
        var cfg := S.ParserConfig();
        var result := Cli.Parse(argv[..err.tokenIndex], schema, cfg);
        match result {
          case ParseSuccess(parsed) =>
            var raw := S.Decode(parsed);
            if raw.mode == S.ModeHelp || raw.mode == S.ModeVersion {
              return CliTypes.CliRun(raw);
            }
          case ParseFailure(_) =>
        }
      }
      var msg := FormatParseError(err);
      return CliTypes.CliEarlyExit(1, [], msg);
    }

    method RunCore(raw: S.PathchkCmdRaw, io: BenchIO.IO) returns (exit: int)
      modifies io.stdoutRegion, io.stderrRegion
      ensures Spec.Spec(raw, io, exit)
    {
      exit := Core.RunCore(raw, io);
    }
  }
}
