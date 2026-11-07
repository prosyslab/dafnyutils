include "CliSupport.dfy"
include "../Spec/PathchkSpec.dfy"
include "../Impl/PathchkCore.dfy"
include "../Proof/PathchkProof.dfy"

module Pathchk {
  import BenchIO
  import BenchWorld
  import BenchItem
  import CliTypes
  import S = PathchkSchema
  import Core = PathchkCore
  import Spec = PathchkSpec
  import Proof = PathchkProof
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

    method FormatParseError(err: CliTypes.ParseError) returns (msg: BenchWorld.Bytes) {
      msg := Spec.ParseErrorText(err);
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
      return CliTypes.CliEarlyExit(1, [], Spec.ParseErrorText(err));
    }

    method RunCore(raw: S.PathchkCmdRaw, io: BenchIO.IO) returns (exit: int)
      modifies io.stdoutRegion, io.stderrRegion
      ensures Spec.Spec(raw, io, exit)
    {
      exit := Core.RunCore(raw, io);
      Proof.CoreSummaryImpliesSpec(raw, io, exit);
    }
  }
}
