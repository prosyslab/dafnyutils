include "../../core/BenchmarkItem.dfy"
include "../../core/Utf8.dfy"
include "LinkSpec.dfy"
include "LinkCore.dfy"
include "LinkProof.dfy"

module Link {
  import BenchIO
  import BenchWorld
  import BenchItem
  import CliTypes
  import Utf8 = Utf8Semantics
  import S = LinkSchema
  import Core = LinkCore
  import Spec = LinkSpec
  import Proof = LinkProof
  import opened CliExtern

  class LinkBenchmarkItem extends BenchItem.BenchmarkItemTwostate<S.LinkCmdRaw> {
    constructor() {}

    method Name() returns (name: string) {
      name := "link";
    }

    method Schema() returns (schema: CliTypes.CliSchema) {
      schema := S.Schema();
    }

    method ParseConfig() returns (cfg: CliTypes.ParseConfig) {
      cfg := S.ParserConfig();
    }

    method Decode(parsed: CliTypes.ParsedArgs) returns (raw: S.LinkCmdRaw) {
      raw := S.Decode(parsed);
    }

    method FormatParseError(err: CliTypes.ParseError) returns (msg: BenchWorld.Bytes) {
      msg := Spec.ParseErrorText(err);
    }

    method PlanParseFailure(
      e: CliTypes.ParseError,
      argv: seq<string>
    ) returns (plan: CliTypes.CliPlan<S.LinkCmdRaw>)
      decreases *
    {
      if 0 < e.tokenIndex && e.tokenIndex < |argv| {
        var s := S.Schema();
        var cfg := S.ParserConfig();
        var result := Cli.Parse(argv[..e.tokenIndex], s, cfg);
        match result {
          case ParseSuccess(parsed) =>
            var raw := S.Decode(parsed);
            if raw.mode == S.ModeHelp || raw.mode == S.ModeVersion {
              plan := CliTypes.CliRun(raw);
              return;
            }
          case ParseFailure(_) =>
        }
      }
      var msg := Spec.ParseErrorText(e);
      plan := CliTypes.CliEarlyExit(1, [], msg);
    }

    method RunCore(raw: S.LinkCmdRaw, io: BenchIO.IO) returns (exit: int)
      modifies io.fsRegion, io.stdoutRegion, io.stderrRegion
      ensures Spec.Spec(raw, io, exit)
    {
      exit := Core.RunCore(raw, io);
      Proof.CoreSummaryImpliesSpec(raw, io, exit);
    }
  }
}
