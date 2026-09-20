include "../../core/World.dfy"
include "../../core/CliTypes.dfy"
include "../../core/BenchmarkItem.dfy"
include "ExpandSchema.dfy"
include "ExpandCore.dfy"
include "ExpandSpec.dfy"
include "ExpandProof.dfy"

module Expand {
  import BenchIO
  import BenchWorld
  import CliTypes
  import CliExtern
  import BenchItem
  import S = ExpandSchema
  import Core = ExpandCore
  import Proof = ExpandProof
  import ES = ExpandSpec

  class {:termination false} ExpandBenchmarkItem extends BenchItem.BenchmarkItemTwostate<S.ExpandCmdRaw> {
    constructor()
    {
    }

    method Name() returns (name: string)
    {
      name := "expand";
    }

    method Schema() returns (schema: CliTypes.CliSchema)
    {
      schema := S.Schema();
    }

    method ParseConfig() returns (cfg: CliTypes.ParseConfig)
    {
      cfg := S.ParserConfig();
    }

    method Decode(parsed: CliTypes.ParsedArgs) returns (raw: S.ExpandCmdRaw)
    {
      raw := S.Decode(parsed);
    }

    method FormatParseError(err: CliTypes.ParseError) returns (msg: BenchWorld.Bytes)
    {
      msg := S.ExpandFormatParseError(err);
    }

    method PlanParseFailure(err: CliTypes.ParseError, argv: seq<string>) returns (plan: CliTypes.CliPlan<S.ExpandCmdRaw>)
      decreases *
    {
      if 0 <= err.tokenIndex <= |argv| {
        var schema := S.Schema();
        var cfg := S.ParserConfig();
        var prefix := argv[..err.tokenIndex as nat];
        var prefixResult := CliExtern.Cli.Parse(prefix, schema, cfg);
        match prefixResult {
          case ParseSuccess(parsed) =>
            var raw := S.Decode(parsed);
            match Core.ScanCommandOptions(raw) {
              case ScanInvalidTabs(value) =>
                plan := CliTypes.CliEarlyExit(
                  1, [], ES.InvalidTabsMessage(value)
                );
                return;
              case ScanHelp =>
                plan := CliTypes.CliEarlyExit(0, ES.HelpText(), []);
                return;
              case ScanVersion =>
                plan := CliTypes.CliEarlyExit(0, ES.VersionText(), []);
                return;
              case ScanContinue(_) =>
            }
          case ParseFailure(_) =>
        }
      }
      var msg := S.ExpandFormatParseError(err);
      plan := CliTypes.CliEarlyExit(1, [], msg);
    }

    method RunCore(raw: S.ExpandCmdRaw, io: BenchIO.IO) returns (exit: int)
      modifies io.stdinRegion, io.stdoutRegion, io.stderrRegion
      ensures ES.Spec(raw, io, exit)
      decreases *
    {
      exit := Core.RunCore(raw, io);
      Proof.CoreSummaryImpliesSpec(raw, io, exit);
    }
  }
}
