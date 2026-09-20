include "../../core/World.dfy"
include "../../core/CliTypes.dfy"
include "../../core/BenchmarkItem.dfy"
include "HeadSchema.dfy"
include "HeadCore.dfy"
include "HeadSpec.dfy"
include "HeadProof.dfy"

module Head {
  import BenchIO
  import CP = HeadProof
  import BenchWorld
  import CliTypes
  import BenchItem
  import HeadSchema
  import Exec = HeadCore
  import CS = HeadSpec

  class {:termination false} HeadBenchmarkItem extends BenchItem.BenchmarkItemTwostate<HeadSchema.HeadCmdRaw> {
    constructor()
    {
    }

    method Name() returns (name: string)
    {
      name := "head";
    }

    method Schema() returns (schema: CliTypes.CliSchema)
    {
      schema := HeadSchema.Schema();
    }

    method ParseConfig() returns (cfg: CliTypes.ParseConfig)
    {
      cfg := HeadSchema.ParserConfig();
    }

    method Decode(parsed: CliTypes.ParsedArgs) returns (raw: HeadSchema.HeadCmdRaw)
    {
      raw := HeadSchema.Decode(parsed);
    }

    method FormatParseError(err: CliTypes.ParseError) returns (msg: BenchWorld.Bytes)
    {
      msg := HeadSchema.FormatParseError(err);
    }

    method PlanParseFailure(err: CliTypes.ParseError, argv: seq<string>) returns (plan: CliTypes.CliPlan<HeadSchema.HeadCmdRaw>)
      decreases *
    {
      var failurePlan := HeadSchema.PlanParseFailure(err, argv);
      match failurePlan
      case HeadRun(raw) =>
        plan := CliTypes.CliRun(raw);
      case HeadParseError(error) =>
        var msg := HeadSchema.FormatParseError(error);
        plan := CliTypes.CliEarlyExit(1, [], msg);
      case HeadLegacyError(option) =>
        var msg := HeadSchema.FormatLegacyTrailingOption(option);
        plan := CliTypes.CliEarlyExit(1, [], msg);
    }

    method RunCore(raw: HeadSchema.HeadCmdRaw, io: BenchIO.IO) returns (exit: int)
      modifies io.stdinRegion, io.stdoutRegion, io.stderrRegion
      ensures CS.Spec(raw, io, exit)
      decreases *
    {
      exit := Exec.RunCore(raw, io);
      CP.CoreSummaryImpliesSpec(raw, io, exit);
    }
  }
}
