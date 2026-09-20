include "../../core/World.dfy"
include "../../core/CliTypes.dfy"
include "../../core/BenchmarkItem.dfy"
include "TailSchema.dfy"
include "TailCore.dfy"
include "TailSpec.dfy"
include "TailProof.dfy"

module Tail {
  import BenchIO
  import CP = TailProof
  import BenchWorld
  import CliTypes
  import BenchItem
  import TailSchema
  import Exec = TailCore
  import CS = TailSpec

  class {:termination false} TailBenchmarkItem extends BenchItem.BenchmarkItemTwostate<TailSchema.TailCmdRaw> {
    constructor()
    {
    }

    method Name() returns (name: string)
    {
      name := "tail";
    }

    method Schema() returns (schema: CliTypes.CliSchema)
    {
      schema := TailSchema.Schema();
    }

    method ParseConfig() returns (cfg: CliTypes.ParseConfig)
    {
      cfg := TailSchema.ParserConfig();
    }

    method Decode(parsed: CliTypes.ParsedArgs) returns (raw: TailSchema.TailCmdRaw)
    {
      raw := TailSchema.Decode(parsed);
    }

    method FormatParseError(err: CliTypes.ParseError) returns (msg: BenchWorld.Bytes)
    {
      msg := TailSchema.FormatParseError(err);
    }

    method PlanParseFailure(err: CliTypes.ParseError, argv: seq<string>) returns (plan: CliTypes.CliPlan<TailSchema.TailCmdRaw>)
      decreases *
    {
      var failurePlan := TailSchema.PlanParseFailure(err, argv);
      match failurePlan
      case TailRun(raw) =>
        plan := CliTypes.CliRun(raw);
      case TailParseError(error) =>
        var msg := TailSchema.FormatParseError(error);
        plan := CliTypes.CliEarlyExit(1, [], msg);
    }

    method RunCore(raw: TailSchema.TailCmdRaw, io: BenchIO.IO) returns (exit: int)
      modifies io.stdinRegion, io.stdoutRegion, io.stderrRegion
      ensures CS.Spec(raw, io, exit)
      decreases *
    {
      exit := Exec.RunCore(raw, io);
      CP.CoreSummaryImpliesSpec(raw, io, exit);
    }
  }
}
