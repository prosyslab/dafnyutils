include "../../core/World.dfy"
include "../../core/CliTypes.dfy"
include "../../core/BenchmarkItem.dfy"
include "WcSchema.dfy"
include "WcCore.dfy"
include "WcSpec.dfy"
include "WcProof.dfy"

module Wc {
  import BenchIO
  import CP = WcProof
  import BenchWorld
  import CliTypes
  import BenchItem
  import WcSchema
  import Exec = WcCore
  import CS = WcSpec

  class {:termination false} WcBenchmarkItem extends BenchItem.BenchmarkItemTwostate<WcSchema.WcCmdRaw> {
    constructor()
    {
    }

    method Name() returns (name: string)
    {
      name := "wc";
    }

    method Schema() returns (schema: CliTypes.CliSchema)
    {
      schema := WcSchema.Schema();
    }

    method ParseConfig() returns (cfg: CliTypes.ParseConfig)
    {
      cfg := WcSchema.ParserConfig();
    }

    method Decode(parsed: CliTypes.ParsedArgs) returns (raw: WcSchema.WcCmdRaw)
    {
      raw := WcSchema.Decode(parsed);
    }

    method FormatParseError(err: CliTypes.ParseError) returns (msg: BenchWorld.Bytes)
    {
      msg := WcSchema.FormatParseError(err);
    }

    method PlanParseFailure(err: CliTypes.ParseError, argv: seq<string>) returns (plan: CliTypes.CliPlan<WcSchema.WcCmdRaw>)
      decreases *
    {
      plan := WcSchema.PlanParseFailure(err, argv);
    }

    method RunCore(raw: WcSchema.WcCmdRaw, io: BenchIO.IO) returns (exit: int)
      modifies io.stdinRegion, io.stdoutRegion, io.stderrRegion
      ensures CS.Spec(raw, io, exit)
      decreases *
    {
      exit := Exec.RunCore(raw, io);
      CP.CoreSummaryImpliesSpec(raw, io, exit);
    }
  }
}
