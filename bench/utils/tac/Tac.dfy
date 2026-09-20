include "../../core/World.dfy"
include "../../core/CliTypes.dfy"
include "../../core/BenchmarkItem.dfy"
include "TacSchema.dfy"
include "TacCore.dfy"
include "TacSpec.dfy"
include "TacProof.dfy"

module Tac {
  import BenchIO
  import BenchWorld
  import CliTypes
  import BenchItem
  import TacSchema
  import Exec = TacCore
  import TS = TacSpec
  import TP = TacProof

  class {:termination false} TacBenchmarkItem extends BenchItem.BenchmarkItemTwostate<TacSchema.TacCmdRaw> {
    constructor()
    {
    }

    method Name() returns (name: string)
    {
      name := "tac";
    }

    method Schema() returns (schema: CliTypes.CliSchema)
    {
      schema := TacSchema.Schema();
    }

    method ParseConfig() returns (cfg: CliTypes.ParseConfig)
    {
      cfg := TacSchema.ParserConfig();
    }

    method Decode(parsed: CliTypes.ParsedArgs) returns (raw: TacSchema.TacCmdRaw)
    {
      raw := TacSchema.Decode(parsed);
    }

    method FormatParseError(err: CliTypes.ParseError) returns (msg: BenchWorld.Bytes)
    {
      msg := TacSchema.FormatParseError(err);
    }

    method PlanParseFailure(err: CliTypes.ParseError, argv: seq<string>)
      returns (plan: CliTypes.CliPlan<TacSchema.TacCmdRaw>)
      decreases *
    {
      plan := TacSchema.PlanParseFailure(err, argv);
    }

    method RunCore(raw: TacSchema.TacCmdRaw, io: BenchIO.IO) returns (exit: int)
      modifies io.stdinRegion, io.stdoutRegion, io.stderrRegion
      ensures TS.Spec(raw, io, exit)
      decreases *
    {
      exit := Exec.RunCore(raw, io);
      TP.CoreSummaryImpliesSpec(raw, io, exit);
    }
  }
}
