include "../../core/World.dfy"
include "../../core/CliTypes.dfy"
include "../../core/BenchmarkItem.dfy"
include "SeqSchema.dfy"
include "SeqCore.dfy"
include "SeqSpec.dfy"
include "SeqProof.dfy"

module Seq {
  import BenchIO
  import SP = SeqProof
  import BenchWorld
  import CliTypes
  import BenchItem
  import SeqSchema
  import Core = SeqCore
  import SS = SeqSpec

  class {:termination false} SeqBenchmarkItem extends BenchItem.BenchmarkItemTwostate<SeqSchema.SeqCmdRaw> {
    constructor()
    {
    }

    method Name() returns (name: string)
    {
      name := "seq";
    }

    method Schema() returns (schema: CliTypes.CliSchema)
    {
      schema := SeqSchema.Schema();
    }

    method ParseConfig() returns (cfg: CliTypes.ParseConfig)
    {
      cfg := SeqSchema.ParserConfig();
    }

    method Decode(parsed: CliTypes.ParsedArgs) returns (raw: SeqSchema.SeqCmdRaw)
    {
      raw := SeqSchema.Decode(parsed);
    }

    method FormatParseError(err: CliTypes.ParseError) returns (msg: BenchWorld.Bytes)
    {
      msg := SeqSchema.FormatParseError(err);
    }

    method PlanParseFailure(err: CliTypes.ParseError, argv: seq<string>) returns (plan: CliTypes.CliPlan<SeqSchema.SeqCmdRaw>)
      decreases *
    {
      plan := SeqSchema.PlanParseFailure(err, argv);
    }

    method RunCore(raw: SeqSchema.SeqCmdRaw, io: BenchIO.IO) returns (exit: int)
      modifies io.stdoutRegion, io.stderrRegion
      ensures SS.Spec(raw, io, exit)
      decreases *
    {
      exit := Core.RunCore(raw, io);
      SP.CoreSummaryImpliesSpec(raw, io, exit);
    }
  }
}
