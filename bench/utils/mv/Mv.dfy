include "../../core/CliTypes.dfy"
include "../../core/BenchmarkItem.dfy"
include "MvSchema.dfy"
include "MvCore.dfy"
include "MvProof.dfy"
include "MvSpec.dfy"

module Mv {
  import BenchIO
  import MP = MvProof
  import BenchWorld
  import CliTypes
  import BenchItem
  import MvSchema
  import Core = MvCore
  import MS = MvSpec

  class {:termination false} MvBenchmarkItem extends BenchItem.BenchmarkItemTwostate<MvSchema.MvCmdRaw> {
    constructor()
    {
    }

    method Name() returns (name: string)
    {
      name := "mv";
    }

    method Schema() returns (schema: CliTypes.CliSchema)
    {
      schema := MvSchema.Schema();
    }

    method ParseConfig() returns (cfg: CliTypes.ParseConfig)
    {
      cfg := MvSchema.ParserConfig();
    }

    method Decode(parsed: CliTypes.ParsedArgs) returns (raw: MvSchema.MvCmdRaw)
    {
      raw := MvSchema.Decode(parsed);
    }

    method FormatParseError(err: CliTypes.ParseError) returns (msg: BenchWorld.Bytes)
    {
      msg := MvSchema.FormatParseError(err);
    }

    method PlanParseFailure(err: CliTypes.ParseError, argv: seq<string>) returns (plan: CliTypes.CliPlan<MvSchema.MvCmdRaw>)
      decreases *
    {
      plan := MvSchema.PlanParseFailure(err, argv);
    }

    method RunCore(raw: MvSchema.MvCmdRaw, io: BenchIO.IO) returns (exit: int)
      modifies io.fsRegion, io.stdoutRegion, io.stderrRegion
      ensures MS.Spec(raw, io, exit)
      decreases *
    {
      exit := Core.RunCore(raw, io);
      MP.CoreSummaryImpliesSpec(raw, io, exit);
    }
  }
}
