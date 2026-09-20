include "../../core/World.dfy"
include "../../core/IO.dfy"
include "../../core/CliTypes.dfy"
include "../../core/BenchmarkItem.dfy"
include "PwdSchema.dfy"
include "PwdCore.dfy"
include "PwdProof.dfy"
include "PwdSpec.dfy"

module Pwd {
  import BenchIO
  import PP = PwdProof
  import BenchWorld
  import CliTypes
  import BenchItem
  import PwdSchema
  import Core = PwdCore
  import PS = PwdSpec

  class {:termination false} PwdBenchmarkItem extends BenchItem.BenchmarkItemTwostate<PwdSchema.PwdCmdRaw> {
    constructor()
    {
    }

    method Name() returns (name: string)
    {
      name := "pwd";
    }

    method Schema() returns (schema: CliTypes.CliSchema)
    {
      schema := PwdSchema.Schema();
    }

    method ParseConfig() returns (cfg: CliTypes.ParseConfig)
    {
      cfg := PwdSchema.ParserConfig();
    }

    method Decode(parsed: CliTypes.ParsedArgs) returns (raw: PwdSchema.PwdCmdRaw)
    {
      raw := PwdSchema.Decode(parsed);
    }

    method FormatParseError(err: CliTypes.ParseError) returns (msg: BenchWorld.Bytes)
    {
      msg := PwdSchema.FormatParseError(err);
    }

    method PlanParseFailure(err: CliTypes.ParseError, argv: seq<string>) returns (plan: CliTypes.CliPlan<PwdSchema.PwdCmdRaw>)
      decreases *
    {
      plan := PwdSchema.PlanParseFailure(err, argv);
    }

    method RunCore(raw: PwdSchema.PwdCmdRaw, io: BenchIO.IO) returns (exit: int)
      modifies io.stdoutRegion, io.stderrRegion
      ensures PS.Spec(raw, io, exit)
      decreases *
    {
      exit := Core.RunCore(raw, io);
      PP.CoreSummaryImpliesSpec(raw, io, exit);
    }
  }
}
