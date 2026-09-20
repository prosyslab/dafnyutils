include "../../core/World.dfy"
include "../../core/CliTypes.dfy"
include "../../core/BenchmarkItem.dfy"
include "TeeSchema.dfy"
include "TeeCore.dfy"
include "TeeSpec.dfy"
include "TeeProof.dfy"

module Tee {
  import BenchIO
  import BenchWorld
  import CliTypes
  import BenchItem
  import S = TeeSchema
  import Core = TeeCore
  import TS = TeeSpec
  import Proof = TeeProof

  class {:termination false} TeeBenchmarkItem extends BenchItem.BenchmarkItemTwostate<S.TeeCmdRaw> {
    constructor()
    {
    }

    method Name() returns (name: string)
    {
      name := "tee";
    }

    method Schema() returns (schema: CliTypes.CliSchema)
    {
      schema := S.Schema();
    }

    method ParseConfig() returns (cfg: CliTypes.ParseConfig)
    {
      cfg := S.ParserConfig();
    }

    method Decode(parsed: CliTypes.ParsedArgs) returns (raw: S.TeeCmdRaw)
    {
      raw := S.Decode(parsed);
    }

    method FormatParseError(err: CliTypes.ParseError) returns (msg: BenchWorld.Bytes)
    {
      msg := S.FormatParseError(err);
    }

    method PlanParseFailure(err: CliTypes.ParseError, argv: seq<string>) returns (plan: CliTypes.CliPlan<S.TeeCmdRaw>)
      decreases *
    {
      plan := S.PlanParseFailure(err, argv);
    }

    method RunCore(raw: S.TeeCmdRaw, io: BenchIO.IO) returns (exit: int)
      modifies io.fsRegion, io.stdinRegion, io.stdoutRegion, io.stderrRegion
      ensures TS.Spec(raw, io, exit)
      decreases *
    {
      exit := Core.RunCore(raw, io);
      Proof.CoreSummaryImpliesSpec(raw, io, exit);
    }
  }
}
