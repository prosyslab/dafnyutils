include "../../core/World.dfy"
include "../../core/CliTypes.dfy"
include "../../core/BenchmarkItem.dfy"
include "TrSchema.dfy"
include "TrCore.dfy"
include "TrSpec.dfy"
include "TrProof.dfy"

module Tr {
  import BenchIO
  import BenchWorld
  import CliTypes
  import BenchItem
  import TrSchema
  import Exec = TrCore
  import TS = TrSpec
  import Proof = TrProof

  class {:termination false} TrBenchmarkItem extends BenchItem.BenchmarkItemTwostate<TrSchema.TrCmdRaw> {
    constructor()
    {
    }

    method Name() returns (name: string)
    {
      name := "tr";
    }

    method Schema() returns (schema: CliTypes.CliSchema)
    {
      schema := TrSchema.Schema();
    }

    method ParseConfig() returns (cfg: CliTypes.ParseConfig)
    {
      cfg := TrSchema.ParserConfig();
    }

    method Decode(parsed: CliTypes.ParsedArgs) returns (raw: TrSchema.TrCmdRaw)
    {
      raw := TrSchema.Decode(parsed);
    }

    method FormatParseError(err: CliTypes.ParseError) returns (msg: BenchWorld.Bytes)
    {
      msg := TrSchema.FormatParseError(err);
    }

    method PlanParseFailure(err: CliTypes.ParseError, argv: seq<string>) returns (plan: CliTypes.CliPlan<TrSchema.TrCmdRaw>)
      decreases *
    {
      plan := TrSchema.PlanParseFailure(err, argv);
    }

    method RunCore(raw: TrSchema.TrCmdRaw, io: BenchIO.IO) returns (exit: int)
      modifies io.stdinRegion, io.stdoutRegion, io.stderrRegion
      ensures TS.Spec(raw, io, exit)
      decreases *
    {
      exit := Exec.RunCore(raw, io);
      Proof.CoreSummaryImpliesSpec(raw, io, exit);
    }
  }
}
