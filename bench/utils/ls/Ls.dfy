include "../../core/World.dfy"
include "../../core/IO.dfy"
include "../../core/CliTypes.dfy"
include "../../core/BenchmarkItem.dfy"
include "LsSchema.dfy"
include "LsSpec.dfy"
include "LsCore.dfy"
include "LsProof.dfy"

module Ls {
  import BenchIO
  import BenchWorld
  import CliTypes
  import BenchItem
  import Sch = LsSchema
  import Spec = LsSpec
  import Core = LsCore
  import Proof = LsProof

  class {:termination false} LsBenchmarkItem extends BenchItem.BenchmarkItemTwostate<Sch.LsCmdRaw> {
    constructor()
    {
    }

    method Name() returns (name: string)
    {
      name := "ls";
    }

    method Schema() returns (schema: CliTypes.CliSchema)
    {
      schema := Sch.Schema();
    }

    method ParseConfig() returns (cfg: CliTypes.ParseConfig)
    {
      cfg := Sch.ParserConfig();
    }

    method Decode(parsed: CliTypes.ParsedArgs) returns (raw: Sch.LsCmdRaw)
    {
      raw := Sch.Decode(parsed);
    }

    method FormatParseError(err: CliTypes.ParseError) returns (msg: BenchWorld.Bytes)
    {
      msg := Sch.FormatParseError(err);
    }

    method PlanParseFailure(
      err: CliTypes.ParseError,
      argv: seq<string>
    ) returns (plan: CliTypes.CliPlan<Sch.LsCmdRaw>)
      decreases *
    {
      plan := Sch.PlanParseFailure(err, argv);
    }

    method RunCore(raw: Sch.LsCmdRaw, io: BenchIO.IO) returns (exit: int)
      modifies io.stdoutRegion, io.stderrRegion, io.dirHandlesRegion
      ensures Spec.Spec(raw, io, exit)
      decreases *
    {
      exit := Core.RunCore(raw, io);
      Proof.CoreSummaryImpliesSpec(raw, io, exit);
    }
  }
}
