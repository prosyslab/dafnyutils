include "../../core/World.dfy"
include "../../core/CliTypes.dfy"
include "../../core/BenchmarkItem.dfy"
include "UniqSchema.dfy"
include "UniqCore.dfy"
include "UniqSpec.dfy"
include "UniqProof.dfy"

module Uniq {
  import BenchIO
  import BenchWorld
  import CliTypes
  import BenchItem
  import UniqSchema
  import Exec = UniqCore
  import US = UniqSpec
  import Proof = UniqProof

  class {:termination false} UniqBenchmarkItem extends BenchItem.BenchmarkItemTwostate<UniqSchema.UniqCmdRaw> {
    constructor()
    {
    }

    method Name() returns (name: string)
    {
      name := "uniq";
    }

    method Schema() returns (schema: CliTypes.CliSchema)
    {
      schema := UniqSchema.Schema();
    }

    method ParseConfig() returns (cfg: CliTypes.ParseConfig)
    {
      cfg := UniqSchema.ParserConfig();
    }

    method Decode(parsed: CliTypes.ParsedArgs) returns (raw: UniqSchema.UniqCmdRaw)
    {
      raw := UniqSchema.Decode(parsed);
    }

    method FormatParseError(err: CliTypes.ParseError) returns (msg: BenchWorld.Bytes)
    {
      msg := UniqSchema.FormatParseError(err);
    }

    method PlanParseFailure(err: CliTypes.ParseError, argv: seq<string>) returns (plan: CliTypes.CliPlan<UniqSchema.UniqCmdRaw>)
      decreases *
    {
      plan := UniqSchema.PlanParseFailure(err, argv);
    }

    method RunCore(raw: UniqSchema.UniqCmdRaw, io: BenchIO.IO) returns (exit: int)
      modifies io.stdinRegion, io.stdoutRegion, io.stderrRegion
      ensures US.Spec(raw, io, exit)
      decreases *
    {
      ghost var witnessResult: BenchWorld.Result<BenchWorld.Bytes>;
      ghost var stdoutPart: BenchWorld.Bytes;
      ghost var stderrPart: BenchWorld.Bytes;
      ghost var hadError: bool;
      exit, witnessResult, stdoutPart, stderrPart, hadError :=
        Exec.RunCore(raw, io);
      Proof.CoreSummaryImpliesSpec(
        raw, io, exit, [witnessResult], stdoutPart, stderrPart, hadError
      );
    }
  }
}
