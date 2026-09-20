include "../../core/World.dfy"
include "../../core/CliTypes.dfy"
include "../../core/BenchmarkItem.dfy"
include "ExprSchema.dfy"
include "ExprCore.dfy"
include "ExprSpec.dfy"
include "ExprProof.dfy"

module Expr {
  import BenchIO
  import CP = ExprProof
  import BenchWorld
  import CliTypes
  import BenchItem
  import ExprSchema
  import Exec = ExprCore
  import ES = ExprSpec

  class {:termination false} ExprBenchmarkItem extends BenchItem.BenchmarkItemTwostate<ExprSchema.ExprCmdRaw> {
    constructor()
    {
    }

    method Name() returns (name: string)
    {
      name := "expr";
    }

    method Schema() returns (schema: CliTypes.CliSchema)
    {
      schema := ExprSchema.Schema();
    }

    method ParseConfig() returns (cfg: CliTypes.ParseConfig)
    {
      cfg := ExprSchema.ParserConfig();
    }

    method Decode(parsed: CliTypes.ParsedArgs) returns (raw: ExprSchema.ExprCmdRaw)
    {
      raw := ExprSchema.Decode(parsed);
    }

    method FormatParseError(err: CliTypes.ParseError) returns (msg: BenchWorld.Bytes)
    {
      msg := ExprSchema.ExprFormatParseError(err);
    }

    method PlanParseFailure(err: CliTypes.ParseError, argv: seq<string>) returns (plan: CliTypes.CliPlan<ExprSchema.ExprCmdRaw>)
      decreases *
    {
      var args := if |argv| > 0 then argv[1..] else [];
      plan := CliTypes.CliRun(ExprSchema.ExprCmdRaw(args));
    }

    method RunCore(raw: ExprSchema.ExprCmdRaw, io: BenchIO.IO) returns (exit: int)
      modifies io.stdoutRegion, io.stderrRegion
      ensures ES.Spec(raw, io, exit)
      decreases *
    {
      exit := Exec.RunCore(raw, io);
      CP.CoreSummaryImpliesSpec(raw, io, exit);
    }
  }
}
