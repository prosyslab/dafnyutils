include "../../core/CliTypes.dfy"
include "../../core/BenchmarkItem.dfy"
include "TouchSchema.dfy"
include "TouchCore.dfy"
include "TouchProof.dfy"
include "TouchSpec.dfy"

module Touch {
  import BenchIO
  import TP = TouchProof
  import BenchWorld
  import CliTypes
  import BenchItem
  import TouchSchema
  import Core = TouchCore
  import TS = TouchSpec

  class {:termination false} TouchBenchmarkItem extends BenchItem.BenchmarkItemTwostate<TouchSchema.TouchCmdRaw> {
    constructor()
    {
    }

    method Name() returns (name: string)
    {
      name := "touch";
    }

    method Schema() returns (schema: CliTypes.CliSchema)
    {
      schema := TouchSchema.Schema();
    }

    method ParseConfig() returns (cfg: CliTypes.ParseConfig)
    {
      cfg := TouchSchema.ParserConfig();
    }

    method Decode(parsed: CliTypes.ParsedArgs) returns (raw: TouchSchema.TouchCmdRaw)
    {
      raw := TouchSchema.Decode(parsed);
    }

    method FormatParseError(err: CliTypes.ParseError) returns (msg: BenchWorld.Bytes)
      ensures msg == TS.ParseErrorMessageSpec(err)
    {
      msg := TouchSchema.FormatParseError(err);
      TP.ParseErrorMessageImpliesSpec(err);
    }

    method PlanParseFailure(err: CliTypes.ParseError, argv: seq<string>) returns (plan: CliTypes.CliPlan<TouchSchema.TouchCmdRaw>)
      ensures TS.ParseFailureSpec(err, plan)
      decreases *
    {
      plan := TouchSchema.PlanParseFailure(err, argv);
      TP.ParseFailurePlanImpliesSpec(err, plan);
    }

    method RunCore(raw: TouchSchema.TouchCmdRaw, io: BenchIO.IO) returns (exit: int)
      modifies io.fsRegion, io.stdoutRegion, io.stderrRegion, io.stdoutTimestampRegion
      ensures TS.Spec(raw, io, exit)
      decreases *
    {
      exit := Core.RunCore(raw, io);
      TP.CoreSummaryImpliesSpec(raw, io, exit);
    }
  }
}
