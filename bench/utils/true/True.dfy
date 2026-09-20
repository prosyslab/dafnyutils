include "../../core/World.dfy"
include "../../core/CliTypes.dfy"
include "../../core/BenchmarkItem.dfy"
include "TrueSchema.dfy"
include "TrueCore.dfy"
include "TrueSpec.dfy"
include "TrueProof.dfy"

module True {
  import BenchIO
  import TP = TrueProof
  import BenchWorld
  import CliTypes
  import BenchItem
  import TrueSchema
  import Core = TrueCore
  import TS = TrueSpec

  class {:termination false} TrueBenchmarkItem extends BenchItem.BenchmarkItemTwostate<TrueSchema.TrueCmdRaw> {
    constructor()
    {
    }

    method Name() returns (name: string)
    {
      name := "true";
    }

    method Schema() returns (schema: CliTypes.CliSchema)
    {
      schema := TrueSchema.Schema();
    }

    method ParseConfig() returns (cfg: CliTypes.ParseConfig)
    {
      cfg := TrueSchema.ParserConfig();
    }

    method Decode(parsed: CliTypes.ParsedArgs) returns (raw: TrueSchema.TrueCmdRaw)
    {
      raw := TrueSchema.Decode(parsed);
    }

    method FormatParseError(err: CliTypes.ParseError) returns (msg: BenchWorld.Bytes)
    {
      msg := TrueSchema.FormatParseError(err);
    }

    method PlanParseFailure(err: CliTypes.ParseError, argv: seq<string>) returns (plan: CliTypes.CliPlan<TrueSchema.TrueCmdRaw>)
      decreases *
    {
      plan := TrueSchema.PlanParseFailure(err, argv);
    }

    method PlanArgv(argv: seq<string>) returns (plan: CliTypes.CliPlan<TrueSchema.TrueCmdRaw>)
      decreases *
    {
      var raw := TrueSchema.FromArgv(argv);
      plan := CliTypes.CliRun(raw);
    }

    method RunCore(raw: TrueSchema.TrueCmdRaw, io: BenchIO.IO) returns (exit: int)
      modifies io.stdoutRegion
      ensures TS.Spec(raw, io, exit)
      decreases *
    {
      exit := Core.RunCore(raw, io);
      TP.CoreSummaryImpliesSpec(raw, io, exit);
    }
  }
}
