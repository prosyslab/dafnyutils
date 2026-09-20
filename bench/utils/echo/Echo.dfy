include "../../core/World.dfy"
include "../../core/CliTypes.dfy"
include "../../core/BenchmarkItem.dfy"
include "EchoSchema.dfy"
include "EchoCore.dfy"
include "EchoSpec.dfy"
include "EchoProof.dfy"

module Echo {
  import BenchIO
  import CP = EchoProof
  import BenchWorld
  import CliTypes
  import BenchItem
  import EchoSchema
  import Exec = EchoCore
  import ES = EchoSpec

  class {:termination false} EchoBenchmarkItem extends BenchItem.BenchmarkItemTwostate<EchoSchema.EchoCmdRaw> {
    constructor()
    {
    }

    method Name() returns (name: string)
    {
      name := "echo";
    }

    method Schema() returns (schema: CliTypes.CliSchema)
    {
      schema := EchoSchema.Schema();
    }

    method ParseConfig() returns (cfg: CliTypes.ParseConfig)
    {
      cfg := EchoSchema.ParserConfig();
    }

    method Decode(parsed: CliTypes.ParsedArgs) returns (raw: EchoSchema.EchoCmdRaw)
    {
      raw := EchoSchema.Decode(parsed);
    }

    method FormatParseError(err: CliTypes.ParseError) returns (msg: BenchWorld.Bytes)
    {
      msg := EchoSchema.EchoFormatParseError(err);
    }

    method PlanParseFailure(err: CliTypes.ParseError, argv: seq<string>) returns (plan: CliTypes.CliPlan<EchoSchema.EchoCmdRaw>)
      decreases *
    {
      var args := if |argv| > 0 then argv[1..] else [];
      plan := CliTypes.CliRun(EchoSchema.EchoCmdRaw(args));
    }

    method RunCore(raw: EchoSchema.EchoCmdRaw, io: BenchIO.IO) returns (exit: int)
      modifies io.stdoutRegion
      ensures ES.Spec(raw, io, exit)
      decreases *
    {
      exit := Exec.RunCore(raw, io);
      CP.CoreSummaryImpliesSpec(raw, io, exit);
    }
  }
}
