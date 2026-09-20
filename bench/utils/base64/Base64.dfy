include "../../core/World.dfy"
include "../../core/CliTypes.dfy"
include "../../core/BenchmarkItem.dfy"
include "Base64Schema.dfy"
include "Base64Core.dfy"
include "Base64Spec.dfy"
include "Base64Proof.dfy"

module Base64 {
  import BenchIO
  import BenchWorld
  import CliTypes
  import BenchItem
  import S = Base64Schema
  import Core = Base64Core
  import ES = Base64Spec
  import Proof = Base64Proof

  class {:termination false} Base64BenchmarkItem extends BenchItem.BenchmarkItemTwostate<S.Base64CmdRaw> {
    constructor()
    {
    }

    method Name() returns (name: string)
    {
      name := "base64";
    }

    method Schema() returns (schema: CliTypes.CliSchema)
    {
      schema := S.Schema();
    }

    method ParseConfig() returns (cfg: CliTypes.ParseConfig)
    {
      cfg := S.ParserConfig();
    }

    method Decode(parsed: CliTypes.ParsedArgs) returns (raw: S.Base64CmdRaw)
    {
      raw := S.Decode(parsed);
    }

    method FormatParseError(err: CliTypes.ParseError) returns (msg: BenchWorld.Bytes)
    {
      msg := S.Base64FormatParseError(err);
    }

    method PlanParseFailure(err: CliTypes.ParseError, argv: seq<string>) returns (plan: CliTypes.CliPlan<S.Base64CmdRaw>)
      decreases *
    {
      plan := Core.PlanParseFailure(err, argv);
    }

    method RunCore(raw: S.Base64CmdRaw, io: BenchIO.IO) returns (exit: int)
      modifies io.stdinRegion, io.stdoutRegion, io.stderrRegion
      ensures ES.Spec(raw, io, exit)
      decreases *
    {
      exit := Core.RunCore(raw, io);
      Proof.CoreSummaryImpliesSpec(raw, io, exit);
    }
  }
}
