include "../../core/World.dfy"
include "../../core/CliTypes.dfy"
include "../../core/BenchmarkItem.dfy"
include "CutSchema.dfy"
include "CutCore.dfy"
include "CutProof.dfy"
include "CutSpec.dfy"

module Cut {
  import BenchIO
  import BenchWorld
  import CliTypes
  import BenchItem
  import CutSchema
  import Exec = CutCore
  import CS = CutSpec
  import Proof = CutProof

  class {:termination false} CutBenchmarkItem extends BenchItem.BenchmarkItemTwostate<CutSchema.CutCmdRaw> {
    constructor()
    {
    }

    method Name() returns (name: string)
    {
      name := "cut";
    }

    method Schema() returns (schema: CliTypes.CliSchema)
    {
      schema := CutSchema.Schema();
    }

    method ParseConfig() returns (cfg: CliTypes.ParseConfig)
    {
      cfg := CutSchema.ParserConfig();
    }

    method Decode(parsed: CliTypes.ParsedArgs) returns (raw: CutSchema.CutCmdRaw)
    {
      raw := CutSchema.Decode(parsed);
    }

    method FormatParseError(err: CliTypes.ParseError) returns (msg: BenchWorld.Bytes)
    {
      msg := CutSchema.ParseErrorMessage(err);
    }

    method PlanParseFailure(err: CliTypes.ParseError, argv: seq<string>) returns (plan: CliTypes.CliPlan<CutSchema.CutCmdRaw>)
      decreases *
    {
      match CliTypes.PriorHelpVersionRequest(argv, err.tokenIndex)
      case RequestHelp =>
        var selection := CutSchema.DefaultSelection();
        plan := CliTypes.CliRun(CutSchema.CutCmdRaw(
                                  CutSchema.ModeHelp, selection, CutSchema.OutputDefault, false, []
                                ));
      case RequestVersion =>
        var selection := CutSchema.DefaultSelection();
        plan := CliTypes.CliRun(CutSchema.CutCmdRaw(
                                  CutSchema.ModeVersion, selection, CutSchema.OutputDefault, false, []
                                ));
      case RequestNone =>
        var msg := CutSchema.ParseErrorMessage(err);
        plan := CliTypes.CliEarlyExit(1, [], msg);
    }

    method PlanParsed(parsed: CliTypes.ParsedArgs) returns (plan: CliTypes.CliPlan<CutSchema.CutCmdRaw>)
      decreases *
    {
      var parsedPlan := CutSchema.PlanParsed(parsed);
      match parsedPlan
      case ParsedRun(raw) =>
        plan := CliTypes.CliRun(raw);
      case ParsedError(error) =>
        var msg := CutSchema.PlanErrorMessage(error);
        plan := CliTypes.CliEarlyExit(1, [], msg);
    }

    method RunCore(raw: CutSchema.CutCmdRaw, io: BenchIO.IO) returns (exit: int)
      modifies io.stdinRegion, io.stdoutRegion, io.stderrRegion
      ensures CS.Spec(raw, io, exit)
      decreases *
    {
      exit := Exec.RunCore(raw, io);
      Proof.CoreSummaryImpliesSpec(raw, io, exit);
    }
  }
}
