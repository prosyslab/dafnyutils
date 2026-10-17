include "../../core/BenchmarkItem.dfy"
include "SortSpec.dfy"
include "SortCore.dfy"
include "SortProof.dfy"

module Sort {
  import BenchIO
  import BenchWorld
  import BenchItem
  import CliTypes
  import S = SortSchema
  import Core = SortCore
  import Spec = SortSpec
  import Proof = SortProof

  class SortBenchmarkItem extends BenchItem.BenchmarkItemTwostate<S.SortCmdRaw> {
    constructor() {}

    method Name() returns (name: string) {
      name := "sort";
    }

    method Schema() returns (schema: CliTypes.CliSchema) {
      schema := S.Schema();
    }

    method ParseConfig() returns (cfg: CliTypes.ParseConfig) {
      cfg := S.ParserConfig();
    }

    method Decode(parsed: CliTypes.ParsedArgs) returns (raw: S.SortCmdRaw) {
      raw := S.Decode(parsed);
    }

    method FormatParseError(err: CliTypes.ParseError) returns (msg: BenchWorld.Bytes) {
      // TODO: implement and test GNU parse-error behavior, including early exits.
      assert false;
      msg := Spec.ParseErrorText(err);
    }

    method RunCore(raw: S.SortCmdRaw, io: BenchIO.IO) returns (exit: int)
      modifies io.stdinRegion, io.stdoutRegion, io.stderrRegion
      ensures Spec.Spec(raw, io, exit)
    {
      exit := Core.RunCore(raw, io);
      Proof.CoreSummaryImpliesSpec(raw, io, exit);
    }
  }
}
