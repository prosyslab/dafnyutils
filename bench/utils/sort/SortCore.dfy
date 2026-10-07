include "../../core/IO.dfy"
include "SortSchema.dfy"

module SortCore {
  import BenchIO
  import Schema = SortSchema

  twostate predicate CoreSummary(raw: Schema.SortCmdRaw, io: BenchIO.IO, exit: int)
    reads io.stdinRegion, io.stdoutRegion, io.stderrRegion
  {
    // TODO: state what the implementation establishes.
    false
  }

  method RunCore(raw: Schema.SortCmdRaw, io: BenchIO.IO) returns (exit: int)
    modifies io.stdinRegion, io.stdoutRegion, io.stderrRegion
    ensures CoreSummary(raw, io, exit)
  {
    // TODO: implement the agreed behavior and prove CoreSummary.
    assert false;
    exit := 1;
  }
}
