include "../../../core/IO.dfy"
include "../Spec/PathchkSchema.dfy"

module PathchkCore {
  import BenchIO
  import Schema = PathchkSchema

  twostate predicate CoreSummary(raw: Schema.PathchkCmdRaw, io: BenchIO.IO, exit: int)
    reads io.stdinRegion, io.stdoutRegion, io.stderrRegion
  {
    // TODO: state what the implementation establishes.
    false
  }

  method RunCore(raw: Schema.PathchkCmdRaw, io: BenchIO.IO) returns (exit: int)
    modifies io.stdinRegion, io.stdoutRegion, io.stderrRegion
    ensures CoreSummary(raw, io, exit)
  {
    // TODO: implement the specified behavior and prove CoreSummary.
    assert false;
    exit := 1;
  }
}
