include "../../core/IO.dfy"
include "FalseSchema.dfy"
include "FalseSpec.dfy"

module FalseCore {
  import BenchIO
  import Schema = FalseSchema
  import Spec = FalseSpec

  twostate predicate CoreSummary(raw: Schema.FalseCmdRaw, io: BenchIO.IO, exit: int)
    reads io.Footprint()
  {
    var cmd := Schema.Command(raw);
    if cmd.mode == Schema.ModeHelp then
      io.stdout() == old(io.stdout()) + Spec.HelpTextSpec() &&
      io.stderr() == old(io.stderr()) &&
      exit == 1
    else if cmd.mode == Schema.ModeVersion then
      io.stdout() == old(io.stdout()) + Spec.VersionTextSpec() &&
      io.stderr() == old(io.stderr()) &&
      exit == 1
    else
      io.stdout() == old(io.stdout()) &&
      io.stderr() == old(io.stderr()) &&
      exit == 1
  }

  method RunCore(raw: Schema.FalseCmdRaw, io: BenchIO.IO) returns (exit: int)
    modifies io.stdoutRegion
    ensures CoreSummary(raw, io, exit)
    decreases *
  {
    var cmd := Schema.Command(raw);
    if cmd.mode == Schema.ModeHelp {
      var out := Spec.HelpTextSpec();
      io.AppendStdout(out);
      exit := 1;
    } else if cmd.mode == Schema.ModeVersion {
      var out := Spec.VersionTextSpec();
      io.AppendStdout(out);
      exit := 1;
    } else {
      exit := 1;
    }
  }
}
