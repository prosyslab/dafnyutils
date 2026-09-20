include "../../core/IO.dfy"
include "TrueSchema.dfy"
include "TrueSpec.dfy"

module TrueCore {
  import BenchIO
  import Schema = TrueSchema
  import Spec = TrueSpec

  twostate predicate CoreSummary(raw: Schema.TrueCmdRaw, io: BenchIO.IO, exit: int)
    reads io.Footprint()
  {
    var cmd := Schema.Command(raw);
    if cmd.mode == Schema.ModeHelp then
      io.stdout() == old(io.stdout()) + Spec.HelpTextSpec() &&
      exit == 0
    else if cmd.mode == Schema.ModeVersion then
      io.stdout() == old(io.stdout()) + Spec.VersionTextSpec() &&
      exit == 0
    else
      io.stdout() == old(io.stdout()) &&
      exit == 0
  }

  method RunCore(raw: Schema.TrueCmdRaw, io: BenchIO.IO) returns (exit: int)
    modifies io.stdoutRegion
    ensures CoreSummary(raw, io, exit)
    decreases *
  {
    var cmd := Schema.Command(raw);
    if cmd.mode == Schema.ModeHelp {
      var out := Spec.HelpTextSpec();
      io.AppendStdout(out);
      exit := 0;
    } else if cmd.mode == Schema.ModeVersion {
      var out := Spec.VersionTextSpec();
      io.AppendStdout(out);
      exit := 0;
    } else {
      exit := 0;
    }
  }
}
