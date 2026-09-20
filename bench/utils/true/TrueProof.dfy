include "TrueSchema.dfy"
include "TrueCore.dfy"
include "TrueSpec.dfy"

module TrueProof {
  import BenchIO
  import Schema = TrueSchema
  import Core = TrueCore
  import Spec = TrueSpec

  twostate lemma CoreSummaryImpliesSpec(raw: Schema.TrueCmdRaw, io: BenchIO.IO, exit: int)
    requires Core.CoreSummary(raw, io, exit)
    ensures Spec.Spec(raw, io, exit)
  {
    var cmd := Schema.Command(raw);
    if cmd.mode == Schema.ModeHelp {
    } else if cmd.mode == Schema.ModeVersion {
    }
  }
}
