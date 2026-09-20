include "FalseSchema.dfy"
include "FalseCore.dfy"
include "FalseSpec.dfy"

module FalseProof {
  import BenchIO
  import Schema = FalseSchema
  import Core = FalseCore
  import Spec = FalseSpec

  twostate lemma CoreSummaryImpliesSpec(raw: Schema.FalseCmdRaw, io: BenchIO.IO, exit: int)
    requires Core.CoreSummary(raw, io, exit)
    ensures Spec.Spec(raw, io, exit)
  {
    reveal Core.CoreSummary();
    reveal Spec.Spec();
    var cmd := Schema.Command(raw);
    if cmd.mode == Schema.ModeHelp {
    } else if cmd.mode == Schema.ModeVersion {
    }
  }
}
