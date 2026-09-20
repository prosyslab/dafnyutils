include "../../core/IO.dfy"
include "LognameSchema.dfy"
include "LognameCore.dfy"
include "LognameSpec.dfy"

module LognameProof {
  import BenchIO
  import BenchWorld
  import Schema = LognameSchema
  import Core = LognameCore
  import Spec = LognameSpec

  twostate lemma CoreSummaryImpliesSpec(raw: Schema.LognameCmdRaw, io: BenchIO.IO, exit: int)
    requires Core.CoreSummary(raw, io, exit)
    ensures Spec.Spec(raw, io, exit)
  {
    var cmd := Schema.Command(raw);
    if cmd.mode == Schema.ModeHelp {
    } else if cmd.mode == Schema.ModeVersion {
    } else if |cmd.operands| > 0 {
    } else {
      var login: BenchWorld.Result<string> :|
        Core.LoginNameResultFields(
          old(io.props()),
          login,
          old(io.stdout()),
          old(io.stderr()),
          io.stdout(),
          io.stderr(),
          exit
        );
      match login
      case Ok(name) =>
        assert Spec.HasLoginNameProps(old(io.props()));
        assert name == old(io.props())["loginName"];
      case Err(_) =>
        assert !Spec.HasLoginNameProps(old(io.props()));
    }
  }
}
