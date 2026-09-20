include "TrueSchema.dfy"

module TrueTests {
  import TrueSchema

  // Ordinary operands do not select the special version mode.
  method {:test} TestIgnoredOperands() {
    var raw := TrueSchema.TrueCmdRaw(false, false, -1, -1, ["ignored"]);
    expect TrueSchema.Command(raw).mode == TrueSchema.ModeRun;
  }
}
