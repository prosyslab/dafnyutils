include "FalseSchema.dfy"

module FalseTests {
  import FalseSchema

  // Ordinary operands do not select the special help mode.
  method {:test} TestIgnoredOperands() {
    var raw := FalseSchema.FalseCmdRaw(false, false, -1, -1, ["ignored"]);
    expect FalseSchema.Command(raw).mode == FalseSchema.ModeRun;
  }
}
