include "LognameSchema.dfy"

module LognameTests {
  import LognameSchema

  // A sole version request takes precedence over ordinary execution.
  method {:test} TestVersionMode() {
    var raw := LognameSchema.LognameCmdRaw(false, true, -1, 0, []);
    expect LognameSchema.Command(raw).mode == LognameSchema.ModeVersion;
  }
}
