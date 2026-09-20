include "TeeCore.dfy"

module TeeTests {
  import TeeCore
  import TeeSchema

  // Append mode remains set when tee has an output operand.
  method {:test} TestAppendCommand() {
    var raw := TeeSchema.TeeCmdRaw(true, false, false, false, -1, -1, ["out"]);
    expect TeeCore.Command(raw).append;
  }
}
