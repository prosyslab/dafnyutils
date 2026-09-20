include "LnSchema.dfy"

module LnTests {
  import LnSchema

  // Symbolic link mode retains the selected flag in the decoded command.
  method {:test} TestSymbolicCommand() {
    var raw := LnSchema.LnCmdRaw(true, false, false, -1, -1, ["source", "target"]);
    expect LnSchema.Command(raw).symbolic;
  }
}
