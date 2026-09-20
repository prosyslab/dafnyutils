include "DuCore.dfy"

module DuTests {
  import DuCore

  // Disk-use counts render decimal digits without padding.
  method {:test} TestDecimalCount() {
    expect DuCore.NatText(1205) == "1205";
  }
}
