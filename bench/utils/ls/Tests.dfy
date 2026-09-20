include "LsCore.dfy"

module LsTests {
  import LsCore

  // Long listing sizes render as ordinary decimal numbers.
  method {:test} TestDecimalSize() {
    expect LsCore.NatTextCore(1205) == "1205";
  }
}
