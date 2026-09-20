include "TrCore.dfy"

module TrTests {
  import TrCore

  // A character range expands inclusively for translation.
  method {:test} TestInclusiveRange() {
    expect TrCore.RangeChars('a', 'c') == ['a', 'b', 'c'];
  }
}
