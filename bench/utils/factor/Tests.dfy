include "FactorCore.dfy"

module FactorTests {
  import FactorCore

  // Factor input ignores whitespace surrounding a number.
  method {:test} TestTrimInput() {
    expect FactorCore.TrimWhitespace("  12 \n") == "12";
  }
}
