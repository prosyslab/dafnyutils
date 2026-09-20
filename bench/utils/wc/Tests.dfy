include "WcCore.dfy"

module WcTests {
  import WcCore

  // Tabs separate words in word-count mode.
  method {:test} TestTabWordSeparator() {
    expect WcCore.IsWordSpace('\t');
  }
}
