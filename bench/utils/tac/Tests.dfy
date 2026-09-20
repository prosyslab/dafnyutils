include "TacCore.dfy"

module TacTests {
  import TacCore

  // A record separator is recognized only at its exact byte offset.
  method {:test} TestSeparatorOffset() {
    expect TacCore.MatchAt(['a', '\n', 'b'], ['\n'], 1);
    expect !TacCore.MatchAt(['a', '\n', 'b'], ['\n'], 2);
  }
}
