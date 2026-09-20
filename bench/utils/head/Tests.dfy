include "HeadCore.dfy"

module HeadTests {
  import HeadCore

  // A byte limit truncates a larger input at the requested boundary.
  method {:test} TestFirstBytes() {
    expect HeadCore.TakeFirstBytes(['a', 'b', 'c'], 2) == ['a', 'b'];
  }
}
