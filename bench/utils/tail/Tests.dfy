include "TailCore.dfy"

module TailTests {
  import TailCore

  // A trailing byte limit keeps the final bytes.
  method {:test} TestLastBytes() {
    expect TailCore.TakeLastBytes(['a', 'b', 'c'], 2) == ['b', 'c'];
  }
}
