include "FoldCore.dfy"

module FoldTests {
  import FoldCore

  // Width parsing accepts decimal digits and rejects letters.
  method {:test} TestWidthDigit() {
    expect FoldCore.IsDigit('4');
    expect !FoldCore.IsDigit('a');
  }
}
