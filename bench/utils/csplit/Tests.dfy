include "CsplitCore.dfy"

module CsplitTests {
  import CsplitCore

  // Splitting at the second line starts after the first newline.
  method {:test} TestSecondLineStart() {
    expect CsplitCore.LineStart(['a', '\n', 'b'], 2) == 2;
  }
}
