include "ExprCore.dfy"

module ExprTests {
  import ExprCore

  // Multi-digit unsigned operands retain their decimal value.
  method {:test} TestUnsignedOperand() {
    expect ExprCore.ParseUnsigned("204", 0, 0) == 204;
  }
}
