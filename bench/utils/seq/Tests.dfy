include "SeqCore.dfy"

module SeqTests {
  import SeqCore

  // Sequence number parsing rejects a sign as a decimal digit.
  method {:test} TestDecimalDigit() {
    expect SeqCore.IsDigit('9');
    expect !SeqCore.IsDigit('-');
  }
}
