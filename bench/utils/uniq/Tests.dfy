include "UniqCore.dfy"

module UniqTests {
  import UniqCore

  // Case-insensitive comparison folds uppercase ASCII.
  method {:test} TestAsciiCaseFold() {
    expect UniqCore.LowerAscii('A') == 'a';
  }
}
