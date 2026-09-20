include "Base64Core.dfy"

module Base64Tests {
  import Base64Core

  // A base64 alphabet boundary maps index 62 to the plus sign.
  method {:test} TestAlphabetSymbol() {
    expect Base64Core.Alphabet(62) == '+';
  }
}
