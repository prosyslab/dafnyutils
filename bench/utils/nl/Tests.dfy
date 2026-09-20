include "NlCore.dfy"

module NlTests {
  import NlCore

  // Blank padding emits the requested number of characters.
  method {:test} TestNumberPadding() {
    expect NlCore.RepeatChar(' ', 3) == [' ', ' ', ' '];
  }
}
