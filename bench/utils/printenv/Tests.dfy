include "PrintenvCore.dfy"

module PrintenvTests {
  import PrintenvCore

  // An environment value may itself contain an equals sign.
  method {:test} TestEmbeddedEquals() {
    expect PrintenvCore.EntryValue("KEY=a=b") == "a=b";
  }
}
