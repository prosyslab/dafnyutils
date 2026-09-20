include "MvCore.dfy"

module MvTests {
  import MvCore

  // Moving into a directory keeps the source leaf name.
  method {:test} TestSourceLeaf() {
    expect MvCore.SourceLeafName("a/report") == "report";
  }
}
