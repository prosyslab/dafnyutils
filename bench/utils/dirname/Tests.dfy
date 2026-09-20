include "DirnameCore.dfy"

module DirnameTests {
  import DirnameCore

  // The parent of a nested path survives trailing slashes.
  method {:test} TestNestedParent()
    decreases *
  {
    var value := DirnameCore.ComputeDirnameValue("/tmp/report///");
    expect value == "/tmp";
  }
}
