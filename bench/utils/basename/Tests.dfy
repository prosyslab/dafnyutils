include "BasenameCore.dfy"

module BasenameTests {
  import BasenameCore

  // Trailing slashes must not change the last path component.
  method {:test} TestTrailingSlash()
    decreases *
  {
    var value := BasenameCore.ComputeBasenameValue("/tmp/report///");
    expect value == "report";
  }
}
