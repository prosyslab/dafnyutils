include "ExpandCore.dfy"

module ExpandTests {
  import ExpandCore

  // A nondecimal tab-stop character must be rejected.
  method {:test} TestTabStopDigit() {
    expect ExpandCore.IsDigit('8');
    expect !ExpandCore.IsDigit('x');
  }
}
