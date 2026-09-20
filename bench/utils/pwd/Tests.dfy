include "PwdCore.dfy"

module PwdTests {
  import PwdCore

  // Logical PWD rejects a parent-directory component.
  method {:test} TestUnsafeLogicalPath() {
    expect PwdCore.ContainsUnsafeComponent(["home", "..", "work"], 0);
  }
}
