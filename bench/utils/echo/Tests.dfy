include "EchoCore.dfy"

module EchoTests {
  import EchoCore

  // A combined option token must be recognized, while an unknown letter remains an operand.
  method {:test} TestOptionTokenClassification() {
    expect EchoCore.IsEchoOptionToken("-ne");
    expect !EchoCore.IsEchoOptionToken("-nx");
  }
}
