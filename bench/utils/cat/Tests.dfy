include "CatCore.dfy"

module CatTests {
  import CatCoreModel

  // Numbered output uses a six-column field followed by a tab.
  method {:test} TestLineNumberText() {
    expect CatCoreModel.LineNumberText(12) == [' ', ' ', ' ', ' ', '1', '2', '\t'];
  }
}
