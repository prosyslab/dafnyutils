include "PrintfCore.dfy"

module PrintfTests {
  import PrintfCore

  // A string directive consumes one argument and emits its bytes.
  method {:test} TestStringDirective() {
    var rendered := PrintfCore.RenderRepeated("%s", ["ok"]);
    expect rendered.0 && rendered.1 == ['o', 'k'];
  }
}
