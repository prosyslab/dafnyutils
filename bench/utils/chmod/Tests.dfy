include "ChmodSchema.dfy"

module ChmodTests {
  import ChmodSchema

  // The symbolic mode parser recognizes a change operator.
  method {:test} TestSymbolicModeOperator() {
    expect ChmodSchema.ModeIsOp('+');
    expect !ChmodSchema.ModeIsOp('x');
  }
}
