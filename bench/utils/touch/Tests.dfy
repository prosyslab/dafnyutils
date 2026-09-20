include "TouchSchema.dfy"

module TouchTests {
  import TouchSchema

  // A shortened access-time word still selects access time.
  method {:test} TestAccessTimeAbbreviation() {
    expect TouchSchema.ClassifyTimeWord("acc") == TouchSchema.TimeWordAccess;
  }
}
