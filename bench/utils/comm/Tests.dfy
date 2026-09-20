include "CommRenderCore.dfy"

module CommTests {
  import CommRenderCore

  // Null-delimited comparison uses NUL as its record terminator.
  method {:test} TestNullRecordDelimiter() {
    expect CommRenderCore.RecordDelimiter(true) == '\0';
  }
}
