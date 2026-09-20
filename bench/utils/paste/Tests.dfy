include "PasteCore.dfy"

module PasteTests {
  import PasteCore

  // Zero-terminated paste records use NUL as the separator.
  method {:test} TestNullRecordDelimiter() {
    expect PasteCore.RecordDelimiter(true) == '\0';
  }
}
