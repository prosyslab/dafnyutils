include "CutCore.dfy"

module CutTests {
  import CutCore

  // Zero-terminated cut records use NUL instead of newline.
  method {:test} TestNullRecordDelimiter() {
    expect CutCore.RecordDelimiter(true) == '\0';
  }
}
