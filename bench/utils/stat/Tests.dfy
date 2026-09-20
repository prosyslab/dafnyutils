include "StatSchema.dfy"

module StatTests {
  import StatSchema

  // A format is required before stat can enter run mode.
  method {:test} TestMissingFormatMode() {
    var raw := StatSchema.StatCmdRaw(false, false, "", false, false, -1, -1, ["file"]);
    expect StatSchema.RequestedMode(raw) == StatSchema.ModeMissingFormat;
  }
}
