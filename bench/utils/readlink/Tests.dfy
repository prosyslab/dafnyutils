include "ReadlinkCore.dfy"

module ReadlinkTests {
  import ReadlinkCore
  import BenchWorld

  // A missing link is classified as a missing file.
  method {:test} TestMissingLinkError() {
    expect ReadlinkCore.IOErrorFromErrno(2) == BenchWorld.NoSuchFile;
  }
}
