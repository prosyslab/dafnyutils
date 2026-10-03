include "SortSchema.dfy"
include "../../core/IO.dfy"

module SortSpec {
  import BenchIO
  import BenchWorld
  import CliTypes
  import Schema = SortSchema

  function ParseErrorText(err: CliTypes.ParseError): BenchWorld.Bytes
  {
    // TODO: define the exact GNU diagnostic bytes here, including fixed text.
    []
  }

  // TODO: define the declarative observable specification.
  // These stream frames are a starting point; use the utility's exact IO regions.
  twostate predicate Spec(raw: Schema.SortCmdRaw, io: BenchIO.IO, exit: int)
    reads io.stdinRegion, io.stdoutRegion, io.stderrRegion
  {
    false
  }
}
