include "../Spec/PathchkSchema.dfy"
include "../../../core/IO.dfy"

module PathchkSpec {
  import BenchIO
  import BenchWorld
  import CliTypes
  import Schema = PathchkSchema

  function ParseErrorText(err: CliTypes.ParseError): BenchWorld.Bytes
  {
    // TODO: define the exact diagnostic bytes here, including fixed text.
    []
  }

  // TODO: define the declarative observable specification.
  // These stream frames are a starting point; use the task's exact IO regions.
  twostate predicate Spec(raw: Schema.PathchkCmdRaw, io: BenchIO.IO, exit: int)
    reads io.stdinRegion, io.stdoutRegion, io.stderrRegion
  {
    false
  }
}
