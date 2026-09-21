include "{{CLASS_NAME}}Schema.dfy"
include "../../core/IO.dfy"

module {{CLASS_NAME}}Spec {
  import BenchIO
  import BenchWorld
  import CliTypes
  import Schema = {{CLASS_NAME}}Schema

  function ParseErrorText(err: CliTypes.ParseError): BenchWorld.Bytes
  {
    // TODO: define the exact GNU diagnostic bytes here, including fixed text.
    []
  }

  // TODO: define the declarative observable specification.
  // These stream frames are a starting point; use the utility's exact IO regions.
  twostate predicate Spec(raw: Schema.{{CLASS_NAME}}CmdRaw, io: BenchIO.IO, exit: int)
    reads io.stdinRegion, io.stdoutRegion, io.stderrRegion
  {
    false
  }
}
