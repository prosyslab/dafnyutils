include "IO.dfy"
include "CliTypes.dfy"
include "CliExtern.dfy"

module {:verify false} BenchItem {
  import opened BenchWorld
  import BenchIO
  import opened CliTypes
  import opened CliExtern

  trait {:termination false} BenchmarkItemTwostate<CmdRaw> {
    method Name() returns (name: string)
    method Schema() returns (schema: CliSchema)
    method ParseConfig() returns (cfg: ParseConfig)
    method Decode(parsed: ParsedArgs) returns (raw: CmdRaw)
    method FormatParseError(err: ParseError) returns (msg: Bytes)
    method PlanParsed(parsed: ParsedArgs) returns (plan: CliPlan<CmdRaw>)
      decreases *
    {
      var raw := Decode(parsed);
      plan := CliRun(raw);
    }

    method PlanArgv(argv: seq<string>) returns (plan: CliPlan<CmdRaw>)
      decreases *
    {
      var schema := Schema();
      var cfg := ParseConfig();
      var parseRes := Cli.Parse(argv, schema, cfg);

      match parseRes {
        case ParseFailure(err) =>
          plan := PlanParseFailure(err, argv);
        case ParseSuccess(parsed) =>
          plan := PlanParsed(parsed);
      }
    }

    method RunCore(raw: CmdRaw, io: BenchIO.IO) returns (exit: int)
      modifies io.Footprint()
      decreases *

    method PlanParseFailure(err: ParseError, argv: seq<string>) returns (plan: CliPlan<CmdRaw>)
      decreases *
    {
      var msg := FormatParseError(err);
      plan := CliEarlyExit(1, [], msg);
    }
  }

  method RunMain<CmdRaw>(item: BenchmarkItemTwostate<CmdRaw>, argv: seq<string>, io: BenchIO.IO) returns (exit: int)
    modifies io.Footprint()
    decreases *
  {
    var plan := item.PlanArgv(argv);

    match plan {
      case CliRun(raw) =>
        exit := item.RunCore(raw, io);
      case CliEarlyExit(code, stdout, stderr) =>
        io.AppendStdout(stdout);
        io.AppendStderr(stderr);
        exit := code;
    }
  }
}
