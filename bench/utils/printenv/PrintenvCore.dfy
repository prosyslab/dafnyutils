include "../../core/World.dfy"
include "../../core/IO.dfy"
include "../../core/IOContract.dfy"
include "PrintenvSchema.dfy"
include "PrintenvSpec.dfy"

module PrintenvCore {
  import BenchIO
  import Schema = PrintenvSchema
  import BenchWorld
  import IOContract
  import Spec = PrintenvSpec

  function Terminator(nullTerminated: bool): BenchWorld.Bytes
  {
    if nullTerminated then [(0 as char)] else "\n"
  } by method {
    return if nullTerminated then [(0 as char)] else "\n";
  }

  function RenderEnvEntries(entries: seq<string>, terminator: BenchWorld.Bytes): BenchWorld.Bytes
    decreases |entries|
  {
    if |entries| == 0 then
      []
    else
      entries[0] + terminator + RenderEnvEntries(entries[1..], terminator)
  } by method {
    if |entries| == 0 {
      return [];
    } else {
      var rest := RenderEnvEntries(entries[1..], terminator);
      return entries[0] + terminator + rest;
    }
  }

  datatype EnvLookup = Missing | Found(value: string)

  function FindEquals(text: string, i: nat): nat
    requires i <= |text|
    ensures i <= FindEquals(text, i) <= |text|
    decreases |text| - i
  {
    if i >= |text| || text[i] == '=' then
      i
    else
      FindEquals(text, i + 1)
  } by method {
    if i >= |text| || text[i] == '=' {
      return i;
    } else {
      return FindEquals(text, i + 1);
    }
  }

  function EntryName(entry: string): string
  {
    var eq := FindEquals(entry, 0);
    entry[..eq]
  } by method {
    var eq := FindEquals(entry, 0);
    return entry[..eq];
  }

  function EntryValue(entry: string): string
  {
    var eq := FindEquals(entry, 0);
    if eq < |entry| then entry[eq + 1..] else ""
  } by method {
    var eq := FindEquals(entry, 0);
    if eq < |entry| {
      return entry[eq + 1..];
    } else {
      return "";
    }
  }

  function LookupEntry(name: string, entries: seq<string>): EnvLookup
    decreases |entries|
  {
    if |entries| == 0 then
      Missing
    else if EntryName(entries[0]) == name then
      Found(EntryValue(entries[0]))
    else
      LookupEntry(name, entries[1..])
  } by method {
    if |entries| == 0 {
      return Missing;
    } else {
      var entryName := EntryName(entries[0]);
      if entryName == name {
        var entryValue := EntryValue(entries[0]);
        return Found(entryValue);
      } else {
        return LookupEntry(name, entries[1..]);
      }
    }
  }

  function LookupOutput(operands: seq<string>, entries: seq<string>, terminator: BenchWorld.Bytes): BenchWorld.Bytes
    decreases |operands|
  {
    if |operands| == 0 then
      []
    else
      match LookupEntry(operands[0], entries)
      case Missing => LookupOutput(operands[1..], entries, terminator)
      case Found(value) => value + terminator + LookupOutput(operands[1..], entries, terminator)
  } by method {
    if |operands| == 0 {
      return [];
    } else {
      var rest := LookupOutput(operands[1..], entries, terminator);
      var lookup := LookupEntry(operands[0], entries);
      match lookup
      case Missing =>
        return rest;
      case Found(value) =>
        return value + terminator + rest;
    }
  }

  function AnyMissing(operands: seq<string>, entries: seq<string>): bool
    decreases |operands|
  {
    |operands| > 0 &&
    (LookupEntry(operands[0], entries) == Missing || AnyMissing(operands[1..], entries))
  } by method {
    if |operands| == 0 {
      return false;
    } else {
      var lookup := LookupEntry(operands[0], entries);
      if lookup == Missing {
        return true;
      } else {
        return AnyMissing(operands[1..], entries);
      }
    }
  }

  function Output(cmd: Schema.PrintenvCmd, entries: seq<string>): BenchWorld.Bytes
  {
    if |cmd.operands| == 0 then
      RenderEnvEntries(entries, Terminator(cmd.nullTerminated))
    else
      LookupOutput(cmd.operands, entries, Terminator(cmd.nullTerminated))
  } by method {
    var terminator := Terminator(cmd.nullTerminated);
    if |cmd.operands| == 0 {
      return RenderEnvEntries(entries, terminator);
    } else {
      return LookupOutput(cmd.operands, entries, terminator);
    }
  }

  function ExitStatus(cmd: Schema.PrintenvCmd, entries: seq<string>): int
  {
    if |cmd.operands| > 0 && AnyMissing(cmd.operands, entries) then 1 else 0
  } by method {
    return
      if |cmd.operands| > 0 && AnyMissing(cmd.operands, entries)
      then 1
      else 0;
  }

  twostate predicate CoreSummary(raw: Schema.PrintenvCmdRaw, io: BenchIO.IO, exit: int)
    reads io.envRegion, io.stdoutRegion, io.stderrRegion
  {
    var cmd := Schema.Command(raw);
    if cmd.mode == Schema.ModeHelp then
      io.stdout() == old(io.stdout()) + Spec.HelpTextSpec() &&
      io.stderr() == old(io.stderr()) &&
      exit == 0
    else if cmd.mode == Schema.ModeVersion then
      io.stdout() == old(io.stdout()) + Spec.VersionTextSpec() &&
      io.stderr() == old(io.stderr()) &&
      exit == 0
    else
      exists entries: seq<string> ::
        IOContract.GetEnvironmentContractFields(old(io.env()), entries) &&
        io.stdout() == old(io.stdout()) + Output(cmd, entries) &&
        io.stderr() == old(io.stderr()) &&
        exit == ExitStatus(cmd, entries)
  }

  method RunCore(raw: Schema.PrintenvCmdRaw, io: BenchIO.IO) returns (exit: int)
    modifies io.stdoutRegion
    ensures CoreSummary(raw, io, exit)
    decreases *
  {
    ghost var preEnv := io.env();
    ghost var preStdout := io.stdout();
    var cmd := Schema.Command(raw);

    if cmd.mode == Schema.ModeHelp {
      var out := Spec.HelpTextSpec();
      io.AppendStdout(out);
      exit := 0;
      assert CoreSummary(raw, io, exit);
      return;
    }

    if cmd.mode == Schema.ModeVersion {
      var out := Spec.VersionTextSpec();
      io.AppendStdout(out);
      exit := 0;
      assert CoreSummary(raw, io, exit);
      return;
    }

    var entries := io.GetEnvironment();
    assert IOContract.GetEnvironmentContractFields(preEnv, entries);
    var out := Output(cmd, entries);
    var status := ExitStatus(cmd, entries);
    io.AppendStdout(out);
    exit := status;
    assert io.stdout() == preStdout + out;
    assert CoreSummary(raw, io, exit);
  }
}
