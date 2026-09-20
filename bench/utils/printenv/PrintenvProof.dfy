include "../../core/World.dfy"
include "../../core/IO.dfy"
include "../../core/IOContract.dfy"
include "PrintenvSchema.dfy"
include "PrintenvCore.dfy"
include "PrintenvSpec.dfy"

module PrintenvProof {
  import BenchIO
  import BW = BenchWorld
  import IOC = IOContract
  import Schema = PrintenvSchema
  import Core = PrintenvCore
  import Spec = PrintenvSpec

  lemma FindEqualsEnvironmentEntry(
    key: string, value: string, i: nat
  )
    requires IOC.EnvironmentKey(key)
    requires i <= |key|
    ensures Core.FindEquals(key + "=" + value, i) == |key|
    decreases |key| - i
  {
    reveal IOC.EnvironmentKey();
    if i < |key| {
      assert (key + "=" + value)[i] == key[i];
      FindEqualsEnvironmentEntry(key, value, i + 1);
    } else {
      assert i == |key|;
      assert (key + "=" + value)[i] == '=';
    }
  }

  lemma EnvironmentEntryFields(key: string, value: string)
    requires IOC.EnvironmentKey(key)
    ensures Core.EntryName(key + "=" + value) == key
    ensures Core.EntryValue(key + "=" + value) == value
  {
    FindEqualsEnvironmentEntry(key, value, 0);
  }

  lemma LookupEntryFromEnvironmentEntries(
    env: map<string, string>,
    entries: seq<string>,
    keys: seq<string>,
    name: string
  )
    requires forall key :: key in env ==> IOC.EnvironmentKey(key)
    requires |keys| == |entries|
    requires forall i :: 0 <= i < |entries| ==>
                           keys[i] in env &&
                           entries[i] == keys[i] + "=" + env[keys[i]]
    requires name in env ==>
               exists i :: 0 <= i < |entries| &&
                           entries[i] == name + "=" + env[name]
    ensures name in env ==>
              Core.LookupEntry(name, entries) == Core.Found(env[name])
    ensures name !in env ==>
              Core.LookupEntry(name, entries) == Core.Missing
    decreases |entries|
  {
    if |entries| > 0 {
      var key := keys[0];
      EnvironmentEntryFields(key, env[key]);
      if key != name {
        assert forall j :: 0 <= j < |entries[1..]| ==>
                             keys[1..][j] in env &&
                             entries[1..][j] ==
                             keys[1..][j] + "=" + env[keys[1..][j]] by {
          forall j | 0 <= j < |entries[1..]|
            ensures keys[1..][j] in env &&
                    entries[1..][j] ==
                    keys[1..][j] + "=" + env[keys[1..][j]]
          {
            assert 0 <= j + 1 < |entries|;
          }
        }
        if name in env {
          var index :| 0 <= index < |entries| &&
                       entries[index] == name + "=" + env[name];
          EnvironmentEntryFields(name, env[name]);
          assert index != 0;
          assert (exists j ::
                    0 <= j < |entries[1..]| &&
                    entries[1..][j] == name + "=" + env[name]) by {
            var j := index - 1;
            assert 0 <= j < |entries[1..]|;
            assert entries[1..][j] == entries[index];
          }
        }
        LookupEntryFromEnvironmentEntries(
          env, entries[1..], keys[1..], name
        );
      }
    }
  }

  lemma LookupEntryRepresentedEnvironment(
    env: map<string, string>, entries: seq<string>, name: string
  )
    requires IOC.EnvEntriesRepresentEnv(env, entries)
    ensures name in env ==>
              Core.LookupEntry(name, entries) == Core.Found(env[name])
    ensures name !in env ==>
              Core.LookupEntry(name, entries) == Core.Missing
  {
    reveal IOC.EnvEntriesRepresentEnv();
    assert forall key :: key in env ==> IOC.EnvironmentKey(key);
    var keys: seq<string> :|
      |keys| == |entries| &&
      (forall i :: 0 <= i < |entries| ==>
                     keys[i] in env &&
                     entries[i] == keys[i] + "=" + env[keys[i]]);
    assert name in env ==>
        exists i :: 0 <= i < |entries| &&
                    entries[i] == name + "=" + env[name];
    LookupEntryFromEnvironmentEntries(env, entries, keys, name);
  }

  lemma OperandResultFromEnvironmentEntries(
    env: map<string, string>,
    operands: seq<string>,
    entries: seq<string>,
    terminator: BW.Bytes
  )
    requires IOC.EnvEntriesRepresentEnv(env, entries)
    ensures Spec.OperandResultRelation(
              env,
              operands,
              terminator,
              Core.LookupOutput(operands, entries, terminator),
              if |operands| > 0 && Core.AnyMissing(operands, entries) then 1 else 0
            )
    decreases |operands|
  {
    if |operands| > 0 {
      LookupEntryRepresentedEnvironment(env, entries, operands[0]);
      OperandResultFromEnvironmentEntries(
        env, operands[1..], entries, terminator
      );
      var rest := Core.LookupOutput(operands[1..], entries, terminator);
      reveal Spec.OperandResultRelation();
      if operands[0] in env {
        assert Core.LookupEntry(operands[0], entries) ==
               Core.Found(env[operands[0]]);
        assert Core.LookupOutput(operands, entries, terminator) ==
               env[operands[0]] + terminator + rest;
        assert Core.AnyMissing(operands, entries) ==
               Core.AnyMissing(operands[1..], entries);
        assert exists tailOut: BW.Bytes, tailExit: int ::
            Spec.OperandResultRelation(
              env, operands[1..], terminator, tailOut, tailExit
            ) &&
            Core.LookupOutput(operands, entries, terminator) ==
            env[operands[0]] + terminator + tailOut &&
            (if |operands| > 0 && Core.AnyMissing(operands, entries)
             then 1 else 0) == tailExit;
      } else {
        assert Core.LookupEntry(operands[0], entries) == Core.Missing;
        assert Core.LookupOutput(operands, entries, terminator) == rest;
        assert Core.AnyMissing(operands, entries);
        assert exists tailOut: BW.Bytes, tailExit: int ::
            Spec.OperandResultRelation(
              env, operands[1..], terminator, tailOut, tailExit
            ) &&
            Core.LookupOutput(operands, entries, terminator) == tailOut &&
            (if |operands| > 0 && Core.AnyMissing(operands, entries)
             then 1 else 0) == 1;
      }
    } else {
      reveal Spec.OperandResultRelation();
    }
  }

  lemma TerminatorEq(nullTerminated: bool)
    ensures Core.Terminator(nullTerminated) == Spec.Terminator(nullTerminated)
  {
  }

  lemma RenderEnvEntriesRefines(entries: seq<string>, terminator: BW.Bytes)
    ensures Spec.EnvironmentOutputRelation(
              entries, terminator, Core.RenderEnvEntries(entries, terminator))
    decreases |entries|
  {
    if |entries| > 0 {
      RenderEnvEntriesRefines(entries[1..], terminator);
      reveal Spec.EnvironmentOutputRelation();
      assert exists rest: BW.Bytes ::
          Spec.EnvironmentOutputRelation(entries[1..], terminator, rest) &&
          Core.RenderEnvEntries(entries, terminator) ==
          entries[0] + terminator + rest by {
        ghost var rest := Core.RenderEnvEntries(entries[1..], terminator);
      }
    } else {
      reveal Spec.EnvironmentOutputRelation();
    }
  }

  twostate lemma CoreSummaryImpliesSpec(raw: Schema.PrintenvCmdRaw, io: BenchIO.IO, exit: int)
    requires Core.CoreSummary(raw, io, exit)
    ensures Spec.Spec(raw, io, exit)
  {
    var cc := Schema.Command(raw);

    if cc.mode == Schema.ModeHelp {
    } else if cc.mode == Schema.ModeVersion {
    } else {
      var entries: seq<string> :|
        IOC.GetEnvironmentContractFields(old(io.env()), entries) &&
        io.stdout() == old(io.stdout()) + Core.Output(cc, entries) &&
        io.stderr() == old(io.stderr()) &&
        exit == Core.ExitStatus(cc, entries);
      if |cc.operands| == 0 {
        TerminatorEq(cc.nullTerminated);
        RenderEnvEntriesRefines(
          entries, Core.Terminator(cc.nullTerminated)
        );
      } else {
        reveal IOC.GetEnvironmentContractFields();
        OperandResultFromEnvironmentEntries(
          old(io.env()),
          cc.operands,
          entries,
          Core.Terminator(cc.nullTerminated)
        );
        assert Spec.OperandResultRelation(
            old(io.env()),
            cc.operands,
            Core.Terminator(cc.nullTerminated),
            Core.Output(cc, entries),
            Core.ExitStatus(cc, entries)
          );
        TerminatorEq(cc.nullTerminated);
      }
    }
  }
}
