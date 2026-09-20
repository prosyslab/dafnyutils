"""Verify the live environment domain and returning-contract boundary."""

from __future__ import annotations

import os
import subprocess
from pathlib import Path

from dafny_cli import dafny_command

ROOT = Path(__file__).resolve().parents[2]
IO_CONTRACT = ROOT / "bench" / "core" / "IOContract.dfy"
IO_SOURCE = ROOT / "bench" / "core" / "IO.dfy"
DAFNY_FLAGS = (
    "--cores:1",
    "--verification-time-limit:30",
    "--standard-libraries:false",
    "--allow-external-contracts",
    "--dont-verify-dependencies",
)
CONSTRUCTIVE_WITNESS_BODY = r"""  lemma EncodedEnvironmentKeysEqual(
    leftKey: string,
    leftValue: string,
    rightKey: string,
    rightValue: string
  )
    requires C.EnvironmentKey(leftKey)
    requires C.EnvironmentKey(rightKey)
    requires leftKey + "=" + leftValue == rightKey + "=" + rightValue
    ensures leftKey == rightKey
  {
    reveal C.EnvironmentKey();
    if |leftKey| < |rightKey| {
      assert (leftKey + "=" + leftValue)[|leftKey|] == '=';
      assert (rightKey + "=" + rightValue)[|leftKey|] ==
        rightKey[|leftKey|];
    } else if |rightKey| < |leftKey| {
      assert (rightKey + "=" + rightValue)[|rightKey|] == '=';
      assert (leftKey + "=" + leftValue)[|rightKey|] ==
        leftKey[|rightKey|];
    } else {
      assert leftKey == (leftKey + "=" + leftValue)[..|leftKey|];
      assert rightKey == (rightKey + "=" + rightValue)[..|rightKey|];
    }
  }

  lemma MapKeysHaveSequence(env: map<string, string>)
    ensures exists keys: seq<string> ::
      |keys| == |env| &&
      (forall key :: key in env <==> key in keys) &&
      (forall i: nat, j: nat ::
        i < j < |keys| ==> keys[i] != keys[j])
    decreases |env|
  {
    if |env| == 0 {
      assert env == map[];
    } else {
      var key :| key in env;
      var rest := env - {key};
      MapKeysHaveSequence(rest);
      var restKeys :|
        |restKeys| == |rest| &&
        (forall restKey :: restKey in rest <==> restKey in restKeys) &&
        (forall i: nat, j: nat ::
          i < j < |restKeys| ==> restKeys[i] != restKeys[j]);
      var keys := [key] + restKeys;
      assert |rest| + 1 == |env|;
      assert forall envKey :: envKey in env <==> envKey in keys by {
        forall envKey
          ensures envKey in env <==> envKey in keys
        {
          if envKey != key {
            assert envKey in env <==> envKey in rest;
            assert envKey in rest <==> envKey in restKeys;
          }
        }
      }
      assert forall i: nat, j: nat ::
        i < j < |keys| ==> keys[i] != keys[j] by {
        forall i: nat, j: nat | i < j < |keys|
          ensures keys[i] != keys[j]
        {
          if i == 0 {
            assert keys[j] == restKeys[j - 1];
            assert restKeys[j - 1] in rest;
            assert key !in rest;
          } else {
            assert keys[i] == restKeys[i - 1];
            assert keys[j] == restKeys[j - 1];
          }
        }
      }
    }
  }

  ghost function EnvironmentEntries(
    env: map<string, string>,
    keys: seq<string>
  ): seq<string>
    requires forall i: nat :: i < |keys| ==> keys[i] in env
  {
    seq(|keys|, i requires 0 <= i < |keys| =>
      keys[i] + "=" + env[keys[i]])
  }

  lemma EnvironmentEntriesAlign(
    env: map<string, string>,
    keys: seq<string>
  )
    requires forall i: nat :: i < |keys| ==> keys[i] in env
    ensures |EnvironmentEntries(env, keys)| == |keys|
    ensures forall i :: 0 <= i < |keys| ==>
      EnvironmentEntries(env, keys)[i] ==
        keys[i] + "=" + env[keys[i]]
  {
  }

  lemma EnvironmentEntriesAreDistinct(
    env: map<string, string>,
    keys: seq<string>
  )
    requires C.ValidEnvironment(env)
    requires forall i: nat :: i < |keys| ==> keys[i] in env
    requires forall i: nat, j: nat ::
      i < j < |keys| ==> keys[i] != keys[j]
    ensures forall i: nat, j: nat ::
      i < j < |EnvironmentEntries(env, keys)| ==>
        EnvironmentEntries(env, keys)[i] !=
          EnvironmentEntries(env, keys)[j]
  {
    reveal C.ValidEnvironment();
    forall i: nat, j: nat |
      i < j < |EnvironmentEntries(env, keys)|
      ensures EnvironmentEntries(env, keys)[i] !=
        EnvironmentEntries(env, keys)[j]
    {
      if EnvironmentEntries(env, keys)[i] ==
          EnvironmentEntries(env, keys)[j] {
        assert C.EnvironmentKey(keys[i]);
        assert C.EnvironmentKey(keys[j]);
        EncodedEnvironmentKeysEqual(
          keys[i],
          env[keys[i]],
          keys[j],
          env[keys[j]]
        );
      }
    }
  }

  lemma EnvironmentEntriesCover(
    env: map<string, string>,
    keys: seq<string>
  )
    requires forall i: nat :: i < |keys| ==> keys[i] in env
    requires forall envKey :: envKey in env ==> envKey in keys
    ensures forall envKey :: envKey in env ==>
      exists i ::
        0 <= i < |EnvironmentEntries(env, keys)| &&
        EnvironmentEntries(env, keys)[i] ==
          envKey + "=" + env[envKey]
  {
    forall envKey | envKey in env
      ensures exists i ::
        0 <= i < |EnvironmentEntries(env, keys)| &&
        EnvironmentEntries(env, keys)[i] ==
          envKey + "=" + env[envKey]
    {
      assert envKey in keys;
      var i :| 0 <= i < |keys| && keys[i] == envKey;
      assert EnvironmentEntries(env, keys)[i] ==
        envKey + "=" + env[envKey];
    }
  }

  lemma {:isolate_assertions} ChosenKeysGiveEnvironmentEntries(
    env: map<string, string>,
    keys: seq<string>
  )
    requires C.ValidEnvironment(env)
    requires |keys| == |env|
    requires forall key :: key in env <==> key in keys
    requires forall i: nat, j: nat ::
      i < j < |keys| ==> keys[i] != keys[j]
    ensures C.GetEnvironmentContractFields(
      env,
      EnvironmentEntries(env, keys)
    )
  {
    reveal C.ValidEnvironment();
    assert forall i: nat :: i < |keys| ==> keys[i] in env;
    var entries := EnvironmentEntries(env, keys);
    EnvironmentEntriesAlign(env, keys);
    EnvironmentEntriesAreDistinct(env, keys);
    EnvironmentEntriesCover(env, keys);
    assert C.EnvEntriesRepresentEnv(env, entries) by {
      reveal C.EnvEntriesRepresentEnv();
      assert exists witnessKeys: seq<string> ::
        |witnessKeys| == |entries| &&
        (forall i :: 0 <= i < |entries| ==>
          witnessKeys[i] in env &&
          entries[i] ==
            witnessKeys[i] + "=" + env[witnessKeys[i]]) by {
        assert |keys| == |entries|;
        assert forall i :: 0 <= i < |entries| ==>
          keys[i] in env &&
          entries[i] == keys[i] + "=" + env[keys[i]];
      }
    }
    assert C.GetEnvironmentContractFields(env, entries) by {
      reveal C.GetEnvironmentContractFields();
    }
  }

  lemma EveryValidEnvironmentHasEntries(env: map<string, string>)
    requires C.ValidEnvironment(env)
    ensures exists entries: seq<string> ::
      C.GetEnvironmentContractFields(env, entries)
  {
    MapKeysHaveSequence(env);
    var keys :|
      |keys| == |env| &&
      (forall key :: key in env <==> key in keys) &&
      (forall i: nat, j: nat ::
        i < j < |keys| ==> keys[i] != keys[j]);
    assert forall i: nat :: i < |keys| ==> keys[i] in env;
    var entries := EnvironmentEntries(env, keys);
    ChosenKeysGiveEnvironmentEntries(env, keys);
  }"""


def verify_client(
    tmp_path: Path,
    body: str,
    *,
    include_path: Path = IO_CONTRACT,
    extra_imports: str = "",
) -> subprocess.CompletedProcess[str]:
    """Verify one client against the live IO contract."""
    source = tmp_path / "EnvironmentContractClient.dfy"
    source.write_text(
        f"""include "{include_path.as_posix()}"

module EnvironmentContractClient {{
  import C = IOContract
{extra_imports}

{body}
}}
""",
        encoding="utf-8",
    )
    return subprocess.run(
        [dafny_command(), "verify", *DAFNY_FLAGS, str(source)],
        cwd=ROOT,
        env={**os.environ, "TMPDIR": "/tmp"},
        check=False,
        text=True,
        capture_output=True,
        timeout=45,
    )


def assert_verified(result: subprocess.CompletedProcess[str]) -> None:
    """Report both verifier streams when a positive client fails."""
    assert result.returncode == 0, result.stdout + result.stderr
    assert "0 errors" in result.stdout + result.stderr


def assert_precondition_rejected(result: subprocess.CompletedProcess[str]) -> None:
    """Require rejection at the returning contract's valid-domain boundary."""
    output = result.stdout + result.stderr
    assert result.returncode != 0, output
    assert "precondition" in output
    assert "timed out" not in output


# The inhabited environment type must admit the empty map and its empty entry witness.
def test_empty_environment_has_a_returning_contract_witness(tmp_path: Path) -> None:
    result = verify_client(
        tmp_path,
        """  lemma EmptyEnvironmentHasWitness()
  {
    var env: C.Environment := map[];
    assert C.GetEnvironmentContractFields(env, []);
  }""",
    )

    assert_verified(result)


# Valid keys must permit unrestricted values while retaining an explicit entry witness.
def test_ordinary_environment_values_are_unrestricted(tmp_path: Path) -> None:
    result = verify_client(
        tmp_path,
        """  lemma OrdinaryEnvironmentHasWitness()
  {
    var unrestrictedValue: string := \"left=right\" + [(0 as char)];
    var env: C.Environment := map[\"NAME\" := unrestrictedValue];
    var entries := [\"NAME=\" + unrestrictedValue];
    assert C.EnvEntriesRepresentEnv(env, entries) by {
      reveal C.EnvEntriesRepresentEnv();
      var keys := [\"NAME\"];
      assert exists witnessKeys: seq<string> ::
        |witnessKeys| == |entries| &&
        (forall i :: 0 <= i < |entries| ==>
          witnessKeys[i] in env &&
          entries[i] == witnessKeys[i] + \"=\" + env[witnessKeys[i]]) by {
        assert |keys| == |entries|;
        assert forall i :: 0 <= i < |entries| ==>
          keys[i] in env &&
          entries[i] == keys[i] + \"=\" + env[keys[i]];
      }
      assert forall key :: key in env ==>
        exists i :: 0 <= i < |entries| &&
          entries[i] == key + \"=\" + env[key] by {
        forall key | key in env
          ensures exists i ::
            0 <= i < |entries| &&
            entries[i] == key + \"=\" + env[key]
        {
          assert key == \"NAME\";
          assert entries[0] == key + \"=\" + env[key];
        }
      }
    }
    assert C.GetEnvironmentContractFields(env, entries) by {
      reveal C.GetEnvironmentContractFields();
    }
  }""",
    )

    assert_verified(result)


# Every valid finite map must construct a distinct KEY=VALUE entry witness.
def test_every_valid_environment_has_a_constructive_witness(tmp_path: Path) -> None:
    result = verify_client(tmp_path, CONSTRUCTIVE_WITNESS_BODY)

    assert_verified(result)


# The process observer's environment type permits GetEnvironment without a new assumption.
def test_process_io_can_call_get_environment_without_client_precondition(
    tmp_path: Path,
) -> None:
    result = verify_client(
        tmp_path,
        """  method ProcessEnvironmentSupportsGetEnvironment()
  {
    var io := B.Process();
    assert C.ValidEnvironment(io.env());
    var entries := io.GetEnvironment();
  }""",
        include_path=IO_SOURCE,
        extra_imports="  import B = BenchIO",
    )

    assert_verified(result)


def invalid_contract_client(key_expression: str) -> str:
    """Build a client that crosses the returning API with one invalid key."""
    return f"""  lemma InvalidEnvironmentCannotUseReturningContract(
    entries: seq<string>
  )
  {{
    var env := map[{key_expression} := \"value\"];
    assert C.GetEnvironmentContractFields(env, entries);
  }}"""


# An empty key must be rejected before the returning contract can be used.
def test_empty_environment_key_is_rejected_by_api(tmp_path: Path) -> None:
    result = verify_client(tmp_path, invalid_contract_client('""'))

    assert_precondition_rejected(result)


# A key containing '=' must be rejected before the returning contract can be used.
def test_equals_environment_key_is_rejected_by_api(tmp_path: Path) -> None:
    result = verify_client(tmp_path, invalid_contract_client('"LEFT=RIGHT"'))

    assert_precondition_rejected(result)


# A key containing NUL must be rejected before the returning contract can be used.
def test_nul_environment_key_is_rejected_by_api(tmp_path: Path) -> None:
    result = verify_client(
        tmp_path,
        invalid_contract_client('"KEY" + [(0 as char)]'),
    )

    assert_precondition_rejected(result)
