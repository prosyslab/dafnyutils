"""Check evaluation stage planning derives oracle commands from utility profiles."""

from __future__ import annotations

import os
import subprocess
from pathlib import Path

import pytest

from benchmarks.checks import (
    EvaluationName,
    OracleExecutionLocation,
    required_checks_for_evaluation,
)
from benchmarks.profiles import (
    COREUTILS_IMPLEMENTATION_SUPPORT_FILES,
    FUNCTIONAL_CORE_SOURCE,
    ResolvedBenchmark,
    coreutils_dafny_analysis_support_files,
    required_checks_for_task,
)
from evaluation.submission.oracle_environment import (
    containerized_evaluation,
)
from evaluation.submission.oracles import (
    build_evaluations,
    configured_oracle_commands,
    derived_oracle_commands,
)
from evaluation.submission.sandbox import SandboxContext
from tests.evaluation.evaluation_test_support import (
    benchmark_utility_configs,
    utility_config,
)


# Coreutils definition analysis must explicitly target every Dafny support source.
def test_coreutils_analysis_support_selects_only_dafny_sources() -> None:
    selected = coreutils_dafny_analysis_support_files("cat")

    assert selected == tuple(
        path for path in COREUTILS_IMPLEMENTATION_SUPPORT_FILES if path.endswith(".dfy")
    )


# Algorithm analysis adds only the shared functional source outside its utility root.
def test_algorithm_analysis_adds_functional_core_support() -> None:
    assert coreutils_dafny_analysis_support_files("algorithm-1") == (FUNCTIONAL_CORE_SOURCE,)


def _utility_cfg(utility_name: str) -> ResolvedBenchmark:
    return utility_config(utility_name)


# Coreutils evaluator stages must run the entry-driven generated gates on the candidate target.
def test_coreutils_oracles_use_generated_entry_gates() -> None:
    commands = derived_oracle_commands(_utility_cfg("cat"))

    assert commands["impl_layout"] == "./eval_support/build.sh"
    assert commands["proof_layout"] == "./eval_support/check_proof_layout.sh"
    assert commands["dafny_verify"] == "./eval_support/verify.sh"
    assert "bench/utils/cat" in commands["implementation_tests"]
    assert "make" in commands["implementation_tests"]
    assert "EVAL_BENCH_DLL=_build/bench/cat_bench.dll" in commands["implementation_tests"]
    assert commands["spec_consistency"].startswith("pytest -q -n0 ")
    for command_name in ("spec_shape", "spec_consistency"):
        assert "--allow-axioms" not in commands[command_name]
        assert "--allow-warnings" not in commands[command_name]
    assert "--allow-external-contracts" in commands["spec_shape"]
    assert "--dont-verify-dependencies" in commands["spec_shape"]


# Generated specification checks select the benchmark override when PATH has another Dafny.
@pytest.mark.parametrize(
    ("utility_name", "command_name"),
    (
        ("cat", "spec_shape"),
        ("algorithm-63", "spec_shape"),
        ("algorithm-63", "spec_consistency"),
    ),
)
def test_specification_oracles_use_configured_dafny(
    tmp_path: Path,
    utility_name: str,
    command_name: str,
) -> None:
    configured_dafny = tmp_path / "configured-dafny"
    path_dir = tmp_path / "path"
    path_dafny = path_dir / "dafny-benchmark"
    path_dir.mkdir()
    for executable, marker in ((configured_dafny, "configured"), (path_dafny, "path")):
        executable.write_text(
            f"#!/usr/bin/env bash\nprintf '%s\\n' {marker}\n",
            encoding="utf-8",
        )
        executable.chmod(0o755)
    env = {
        **os.environ,
        "DAFNY": str(path_dafny),
        "DAFNY_BENCHMARK": str(configured_dafny),
        "PATH": f"{path_dir}:{os.environ['PATH']}",
        "EVAL_TARGET_ROOT": str(tmp_path),
    }

    completed = subprocess.run(
        ["bash", "-c", derived_oracle_commands(_utility_cfg(utility_name))[command_name]],
        check=True,
        capture_output=True,
        text=True,
        env=env,
    )

    assert completed.stdout.strip() == "configured"


# Coreutils evaluation fuzzing compares stderr unless a caller explicitly opts out.
def test_coreutils_fuzzer_command_checks_stderr() -> None:
    command = derived_oracle_commands(_utility_cfg("cat"))["fuzzer"]

    assert command.endswith("fuzz cat")


# Coreutils evaluation assigns all five mandatory commands to the four evaluation types.
def test_coreutils_evaluations_select_all_required_checks() -> None:
    utility_cfg = _utility_cfg("cat")
    commands = derived_oracle_commands(utility_cfg)
    layout, testcase, fuzzing, verification = build_evaluations(
        utility_cfg=utility_cfg,
        checkout_root=Path("/tmp/evaluator_checkout"),
    )
    assert layout.required_checks == ("impl_layout", "proof_layout")
    assert testcase.required_checks == ("implementation_tests",)
    assert fuzzing.required_checks == ("fuzzer",)
    assert verification.required_checks == ("dafny_verify",)
    for plan in (layout, testcase, fuzzing, verification):
        assert [command.command for command in plan.commands] == [
            commands[name] for name in plan.required_checks
        ]


# A coreutils archive runs only its container-managing fuzzer on the trusted host.
def test_coreutils_fuzzer_stays_on_host_when_evaluator_checks_are_wrapped() -> None:
    layout, _, fuzzing, _ = build_evaluations(
        utility_cfg=_utility_cfg("cat"),
        checkout_root=Path("/trusted/repository"),
    )
    context = SandboxContext((Path("/trusted/compose.yml"),), "evaluation", "evaluator")

    mapped_layout = containerized_evaluation(layout, context)
    mapped_fuzzing = containerized_evaluation(fuzzing, context)

    assert all(
        command.location is OracleExecutionLocation.EVALUATOR_CONTAINER
        for command in mapped_layout.commands
    )
    assert all(
        mapped.command != original.command
        for mapped, original in zip(mapped_layout.commands, layout.commands, strict=True)
    )
    assert mapped_fuzzing.commands[0].location is OracleExecutionLocation.TRUSTED_HOST
    assert mapped_fuzzing.commands[0].command == fuzzing.commands[0].command
    assert mapped_fuzzing.commands[0].cwd == fuzzing.commands[0].cwd


# Algorithm evaluations use the same generated scripts and skip only fuzzing.
def test_algorithm_oracles_use_container_visible_repo_and_workspace_paths() -> None:
    utility_cfg = _utility_cfg("algorithm-63")
    commands = derived_oracle_commands(utility_cfg)
    layout, testcase, fuzzing, verification = build_evaluations(
        utility_cfg=utility_cfg,
        checkout_root=Path("/tmp/evaluator_checkout"),
    )

    assert commands["impl_layout"] == "./eval_support/build.sh"
    assert commands["proof_layout"] == "./eval_support/check_proof_layout.sh"
    assert commands["dafny_verify"] == "./eval_support/verify.sh"
    assert testcase.commands[0].command == commands["implementation_tests"]
    assert "ALGORITHM_BENCH_ID=63" in testcase.commands[0].command
    assert [command.name for command in layout.commands] == ["impl_layout", "proof_layout"]
    assert verification.commands[0].name == "dafny_verify"
    assert fuzzing.required_checks == ()
    assert fuzzing.commands == ()
    assert (
        '"${EVAL_REPO_ROOT:-.}/tools/bench/test_bench_algorithm.py"'
        in commands["implementation_tests"]
    )
    for command_name in ("spec_shape", "spec_consistency"):
        assert "--allow-axioms" not in commands[command_name]
        assert "--allow-warnings" not in commands[command_name]


# Empty oracle commands are invalid configuration data.
def test_configured_oracle_commands_rejects_empty_command() -> None:
    with pytest.raises(ValueError, match="oracle commands must not be empty: dafny_verify"):
        configured_oracle_commands({"dafny_verify": ""})


# Missing required oracle commands block their evaluation without shrinking required checks.
def test_missing_required_oracle_command_blocks_evaluation() -> None:
    utility_cfg = _utility_cfg("cat")
    commands = derived_oracle_commands(utility_cfg)
    del commands["fuzzer"]

    fuzzing = build_evaluations(
        utility_cfg=utility_cfg,
        checkout_root=Path("/tmp/evaluator_checkout"),
        oracle_commands=commands,
    )[2]

    assert fuzzing.required_checks == ("fuzzer",)
    assert fuzzing.commands == ()
    assert fuzzing.blocked_reason == "missing oracle commands for required checks: fuzzer"


# An unrecognized public check cannot be silently dropped from evaluations.
def test_unknown_required_check_rejects_evaluation_selection() -> None:
    with pytest.raises(ValueError, match="unknown required benchmark checks: security_scan"):
        required_checks_for_evaluation(("impl_layout", "security_scan"), EvaluationName.LAYOUT)


# Every benchmark task keeps each required command in exactly one evaluation.
def test_benchmark_tasks_declare_all_required_oracle_checks() -> None:
    for utility_cfg in benchmark_utility_configs():
        commands = derived_oracle_commands(utility_cfg)
        required = required_checks_for_task(utility_cfg)
        missing = [check for check in required if not str(commands.get(check, "")).strip()]
        assert missing == [], utility_cfg.name
        assigned = tuple(
            check
            for evaluation in EvaluationName
            for check in required_checks_for_evaluation(required, evaluation)
        )
        assert sorted(assigned) == sorted(required), utility_cfg.name
