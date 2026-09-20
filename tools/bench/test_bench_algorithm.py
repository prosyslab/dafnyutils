"""Validate algorithm benchmarks by parsing apps stdin/stdout cases into typed values."""

from __future__ import annotations

import json
import os
import re
import subprocess
import time
from pathlib import Path
from typing import Any

import pytest

from dafny_cli import dafny_command
from evaluation.submission.candidate_execution import run_candidate
from standard_library import DAFNY_STANDARD_LIBRARY_OPTION
from tools.bench.bench_test_support import (
    BENCH_COMMAND_TIMEOUT_SEC,
    evaluation_target_root,
    parity_env,
    run_checked_subprocess,
    run_override_build,
)

ROOT = evaluation_target_root(Path(__file__).resolve().parents[2])
TRUSTED_ROOT = Path(__file__).resolve().parents[2]
CASE_FRAME_PREFIX_RE = re.compile(r"^CASE -?\d+ (?:OUTPUT|PASS|FAIL)(?:\s|$)")
CASE_RESULT_RE = re.compile(r"^CASE (?P<index>\d+) (?P<status>PASS|FAIL)$")
CASE_OUTPUT_RE = re.compile(r"^CASE (?P<index>\d+) OUTPUT (?P<body>.*)$")


def _algorithm_id() -> str:
    raw = os.environ.get("ALGORITHM_BENCH_ID")
    if not raw:
        pytest.skip("ALGORITHM_BENCH_ID is not set")
    return raw


def _class_name(algorithm_id: str) -> str:
    return f"Algorithm{algorithm_id}"


def _load_case_data(algorithm_id: str) -> dict[str, Any]:
    cases_path = TRUSTED_ROOT / "bench" / "algorithm" / algorithm_id / "cases.json"
    with cases_path.open(encoding="utf-8") as handle:
        return json.load(handle)


def _parse_cases(data: dict[str, Any]) -> list[tuple[tuple[Any, ...], tuple[Any, ...]]]:
    namespace: dict[str, Any] = {"re": re}
    exec(data["parser"], namespace)
    parser = namespace["parser"]
    input_count = int(data["input_count"])
    parsed = []
    for case in data["positive"]:
        values = tuple(parser(case["input"], case["output"]))
        parsed.append((values[:input_count], values[input_count:]))
    return parsed


def pytest_generate_tests(metafunc: pytest.Metafunc) -> None:
    if "parsed_case" not in metafunc.fixturenames:
        return
    algorithm_id = os.environ.get("ALGORITHM_BENCH_ID")
    if not algorithm_id:
        metafunc.parametrize(("case_index", "parsed_case"), [(0, None)], ids=["no-env"])
        return
    parsed_cases = _parse_cases(_load_case_data(algorithm_id))
    if not parsed_cases:
        metafunc.parametrize(("case_index", "parsed_case"), [(0, None)], ids=["no-cases"])
        return
    metafunc.parametrize(
        ("case_index", "parsed_case"),
        list(enumerate(parsed_cases)),
        ids=[f"case-{index}" for index in range(len(parsed_cases))],
    )


def _dafny_literal(value: Any) -> str:
    if isinstance(value, bool):
        return "true" if value else "false"
    if isinstance(value, int):
        return str(value)
    if isinstance(value, str):
        return json.dumps(value)
    if isinstance(value, list):
        return "[" + ", ".join(_dafny_literal(item) for item in value) + "]"
    raise TypeError(f"unsupported Dafny literal value: {value!r}")


def _input_reader(value: Any) -> tuple[str, str]:
    if isinstance(value, int) and not isinstance(value, bool):
        return "int", "ReadInt"
    if isinstance(value, str):
        return "string", "ReadString"
    if isinstance(value, list):
        if all(type(item) is int for item in value):
            return "seq<int>", "ReadInts"
        if all(isinstance(item, str) for item in value):
            return "seq<string>", "ReadStrings"
    raise TypeError(f"unsupported algorithm input type: {type(value).__name__}")


def _emit_harness(
    algorithm_id: str,
    parsed_cases: list[tuple[tuple[Any, ...], tuple[Any, ...]]],
) -> str:
    class_name = _class_name(algorithm_id)
    inputs, outputs = parsed_cases[0]
    readers = [_input_reader(value) for value in inputs]
    # Empty sequences use the nonempty corpus members solely to infer the public input type.
    for index, value in enumerate(inputs):
        if value == []:
            for case_inputs, _ in parsed_cases:
                if case_inputs[index]:
                    readers[index] = _input_reader(case_inputs[index])
                    break
    lines = [
        f'include "{ROOT / "bench" / "algorithm" / algorithm_id / f"{class_name}.dfy"}"',
        "",
        f"module {class_name}Harness {{",
        f"  import Implementation = {class_name}",
        '  method {:extern "BenchmarkOutput.Capture", "NextCase"} NextCase() returns (more: bool)',
        '  method {:extern "BenchmarkOutput.Capture", "ReadInt"} '
        "ReadInt(index: int) returns (value: int)",
        '  method {:extern "BenchmarkOutput.Capture", "ReadString"} '
        "ReadString(index: int) returns (value: string)",
        '  method {:extern "BenchmarkOutput.Capture", "ReadInts"} '
        "ReadInts(index: int) returns (value: seq<int>)",
        '  method {:extern "BenchmarkOutput.Capture", "ReadStrings"} '
        "ReadStrings(index: int) returns (value: seq<string>)",
        '  method {:extern "BenchmarkOutput.Capture", "Begin"} Begin()',
        '  method {:extern "BenchmarkOutput.Capture", "Emit"} Emit<T>(value: T)',
        '  method {:extern "BenchmarkOutput.Capture", "End"} End()',
        '  method {:extern "BenchmarkOutput.Capture", "Result"} Result(passed: bool)',
        "",
        "  method Main()",
        "  {",
        "    var more := NextCase();",
        "    while more {",
    ]
    for index, (value_type, reader) in enumerate(readers):
        lines.append(f"      var input{index}: {value_type} := {reader}({index});")
    args = ", ".join(f"input{index}" for index in range(len(inputs)))
    out_names = [f"output{index}" for index in range(len(outputs))]
    lines.append(f"      var {', '.join(out_names)} := Implementation.RunCore({args});")
    lines.append("      Begin();")
    lines.extend(f"      Emit({name});" for name in out_names)
    lines.append("      End();")
    lines.extend(["      more := NextCase();", "    }", "  }", "}"])
    return "\n".join(lines) + "\n"


def _input_stream(parsed_cases: list[tuple[tuple[Any, ...], tuple[Any, ...]]]) -> str:
    return "".join(
        json.dumps({"index": index, "inputs": inputs}, ensure_ascii=True) + "\n"
        for index, (inputs, _) in enumerate(parsed_cases)
    )


def _emit_algorithm100_validator() -> str:
    return f"""include "{TRUSTED_ROOT / "bench/algorithm/100/Spec.dfy"}"
module Algorithm100Validator {{
  import Validation = Algorithm100Spec
  method {{:extern "BenchmarkOutput.Capture", "NextCase"}} NextCase() returns (more: bool)
  method {{:extern "BenchmarkOutput.Capture", "ReadInt"}} ReadInt(index: int) returns (value: int)
  method {{:extern "BenchmarkOutput.Capture", "ReadStrings"}}
    ReadStrings(index: int) returns (value: seq<string>)
  method {{:extern "BenchmarkOutput.Capture", "Result"}} Result(passed: bool)
  method Main() {{
    var more := NextCase();
    while more {{
      var n := ReadInt(0);
      var m := ReadInt(1);
      var screen := ReadStrings(2);
      var observed := ReadStrings(3);
      Result(Validation.Spec(n, m, screen, observed));
      more := NextCase();
    }}
  }}
}}
"""


def _build_capture_harness(source: Path, dll: Path, env: dict[str, str]) -> None:
    run_checked_subprocess(
        [
            dafny_command(),
            "build",
            "--no-verify",
            "--target:cs",
            DAFNY_STANDARD_LIBRARY_OPTION,
            "--output",
            str(dll),
            str(source),
            str(TRUSTED_ROOT / "tools/fixtures/algorithm/OutputCapture.cs"),
        ],
        cwd=source.parent,
        env={**env, "TMPDIR": "/tmp"},
        label="build algorithm capture harness",
    )


# A maximum-size sparse screen must complete within the standard benchmark command budget.
def test_algorithm100_large_sparse_screen_completes(
    tmp_path: Path,
) -> None:
    # upstream: none - Covers the benchmark-only performance budget for algorithm 100.
    if _algorithm_id() != "100":
        pytest.skip("algorithm 100 performance regression")
    run_override_build(ROOT)
    harness_path = tmp_path / "Algorithm100LargeHarness.dfy"
    harness_path.write_text(
        f'''include "{ROOT / "bench/algorithm/100/Algorithm100.dfy"}"

module Algorithm100LargeHarness {{
  import Implementation = Algorithm100

  function Repeat(ch: char, count: nat): string
    decreases count
  {{
    if count == 0 then "" else [ch] + Repeat(ch, count - 1)
  }}

  method Main() {{
    var empty := Repeat('.', 2000);
    var screen := ["w" + Repeat('.', 1999)] + seq(1999, _ => empty);
    var output := Implementation.RunCore(2000, 2000, screen);
    if |output| != 2000 {{
      return;
    }}
  }}
}}
''',
        encoding="utf-8",
    )
    dll_path = tmp_path / "algorithm-100-large.dll"
    env = parity_env()
    run_checked_subprocess(
        [
            dafny_command(),
            "build",
            "--no-verify",
            "--target:cs",
            DAFNY_STANDARD_LIBRARY_OPTION,
            "--output",
            str(dll_path),
            str(harness_path),
        ],
        cwd=tmp_path,
        env={**env, "TMPDIR": "/tmp"},
        label="build large algorithm 100 harness",
    )
    run_candidate(
        dll_path,
        [],
        cwd=tmp_path,
        check=True,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
        env=env,
        timeout=BENCH_COMMAND_TIMEOUT_SEC,
    )


def _algorithm75_candidate_covers(
    n: int,
    m: int,
    grid: list[str],
    x: int,
    y: int,
) -> bool:
    if not (1 <= x <= n and 1 <= y <= m):
        return False
    row = x - 1
    col = y - 1
    return all(grid[r][c] != "*" or r == row or c == col for r in range(n) for c in range(m))


def _algorithm75_accepts(inputs: tuple[Any, ...], outputs: tuple[Any, ...]) -> bool:
    n, m, grid = inputs
    out_status, out_x, out_y = outputs
    if not isinstance(n, int) or not isinstance(m, int) or not isinstance(grid, list):
        return False
    if not isinstance(out_status, str) or not isinstance(out_x, int) or not isinstance(out_y, int):
        return False
    if out_status == "YES":
        return _algorithm75_candidate_covers(n, m, grid, out_x, out_y)
    if out_status == "NO":
        has_solution = any(
            _algorithm75_candidate_covers(n, m, grid, x, y)
            for x in range(1, n + 1)
            for y in range(1, m + 1)
        )
        return out_x == 0 and out_y == 0 and not has_solution
    return False


def _parse_harness_results(output: str, case_count: int) -> dict[int, bool]:
    results: dict[int, bool] = {}
    for raw_line in output.splitlines():
        if CASE_FRAME_PREFIX_RE.match(raw_line) is None:
            continue
        match = CASE_RESULT_RE.fullmatch(raw_line)
        if match is None:
            raise ValueError("malformed algorithm result frame")
        index = int(match.group("index"))
        if index >= case_count or index in results:
            raise ValueError("unknown or duplicate algorithm case index")
        results[index] = match.group("status") == "PASS"
    if len(results) != case_count:
        raise ValueError("missing algorithm result frame")
    return results


def _matches_output_type(value: Any, expected: Any) -> bool:
    if type(value) is not type(expected):
        return False
    if isinstance(expected, list):
        # All currently released sequence outputs contain strings; empty sequences carry
        # the same public element type, independent of their private expected contents.
        return all(isinstance(item, str) for item in value)
    return isinstance(expected, (int, bool, str))


def _parse_harness_outputs(
    output: str,
    parsed_cases: list[tuple[tuple[Any, ...], tuple[Any, ...]]],
) -> dict[int, tuple[Any, ...]]:
    results: dict[int, tuple[Any, ...]] = {}
    for raw_line in output.splitlines():
        if CASE_FRAME_PREFIX_RE.match(raw_line) is None:
            continue
        match = CASE_OUTPUT_RE.fullmatch(raw_line)
        if match is None:
            raise ValueError("malformed algorithm output frame")
        index = int(match.group("index"))
        if index >= len(parsed_cases) or index in results:
            raise ValueError("unknown or duplicate algorithm case index")
        values = json.loads(match.group("body"))
        expected_outputs = parsed_cases[index][1]
        if not isinstance(values, list) or len(values) != len(expected_outputs):
            raise ValueError("incorrect algorithm output arity")
        if not all(
            _matches_output_type(value, expected)
            for value, expected in zip(values, expected_outputs, strict=True)
        ):
            raise ValueError("incorrect algorithm output type")
        results[index] = tuple(values)
    if len(results) != len(parsed_cases):
        raise ValueError("missing algorithm output frame")
    return results


def _ordinary_case_results(
    outputs_by_case: dict[int, tuple[Any, ...]],
    parsed_cases: list[tuple[tuple[Any, ...], tuple[Any, ...]]],
) -> dict[int, bool]:
    return {
        index: outputs_by_case[index] == expected
        for index, (_, expected) in enumerate(parsed_cases)
    }


@pytest.fixture(scope="session")
def case_results(tmp_path_factory: pytest.TempPathFactory) -> dict[int, bool]:
    algorithm_id = _algorithm_id()
    parsed_cases = _parse_cases(_load_case_data(algorithm_id))
    assert parsed_cases

    run_override_build(ROOT)
    tmp_path = tmp_path_factory.mktemp(f"algorithm-{algorithm_id}")
    harness_path = tmp_path / f"{_class_name(algorithm_id)}Harness.dfy"
    harness_path.write_text(
        _emit_harness(algorithm_id, parsed_cases),
        encoding="utf-8",
    )
    dll_path = tmp_path / f"algorithm-{algorithm_id}-harness.dll"
    env = parity_env()
    _build_capture_harness(harness_path, dll_path, env)
    validator_dll = tmp_path / "algorithm-100-validator.dll"
    if algorithm_id == "100":
        validator_source = tmp_path / "Algorithm100Validator.dfy"
        validator_source.write_text(_emit_algorithm100_validator(), encoding="utf-8")
        _build_capture_harness(validator_source, validator_dll, env)
    execution_started = time.monotonic()
    completed = run_candidate(
        dll_path,
        [],
        input=_input_stream(parsed_cases),
        cwd=tmp_path,
        check=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.DEVNULL,
        text=True,
        env=env,
        timeout=BENCH_COMMAND_TIMEOUT_SEC,
    )
    if algorithm_id == "75":
        outputs_by_case = _parse_harness_outputs(completed.stdout, parsed_cases)
        assert len(outputs_by_case) == len(parsed_cases)
        return {
            index: _algorithm75_accepts(inputs, outputs_by_case[index])
            for index, (inputs, _) in enumerate(parsed_cases)
        }
    if algorithm_id == "100":
        outputs_by_case = _parse_harness_outputs(completed.stdout, parsed_cases)
        validation_cases = [
            ((*inputs, outputs_by_case[index][0]), ())
            for index, (inputs, _) in enumerate(parsed_cases)
        ]
        remaining = BENCH_COMMAND_TIMEOUT_SEC - (time.monotonic() - execution_started)
        if remaining <= 0:
            raise subprocess.TimeoutExpired(
                ["dotnet", str(validator_dll)], BENCH_COMMAND_TIMEOUT_SEC
            )
        validated = subprocess.run(
            ["dotnet", str(validator_dll)],
            input=_input_stream(validation_cases),
            cwd=tmp_path,
            env=env,
            check=True,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=remaining,
        )
        return _parse_harness_results(validated.stdout, len(parsed_cases))
    outputs_by_case = _parse_harness_outputs(completed.stdout, parsed_cases)
    return _ordinary_case_results(outputs_by_case, parsed_cases)


def test_positive_parser_case(
    case_index: int,
    parsed_case: tuple[tuple[Any, ...], tuple[Any, ...]] | None,
    case_results: dict[int, bool],
) -> None:
    # upstream: none - Validates local Dafny algorithm benchmark cases rather than a GNU coreutils
    # upstream-reason: script.
    assert parsed_case is not None
    assert case_results[case_index]
