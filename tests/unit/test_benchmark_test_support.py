"""Check benchmark oracle helpers through controlled process boundaries."""

from __future__ import annotations

import sys
from pathlib import Path
from unittest.mock import Mock

import pytest

import tools.test_support as support


# A direct oracle build uses the local contributor command with the selected benchmark root.
def test_benchmark_build_uses_local_contributor_command(monkeypatch: pytest.MonkeyPatch) -> None:
    calls: list[tuple[list[str], dict[str, object]]] = []
    monkeypatch.setattr(support.os, "environ", {})
    monkeypatch.setattr(
        support,
        "run_checked_subprocess",
        lambda command, **kwargs: calls.append((command, kwargs)),
    )

    support.build_bench_utility(Path("/virtual/benchmark"), "cat")

    assert calls[0][0] == [
        sys.executable,
        "-m",
        "tools.contribution.make_tasks",
        "build",
        "--root",
        "/virtual/benchmark",
        "--task",
        "cat",
    ]
    assert calls[0][1]["cwd"] == Path("/virtual/benchmark")
    assert calls[0][1]["label"] == "build cat"


# A selected prebuilt file replaces legacy callbacks for both candidate runtimes.
@pytest.mark.parametrize("artifact", ("_build/bench/cat_bench.dll", "/native/cat"))
def test_benchmark_build_uses_selected_prebuilt_file(
    monkeypatch: pytest.MonkeyPatch,
    artifact: str,
) -> None:
    monkeypatch.setattr(
        support.os,
        "environ",
        {
            support.EVAL_BENCH_DLL_ENV: artifact,
            support.EVAL_BENCH_BUILD_SCRIPT_ENV: "eval_support/build.sh",
        },
    )
    inspected: list[Path] = []

    def is_file(path: Path) -> bool:
        inspected.append(path)
        return True

    process = Mock()
    monkeypatch.setattr(Path, "is_file", is_file)
    monkeypatch.setattr(support, "run_checked_subprocess", process)

    support.build_bench_utility(Path("/virtual/benchmark"), "cat")

    expected = Path(artifact)
    if not expected.is_absolute():
        expected = Path("/virtual/benchmark") / expected
    assert inspected == [expected]
    process.assert_not_called()


# A selected artifact that is absent or a directory must fail without rebuilding it.
def test_benchmark_build_rejects_missing_prebuilt_file(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(
        support.os,
        "environ",
        {support.EVAL_BENCH_DLL_ENV: "_build/bench/cat_bench.dll"},
    )
    monkeypatch.setattr(Path, "is_file", lambda path: False)
    process = Mock()
    monkeypatch.setattr(support, "run_checked_subprocess", process)

    with pytest.raises(FileNotFoundError, match="requires a prebuilt candidate file"):
        support.build_bench_utility(Path("/virtual/benchmark"), "cat")

    process.assert_not_called()


# An empty explicit artifact selection cannot silently request a local build.
def test_benchmark_build_rejects_empty_prebuilt_selection(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(support.os, "environ", {support.EVAL_BENCH_DLL_ENV: ""})
    process = Mock()
    monkeypatch.setattr(support, "run_checked_subprocess", process)

    with pytest.raises(ValueError, match="must select a prebuilt candidate file"):
        support.build_bench_utility(Path("/virtual/benchmark"), "cat")

    process.assert_not_called()


# A callback request without a prebuilt artifact fails instead of executing foreign code.
def test_benchmark_build_rejects_unsupported_callback(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(
        support.os,
        "environ",
        {support.EVAL_BENCH_BUILD_SCRIPT_ENV: "eval_support/build.sh"},
    )
    process = Mock()
    monkeypatch.setattr(support, "run_checked_subprocess", process)

    with pytest.raises(ValueError, match="callbacks are unsupported"):
        support.build_bench_utility(Path("/virtual/benchmark"), "cat")

    process.assert_not_called()


# Ordinary Dafny installations can verify with the fixed benchmark library policy.
def test_verify_uses_ordinary_dafny_and_runtime_limits(monkeypatch: pytest.MonkeyPatch) -> None:
    calls: list[tuple[list[str], dict[str, object]]] = []
    monkeypatch.setattr(support.os, "environ", {})
    monkeypatch.setattr(
        support,
        "run_checked_subprocess",
        lambda command, **kwargs: calls.append((command, kwargs)),
    )

    support.run_dafny_verify(Path("/benchmark/Proof.dfy"), ("--cores:1",))

    assert calls[0][0] == [
        "dafny",
        "verify",
        "/benchmark/Proof.dfy",
        "--standard-libraries:false",
        "--allow-external-contracts",
        "--dont-verify-dependencies",
        "--cores:1",
    ]
    assert calls[0][1]["cwd"] == "/tmp"
    assert calls[0][1]["env"] == {
        "TMPDIR": "/tmp",
        "DOTNET_ROOT": "/usr/share/dotnet",
        "DOTNET_GCHeapHardLimit": hex(10 * 1024 * 1024 * 1024),
        "COMPlus_GCHeapHardLimit": hex(10 * 1024 * 1024 * 1024),
    }


# Explicit compiler and runtime settings remain authoritative during proof checks.
def test_verify_preserves_configured_dafny_and_heap_limit(monkeypatch: pytest.MonkeyPatch) -> None:
    calls: list[tuple[list[str], dict[str, object]]] = []
    monkeypatch.setattr(
        support.os,
        "environ",
        {"DAFNY_BENCHMARK": "/tools/dafny", "DOTNET_GCHeapHardLimit": "0x100"},
    )
    monkeypatch.setattr(
        support,
        "run_checked_subprocess",
        lambda command, **kwargs: calls.append((command, kwargs)),
    )

    support.run_dafny_verify(Path("/benchmark/Proof.dfy"))

    assert calls[0][0][0] == "/tools/dafny"
    assert calls[0][1]["env"]["DOTNET_GCHeapHardLimit"] == "0x100"
    assert calls[0][1]["env"]["COMPlus_GCHeapHardLimit"] == "0x100"


# Successful parity checks retain exact exit status and byte stream comparisons.
def test_parity_accepts_identical_results() -> None:
    support.assert_result_matches_reference((b"output", b"error", 0), (b"output", b"error", 0))


# Successful commands cannot hide a changed stream or exit status.
@pytest.mark.parametrize(
    "changed", ((b"changed", b"error", 0), (b"output", b"changed", 0), (b"output", b"error", 1))
)
def test_parity_rejects_changed_successful_results(changed: tuple[bytes, bytes, int]) -> None:
    with pytest.raises(AssertionError):
        support.assert_result_matches_reference((b"output", b"error", 0), changed)


# Error text can vary when exit status and the normal output agree.
def test_parity_ignores_nonzero_error_text_by_default() -> None:
    support.assert_result_matches_reference((b"", b"reference", 2), (b"", b"candidate", 2))


# Callers can require exact error messages even for a failed command.
def test_parity_honors_strict_nonzero_error_text() -> None:
    with pytest.raises(AssertionError):
        support.assert_result_matches_reference(
            (b"", b"reference", 2),
            (b"", b"candidate", 2),
            ignore_stderr_when_exit_nonzero=False,
        )


# Message checks compare stream presence while permitting different message text.
def test_requested_messages_compare_presence() -> None:
    support.assert_requested_message_behavior((b"help", b"", 0), (b"usage", b"", 0))


# Message checks still fail when the requested output is missing.
def test_requested_messages_reject_missing_output() -> None:
    with pytest.raises(AssertionError):
        support.assert_requested_message_behavior((b"help", b"", 0), (b"", b"", 0))


# Explicit normalizers apply to both reference and candidate streams.
def test_parity_normalizes_selected_streams() -> None:
    support.assert_result_matches_reference(
        (b"output\n", b"error\n", 0),
        (b"output", b"error", 0),
        stdout_normalizer=bytes.strip,
        stderr_normalizer=bytes.strip,
    )
