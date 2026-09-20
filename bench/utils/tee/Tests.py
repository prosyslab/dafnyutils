"""Check tee stdin fan-out parity against GNU coreutils and verify proof surface."""

import fcntl
import tempfile
from pathlib import Path

import pytest

from tools.bench.bench_test_support import (
    assert_requested_message_behavior,
    assert_result_matches_reference,
    bench_dll_path,
    build_bench_utility,
    build_coreutils_utility,
    coreutils_binary_path,
    evaluation_target_root,
    latest_bench_utility_source_mtime,
    run_bench_utility,
    run_coreutils_utility,
    run_dafny_verify,
)

ROOT = evaluation_target_root(Path(__file__).resolve().parents[3])

BENCH_TEE_DLL = bench_dll_path(ROOT, ROOT / "_build" / "bench" / "tee_bench.dll")
COREUTILS_TEE = coreutils_binary_path(ROOT, ROOT / "_build" / "coreutils" / "src" / "tee")
TEE_VERIFY_TARGETS = [
    ROOT / "bench" / "utils" / "tee" / "TeeSchema.dfy",
    ROOT / "bench" / "utils" / "tee" / "TeeCore.dfy",
    ROOT / "bench" / "utils" / "tee" / "TeeSpec.dfy",
    ROOT / "bench" / "utils" / "tee" / "TeeProof.dfy",
    ROOT / "bench" / "utils" / "tee" / "Tee.dfy",
]


@pytest.fixture(scope="session", autouse=True)
def build_tee_once(request: pytest.FixtureRequest) -> None:
    # Source verification needs no candidate or GNU executable build.
    if request.session.items and all(
        item.get_closest_marker("dafny_verify") for item in request.session.items
    ):
        return
    lock_path = ROOT / "_build" / "bench" / ".build_bench_lock"
    lock_path.parent.mkdir(parents=True, exist_ok=True)
    with lock_path.open("w", encoding="utf-8") as lock_file:
        fcntl.flock(lock_file, fcntl.LOCK_EX)
        if (
            not BENCH_TEE_DLL.exists()
            or latest_bench_utility_source_mtime(ROOT, "tee") > BENCH_TEE_DLL.stat().st_mtime
        ):
            build_bench_utility(ROOT, "tee")
        if not COREUTILS_TEE.exists():
            build_coreutils_utility(ROOT, "tee")
        fcntl.flock(lock_file, fcntl.LOCK_UN)


def run_bench_tee(
    args: list[str],
    cwd: Path,
    *,
    input_data: bytes,
) -> tuple[bytes, bytes, int]:
    return run_bench_utility(BENCH_TEE_DLL, args, cwd, input_data=input_data)


def run_system_tee(
    args: list[str],
    cwd: Path,
    *,
    input_data: bytes,
) -> tuple[bytes, bytes, int]:
    return run_coreutils_utility(COREUTILS_TEE, "tee", args, cwd, input_data=input_data)


def assert_tee_parity(
    args: list[str],
    ref_cwd: Path,
    bench_cwd: Path,
    *,
    input_data: bytes,
) -> None:
    ref = run_system_tee(args, ref_cwd, input_data=input_data)
    bench = run_bench_tee(args, bench_cwd, input_data=input_data)
    assert_result_matches_reference(ref, bench)


# Stdin is copied to stdout and the named output file.
def test_writes_stdin_to_stdout_and_file_matches_coreutils() -> None:
    # upstream: coreutils/tests/tee/tee.sh
    with tempfile.TemporaryDirectory() as ref_tmp, tempfile.TemporaryDirectory() as bench_tmp:
        ref_cwd = Path(ref_tmp)
        bench_cwd = Path(bench_tmp)

        input_data = b"line\n"
        assert_tee_parity(["out"], ref_cwd, bench_cwd, input_data=input_data)

        assert (ref_cwd / "out").read_bytes() == input_data
        assert (bench_cwd / "out").read_bytes() == input_data


# Append mode keeps the existing file prefix and writes only new input to stdout.
def test_append_option_preserves_existing_prefix_matches_coreutils() -> None:
    # upstream: coreutils/tests/tee/append.sh
    with tempfile.TemporaryDirectory() as ref_tmp, tempfile.TemporaryDirectory() as bench_tmp:
        ref_cwd = Path(ref_tmp)
        bench_cwd = Path(bench_tmp)
        for cwd in [ref_cwd, bench_cwd]:
            (cwd / "out").write_bytes(b"line 1\n")

        input_data = b"line 2\n"
        assert_tee_parity(["-a", "out"], ref_cwd, bench_cwd, input_data=input_data)

        assert (ref_cwd / "out").read_bytes() == b"line 1\nline 2\n"
        assert (bench_cwd / "out").read_bytes() == b"line 1\nline 2\n"


# Multiple output operands each receive the same stdin bytes.
def test_multiple_outputs_receive_same_data_matches_coreutils() -> None:
    # upstream: coreutils/tests/tee/tee.sh
    with tempfile.TemporaryDirectory() as ref_tmp, tempfile.TemporaryDirectory() as bench_tmp:
        ref_cwd = Path(ref_tmp)
        bench_cwd = Path(bench_tmp)

        input_data = b"payload\n"
        args = ["one", "two", "three"]
        assert_tee_parity(args, ref_cwd, bench_cwd, input_data=input_data)

        for name in args:
            assert (ref_cwd / name).read_bytes() == input_data
            assert (bench_cwd / name).read_bytes() == input_data


# Help exits successfully with the shared requested-message contract.
def test_help_exit_successfully_matches_coreutils() -> None:
    # upstream: coreutils/tests/help/help-version.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_requested_message_behavior(
            run_system_tee(["--help"], cwd, input_data=b"ignored"),
            run_bench_tee(["--help"], cwd, input_data=b"ignored"),
        )


# Version exits successfully with the shared requested-message contract.
def test_version_exit_successfully_matches_coreutils() -> None:
    # upstream: coreutils/tests/help/help-version.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_requested_message_behavior(
            run_system_tee(["--version"], cwd, input_data=b"ignored"),
            run_bench_tee(["--version"], cwd, input_data=b"ignored"),
        )


# Dafny modules for tee verify independently.
@pytest.mark.dafny_verify
def test_tee_verified_surface_targets() -> None:
    # upstream: none - Verifies the Dafny proof surface rather than an upstream runtime script.
    for target in TEE_VERIFY_TARGETS:
        run_dafny_verify(target)
