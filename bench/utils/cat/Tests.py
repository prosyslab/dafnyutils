"""Check cat parity against GNU coreutils and verify its Dafny proof surface."""

import fcntl
import os
import subprocess
import tempfile
from pathlib import Path

import pytest

from evaluation.submission.candidate_execution import run_candidate
from tools.bench.bench_test_support import (
    BENCH_COMMAND_TIMEOUT_SEC,
    assert_requested_message_behavior,
    assert_result_matches_reference,
    bench_dll_path,
    build_bench_utility,
    build_coreutils_utility,
    coreutils_binary_path,
    evaluation_target_root,
    run_dafny_verify,
)

ROOT = evaluation_target_root(Path(__file__).resolve().parents[3])

BENCH_CAT_DLL = bench_dll_path(ROOT, ROOT / "_build" / "bench" / "cat_bench.dll")
COREUTILS_CAT = coreutils_binary_path(ROOT, ROOT / "_build" / "coreutils" / "src" / "cat")
CAT_VERIFY_TARGETS = [
    ROOT / "bench" / "utils" / "cat" / "CatCore.dfy",
    ROOT / "bench" / "utils" / "cat" / "CatProof.dfy",
    ROOT / "bench" / "utils" / "cat" / "Cat.dfy",
]


def build_bench_cat() -> None:
    build_bench_utility(ROOT, "cat")


def build_coreutils_cat() -> None:
    build_coreutils_utility(ROOT, "cat")


def latest_bench_cat_source_mtime() -> float:
    sources = [
        ROOT / "bench" / "core" / "IO.dfy",
        ROOT / "bench" / "core" / "IOExtern.cs",
    ]
    sources.extend((ROOT / "bench" / "core").glob("*.dfy"))
    sources.extend((ROOT / "bench" / "utils" / "cat").glob("*.dfy"))
    newest = 0.0
    for source in sources:
        try:
            newest = max(newest, source.stat().st_mtime)
        except FileNotFoundError:
            continue
    return newest


@pytest.fixture(scope="session", autouse=True)
def build_cat_once(request: pytest.FixtureRequest) -> None:
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
            not BENCH_CAT_DLL.exists()
            or latest_bench_cat_source_mtime() > BENCH_CAT_DLL.stat().st_mtime
        ):
            build_bench_cat()
        if not COREUTILS_CAT.exists():
            build_coreutils_cat()
        fcntl.flock(lock_file, fcntl.LOCK_UN)


def parity_env() -> dict[str, str]:
    env = os.environ.copy()
    env["LC_ALL"] = "C"
    env["LANG"] = "C"
    env["TZ"] = "UTC0"
    env["TERM"] = "dumb"
    env["NO_COLOR"] = "1"
    env["CLICOLOR_FORCE"] = "0"
    env["FORCE_COLOR"] = "0"
    return env


def run_bench_cat(
    args: list[str], cwd: Path, *, input_data: bytes = b""
) -> tuple[bytes, bytes, int]:
    completed = run_candidate(
        BENCH_CAT_DLL,
        args,
        cwd=cwd,
        check=False,
        input=input_data,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=False,
        env=parity_env(),
        timeout=BENCH_COMMAND_TIMEOUT_SEC,
    )
    return completed.stdout, completed.stderr, completed.returncode


def run_system_cat(
    args: list[str], cwd: Path, *, input_data: bytes = b""
) -> tuple[bytes, bytes, int]:
    completed = subprocess.run(
        ["cat", *args],
        executable=str(COREUTILS_CAT),
        cwd=cwd,
        check=False,
        input=input_data,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=False,
        env=parity_env(),
        timeout=BENCH_COMMAND_TIMEOUT_SEC,
    )
    return completed.stdout, completed.stderr, completed.returncode


def verify_cat_module(target: Path) -> None:
    run_dafny_verify(target)


def assert_same_result(
    ref_result: tuple[bytes, bytes, int],
    bench_result: tuple[bytes, bytes, int],
) -> None:
    def normalize_stdout(stdout: bytes) -> bytes:
        text = stdout.decode("latin1")
        text = text.replace("TorbjÃ¶rn", "Torbjörn")
        return text.encode("latin1")

    assert_result_matches_reference(
        ref_result,
        bench_result,
        stdout_normalizer=normalize_stdout,
    )


def test_file_passthrough_matches_coreutils() -> None:
    # upstream: coreutils/tests/cat/cat-self.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        input_file = cwd / "input.txt"
        _ = input_file.write_bytes(b"alpha\nbeta\n")

        args = ["input.txt"]
        ref = run_system_cat(args, cwd)
        bench = run_bench_cat(args, cwd)
        assert_same_result(ref, bench)


def test_multiple_files_match_coreutils() -> None:
    # upstream: coreutils/tests/cat/cat-self.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        first = cwd / "first.txt"
        second = cwd / "second.txt"
        _ = first.write_bytes(b"A\n")
        _ = second.write_bytes(b"B\n")

        args = ["first.txt", "second.txt"]
        ref = run_system_cat(args, cwd)
        bench = run_bench_cat(args, cwd)
        assert_same_result(ref, bench)


def test_repeated_large_file_matches_coreutils_without_stack_overflow() -> None:
    # upstream: coreutils/tests/cat/cat-self.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        payload = bytes(range(256)) * 16
        input_file = cwd / "input.bin"
        _ = input_file.write_bytes(payload)

        args = ["input.bin", "input.bin"]
        ref = run_system_cat(args, cwd)
        bench = run_bench_cat(args, cwd)
        assert_same_result(ref, bench)


def test_stdin_only_matches_coreutils() -> None:
    # upstream: coreutils/tests/cat/cat-self.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        stdin_payload = b"stdin-line-1\nstdin-line-2\n"

        ref = run_system_cat([], cwd, input_data=stdin_payload)
        bench = run_bench_cat([], cwd, input_data=stdin_payload)
        assert_same_result(ref, bench)


def test_dash_operand_matches_coreutils() -> None:
    # upstream: coreutils/tests/cat/cat-self.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        file_path = cwd / "tail.txt"
        _ = file_path.write_bytes(b"tail\n")
        stdin_payload = b"head\n"

        args = ["-", "tail.txt"]
        ref = run_system_cat(args, cwd, input_data=stdin_payload)
        bench = run_bench_cat(args, cwd, input_data=stdin_payload)
        assert_same_result(ref, bench)


def test_repeated_dash_consumes_stdin_once_matches_coreutils() -> None:
    # upstream: coreutils/tests/cat/cat-self.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        stdin_payload = b"only-once\n"

        args = ["-", "-"]
        ref = run_system_cat(args, cwd, input_data=stdin_payload)
        bench = run_bench_cat(args, cwd, input_data=stdin_payload)
        assert_same_result(ref, bench)


def test_relative_symlink_matches_coreutils() -> None:
    # upstream: coreutils/tests/cat/cat-self.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        link_dir = cwd / "dir"
        link_dir.mkdir()
        target = link_dir / "target.txt"
        link = link_dir / "link.txt"
        _ = target.write_bytes(b"via-link\n")
        link.symlink_to("target.txt")

        args = ["dir/link.txt"]
        ref = run_system_cat(args, cwd)
        bench = run_bench_cat(args, cwd)
        assert_same_result(ref, bench)


def test_number_all_lines_matches_coreutils() -> None:
    # upstream: coreutils/tests/cat/cat-self.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        input_file = cwd / "input.txt"
        _ = input_file.write_bytes(b"a\n\nb\n")

        args = ["-n", "input.txt"]
        ref = run_system_cat(args, cwd)
        bench = run_bench_cat(args, cwd)
        assert_same_result(ref, bench)


def test_number_nonblank_lines_matches_coreutils() -> None:
    # upstream: coreutils/tests/cat/cat-self.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        input_file = cwd / "input.txt"
        _ = input_file.write_bytes(b"a\n\nb\n")

        args = ["-b", "input.txt"]
        ref = run_system_cat(args, cwd)
        bench = run_bench_cat(args, cwd)
        assert_same_result(ref, bench)


def test_number_nonblank_overrides_number_matches_coreutils() -> None:
    # upstream: coreutils/tests/cat/cat-self.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        input_file = cwd / "input.txt"
        _ = input_file.write_bytes(b"a\n\nb\n")

        args = ["-n", "-b", "input.txt"]
        ref = run_system_cat(args, cwd)
        bench = run_bench_cat(args, cwd)
        assert_same_result(ref, bench)


def test_squeeze_blank_matches_coreutils() -> None:
    # upstream: coreutils/tests/cat/cat-self.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        input_file = cwd / "input.txt"
        _ = input_file.write_bytes(b"x\n\n\n\ny\n")

        args = ["-s", "input.txt"]
        ref = run_system_cat(args, cwd)
        bench = run_bench_cat(args, cwd)
        assert_same_result(ref, bench)


def test_show_ends_matches_coreutils() -> None:
    # upstream: coreutils/tests/cat/cat-E.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        input_file = cwd / "input.txt"
        _ = input_file.write_bytes(b"a\rb\r\nc\n")

        args = ["-E", "input.txt"]
        ref = run_system_cat(args, cwd)
        bench = run_bench_cat(args, cwd)
        assert_same_result(ref, bench)


def test_show_ends_crosses_file_boundary_matches_coreutils() -> None:
    # upstream: coreutils/tests/cat/cat-E.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        first = cwd / "first.txt"
        second = cwd / "second.txt"
        _ = first.write_bytes(b"\r")
        _ = second.write_bytes(b"\n")

        args = ["-E", "first.txt", "second.txt"]
        ref = run_system_cat(args, cwd)
        bench = run_bench_cat(args, cwd)
        assert_same_result(ref, bench)


@pytest.mark.parametrize(
    ("payloads", "file_names"),
    [
        ([b"a\rb\r\nc\n\r\nd\r"], ["input.txt"]),
        ([b"1\r", b"\n2\r\n"], ["first.txt", "second.txt"]),
        ([b"1\r", b"2\r\n"], ["first.txt", "second.txt"]),
    ],
    ids=["mixed-crlf", "crlf-spans-files", "lone-cr-before-next-file"],
)
def test_show_ends_regression_matrix_matches_coreutils(
    payloads: list[bytes],
    file_names: list[str],
) -> None:
    # upstream: coreutils/tests/cat/cat-E.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        for payload, file_name in zip(payloads, file_names, strict=True):
            _ = (cwd / file_name).write_bytes(payload)

        args = ["-E", *file_names]
        ref = run_system_cat(args, cwd)
        bench = run_bench_cat(args, cwd)
        assert_same_result(ref, bench)


def test_show_tabs_matches_coreutils() -> None:
    # upstream: coreutils/tests/cat/cat-E.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        input_file = cwd / "input.txt"
        _ = input_file.write_bytes(b"\tX\n")

        args = ["-T", "input.txt"]
        ref = run_system_cat(args, cwd)
        bench = run_bench_cat(args, cwd)
        assert_same_result(ref, bench)


def test_show_nonprinting_matches_coreutils() -> None:
    # upstream: coreutils/tests/cat/cat-E.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        input_file = cwd / "input.bin"
        _ = input_file.write_bytes(b"\x01\n")

        args = ["-v", "input.bin"]
        ref = run_system_cat(args, cwd)
        bench = run_bench_cat(args, cwd)
        assert_same_result(ref, bench)


def test_show_nonprinting_flush_timing_placeholder() -> None:
    # Not ported yet: this needs FIFO/pipe timing and observation before process
    # completion, while the current bench runner only returns completed output.
    # upstream: coreutils/tests/cat/cat-buf.sh
    pytest.skip("requires a timing-aware pipe/FIFO runner")


def test_show_all_matches_coreutils() -> None:
    # upstream: coreutils/tests/cat/cat-E.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        input_file = cwd / "input.bin"
        _ = input_file.write_bytes(b"\t\x01\n")

        args = ["-A", "input.bin"]
        ref = run_system_cat(args, cwd)
        bench = run_bench_cat(args, cwd)
        assert_same_result(ref, bench)


def test_short_equivalent_e_matches_coreutils() -> None:
    # upstream: coreutils/tests/cat/cat-E.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        input_file = cwd / "input.bin"
        _ = input_file.write_bytes(b"\x01\n")

        args = ["-e", "input.bin"]
        ref = run_system_cat(args, cwd)
        bench = run_bench_cat(args, cwd)
        assert_same_result(ref, bench)


def test_short_equivalent_t_matches_coreutils() -> None:
    # upstream: coreutils/tests/cat/cat-E.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        input_file = cwd / "input.bin"
        _ = input_file.write_bytes(b"\t\x01\n")

        args = ["-t", "input.bin"]
        ref = run_system_cat(args, cwd)
        bench = run_bench_cat(args, cwd)
        assert_same_result(ref, bench)


def test_long_options_match_coreutils() -> None:
    # upstream: coreutils/tests/cat/cat-E.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        input_file = cwd / "input.txt"
        _ = input_file.write_bytes(b"a\n\nb\n")

        args = ["--number", "--squeeze-blank", "input.txt"]
        ref = run_system_cat(args, cwd)
        bench = run_bench_cat(args, cwd)
        assert_same_result(ref, bench)


def test_missing_file_matches_coreutils() -> None:
    # upstream: coreutils/tests/cat/cat-self.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        args = ["missing.txt"]
        ref = run_system_cat(args, cwd)
        bench = run_bench_cat(args, cwd)
        assert_same_result(ref, bench)


def test_missing_file_with_space_operand_quotes_diagnostic_matches_coreutils() -> None:
    # upstream: coreutils/tests/cat/cat-self.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        # Fuzzing found this as a missing-file stderr mismatch; one spaced
        # operand is minimal.
        args = ["a b"]
        ref = run_system_cat(args, cwd)
        bench = run_bench_cat(args, cwd)
        assert_result_matches_reference(
            ref,
            bench,
            ignore_stderr_when_exit_nonzero=False,
        )


# A missing chmod-style path preserves GNU's shell-special quoting.
def test_missing_file_with_chmod_style_operand_quotes_diagnostic_matches_coreutils() -> None:
    # upstream: none - Covers a fuzzer-found byte-exact diagnostic for a missing
    # chmod-like shell-special operand.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        args = ["go=Xs,o=o,-g"]
        ref = run_system_cat(args, cwd)
        bench = run_bench_cat(args, cwd)
        assert_result_matches_reference(
            ref,
            bench,
            ignore_stderr_when_exit_nonzero=False,
        )


def test_directory_operand_matches_coreutils() -> None:
    # upstream: coreutils/tests/cat/cat-self.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        directory = cwd / "dir"
        directory.mkdir()

        args = ["dir"]
        ref = run_system_cat(args, cwd)
        bench = run_bench_cat(args, cwd)
        assert_same_result(ref, bench)


def test_proc_cpuinfo_show_ends_placeholder() -> None:
    # Not ported yet: /proc/cpuinfo is dynamic procfs state rather than stable
    # tempdir fixture data, so it needs a dedicated dynamic-output normalizer.
    # upstream: coreutils/tests/cat/cat-proc.sh
    pytest.skip("requires procfs-specific dynamic output normalization")


def test_same_input_output_descriptor_placeholder() -> None:
    # Not ported yet: these regressions require stdout opened as the input file
    # in truncate, append, or read/write fd modes instead of stdout=PIPE.
    # upstream: coreutils/tests/cat/cat-self.sh
    pytest.skip("requires direct file descriptor redirection support")


def test_help_version_dev_full_placeholder() -> None:
    # Not ported yet: exact generated help/version text and /dev/full write-
    # failure checks need stdout redirection beyond the current runner.
    # upstream: coreutils/tests/help/help-version.sh
    pytest.skip("requires stdout redirection support")


# Version output preserves the exact GNU C-locale authorship bytes and exit behavior.
def test_version_bytes_match_coreutils(tmp_path: Path) -> None:
    # upstream: none - repository-local GNU parity regression
    assert run_bench_cat(["--version"], tmp_path) == run_system_cat(["--version"], tmp_path)


def test_help_and_version_exit_successfully() -> None:
    # upstream: coreutils/tests/help/help-version.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        # Exact help/version text is unnecessary here.
        # We only care that both commands surface the requested output behavior.
        for args in (["--help"], ["--version"]):
            ref = run_system_cat(args, cwd)
            bench = run_bench_cat(args, cwd)
            assert_requested_message_behavior(ref, bench)


@pytest.mark.dafny_verify
@pytest.mark.parametrize("target", CAT_VERIFY_TARGETS, ids=lambda path: path.name)
def test_cat_modules_verify(target: Path) -> None:
    # upstream: none - Verifies the Dafny proof surface rather than an upstream runtime script.
    verify_cat_module(target)
