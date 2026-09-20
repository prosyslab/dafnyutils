"""Check touch parity against GNU coreutils and verify its Dafny proof surface."""

import fcntl
import os
import re
import subprocess
import tempfile
import time
from datetime import datetime, timezone
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

BENCH_TOUCH_DLL = bench_dll_path(ROOT, ROOT / "_build" / "bench" / "touch_bench.dll")
COREUTILS_TOUCH = coreutils_binary_path(ROOT, ROOT / "_build" / "coreutils" / "src" / "touch")
TOUCH_TIME_PARSER = ROOT / "_build" / "bench" / "touch_time_parser"
TOUCH_TIME_PARSER_PROTOCOL = "dafnyutils-touch-time-parser-v1"
TOUCH_VERIFY_TARGETS = [
    ROOT / "bench" / "utils" / "touch" / "TouchCore.dfy",
    ROOT / "bench" / "utils" / "touch" / "TouchProof.dfy",
    ROOT / "bench" / "utils" / "touch" / "Touch.dfy",
]
INITIAL_ATIME_NS = 946_684_800_123_456_789
INITIAL_MTIME_NS = 946_684_801_987_654_321
Y2K_NS = 946_684_800_000_000_000
FEB_2001_NS = 981_173_106_000_000_000
MAR_2002_NS = 1_015_218_367_000_000_000
APR_2003_NS = 1_049_522_828_000_000_000
REFERENCE_ATIME_NS = 1_000_000_000_123_456_789
REFERENCE_MTIME_NS = 1_000_000_001_987_654_321
LINK_ATIME_NS = 1_100_000_000_123_456_789
LINK_MTIME_NS = 1_100_000_001_987_654_321
FILESYSTEM_CURRENT_TIME_TOLERANCE_NS = 1_000_000_000


def build_bench_touch() -> None:
    build_bench_utility(ROOT, "touch")


def build_coreutils_touch() -> None:
    build_coreutils_utility(ROOT, "touch")


def latest_bench_touch_source_mtime() -> float:
    sources = [
        ROOT / "bench" / "core" / "IO.dfy",
        ROOT / "bench" / "core" / "IOExtern.cs",
        ROOT / "bench" / "core" / "TouchTimeParser.c",
    ]
    sources.extend((ROOT / "bench" / "core").glob("*.dfy"))
    sources.extend((ROOT / "bench" / "utils" / "touch").glob("*.dfy"))
    newest = 0.0
    for source in sources:
        try:
            newest = max(newest, source.stat().st_mtime)
        except FileNotFoundError:
            continue
    return newest


@pytest.fixture(scope="session", autouse=True)
def build_touch_once(request: pytest.FixtureRequest) -> None:
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
            not BENCH_TOUCH_DLL.exists()
            or not TOUCH_TIME_PARSER.exists()
            or latest_bench_touch_source_mtime() > BENCH_TOUCH_DLL.stat().st_mtime
        ):
            build_bench_touch()
        if not COREUTILS_TOUCH.exists():
            build_coreutils_touch()
        fcntl.flock(lock_file, fcntl.LOCK_UN)


def parity_env() -> dict[str, str]:
    env = os.environ.copy()
    _ = env.setdefault("DOTNET_ROOT", "/usr/share/dotnet")
    _ = env.setdefault("NUGET_PACKAGES", "/home/vscode/.nuget/packages")
    _ = env.setdefault("RestoreSources", env["NUGET_PACKAGES"])
    _ = env.setdefault("RestoreIgnoreFailedSources", "true")
    env["LC_ALL"] = "C"
    env["LANG"] = "C"
    env["TZ"] = "UTC0"
    env["TERM"] = "dumb"
    env["NO_COLOR"] = "1"
    env["CLICOLOR_FORCE"] = "0"
    env["FORCE_COLOR"] = "0"
    return env


def run_bench_touch(args: list[str], cwd: Path) -> tuple[bytes, bytes, int]:
    completed = run_candidate(
        BENCH_TOUCH_DLL,
        args,
        runtime_files=[TOUCH_TIME_PARSER],
        python_helpers=True,
        cwd=cwd,
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=False,
        env=parity_env(),
        timeout=BENCH_COMMAND_TIMEOUT_SEC,
    )
    return completed.stdout, completed.stderr, completed.returncode


def run_system_touch(args: list[str], cwd: Path) -> tuple[bytes, bytes, int]:
    completed = subprocess.run(
        ["touch", *args],
        executable=str(COREUTILS_TOUCH),
        cwd=cwd,
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=False,
        env=parity_env(),
        timeout=BENCH_COMMAND_TIMEOUT_SEC,
    )
    return completed.stdout, completed.stderr, completed.returncode


def run_touch_time_parser(
    operation: str,
    text: str,
    reference_seconds: int,
    reference_nanoseconds: int,
) -> subprocess.CompletedProcess[bytes]:
    payload = text.encode("utf-8")
    header = (
        f"{TOUCH_TIME_PARSER_PROTOCOL}\n{operation}\n{reference_seconds}\n"
        f"{reference_nanoseconds}\n{len(payload)}\n"
    ).encode("ascii")
    return subprocess.run(
        [str(TOUCH_TIME_PARSER)],
        input=header + payload,
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        timeout=BENCH_COMMAND_TIMEOUT_SEC,
    )


def decode_touch_time_parser_success(output: bytes) -> tuple[int, int]:
    version, status, seconds, nanoseconds, terminal = output.decode("ascii").split("\n")
    assert version == TOUCH_TIME_PARSER_PROTOCOL
    assert status == "ok"
    assert terminal == ""
    return int(seconds), int(nanoseconds)


def write_fake_time_parser(path: Path, program: str) -> None:
    path.write_text(program, encoding="utf-8")
    path.chmod(0o755)


def run_touch_with_stdout_target(
    command: list[str],
    args: list[str],
    cwd: Path,
    stdout_target: Path,
) -> tuple[tuple[bytes, bytes, int], tuple[int, int]]:
    with stdout_target.open("r+b") as stdout_stream:
        if command[0] == "dotnet":
            completed = run_candidate(
                Path(command[1]),
                args,
                cwd=cwd,
                runtime_files=[TOUCH_TIME_PARSER],
                python_helpers=True,
                check=False,
                stdout=stdout_stream,
                stderr=subprocess.PIPE,
                text=False,
                env=parity_env(),
                timeout=BENCH_COMMAND_TIMEOUT_SEC,
            )
        else:
            completed = subprocess.run(
                [*command, *args],
                cwd=cwd,
                check=False,
                stdout=stdout_stream,
                stderr=subprocess.PIPE,
                text=False,
                env=parity_env(),
                timeout=BENCH_COMMAND_TIMEOUT_SEC,
            )
        stdout_length = stdout_stream.tell()
        target_times = path_times_ns(stdout_target)
        stdout_stream.seek(0)
        stdout_bytes = stdout_stream.read(stdout_length)
    return (stdout_bytes, completed.stderr, completed.returncode), target_times


def verify_touch_target(target: Path) -> None:
    run_dafny_verify(target)


def assert_same_result(
    ref_result: tuple[bytes, bytes, int],
    bench_result: tuple[bytes, bytes, int],
) -> None:
    def normalize_help_hint(stderr: bytes) -> bytes:
        text = stderr.decode("latin1")
        text = re.sub(
            r"Try '.*touch --help' for more information\.\n",
            "Try 'touch --help' for more information.\n",
            text,
        )
        return text.encode("latin1")

    assert_result_matches_reference(
        ref_result,
        bench_result,
        stderr_normalizer=normalize_help_hint,
    )


def write_timestamped_file(
    directory: Path,
    name: str,
    atime_ns: int = INITIAL_ATIME_NS,
    mtime_ns: int = INITIAL_MTIME_NS,
) -> Path:
    path = directory / name
    _ = path.write_text("payload\n", encoding="utf-8")
    os.utime(path, ns=(atime_ns, mtime_ns))
    return path


def path_times_ns(path: Path) -> tuple[int, int]:
    stat_result = path.stat()
    return stat_result.st_atime_ns, stat_result.st_mtime_ns


def symlink_times_ns(path: Path) -> tuple[int, int]:
    stat_result = path.lstat()
    return stat_result.st_atime_ns, stat_result.st_mtime_ns


def test_missing_operand_matches_coreutils() -> None:
    # upstream: coreutils/tests/touch/no-create-missing.sh
    # upstream: coreutils/tests/touch/dangling-symlink.sh
    # upstream: coreutils/tests/touch/dir-1.sh
    # upstream: coreutils/tests/touch/60-seconds.sh
    # upstream: coreutils/tests/touch/trailing-slash.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        args: list[str] = []
        ref = run_system_touch(args, cwd)
        bench = run_bench_touch(args, cwd)
        assert_same_result(ref, bench)


# GNU parser regression: missing required option arguments use canonical diagnostics.
@pytest.mark.parametrize(
    "args",
    [
        ["-d"],
        ["-r"],
        ["-t"],
        ["-ar"],
        ["--date"],
        ["--reference"],
        ["--ref"],
        ["--time"],
    ],
)
def test_missing_required_argument_matches_coreutils(args: list[str]) -> None:
    # upstream: none - repository-local GNU parity regression
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        ref = run_system_touch(args, cwd)
        bench = run_bench_touch(args, cwd)
        assert_same_result(ref, bench)


# GNU reference regression: reference lookup failure precedes the missing operand check.
def test_missing_reference_file_without_operand_matches_coreutils() -> None:
    # upstream: none - repository-local GNU parity regression
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        args = ["-r", "missing-reference"]
        ref = run_system_touch(args, cwd)
        bench = run_bench_touch(args, cwd)
        assert_same_result(ref, bench)


def test_no_create_missing_matches_coreutils() -> None:
    # upstream: coreutils/tests/touch/no-create-missing.sh
    # upstream: coreutils/tests/touch/dangling-symlink.sh
    # upstream: coreutils/tests/touch/dir-1.sh
    # upstream: coreutils/tests/touch/60-seconds.sh
    # upstream: coreutils/tests/touch/trailing-slash.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        args = ["-c", "missing.txt"]
        ref = run_system_touch(args, cwd)
        bench = run_bench_touch(args, cwd)
        assert_same_result(ref, bench)
        assert not (cwd / "missing.txt").exists()


@pytest.mark.parametrize("args", [["-cm", "missing.txt"], ["-ca", "missing.txt"]])
def test_no_create_missing_mode_variants_match_coreutils(args: list[str]) -> None:
    # upstream: coreutils/tests/touch/no-create-missing.sh
    # upstream: coreutils/tests/touch/dangling-symlink.sh
    # upstream: coreutils/tests/touch/dir-1.sh
    # upstream: coreutils/tests/touch/60-seconds.sh
    # upstream: coreutils/tests/touch/trailing-slash.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        ref = run_system_touch(args, cwd)
        bench = run_bench_touch(args, cwd)
        assert_same_result(ref, bench)
        assert not (cwd / "missing.txt").exists()


def test_invalid_time_argument_does_not_create_files_matches_coreutils() -> None:
    # upstream: coreutils/tests/touch/no-create-missing.sh
    # upstream: coreutils/tests/touch/dangling-symlink.sh
    # upstream: coreutils/tests/touch/dir-1.sh
    # upstream: coreutils/tests/touch/60-seconds.sh
    # upstream: coreutils/tests/touch/trailing-slash.sh
    with (
        tempfile.TemporaryDirectory() as ref_tmp_dir,
        tempfile.TemporaryDirectory() as bench_tmp_dir,
    ):
        ref_cwd = Path(ref_tmp_dir)
        bench_cwd = Path(bench_tmp_dir)

        args = ["--time", "-m", "created.txt"]
        ref = run_system_touch(args, ref_cwd)
        bench = run_bench_touch(args, bench_cwd)
        assert_same_result(ref, bench)
        assert not (ref_cwd / "created.txt").exists()
        assert not (bench_cwd / "created.txt").exists()


def test_invalid_time_before_help_matches_coreutils() -> None:
    # From fuzzing: a later --help must not override an earlier invalid --time value.
    # upstream: coreutils/tests/touch/no-create-missing.sh
    # upstream: coreutils/tests/touch/dangling-symlink.sh
    # upstream: coreutils/tests/touch/dir-1.sh
    # upstream: coreutils/tests/touch/60-seconds.sh
    # upstream: coreutils/tests/touch/trailing-slash.sh
    with (
        tempfile.TemporaryDirectory() as ref_tmp_dir,
        tempfile.TemporaryDirectory() as bench_tmp_dir,
    ):
        ref_cwd = Path(ref_tmp_dir)
        bench_cwd = Path(bench_tmp_dir)

        args = ["--time", "-r", "--help"]
        ref = run_system_touch(args, ref_cwd)
        bench = run_bench_touch(args, bench_cwd)
        assert_same_result(ref, bench)


@pytest.mark.parametrize(
    "args",
    [
        ["--time=access", "--help", "--time=bad"],
        ["--time=bad", "--time=access", "--help"],
        ["--time=a", "--help"],
        ["--time=", "--help"],
    ],
)
def test_time_arg_order_and_argmatch_before_help_match_coreutils(args: list[str]) -> None:
    # upstream: coreutils/tests/touch/no-create-missing.sh
    # upstream: coreutils/tests/touch/dangling-symlink.sh
    # upstream: coreutils/tests/touch/dir-1.sh
    # upstream: coreutils/tests/touch/60-seconds.sh
    # upstream: coreutils/tests/touch/trailing-slash.sh
    with (
        tempfile.TemporaryDirectory() as ref_tmp_dir,
        tempfile.TemporaryDirectory() as bench_tmp_dir,
    ):
        ref_cwd = Path(ref_tmp_dir)
        bench_cwd = Path(bench_tmp_dir)

        ref = run_system_touch(args, ref_cwd)
        bench = run_bench_touch(args, bench_cwd)
        assert_requested_message_behavior(ref, bench)


def test_time_abbreviation_creates_file_matches_coreutils() -> None:
    # upstream: coreutils/tests/touch/no-create-missing.sh
    # upstream: coreutils/tests/touch/dangling-symlink.sh
    # upstream: coreutils/tests/touch/dir-1.sh
    # upstream: coreutils/tests/touch/60-seconds.sh
    # upstream: coreutils/tests/touch/trailing-slash.sh
    with (
        tempfile.TemporaryDirectory() as ref_tmp_dir,
        tempfile.TemporaryDirectory() as bench_tmp_dir,
    ):
        ref_cwd = Path(ref_tmp_dir)
        bench_cwd = Path(bench_tmp_dir)

        args = ["--time=a", "created.txt"]
        ref = run_system_touch(args, ref_cwd)
        bench = run_bench_touch(args, bench_cwd)
        assert_same_result(ref, bench)
        assert (ref_cwd / "created.txt").exists()
        assert (bench_cwd / "created.txt").exists()


# GNU date regression: relative weekdays resolve before touching the operand.
def test_next_weekday_date_matches_coreutils(monkeypatch: pytest.MonkeyPatch) -> None:
    # upstream: none - repository-local GNU parity regression
    monkeypatch.setenv("TZ", "UTC0")
    with (
        tempfile.TemporaryDirectory() as ref_tmp_dir,
        tempfile.TemporaryDirectory() as bench_tmp_dir,
    ):
        ref_cwd = Path(ref_tmp_dir)
        bench_cwd = Path(bench_tmp_dir)
        ref_file = write_timestamped_file(ref_cwd, "file")
        bench_file = write_timestamped_file(bench_cwd, "file")

        args = ["-d", "next monday", "file"]
        ref = run_system_touch(args, ref_cwd)
        bench = run_bench_touch(args, bench_cwd)
        assert_same_result(ref, bench)
        assert path_times_ns(ref_file) == path_times_ns(bench_file)


# GNU date regression: a lone dash resolves to local midnight.
def test_dash_date_matches_coreutils(monkeypatch: pytest.MonkeyPatch) -> None:
    # upstream: none - repository-local GNU parity regression
    monkeypatch.setenv("TZ", "UTC0")
    with (
        tempfile.TemporaryDirectory() as ref_tmp_dir,
        tempfile.TemporaryDirectory() as bench_tmp_dir,
    ):
        ref_cwd = Path(ref_tmp_dir)
        bench_cwd = Path(bench_tmp_dir)
        ref_file = write_timestamped_file(ref_cwd, "file")
        bench_file = write_timestamped_file(bench_cwd, "file")

        args = ["-d", "-", "file"]
        ref = run_system_touch(args, ref_cwd)
        bench = run_bench_touch(args, bench_cwd)
        assert_same_result(ref, bench)
        assert path_times_ns(ref_file) == path_times_ns(bench_file)


# GNU-valid date forms must be delegated unchanged to the pinned gnulib parser.
@pytest.mark.parametrize("date_text", ["yesterday", "@0", "2 hours ago"])
def test_gnu_date_expressions_match_coreutils(tmp_path: Path, date_text: str) -> None:
    # upstream: none - repository-local GNU parity regression
    ref_dir, bench_dir = tmp_path / "ref", tmp_path / "bench"
    ref_dir.mkdir()
    bench_dir.mkdir()
    for cwd in [ref_dir, bench_dir]:
        write_timestamped_file(cwd, "reference", REFERENCE_ATIME_NS, REFERENCE_MTIME_NS)
        write_timestamped_file(cwd, "file")

    args = ["-r", "reference", "-d", date_text, "file"]
    assert_same_result(run_system_touch(args, ref_dir), run_bench_touch(args, bench_dir))
    ref_times = path_times_ns(ref_dir / "file")
    bench_times = path_times_ns(bench_dir / "file")
    assert ref_times == bench_times
    if date_text == "@0":
        assert bench_times == (0, 0)
    elif date_text == "2 hours ago":
        assert bench_times == (
            REFERENCE_ATIME_NS - 7_200_000_000_000,
            REFERENCE_MTIME_NS - 7_200_000_000_000,
        )


# An empty -d value is a valid gnulib request and uses the supplied reference date.
def test_empty_date_matches_coreutils_and_does_not_become_absent(tmp_path: Path) -> None:
    # upstream: none - repository-local GNU parity regression
    ref_dir, bench_dir = tmp_path / "ref", tmp_path / "bench"
    ref_dir.mkdir()
    bench_dir.mkdir()
    for cwd in [ref_dir, bench_dir]:
        write_timestamped_file(cwd, "reference", REFERENCE_ATIME_NS, REFERENCE_MTIME_NS)
        write_timestamped_file(cwd, "file")

    args = ["-r", "reference", "-d", "", "file"]
    assert_same_result(run_system_touch(args, ref_dir), run_bench_touch(args, bench_dir))
    assert path_times_ns(ref_dir / "file") == path_times_ns(bench_dir / "file")


# The helper's wrapped rpl_time makes an 8-digit -t use the supplied current year.
def test_timestamp_parser_uses_supplied_year_for_eight_digits() -> None:
    # upstream: none - repository-local time parser regression
    supplied_now = int(datetime(2000, 6, 1, tzinfo=timezone.utc).timestamp())
    completed = run_touch_time_parser("timestamp", "01020304", supplied_now, 987_654_321)

    assert completed.returncode == 0
    assert completed.stderr == b""
    assert decode_touch_time_parser_success(completed.stdout) == (
        int(datetime(2000, 1, 2, 3, 4, tzinfo=timezone.utc).timestamp()),
        0,
    )


# Invalid parser text is a successful protocol exchange with an explicit invalid result.
def test_time_parser_protocol_separates_invalid_text_from_process_failure() -> None:
    # upstream: none - repository-local time parser regression
    completed = run_touch_time_parser("date", "not-a-date", 1_000_000_000, 123_456_789)

    assert completed.returncode == 0
    assert completed.stderr == b""
    assert completed.stdout == (f"{TOUCH_TIME_PARSER_PROTOCOL}\ninvalid\n".encode("ascii"))


# A missing trusted helper aborts as infrastructure failure instead of reporting invalid date.
def test_missing_time_parser_is_infrastructure_failure(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    # upstream: none - repository-local time parser regression
    monkeypatch.setenv("DAFNYUTILS_TOUCH_TIME_PARSER", str(tmp_path / "missing-parser"))

    _stdout, stderr, returncode = run_bench_touch(["-d", "@0", "file"], tmp_path)

    assert returncode != 0
    assert b"trusted time parser infrastructure failure" in stderr
    assert b"invalid date format" not in stderr


# A nonzero trusted helper exit remains an infrastructure failure with its process status.
def test_nonzero_time_parser_is_infrastructure_failure(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    # upstream: none - repository-local time parser regression
    helper = tmp_path / "nonzero-parser"
    write_fake_time_parser(
        helper,
        "#!/usr/bin/env python3\nimport sys\nsys.stdin.buffer.read()\nraise SystemExit(42)\n",
    )
    monkeypatch.setenv("DAFNYUTILS_TOUCH_TIME_PARSER", str(helper))

    _stdout, stderr, returncode = run_bench_touch(["-d", "@0", "file"], tmp_path)

    assert returncode != 0
    assert b"helper exited with status 42" in stderr
    assert b"invalid date format" not in stderr


# A zero-exit malformed response is infrastructure failure, not a parser rejection.
def test_malformed_time_parser_response_is_infrastructure_failure(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    # upstream: none - repository-local time parser regression
    helper = tmp_path / "malformed-parser"
    write_fake_time_parser(
        helper,
        "#!/usr/bin/env python3\n"
        "import sys\n"
        "sys.stdin.buffer.read()\n"
        "sys.stdout.buffer.write(b'malformed\\n')\n",
    )
    monkeypatch.setenv("DAFNYUTILS_TOUCH_TIME_PARSER", str(helper))

    _stdout, stderr, returncode = run_bench_touch(["-d", "@0", "file"], tmp_path)

    assert returncode != 0
    assert b"malformed protocol response" in stderr
    assert b"invalid date format" not in stderr


def test_invalid_timestamp_argument_does_not_create_files_matches_coreutils() -> None:
    # upstream: coreutils/tests/touch/no-create-missing.sh
    # upstream: coreutils/tests/touch/dangling-symlink.sh
    # upstream: coreutils/tests/touch/dir-1.sh
    # upstream: coreutils/tests/touch/60-seconds.sh
    # upstream: coreutils/tests/touch/trailing-slash.sh
    with (
        tempfile.TemporaryDirectory() as ref_tmp_dir,
        tempfile.TemporaryDirectory() as bench_tmp_dir,
    ):
        ref_cwd = Path(ref_tmp_dir)
        bench_cwd = Path(bench_tmp_dir)

        args = ["-t", "not-a-timestamp", "created.txt"]
        ref = run_system_touch(args, ref_cwd)
        bench = run_bench_touch(args, bench_cwd)
        assert_same_result(ref, bench)
        assert not (ref_cwd / "created.txt").exists()
        assert not (bench_cwd / "created.txt").exists()


def test_invalid_date_argument_does_not_create_files_matches_coreutils() -> None:
    # upstream: coreutils/tests/touch/no-create-missing.sh
    # upstream: coreutils/tests/touch/dangling-symlink.sh
    # upstream: coreutils/tests/touch/dir-1.sh
    # upstream: coreutils/tests/touch/60-seconds.sh
    # upstream: coreutils/tests/touch/trailing-slash.sh
    with (
        tempfile.TemporaryDirectory() as ref_tmp_dir,
        tempfile.TemporaryDirectory() as bench_tmp_dir,
    ):
        ref_cwd = Path(ref_tmp_dir)
        bench_cwd = Path(bench_tmp_dir)

        args = ["-d", "invalid-date", "created.txt"]
        ref = run_system_touch(args, ref_cwd)
        bench = run_bench_touch(args, bench_cwd)
        assert_same_result(ref, bench)
        assert not (ref_cwd / "created.txt").exists()
        assert not (bench_cwd / "created.txt").exists()


@pytest.mark.parametrize(
    "path,prepare_parent",
    [
        ("missing-dir/file", False),
        ("plain-file/child", True),
    ],
)
def test_create_with_invalid_ancestor_fails(path: str, prepare_parent: bool) -> None:
    # upstream: coreutils/tests/touch/no-create-missing.sh
    # upstream: coreutils/tests/touch/dangling-symlink.sh
    # upstream: coreutils/tests/touch/dir-1.sh
    # upstream: coreutils/tests/touch/60-seconds.sh
    # upstream: coreutils/tests/touch/trailing-slash.sh
    with (
        tempfile.TemporaryDirectory() as ref_tmp_dir,
        tempfile.TemporaryDirectory() as bench_tmp_dir,
    ):
        ref_cwd = Path(ref_tmp_dir)
        bench_cwd = Path(bench_tmp_dir)

        if prepare_parent:
            _ = (ref_cwd / "plain-file").write_text("ancestor\n", encoding="utf-8")
            _ = (bench_cwd / "plain-file").write_text("ancestor\n", encoding="utf-8")

        ref = run_system_touch([path], ref_cwd)
        bench = run_bench_touch([path], bench_cwd)

        assert ref[2] == bench[2] == 1
        assert not (ref_cwd / path).exists()
        assert not (bench_cwd / path).exists()


# Ensure quoteaf-compatible tab quoting preserves exact GNU diagnostic bytes.
def test_tab_path_failure_diagnostic_matches_coreutils() -> None:
    # upstream: none - repository-local GNU parity regression
    with (
        tempfile.TemporaryDirectory() as ref_tmp_dir,
        tempfile.TemporaryDirectory() as bench_tmp_dir,
    ):
        args = ["pm:r/\t2jk"]
        ref = run_system_touch(args, Path(ref_tmp_dir))
        bench = run_bench_touch(args, Path(bench_tmp_dir))

        assert_same_result(ref, bench)
        assert ref[1] == (b"touch: cannot touch 'pm:r/'$'\\t''2jk': No such file or directory\n")


def test_create_missing_file_matches_coreutils() -> None:
    # From fuzzing: minimal reproducer `touch new.txt`.
    # upstream: coreutils/tests/touch/no-create-missing.sh
    # upstream: coreutils/tests/touch/dangling-symlink.sh
    # upstream: coreutils/tests/touch/dir-1.sh
    # upstream: coreutils/tests/touch/60-seconds.sh
    # upstream: coreutils/tests/touch/trailing-slash.sh
    with (
        tempfile.TemporaryDirectory() as ref_tmp_dir,
        tempfile.TemporaryDirectory() as bench_tmp_dir,
    ):
        ref_cwd = Path(ref_tmp_dir)
        bench_cwd = Path(bench_tmp_dir)
        args = ["new.txt"]

        ref_started_ns = time.time_ns()
        ref = run_system_touch(args, ref_cwd)
        ref_finished_ns = time.time_ns()
        bench_started_ns = time.time_ns()
        bench = run_bench_touch(args, bench_cwd)
        bench_finished_ns = time.time_ns()
        assert_same_result(ref, bench)

        ref_file_stat = (ref_cwd / "new.txt").stat()
        bench_file_stat = (bench_cwd / "new.txt").stat()
        assert (
            ref_started_ns - FILESYSTEM_CURRENT_TIME_TOLERANCE_NS
            <= ref_file_stat.st_mtime_ns
            <= ref_finished_ns + FILESYSTEM_CURRENT_TIME_TOLERANCE_NS
        )
        assert (
            bench_started_ns - FILESYSTEM_CURRENT_TIME_TOLERANCE_NS
            <= bench_file_stat.st_mtime_ns
            <= bench_finished_ns + FILESYSTEM_CURRENT_TIME_TOLERANCE_NS
        )
        assert ref_file_stat.st_mtime_ns == ref_cwd.stat().st_mtime_ns
        assert bench_file_stat.st_mtime_ns == bench_cwd.stat().st_mtime_ns

        assert (ref_cwd / "new.txt").read_bytes() == b""
        assert (bench_cwd / "new.txt").read_bytes() == b""


def test_dangling_symlink_without_no_dereference_creates_referent() -> None:
    # upstream: coreutils/tests/touch/no-create-missing.sh
    # upstream: coreutils/tests/touch/dangling-symlink.sh
    # upstream: coreutils/tests/touch/dir-1.sh
    # upstream: coreutils/tests/touch/60-seconds.sh
    # upstream: coreutils/tests/touch/trailing-slash.sh
    with (
        tempfile.TemporaryDirectory() as ref_tmp_dir,
        tempfile.TemporaryDirectory() as bench_tmp_dir,
    ):
        ref_cwd = Path(ref_tmp_dir)
        bench_cwd = Path(bench_tmp_dir)
        (ref_cwd / "dangling").symlink_to("touch-target")
        (bench_cwd / "dangling").symlink_to("touch-target")

        ref = run_system_touch(["dangling"], ref_cwd)
        bench = run_bench_touch(["dangling"], bench_cwd)
        assert_same_result(ref, bench)
        assert (ref_cwd / "touch-target").exists()
        assert (bench_cwd / "touch-target").exists()


def test_directory_operand_matches_coreutils() -> None:
    # upstream: coreutils/tests/touch/no-create-missing.sh
    # upstream: coreutils/tests/touch/dangling-symlink.sh
    # upstream: coreutils/tests/touch/dir-1.sh
    # upstream: coreutils/tests/touch/60-seconds.sh
    # upstream: coreutils/tests/touch/trailing-slash.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        ref = run_system_touch(["."], cwd)
        bench = run_bench_touch(["."], cwd)
        assert_same_result(ref, bench)


def test_touch_existing_file_preserves_contents() -> None:
    # upstream: coreutils/tests/touch/no-create-missing.sh
    # upstream: coreutils/tests/touch/dangling-symlink.sh
    # upstream: coreutils/tests/touch/dir-1.sh
    # upstream: coreutils/tests/touch/60-seconds.sh
    # upstream: coreutils/tests/touch/trailing-slash.sh
    with (
        tempfile.TemporaryDirectory() as ref_tmp_dir,
        tempfile.TemporaryDirectory() as bench_tmp_dir,
    ):
        ref_cwd = Path(ref_tmp_dir)
        bench_cwd = Path(bench_tmp_dir)
        payload = b"payload\n"

        (ref_cwd / "existing.txt").write_bytes(payload)
        (bench_cwd / "existing.txt").write_bytes(payload)

        args = ["existing.txt"]
        ref = run_system_touch(args, ref_cwd)
        bench = run_bench_touch(args, bench_cwd)
        assert_same_result(ref, bench)

        assert (ref_cwd / "existing.txt").read_bytes() == payload
        assert (bench_cwd / "existing.txt").read_bytes() == payload


# GNU utime regression: an explicit -t timestamp sets both file times.
def test_gnulib_utime_timestamp_sets_both_times_match_coreutils(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # upstream: coreutils/gnulib-tests/test-utime
    monkeypatch.setenv("TZ", "UTC0")
    with (
        tempfile.TemporaryDirectory() as ref_tmp_dir,
        tempfile.TemporaryDirectory() as bench_tmp_dir,
    ):
        ref_cwd = Path(ref_tmp_dir)
        bench_cwd = Path(bench_tmp_dir)
        ref_file = write_timestamped_file(ref_cwd, "file")
        bench_file = write_timestamped_file(bench_cwd, "file")

        args = ["-t", "200001010000.00", "file"]
        ref = run_system_touch(args, ref_cwd)
        bench = run_bench_touch(args, bench_cwd)
        assert_same_result(ref, bench)
        assert path_times_ns(ref_file) == (Y2K_NS, Y2K_NS)
        assert path_times_ns(bench_file) == (Y2K_NS, Y2K_NS)


# GNU utime regression: a trailing slash on a file fails without updating times.
def test_gnulib_utime_trailing_slash_failure_preserves_times(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # upstream: coreutils/gnulib-tests/test-utime
    monkeypatch.setenv("TZ", "UTC0")
    with (
        tempfile.TemporaryDirectory() as ref_tmp_dir,
        tempfile.TemporaryDirectory() as bench_tmp_dir,
    ):
        ref_cwd = Path(ref_tmp_dir)
        bench_cwd = Path(bench_tmp_dir)
        ref_file = write_timestamped_file(ref_cwd, "file")
        bench_file = write_timestamped_file(bench_cwd, "file")

        args = ["-t", "200001010000.00", "file/"]
        ref = run_system_touch(args, ref_cwd)
        bench = run_bench_touch(args, bench_cwd)
        assert_same_result(ref, bench)
        assert path_times_ns(ref_file) == (INITIAL_ATIME_NS, INITIAL_MTIME_NS)
        assert path_times_ns(bench_file) == (INITIAL_ATIME_NS, INITIAL_MTIME_NS)


# GNU utime regression: default symlink operands update the referent.
def test_gnulib_utime_symlink_operand_dereferences_target(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # upstream: coreutils/gnulib-tests/test-utime
    # upstream: coreutils/gnulib-tests/test-utimens
    monkeypatch.setenv("TZ", "UTC0")
    with (
        tempfile.TemporaryDirectory() as ref_tmp_dir,
        tempfile.TemporaryDirectory() as bench_tmp_dir,
    ):
        ref_cwd = Path(ref_tmp_dir)
        bench_cwd = Path(bench_tmp_dir)

        for cwd in [ref_cwd, bench_cwd]:
            _ = write_timestamped_file(cwd, "file")
            link = cwd / "link"
            link.symlink_to("file")
            os.utime(link, ns=(LINK_ATIME_NS, LINK_MTIME_NS), follow_symlinks=False)

        args = ["-t", "200001010000.00", "link"]
        ref = run_system_touch(args, ref_cwd)
        bench = run_bench_touch(args, bench_cwd)
        assert_same_result(ref, bench)
        assert path_times_ns(ref_cwd / "file") == (Y2K_NS, Y2K_NS)
        assert path_times_ns(bench_cwd / "file") == (Y2K_NS, Y2K_NS)
        assert symlink_times_ns(ref_cwd / "link")[1] == LINK_MTIME_NS
        assert symlink_times_ns(bench_cwd / "link")[1] == LINK_MTIME_NS


# GNU utimens regression: -r copies nanosecond access and modification times.
def test_gnulib_utimens_reference_copies_nanosecond_times() -> None:
    # upstream: coreutils/gnulib-tests/test-utimens
    with (
        tempfile.TemporaryDirectory() as ref_tmp_dir,
        tempfile.TemporaryDirectory() as bench_tmp_dir,
    ):
        ref_cwd = Path(ref_tmp_dir)
        bench_cwd = Path(bench_tmp_dir)

        for cwd in [ref_cwd, bench_cwd]:
            _ = write_timestamped_file(cwd, "file")
            _ = write_timestamped_file(
                cwd,
                "reference",
                REFERENCE_ATIME_NS,
                REFERENCE_MTIME_NS,
            )

        args = ["-r", "reference", "file"]
        ref = run_system_touch(args, ref_cwd)
        bench = run_bench_touch(args, bench_cwd)
        assert_same_result(ref, bench)
        assert path_times_ns(ref_cwd / "file") == (REFERENCE_ATIME_NS, REFERENCE_MTIME_NS)
        assert path_times_ns(bench_cwd / "file") == (REFERENCE_ATIME_NS, REFERENCE_MTIME_NS)


# GNU no-dereference regression: -h -r reads reference times from the symlink itself.
def test_no_dereference_reference_symlink_uses_link_timestamp() -> None:
    # upstream: coreutils/tests/touch/no-dereference.sh
    with (
        tempfile.TemporaryDirectory() as ref_tmp_dir,
        tempfile.TemporaryDirectory() as bench_tmp_dir,
    ):
        ref_cwd = Path(ref_tmp_dir)
        bench_cwd = Path(bench_tmp_dir)

        for cwd in [ref_cwd, bench_cwd]:
            _ = write_timestamped_file(cwd, "file")
            _ = write_timestamped_file(cwd, "reference", REFERENCE_ATIME_NS, REFERENCE_MTIME_NS)
            link = cwd / "ref-link"
            link.symlink_to("reference")
            os.utime(link, ns=(LINK_ATIME_NS, LINK_MTIME_NS), follow_symlinks=False)

        args = ["-h", "-r", "ref-link", "file"]
        ref = run_system_touch(args, ref_cwd)
        bench = run_bench_touch(args, bench_cwd)
        assert_same_result(ref, bench)
        assert path_times_ns(ref_cwd / "file") == (LINK_ATIME_NS, LINK_MTIME_NS)
        assert path_times_ns(bench_cwd / "file") == (LINK_ATIME_NS, LINK_MTIME_NS)


# GNU utimens UTIME_OMIT regression: -a preserves the old modification time.
def test_gnulib_utimens_access_only_preserves_mtime(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # upstream: coreutils/gnulib-tests/test-utimens
    monkeypatch.setenv("TZ", "UTC0")
    with (
        tempfile.TemporaryDirectory() as ref_tmp_dir,
        tempfile.TemporaryDirectory() as bench_tmp_dir,
    ):
        ref_cwd = Path(ref_tmp_dir)
        bench_cwd = Path(bench_tmp_dir)
        ref_file = write_timestamped_file(ref_cwd, "file")
        bench_file = write_timestamped_file(bench_cwd, "file")

        args = ["-a", "-d", "2002-03-04 05:06:07 UTC", "file"]
        ref = run_system_touch(args, ref_cwd)
        bench = run_bench_touch(args, bench_cwd)
        assert_same_result(ref, bench)
        assert path_times_ns(ref_file) == (MAR_2002_NS, INITIAL_MTIME_NS)
        assert path_times_ns(bench_file) == (MAR_2002_NS, INITIAL_MTIME_NS)


# GNU utimens UTIME_OMIT regression: -m preserves the old access time.
def test_gnulib_utimens_modify_only_preserves_atime(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # upstream: coreutils/gnulib-tests/test-utimens
    monkeypatch.setenv("TZ", "UTC0")
    with (
        tempfile.TemporaryDirectory() as ref_tmp_dir,
        tempfile.TemporaryDirectory() as bench_tmp_dir,
    ):
        ref_cwd = Path(ref_tmp_dir)
        bench_cwd = Path(bench_tmp_dir)
        ref_file = write_timestamped_file(ref_cwd, "file")
        bench_file = write_timestamped_file(bench_cwd, "file")

        args = ["-m", "-d", "2003-04-05 06:07:08 UTC", "file"]
        ref = run_system_touch(args, ref_cwd)
        bench = run_bench_touch(args, bench_cwd)
        assert_same_result(ref, bench)
        assert path_times_ns(ref_file) == (INITIAL_ATIME_NS, APR_2003_NS)
        assert path_times_ns(bench_file) == (INITIAL_ATIME_NS, APR_2003_NS)


# GNU lutimens regression: link/ dereferences a symlink to a directory even with -h.
def test_gnulib_utimens_trailing_slash_symlink_to_directory_dereferences(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # upstream: coreutils/gnulib-tests/test-utimens
    monkeypatch.setenv("TZ", "UTC0")
    with (
        tempfile.TemporaryDirectory() as ref_tmp_dir,
        tempfile.TemporaryDirectory() as bench_tmp_dir,
    ):
        ref_cwd = Path(ref_tmp_dir)
        bench_cwd = Path(bench_tmp_dir)

        for cwd in [ref_cwd, bench_cwd]:
            directory = cwd / "dir"
            directory.mkdir()
            os.utime(directory, ns=(INITIAL_ATIME_NS, INITIAL_MTIME_NS))
            link = cwd / "link"
            link.symlink_to("dir")
            os.utime(link, ns=(LINK_ATIME_NS, LINK_MTIME_NS), follow_symlinks=False)

        args = ["-h", "-t", "200102030405.06", "link/"]
        ref = run_system_touch(args, ref_cwd)
        bench = run_bench_touch(args, bench_cwd)
        assert_same_result(ref, bench)
        assert path_times_ns(ref_cwd / "dir") == (FEB_2001_NS, FEB_2001_NS)
        assert path_times_ns(bench_cwd / "dir") == (FEB_2001_NS, FEB_2001_NS)
        assert symlink_times_ns(ref_cwd / "link")[1] == LINK_MTIME_NS
        assert symlink_times_ns(bench_cwd / "link")[1] == LINK_MTIME_NS


def test_t_option_accepts_sixty_seconds(monkeypatch: pytest.MonkeyPatch) -> None:
    # upstream: coreutils/tests/touch/no-create-missing.sh
    # upstream: coreutils/tests/touch/dangling-symlink.sh
    # upstream: coreutils/tests/touch/dir-1.sh
    # upstream: coreutils/tests/touch/60-seconds.sh
    # upstream: coreutils/tests/touch/trailing-slash.sh
    monkeypatch.setenv("TZ", "UTC0")
    with (
        tempfile.TemporaryDirectory() as ref_tmp_dir,
        tempfile.TemporaryDirectory() as bench_tmp_dir,
    ):
        ref_cwd = Path(ref_tmp_dir)
        bench_cwd = Path(bench_tmp_dir)
        args = ["-t", "197001010000.60", "file"]
        ref = run_system_touch(args, ref_cwd)
        bench = run_bench_touch(args, bench_cwd)
        assert_same_result(ref, bench)
        assert int((ref_cwd / "file").stat().st_mtime) == 60
        assert int((bench_cwd / "file").stat().st_mtime) == 60


def test_help_and_version_exit_successfully() -> None:
    # upstream: coreutils/tests/help/help-version.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        # Exact help/version text is unnecessary here.
        # We only care that both commands surface the requested output behavior.

        help_ref = run_system_touch(["--help"], cwd)
        help_bench = run_bench_touch(["--help"], cwd)
        assert_requested_message_behavior(help_ref, help_bench)

        version_ref = run_system_touch(["--version"], cwd)
        version_bench = run_bench_touch(["--version"], cwd)
        assert_requested_message_behavior(version_ref, version_bench)


def test_no_dereference_dangling_symlink_matches_coreutils() -> None:
    # upstream: coreutils/tests/touch/no-dereference.sh
    with (
        tempfile.TemporaryDirectory() as ref_tmp_dir,
        tempfile.TemporaryDirectory() as bench_tmp_dir,
    ):
        ref_cwd = Path(ref_tmp_dir)
        bench_cwd = Path(bench_tmp_dir)

        (ref_cwd / "dangling").symlink_to("missing-target")
        (bench_cwd / "dangling").symlink_to("missing-target")

        args = ["-h", "dangling"]
        ref = run_system_touch(args, ref_cwd)
        bench = run_bench_touch(args, bench_cwd)
        assert_same_result(ref, bench)

        assert (ref_cwd / "dangling").is_symlink()
        assert (bench_cwd / "dangling").is_symlink()
        assert not (ref_cwd / "missing-target").exists()
        assert not (bench_cwd / "missing-target").exists()


def test_no_dereference_missing_path_matches_coreutils() -> None:
    # upstream: coreutils/tests/touch/no-dereference.sh
    with (
        tempfile.TemporaryDirectory() as ref_tmp_dir,
        tempfile.TemporaryDirectory() as bench_tmp_dir,
    ):
        ref_cwd = Path(ref_tmp_dir)
        bench_cwd = Path(bench_tmp_dir)

        args = ["-h", "missing"]
        ref = run_system_touch(args, ref_cwd)
        bench = run_bench_touch(args, bench_cwd)
        assert_same_result(ref, bench)

        assert not (ref_cwd / "missing").exists()
        assert not (bench_cwd / "missing").exists()


@pytest.mark.parametrize("args", [["file/"], ["dangling/"], ["loop/"], ["-c", "file/"]])
def test_trailing_slash_matrix_matches_coreutils(args: list[str]) -> None:
    # upstream: coreutils/tests/touch/no-create-missing.sh
    # upstream: coreutils/tests/touch/dangling-symlink.sh
    # upstream: coreutils/tests/touch/dir-1.sh
    # upstream: coreutils/tests/touch/60-seconds.sh
    # upstream: coreutils/tests/touch/trailing-slash.sh
    with (
        tempfile.TemporaryDirectory() as ref_tmp_dir,
        tempfile.TemporaryDirectory() as bench_tmp_dir,
    ):
        ref_cwd = Path(ref_tmp_dir)
        bench_cwd = Path(bench_tmp_dir)
        for cwd in [ref_cwd, bench_cwd]:
            _ = (cwd / "file").write_text("payload\n", encoding="utf-8")
            (cwd / "dangling").symlink_to("nowhere")
            (cwd / "loop").symlink_to("loop")

        ref = run_system_touch(args, ref_cwd)
        bench = run_bench_touch(args, bench_cwd)
        assert_same_result(ref, bench)


def test_dash_operand_updates_stdout_not_file() -> None:
    # upstream: coreutils/tests/touch/no-create-missing.sh
    # upstream: coreutils/tests/touch/dangling-symlink.sh
    # upstream: coreutils/tests/touch/dir-1.sh
    # upstream: coreutils/tests/touch/60-seconds.sh
    # upstream: coreutils/tests/touch/trailing-slash.sh
    with (
        tempfile.TemporaryDirectory() as ref_tmp_dir,
        tempfile.TemporaryDirectory() as bench_tmp_dir,
    ):
        ref_cwd = Path(ref_tmp_dir)
        bench_cwd = Path(bench_tmp_dir)

        args = ["-"]
        ref = run_system_touch(args, ref_cwd)
        bench = run_bench_touch(args, bench_cwd)
        assert_same_result(ref, bench)

        assert not (ref_cwd / "-").exists()
        assert not (bench_cwd / "-").exists()


# Ensure `touch -a -` updates only the access time of redirected stdout.
def test_stdout_target_access_only_preserves_mtime() -> None:
    # upstream: none - repository-local GNU parity regression
    with (
        tempfile.TemporaryDirectory() as ref_tmp_dir,
        tempfile.TemporaryDirectory() as bench_tmp_dir,
    ):
        ref_cwd = Path(ref_tmp_dir)
        bench_cwd = Path(bench_tmp_dir)
        ref_stdout = write_timestamped_file(ref_cwd, "stdout")
        bench_stdout = write_timestamped_file(bench_cwd, "stdout")

        args = ["-a", "-"]
        ref, ref_times = run_touch_with_stdout_target(
            [str(COREUTILS_TOUCH)], args, ref_cwd, ref_stdout
        )
        bench, bench_times = run_touch_with_stdout_target(
            ["dotnet", str(BENCH_TOUCH_DLL)], args, bench_cwd, bench_stdout
        )

        assert_same_result(ref, bench)
        assert ref_times[0] != INITIAL_ATIME_NS
        assert bench_times[0] != INITIAL_ATIME_NS
        assert ref_times[1] == bench_times[1] == INITIAL_MTIME_NS


# Ensure `touch -m -` updates only the modification time of redirected stdout.
def test_stdout_target_modify_only_preserves_atime() -> None:
    # upstream: none - repository-local GNU parity regression
    with (
        tempfile.TemporaryDirectory() as ref_tmp_dir,
        tempfile.TemporaryDirectory() as bench_tmp_dir,
    ):
        ref_cwd = Path(ref_tmp_dir)
        bench_cwd = Path(bench_tmp_dir)
        ref_stdout = write_timestamped_file(ref_cwd, "stdout")
        bench_stdout = write_timestamped_file(bench_cwd, "stdout")

        args = ["-m", "-"]
        ref, ref_times = run_touch_with_stdout_target(
            [str(COREUTILS_TOUCH)], args, ref_cwd, ref_stdout
        )
        bench, bench_times = run_touch_with_stdout_target(
            ["dotnet", str(BENCH_TOUCH_DLL)], args, bench_cwd, bench_stdout
        )

        assert_same_result(ref, bench)
        assert ref_times[0] == bench_times[0] == INITIAL_ATIME_NS
        assert ref_times[1] != INITIAL_MTIME_NS
        assert bench_times[1] != INITIAL_MTIME_NS


# Ensure an explicit timestamp sets both times of redirected stdout exactly.
def test_stdout_target_explicit_timestamp_sets_both_times() -> None:
    # upstream: none - repository-local GNU parity regression
    with (
        tempfile.TemporaryDirectory() as ref_tmp_dir,
        tempfile.TemporaryDirectory() as bench_tmp_dir,
    ):
        ref_cwd = Path(ref_tmp_dir)
        bench_cwd = Path(bench_tmp_dir)
        ref_stdout = write_timestamped_file(ref_cwd, "stdout")
        bench_stdout = write_timestamped_file(bench_cwd, "stdout")

        args = ["-t", "200001010000.00", "-"]
        ref, ref_times = run_touch_with_stdout_target(
            [str(COREUTILS_TOUCH)], args, ref_cwd, ref_stdout
        )
        bench, bench_times = run_touch_with_stdout_target(
            ["dotnet", str(BENCH_TOUCH_DLL)], args, bench_cwd, bench_stdout
        )

        assert_same_result(ref, bench)
        assert ref_times == bench_times == (Y2K_NS, Y2K_NS)


def test_multiple_failures_report_per_file_errors() -> None:
    # upstream: coreutils/tests/touch/no-create-missing.sh
    # upstream: coreutils/tests/touch/dangling-symlink.sh
    # upstream: coreutils/tests/touch/dir-1.sh
    # upstream: coreutils/tests/touch/60-seconds.sh
    # upstream: coreutils/tests/touch/trailing-slash.sh
    with (
        tempfile.TemporaryDirectory() as ref_tmp_dir,
        tempfile.TemporaryDirectory() as bench_tmp_dir,
    ):
        ref_cwd = Path(ref_tmp_dir)
        bench_cwd = Path(bench_tmp_dir)

        _ = (ref_cwd / "plain-file").write_text("ancestor\n", encoding="utf-8")
        _ = (bench_cwd / "plain-file").write_text("ancestor\n", encoding="utf-8")

        args = ["plain-file/child", "missing-dir/file"]
        ref = run_system_touch(args, ref_cwd)
        bench = run_bench_touch(args, bench_cwd)
        assert_same_result(ref, bench)

        assert not (ref_cwd / "missing-dir").exists()
        assert not (bench_cwd / "missing-dir").exists()


# GNU selections accumulate across short flags and every valid --time alias.
@pytest.mark.parametrize(
    "selection",
    [
        ["-a", "--time=modify"],
        ["--time=access", "-m"],
        ["--time=atime", "--time=mtime"],
        ["--time=modify", "--time=use"],
        ["--time=m", "--time=a"],
        ["-am", "--time=access"],
    ],
)
def test_time_selection_union_sets_both_fields(tmp_path: Path, selection: list[str]) -> None:
    # upstream: none - repository-local GNU parity regression
    ref_dir, bench_dir = tmp_path / "ref", tmp_path / "bench"
    ref_dir.mkdir()
    bench_dir.mkdir()
    ref_file = write_timestamped_file(ref_dir, "file")
    bench_file = write_timestamped_file(bench_dir, "file")
    args = [*selection, "-t", "200001010000.00", "file"]
    assert_same_result(run_system_touch(args, ref_dir), run_bench_touch(args, bench_dir))
    assert path_times_ns(ref_file) == path_times_ns(bench_file) == (Y2K_NS, Y2K_NS)


# Relative dates use each selected reference field independently at nanosecond precision.
@pytest.mark.parametrize("selection", [[], ["-a"], ["-m"]])
def test_relative_date_preserves_distinct_reference_fields(
    tmp_path: Path, selection: list[str]
) -> None:
    # upstream: none - repository-local GNU parity regression
    ref_dir, bench_dir = tmp_path / "ref", tmp_path / "bench"
    ref_dir.mkdir()
    bench_dir.mkdir()
    reference_atime = REFERENCE_ATIME_NS
    reference_mtime = REFERENCE_MTIME_NS
    for cwd in [ref_dir, bench_dir]:
        write_timestamped_file(cwd, "reference", reference_atime, reference_mtime)
        write_timestamped_file(cwd, "file")
    args = [*selection, "-r", "reference", "-d", "-1 day", "file"]
    assert_same_result(run_system_touch(args, ref_dir), run_bench_touch(args, bench_dir))
    expected = (
        INITIAL_ATIME_NS if selection == ["-m"] else reference_atime - 86_400_000_000_000,
        INITIAL_MTIME_NS if selection == ["-a"] else reference_mtime - 86_400_000_000_000,
    )
    assert path_times_ns(ref_dir / "file") == path_times_ns(bench_dir / "file") == expected


# Fixed stdout updates preserve exactly the timestamp excluded by the selection.
@pytest.mark.parametrize("selection", ["-a", "-m"])
@pytest.mark.parametrize("source", [["-t", "200001010000.00"], ["-r", "reference"]])
def test_fixed_stdout_selection_preserves_other_field(
    tmp_path: Path, selection: str, source: list[str]
) -> None:
    # upstream: none - repository-local GNU parity regression
    ref_dir, bench_dir = tmp_path / "ref", tmp_path / "bench"
    ref_dir.mkdir()
    bench_dir.mkdir()
    for cwd in [ref_dir, bench_dir]:
        write_timestamped_file(cwd, "reference", REFERENCE_ATIME_NS, REFERENCE_MTIME_NS)
        write_timestamped_file(cwd, "stdout")
    args = [selection, *source, "-"]
    ref, ref_times = run_touch_with_stdout_target(
        [str(COREUTILS_TOUCH)], args, ref_dir, ref_dir / "stdout"
    )
    bench, bench_times = run_touch_with_stdout_target(
        ["dotnet", str(BENCH_TOUCH_DLL)], args, bench_dir, bench_dir / "stdout"
    )
    assert_same_result(ref, bench)
    source_times = (
        (Y2K_NS, Y2K_NS) if source[0] == "-t" else (REFERENCE_ATIME_NS, REFERENCE_MTIME_NS)
    )
    expected = (
        (source_times[0], INITIAL_MTIME_NS)
        if selection == "-a"
        else (INITIAL_ATIME_NS, source_times[1])
    )
    assert ref_times == bench_times == expected


# Conflicting timestamp sources fail before changing existing or missing operands.
@pytest.mark.parametrize(
    "sources",
    [
        ["-t", "200001010000.00", "-d", "-5 seconds"],
        ["-d", "", "-t", "200001010000.00"],
        ["-r", "missing-reference", "-t", "200001010000.00"],
        ["-t", "200001010000.00", "-r", ""],
    ],
)
def test_source_conflict_precedes_filesystem_effects(tmp_path: Path, sources: list[str]) -> None:
    # upstream: none - repository-local GNU parity regression
    ref_dir, bench_dir = tmp_path / "ref", tmp_path / "bench"
    ref_dir.mkdir()
    bench_dir.mkdir()
    for cwd in [ref_dir, bench_dir]:
        write_timestamped_file(cwd, "file")
    args = [*sources, "file", "new"]
    ref = run_system_touch(args, ref_dir)
    bench = run_bench_touch(args, bench_dir)
    assert_same_result(ref, bench)
    assert bench == (
        b"",
        b"touch: cannot specify times from more than one source\n"
        b"Try 'touch --help' for more information.\n",
        1,
    )
    for cwd in [ref_dir, bench_dir]:
        assert path_times_ns(cwd / "file") == (INITIAL_ATIME_NS, INITIAL_MTIME_NS)
        assert not (cwd / "new").exists()


# Empty reference and timestamp arguments remain supplied values and fail without creation.
@pytest.mark.parametrize("option", ["-r", "--reference=", "-t"])
def test_empty_source_argument_does_not_become_current_time(tmp_path: Path, option: str) -> None:
    # upstream: none - repository-local GNU parity regression
    args = [option, "new"] if option.endswith("=") else [option, "", "new"]
    ref = run_system_touch(args, tmp_path)
    bench = run_bench_touch(args, tmp_path)
    assert_same_result(ref, bench)
    assert ref == bench
    assert bench[2] == 1
    assert not (tmp_path / "new").exists()


def test_deferred_touch_regressions_placeholder() -> None:
    # Not ported yet: these require FIFO timeout handling, exact diagnostics,
    # symlink timestamp support checks, POSIX timestamp env matrices,
    # root/non-root ownership setup, or permission-sensitive filesystem behavior.
    # upstream: coreutils/tests/touch/empty-file.sh
    # upstream: coreutils/tests/touch/fail-diag.sh
    # upstream: coreutils/tests/touch/fifo.sh
    # upstream: coreutils/tests/touch/no-dereference.sh
    # upstream: coreutils/tests/touch/no-rights.sh
    # upstream: coreutils/tests/touch/not-owner.sh
    # upstream: coreutils/tests/touch/now-owned-by-other.sh
    # upstream: coreutils/tests/touch/obsolescent.sh
    # upstream: coreutils/tests/touch/read-only.sh
    # upstream: coreutils/tests/touch/relative.sh
    pytest.skip("requires privilege-aware or timing-aware filesystem fixtures")


@pytest.mark.dafny_verify
@pytest.mark.parametrize("target", TOUCH_VERIFY_TARGETS, ids=lambda path: path.name)
def test_touch_verify_targets(target: Path) -> None:
    # upstream: none - Verifies the Dafny proof surface rather than an upstream runtime script.
    verify_touch_target(target)
