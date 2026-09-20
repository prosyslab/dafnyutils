"""Check tr stdin byte-transform parity against GNU coreutils and verify proof surface."""

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

BENCH_TR_DLL = bench_dll_path(ROOT, ROOT / "_build" / "bench" / "tr_bench.dll")
COREUTILS_TR = coreutils_binary_path(ROOT, ROOT / "_build" / "coreutils" / "src" / "tr")


@pytest.fixture(scope="session", autouse=True)
def build_tr_once(request: pytest.FixtureRequest) -> None:
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
            not BENCH_TR_DLL.exists()
            or latest_bench_utility_source_mtime(ROOT, "tr") > BENCH_TR_DLL.stat().st_mtime
        ):
            build_bench_utility(ROOT, "tr")
        if not COREUTILS_TR.exists():
            build_coreutils_utility(ROOT, "tr")
        fcntl.flock(lock_file, fcntl.LOCK_UN)


def run_bench_tr(
    args: list[str],
    cwd: Path,
    *,
    input_data: bytes = b"",
) -> tuple[bytes, bytes, int]:
    return run_bench_utility(BENCH_TR_DLL, args, cwd, input_data=input_data)


def run_system_tr(
    args: list[str],
    cwd: Path,
    *,
    input_data: bytes = b"",
) -> tuple[bytes, bytes, int]:
    return run_coreutils_utility(COREUTILS_TR, "tr", args, cwd, input_data=input_data)


def assert_tr_parity(args: list[str], cwd: Path, *, input_data: bytes = b"") -> None:
    ref = run_system_tr(args, cwd, input_data=input_data)
    bench = run_bench_tr(args, cwd, input_data=input_data)
    assert_result_matches_reference(ref, bench)


# Literal set translation maps each input byte through the corresponding set2 byte.
def test_simple_translation_from_stdin_matches_coreutils() -> None:
    # upstream: coreutils/tests/tr/tr.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_tr_parity(["a-a", "z"], cwd, input_data=b"abc")


# Literal punctuation set members translate when they are not class or repeat syntax.
def test_literal_punctuation_set_members_match_coreutils() -> None:
    # upstream: coreutils/tests/tr/tr.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_tr_parity(["[]:=*", "ABCDEF"], cwd, input_data=b"[]:=*x")


# Incomplete bracket constructs remain literal set bytes.
def test_incomplete_bracket_constructs_are_literals_matches_coreutils() -> None:
    # upstream: coreutils/tests/tr/tr.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_tr_parity(["[:[=[a*", "ABCDEF"], cwd, input_data=b"[:[=[a*x")


# Delete mode removes every input byte selected by set1.
def test_delete_set_from_stdin_matches_coreutils() -> None:
    # upstream: coreutils/tests/tr/tr.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_tr_parity(["-d", "a-z"], cwd, input_data=b"abc $code")


# Squeeze mode collapses adjacent output bytes selected by the squeeze set.
def test_squeeze_repeats_from_stdin_matches_coreutils() -> None:
    # upstream: coreutils/tests/tr/tr.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_tr_parity(["-s", "a-z"], cwd, input_data=b"aabbcc")


# Translation reuses the final SET2 byte when SET1 is longer than SET2.
def test_translation_reuses_final_set2_byte_matches_coreutils() -> None:
    # upstream: coreutils/tests/tr/tr.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_tr_parity(["abc", "xy"], cwd, input_data=b"abc cab")


# Duplicate SET1 bytes use the final matching translation pair.
def test_duplicate_set1_uses_last_mapping_matches_coreutils() -> None:
    # upstream: coreutils/tests/tr/tr.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_tr_parity(["aaa", "xyz"], cwd, input_data=b"a")


# Delete with squeeze removes SET1 and squeezes repeats selected by SET2.
def test_delete_then_squeeze_with_set2_matches_coreutils() -> None:
    # upstream: coreutils/tests/tr/tr.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_tr_parity(["-d", "-s", "a", "b"], cwd, input_data=b"aabbbcc")


# Long delete option is accepted before operands.
def test_long_delete_option_matches_coreutils() -> None:
    # upstream: coreutils/tests/tr/tr.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_tr_parity(["--delete", "a-z"], cwd, input_data=b"abc 123")


# Options after the first operand are treated as operands by tr.
def test_option_after_operand_is_extra_operand_matches_coreutils() -> None:
    # upstream: coreutils/tests/tr/tr.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_tr_parity(["a-z", "A-Z", "-s"], cwd, input_data=b"abc")


# Delete-only mode rejects a second set operand as extra.
def test_delete_only_extra_operand_matches_coreutils() -> None:
    # upstream: coreutils/tests/tr/tr.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_tr_parity(["-d", "a", "b"], cwd, input_data=b"aba")


# Hyphen is a literal set byte when it is not a range separator.
def test_literal_hyphen_set_member_matches_coreutils() -> None:
    # upstream: coreutils/tests/tr/tr.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_tr_parity(["-d", "axM-"], cwd, input_data=b"Max-a\n")


# Help exits successfully with the shared requested-message contract.
def test_help_exits_successfully_matches_coreutils() -> None:
    # upstream: coreutils/tests/help/help-version.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_requested_message_behavior(
            run_system_tr(["--help"], cwd, input_data=b"ignored"),
            run_bench_tr(["--help"], cwd, input_data=b"ignored"),
        )


# Version exits successfully with the shared requested-message contract.
def test_version_exits_successfully_matches_coreutils() -> None:
    # upstream: coreutils/tests/help/help-version.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_requested_message_behavior(
            run_system_tr(["--version"], cwd, input_data=b"ignored"),
            run_bench_tr(["--version"], cwd, input_data=b"ignored"),
        )


# Deferred upstream cases name unsupported syntax excluded from this benchmark slice.
def test_deferred_tr_regressions_inventory() -> None:
    # equivalence-class, and multibyte cases.
    # Not ported yet: bracket classes, escapes, repeat constructs, complements,
    # equivalence classes, and non-ASCII byte syntax are outside this benchmark slice.
    # Not ported yet: case conversion classes require locale-sensitive class semantics.
    # upstream: coreutils/tests/tr/tr.pl
    # upstream: coreutils/tests/tr/tr-case-class.sh
    pytest.skip("requires deferred tr set syntax and locale class support")


# The tr CLI schema module verifies independently.
@pytest.mark.dafny_verify
def test_tr_schema_verifies() -> None:
    # upstream: none - Verifies the Dafny proof surface rather than an upstream runtime script.
    run_dafny_verify(ROOT / "bench" / "utils" / "tr" / "TrSchema.dfy")


# The tr executable core module verifies independently.
@pytest.mark.dafny_verify
def test_tr_core_verifies() -> None:
    # upstream: none - Verifies the Dafny proof surface rather than an upstream runtime script.
    run_dafny_verify(ROOT / "bench" / "utils" / "tr" / "TrCore.dfy")


# The tr world-transition spec module verifies independently.
@pytest.mark.dafny_verify
def test_tr_spec_verifies() -> None:
    # upstream: none - Verifies the Dafny proof surface rather than an upstream runtime script.
    run_dafny_verify(ROOT / "bench" / "utils" / "tr" / "TrSpec.dfy")


# The tr proof bridge module verifies independently.
@pytest.mark.dafny_verify
def test_tr_proof_verifies() -> None:
    # upstream: none - Verifies the Dafny proof surface rather than an upstream runtime script.
    run_dafny_verify(ROOT / "bench" / "utils" / "tr" / "TrProof.dfy")


# The tr benchmark item module verifies independently.
@pytest.mark.dafny_verify
def test_tr_benchmark_item_verifies() -> None:
    # upstream: none - Verifies the Dafny proof surface rather than an upstream runtime script.
    run_dafny_verify(ROOT / "bench" / "utils" / "tr" / "Tr.dfy")
