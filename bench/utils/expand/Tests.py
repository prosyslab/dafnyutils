"""Check expand tab expansion parity against GNU coreutils and verify proof surface."""

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

BENCH_EXPAND_DLL = bench_dll_path(ROOT, ROOT / "_build" / "bench" / "expand_bench.dll")
COREUTILS_EXPAND = coreutils_binary_path(ROOT, ROOT / "_build" / "coreutils" / "src" / "expand")


@pytest.fixture(scope="session", autouse=True)
def build_expand_once_if_needed(request: pytest.FixtureRequest) -> None:
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
            not BENCH_EXPAND_DLL.exists()
            or latest_bench_utility_source_mtime(ROOT, "expand") > BENCH_EXPAND_DLL.stat().st_mtime
        ):
            build_bench_utility(ROOT, "expand")
        if not COREUTILS_EXPAND.exists():
            build_coreutils_utility(ROOT, "expand")
        fcntl.flock(lock_file, fcntl.LOCK_UN)


def run_bench_expand(
    args: list[str],
    cwd: Path,
    *,
    input_data: bytes = b"",
) -> tuple[bytes, bytes, int]:
    return run_bench_utility(BENCH_EXPAND_DLL, args, cwd, input_data=input_data)


def run_system_expand(
    args: list[str],
    cwd: Path,
    *,
    input_data: bytes = b"",
) -> tuple[bytes, bytes, int]:
    return run_coreutils_utility(COREUTILS_EXPAND, "expand", args, cwd, input_data=input_data)


def assert_expand_parity(args: list[str], cwd: Path, *, input_data: bytes = b"") -> None:
    ref = run_system_expand(args, cwd, input_data=input_data)
    bench = run_bench_expand(args, cwd, input_data=input_data)
    assert_result_matches_reference(
        ref,
        bench,
        ignore_stderr_when_exit_nonzero=False,
    )


# Default tab stops expand stdin tabs to the next column multiple of eight.
def test_default_tab_stop_expands_stdin_matches_coreutils() -> None:
    # upstream: coreutils/tests/expand/expand.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_expand_parity([], cwd, input_data=b"a\tb\n")


# A single explicit tab stop width is reused for each subsequent tab.
def test_single_tab_stop_option_matches_coreutils() -> None:
    # upstream: coreutils/tests/expand/expand.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_expand_parity(["--tabs=3"], cwd, input_data=b"a\tb")


# GNU's numeric short option selects a repeating tab width.
def test_numeric_short_tab_width_matches_coreutils() -> None:
    # upstream: coreutils/tests/expand/expand.pl
    # Case: u1
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_expand_parity(["-4"], cwd, input_data=b"a\tb\n")


# A multi-digit numeric short option remains one tab-width argument.
def test_multi_digit_numeric_short_tab_width_matches_coreutils() -> None:
    # upstream: coreutils/tests/expand/expand.pl
    # Case: u3
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_expand_parity(["-7022"], cwd, input_data=b"a\tb\n")


# Attached numeric short syntax accepts an increasing tab-stop list.
def test_numeric_short_tab_stop_list_matches_coreutils() -> None:
    # upstream: coreutils/tests/expand/expand.pl
    # Case: u7
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_expand_parity(["-4,8"], cwd, input_data=b"a\tb\tc\n")


# A numeric tab width may follow the bundled initial-only option.
def test_initial_with_numeric_short_tab_width_matches_coreutils() -> None:
    # upstream: none - follows coreutils/src/expand.c shortopts optional numeric arguments
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_expand_parity(["-i4"], cwd, input_data=b" \ta\tb\n")


# Unambiguous GNU long-option abbreviations retain their declared semantics.
def test_abbreviated_long_options_match_coreutils() -> None:
    # upstream: coreutils/tests/misc/invalid-opt.pl
    # Case: abbreviation handling
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_expand_parity(["--t=4", "--ini"], cwd, input_data=b" \ta\tb\n")


# Zero in numeric short form reaches the tab-size validation diagnostic.
def test_zero_numeric_short_tab_width_matches_coreutils() -> None:
    # upstream: none - follows coreutils/src/expand.c numeric short-option switch
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_expand_parity(["-0"], cwd, input_data=b"a\tb\n")


# Double dash keeps a numeric-looking token in the file operand domain.
def test_numeric_short_token_after_double_dash_is_operand_matches_coreutils() -> None:
    # upstream: coreutils/tests/misc/invalid-opt.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_expand_parity(["--", "-4"], cwd, input_data=b"a\tb\n")


# Multiple file operands are read in order and each file's tabs are expanded.
def test_multiple_files_concatenate_expanded_output_matches_coreutils() -> None:
    # upstream: coreutils/tests/expand/expand.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        (cwd / "in1").write_bytes(b"a\tb\n")
        (cwd / "in2").write_bytes(b"c\td\n")

        assert_expand_parity(["--tabs=4", "in1", "in2"], cwd)


# A file boundary without a newline keeps the current output column.
def test_multiple_files_carry_column_across_file_boundary_matches_coreutils() -> None:
    # upstream: coreutils/tests/expand/expand.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        (cwd / "in1").write_bytes(b"a")
        (cwd / "in2").write_bytes(b"\tb\n")

        assert_expand_parity(["--tabs=4", "in1", "in2"], cwd)


# A comma-separated tab stop list expands each tab to the next listed stop.
def test_increasing_tab_stop_list_matches_coreutils() -> None:
    # upstream: coreutils/tests/expand/expand.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_expand_parity(["--tabs=3,6,9"], cwd, input_data=b"a\tb\tc\td\te")


# Horizontal tabs are blank separators in a GNU tab-stop list.
def test_tab_separated_tab_stop_list_matches_coreutils() -> None:
    # upstream: none - follows coreutils/src/expand-common.c parse_tab_stops
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_expand_parity(["--tabs=3\t6\t9"], cwd, input_data=b"a\tb\tc\td")


# Tabs beyond the final listed stop are preserved as one-column progress.
def test_tab_list_exhaustion_after_last_stop_matches_coreutils() -> None:
    # upstream: coreutils/tests/expand/expand.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_expand_parity(["--tabs=6,9"], cwd, input_data=b"a\tbbbbbbbbbbbbb\tc")


# Initial-only mode expands leading blanks and leaves later tabs unchanged.
def test_initial_only_expands_only_leading_tabs_matches_coreutils() -> None:
    # upstream: coreutils/tests/expand/expand.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_expand_parity(["--tabs=3", "-i"], cwd, input_data=b" \ta\tb")


# Backspace bytes reduce the tab column while remaining in the output stream.
def test_backspace_adjusts_column_matches_coreutils() -> None:
    # upstream: coreutils/tests/expand/expand.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_expand_parity([], cwd, input_data=b"aaa\b\b\bc\td\n")


# A trailing slash tab interval repeats fixed-width stops after listed stops.
def test_trailing_slash_tab_interval_matches_coreutils() -> None:
    # upstream: coreutils/tests/expand/expand.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_expand_parity(["--tabs=1,/5"], cwd, input_data=b"\ta\tb\tc")


# A trailing plus tab interval continues from the final explicit tab stop.
def test_incremental_plus_tab_interval_matches_coreutils() -> None:
    # upstream: coreutils/tests/expand/expand.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_expand_parity(["--tabs=1,+5"], cwd, input_data=b"\ta\tb\tc")


# A later -t interval extends the previous explicit tab stop list.
def test_later_incremental_tab_option_extends_previous_stops_matches_coreutils() -> None:
    # upstream: coreutils/tests/expand/expand.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_expand_parity(["--tab=1,2", "-t+5"], cwd, input_data=b"\ta\tb\tc")


# A new -t argument resets only the local marker while preserving accumulated stops.
def test_explicit_stop_after_increment_option_matches_coreutils() -> None:
    # upstream: none - follows coreutils/src/expand.c repeated parse_tab_stops calls
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_expand_parity(["-t1,+5", "-t6"], cwd, input_data=b"\ta\tb\tc")


# A zero interval marker is ignored rather than validated as an explicit zero stop.
def test_zero_increment_marker_matches_coreutils() -> None:
    # upstream: none - follows coreutils/src/expand-common.c finalize_tab_stops
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_expand_parity(["--tabs=+0"], cwd, input_data=b"a\tb\n")


# An explicit stdin operand is expanded in sequence with named file operands.
def test_stdin_operand_between_files_matches_coreutils() -> None:
    # upstream: coreutils/tests/expand/expand.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        (cwd / "in1").write_bytes(b"a\t")
        (cwd / "in2").write_bytes(b"c\t\n")

        assert_expand_parity(["--tabs=4", "in1", "-", "in2"], cwd, input_data=b"b\t")


# A missing file reports failure after writing output for earlier readable inputs.
def test_missing_file_keeps_prior_output_matches_coreutils() -> None:
    # upstream: coreutils/tests/expand/expand.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        (cwd / "in1").write_bytes(b"a\tb\n")

        assert_expand_parity(["--tabs=4", "in1", "missing"], cwd)


# A missing filename containing spaces uses GNU's quoted diagnostic form.
def test_missing_file_with_space_is_quoted_matches_coreutils() -> None:
    # upstream: coreutils/tests/expand/expand.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_expand_parity(["2001-09-09 01:46:40 UTC"], cwd)


# A missing chmod-style operand uses GNU's quoted diagnostic form.
def test_missing_file_with_equals_is_quoted_matches_coreutils() -> None:
    # upstream: coreutils/tests/expand/expand.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_expand_parity(["a=rw"], cwd)


# Non-numeric tab specs fail before reading stdin.
def test_invalid_tab_size_exits_nonzero_matches_coreutils() -> None:
    # upstream: coreutils/tests/expand/expand.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_expand_parity(["--tabs=a"], cwd, input_data=b"a\tb")


# Control characters in invalid tab values use GNU's named diagnostic escapes.
def test_invalid_tab_control_character_diagnostic_matches_coreutils() -> None:
    # upstream: none - follows coreutils/src/expand-common.c quote diagnostics
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_expand_parity(["--tabs=x\ty"], cwd)


# Backslashes in invalid tab values remain unambiguous in GNU diagnostics.
def test_invalid_tab_backslash_diagnostic_matches_coreutils() -> None:
    # upstream: none - follows coreutils/src/expand-common.c quote diagnostics
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_expand_parity([r"--tabs=x\y"], cwd)


# Apostrophes in invalid tab values are escaped inside GNU diagnostic quotes.
def test_invalid_tab_apostrophe_diagnostic_matches_coreutils() -> None:
    # upstream: none - follows coreutils/src/expand-common.c quote diagnostics
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_expand_parity(["--tabs=x'y"], cwd)


# A tab syntax error is emitted immediately and precedes a later help request.
def test_immediate_tab_error_before_help_matches_coreutils() -> None:
    # upstream: none - follows coreutils/src/expand.c option-processing loop
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_expand_parity(["--tabs=a", "--help"], cwd)


# Deferred zero-stop validation does not run when a later help request exits first.
def test_help_precedes_deferred_zero_validation_matches_coreutils() -> None:
    # upstream: none - follows coreutils/src/expand-common.c finalize_tab_stops
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_requested_message_behavior(
            run_system_expand(["--tabs=0", "--help"], cwd),
            run_bench_expand(["--tabs=0", "--help"], cwd),
        )


# Help exits before a later command-line parser error is inspected.
def test_help_before_later_unknown_option_matches_coreutils() -> None:
    # upstream: none - follows coreutils/src/expand.c getopt_long loop
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_requested_message_behavior(
            run_system_expand(["--help", "--unknown"], cwd),
            run_bench_expand(["--help", "--unknown"], cwd),
        )


# An immediate tab syntax error precedes a later command-line parser error.
def test_tab_error_before_later_unknown_option_matches_coreutils() -> None:
    # upstream: none - follows coreutils/src/expand.c getopt_long loop
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_expand_parity(["--tabs=a", "--unknown"], cwd)


# A plus marker embedded after digits names the plus marker and offending suffix.
def test_plus_marker_position_diagnostic_matches_coreutils() -> None:
    # upstream: none - follows coreutils/src/expand-common.c parse_tab_stops
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_expand_parity(["--tabs=3+4"], cwd)


# Multiple misplaced markers preserve every GNU diagnostic in source order.
def test_multiple_marker_position_diagnostics_match_coreutils() -> None:
    # upstream: none - follows coreutils/src/expand-common.c parse_tab_stops
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_expand_parity(["--tabs=1/2/3"], cwd)


# Overflow is diagnosed before a following invalid character in the same value.
def test_overflow_then_invalid_character_diagnostics_match_coreutils() -> None:
    # upstream: none - follows coreutils/src/expand-common.c DECIMAL_DIGIT_ACCUMULATE path
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_expand_parity(["--tabs=9223372036854775808x"], cwd)


# Mixed slash and plus intervals are rejected during final validation.
def test_mixed_repeat_marker_diagnostic_matches_coreutils() -> None:
    # upstream: none - follows coreutils/src/expand-common.c validate_tab_stops
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_expand_parity(["--tabs=1,+5,/6"], cwd)


# A bundled short-option error identifies the failing character, not the first one.
def test_bundled_short_option_diagnostic_matches_coreutils() -> None:
    # upstream: coreutils/tests/misc/invalid-opt.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_expand_parity(["-iZ"], cwd)


# A missing bundled -t argument identifies the argument-taking option.
def test_bundled_missing_tabs_argument_diagnostic_matches_coreutils() -> None:
    # upstream: coreutils/tests/misc/invalid-opt.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_expand_parity(["-iit"], cwd)


# An abbreviated no-argument long option uses the canonical GNU diagnostic name.
def test_abbreviated_unexpected_argument_diagnostic_matches_coreutils() -> None:
    # upstream: coreutils/tests/misc/invalid-opt.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_expand_parity(["--in=value"], cwd)


# Duplicate explicit tab stops fail because the list is not ascending.
def test_duplicate_tab_stop_exits_nonzero_matches_coreutils() -> None:
    # upstream: coreutils/tests/expand/expand.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_expand_parity(["--tabs=3,3"], cwd, input_data=b"a\tb")


# A slash repeat marker before an explicit stop is rejected by GNU syntax.
def test_slash_repeat_before_more_stops_exits_nonzero_matches_coreutils() -> None:
    # upstream: coreutils/tests/expand/expand.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_expand_parity(["--tabs=/3,6,8"], cwd, input_data=b"a\tb")


# Help exits successfully with the shared requested-message contract.
def test_help_exit_successfully_matches_coreutils() -> None:
    # upstream: coreutils/tests/help/help-version.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_requested_message_behavior(
            run_system_expand(["--help"], cwd),
            run_bench_expand(["--help"], cwd),
        )


# Version exits successfully with the shared requested-message contract.
def test_version_exit_successfully_matches_coreutils() -> None:
    # upstream: coreutils/tests/help/help-version.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_requested_message_behavior(
            run_system_expand(["--version"], cwd),
            run_bench_expand(["--version"], cwd),
        )


# The expand CLI schema module verifies independently.
@pytest.mark.dafny_verify
def test_expand_schema_verifies() -> None:
    # upstream: none - Verifies the Dafny proof surface rather than an upstream runtime script.
    run_dafny_verify(ROOT / "bench" / "utils" / "expand" / "ExpandSchema.dfy")


# The expand executable core module verifies independently.
@pytest.mark.dafny_verify
def test_expand_core_verifies() -> None:
    # upstream: none - Verifies the Dafny proof surface rather than an upstream runtime script.
    run_dafny_verify(ROOT / "bench" / "utils" / "expand" / "ExpandCore.dfy")


# The expand world-transition spec module verifies independently.
@pytest.mark.dafny_verify
def test_expand_spec_verifies() -> None:
    # upstream: none - Verifies the Dafny proof surface rather than an upstream runtime script.
    run_dafny_verify(ROOT / "bench" / "utils" / "expand" / "ExpandSpec.dfy")


# The expand proof bridge module verifies independently.
@pytest.mark.dafny_verify
def test_expand_proof_verifies() -> None:
    # upstream: none - Verifies the Dafny proof surface rather than an upstream runtime script.
    run_dafny_verify(ROOT / "bench" / "utils" / "expand" / "ExpandProof.dfy")


# The expand benchmark item module verifies independently.
@pytest.mark.dafny_verify
def test_expand_benchmark_item_verifies() -> None:
    # upstream: none - Verifies the Dafny proof surface rather than an upstream runtime script.
    run_dafny_verify(ROOT / "bench" / "utils" / "expand" / "Expand.dfy")
