"""Check the verified chmod benchmark slice."""

import hashlib
import os
import stat
import subprocess
import tempfile
from pathlib import Path

import pytest

from evaluation.submission.candidate_execution import run_candidate
from tools.bench.bench_test_support import (
    BENCH_COMMAND_TIMEOUT_SEC,
    bench_dll_path,
    coreutils_binary_path,
    evaluation_target_root,
    parity_env,
    run_coreutils_utility,
    run_dafny_verify,
)

ROOT = evaluation_target_root(Path(__file__).resolve().parents[3])
BENCH_CHMOD_DLL = bench_dll_path(ROOT, ROOT / "_build" / "bench" / "chmod_bench.dll")
COREUTILS_CHMOD = coreutils_binary_path(
    ROOT,
    ROOT / "_build" / "coreutils" / "src" / "chmod",
)

CHMOD_HELP_TEXT = """Usage: chmod [OPTION]... MODE[,MODE]... FILE...
  or:  chmod [OPTION]... OCTAL-MODE FILE...
  or:  chmod [OPTION]... --reference=RFILE FILE...
Change the mode of each FILE to MODE.
With --reference, change the mode of each FILE to that of RFILE.

  -c, --changes
         like verbose but report only when a change is made
  -f, --silent, --quiet
         suppress most error messages
  -v, --verbose
         output a diagnostic for every file processed
      --dereference
         affect the referent of each symbolic link,
         rather than the symbolic link itself
  -h, --no-dereference
         affect each symbolic link, rather than the referent
      --no-preserve-root
         do not treat '/' specially (the default)
      --preserve-root
         fail to operate recursively on '/'
      --reference=RFILE
         use RFILE's mode instead of specifying MODE values.
         RFILE is always dereferenced if a symbolic link.
  -R, --recursive
         change files and directories recursively

The following options modify how a hierarchy is traversed when the -R
option is also specified.  If more than one is specified, only the final
one takes effect. -H is the default.

  -H
         if a command line argument is a symlink to a directory, traverse it
  -L
         traverse every symbolic link to a directory encountered
  -P
         do not traverse any symbolic links

      --help
         display this help and exit
      --version
         output version information and exit

Each MODE is of the form '[ugoa]*([-+=]([rwxXst]*|[ugo]))+|[-+=][0-7]+'.

Report bugs to: bug-coreutils@gnu.org
GNU coreutils home page: <https://www.gnu.org/software/coreutils/>
General help using GNU software: <https://www.gnu.org/gethelp/>
Report any translation bugs to <https://translationproject.org/team/>
Full documentation <https://www.gnu.org/software/coreutils/chmod>
or available locally via: info '(coreutils) chmod invocation'
"""

CHMOD_VERSION_TEXT = """chmod (GNU coreutils) 9.10.13-2cf49
Copyright (C) 2026 Free Software Foundation, Inc.
License GPLv3+: GNU GPL version 3 or later <https://gnu.org/licenses/gpl.html>.
This is free software: you are free to change and redistribute it.
There is NO WARRANTY, to the extent permitted by law.

Written by David MacKenzie and Jim Meyering.
"""
CHMOD_HELP_SHA256 = "667306f27890c26f3b56f3f6c000352c304e4ae530f208b158d3e2f000d07d29"
CHMOD_VERSION_SHA256 = "a3e0d01a03cbcc6dd90b33435b7813a576cf270dc6fa936fad6243e13fb9e84b"

USAGE_CASE_ROWS = [
    ("end-options-only", ["--"], [], 0o644),
    ("double-dash-mode-only", ["--", "--"], [], 0o644),
    ("double-dash-mode-two-files", ["--", "--", "--", "f"], ["--", "f"], 0o644),
    ("double-dash-mode-dash-file", ["--", "--", "-w", "f"], ["-w", "f"], 0o644),
    ("double-dash-mode-file", ["--", "--", "f"], ["f"], 0o644),
    ("end-options-dash-mode-only", ["--", "-w"], [], 0o644),
    ("dash-mode-two-files", ["--", "-w", "--", "f"], ["--", "f"], 0o444),
    ("dash-mode-dash-file", ["--", "-w", "-w", "f"], ["-w", "f"], 0o444),
    ("dash-mode-file", ["--", "-w", "f"], ["f"], 0o444),
    ("plain-mode-only-after-end-options", ["--", "f"], [], 0o644),
    ("option-mode-only", ["-w"], [], 0o644),
    ("option-mode-end-options-only", ["-w", "--"], [], 0o644),
    ("option-mode-two-files", ["-w", "--", "--", "f"], ["--", "f"], 0o444),
    ("option-mode-dash-file", ["-w", "--", "-w", "f"], ["-w", "f"], 0o444),
    ("option-mode-file-after-end-options", ["-w", "--", "f"], ["f"], 0o444),
    ("two-option-mode-parts-only", ["-w", "-w"], [], 0o644),
    ("two-option-mode-parts-file", ["-w", "-w", "--", "f"], ["f"], 0o444),
    ("three-option-mode-parts-file", ["-w", "-w", "-w", "f"], ["f"], 0o444),
    ("two-option-mode-parts-direct-file", ["-w", "-w", "f"], ["f"], 0o444),
    ("option-mode-direct-file", ["-w", "f"], ["f"], 0o444),
    ("plain-mode-only", ["f"], [], 0o644),
    ("plain-mode-end-options-only", ["f", "--"], [], 0o644),
    ("plain-mode-option-like-file", ["f", "-w"], ["f"], 0o444),
    ("invalid-plain-mode", ["f", "f"], [], 0o644),
    ("invalid-permission-copy", ["u+gr", "f"], [], 0o644),
    ("invalid-empty-action", ["ug,+x", "f"], [], 0o644),
]

USAGE_FAILURE_STDERR = {
    "end-options-only": "chmod: missing operand\nTry 'chmod --help' for more information.\n",
    "double-dash-mode-only": (
        "chmod: missing operand after '--'\nTry 'chmod --help' for more information.\n"
    ),
    "end-options-dash-mode-only": (
        "chmod: missing operand after '-w'\nTry 'chmod --help' for more information.\n"
    ),
    "plain-mode-only-after-end-options": (
        "chmod: missing operand after 'f'\nTry 'chmod --help' for more information.\n"
    ),
    "option-mode-only": "chmod: missing operand\nTry 'chmod --help' for more information.\n",
    "option-mode-end-options-only": (
        "chmod: missing operand\nTry 'chmod --help' for more information.\n"
    ),
    "two-option-mode-parts-only": (
        "chmod: missing operand\nTry 'chmod --help' for more information.\n"
    ),
    "plain-mode-only": (
        "chmod: missing operand after 'f'\nTry 'chmod --help' for more information.\n"
    ),
    "plain-mode-end-options-only": (
        "chmod: missing operand after 'f'\nTry 'chmod --help' for more information.\n"
    ),
    "invalid-plain-mode": ("chmod: invalid mode: 'f'\nTry 'chmod --help' for more information.\n"),
    "invalid-permission-copy": (
        "chmod: invalid mode: 'u+gr'\nTry 'chmod --help' for more information.\n"
    ),
    "invalid-empty-action": (
        "chmod: invalid mode: 'ug,+x'\nTry 'chmod --help' for more information.\n"
    ),
}

USAGE_SCENARIOS = [
    pytest.param(
        args,
        None,
        files,
        expected_mode,
        USAGE_FAILURE_STDERR.get(case_id, ""),
        id=f"{case_id}-present",
    )
    for case_id, args, files, expected_mode in USAGE_CASE_ROWS
] + [
    pytest.param(
        args,
        missing,
        files,
        expected_mode,
        f"chmod: cannot access '{missing}': No such file or directory\n",
        id=f"{case_id}-missing-{missing}",
    )
    for case_id, args, files, expected_mode in USAGE_CASE_ROWS
    for missing in files
]

EQUALS_CASES = [
    pytest.param("u", "g", 0o070, id="u-to-g"),
    pytest.param("u", "o", 0o007, id="u-to-o"),
    pytest.param("g", "u", 0o700, id="g-to-u"),
    pytest.param("g", "o", 0o007, id="g-to-o"),
    pytest.param("o", "u", 0o700, id="o-to-u"),
    pytest.param("o", "g", 0o070, id="o-to-g"),
]

EQUAL_X_MODES = [
    pytest.param("=x", id="equals-x"),
    pytest.param("=xX", id="equals-x-capital-x"),
    pytest.param("=Xx", id="equals-capital-x-x"),
    pytest.param("=x,=X", id="equals-x-then-capital-x"),
    pytest.param("=X,=x", id="equals-capital-x-then-x"),
]

SETGID_CASES = [
    pytest.param("+", 0o2755, id="plus-empty"),
    pytest.param("-", 0o2755, id="minus-empty"),
    pytest.param("g-s", 0o0755, id="group-minus-setgid"),
    pytest.param("00755", 0o0755, id="five-digit-octal"),
    pytest.param("000755", 0o0755, id="six-digit-octal"),
    pytest.param("=755", 0o0755, id="symbolic-equals-octal"),
    pytest.param("-2000", 0o0755, id="minus-setgid-octal"),
    pytest.param("-7022", 0o0755, id="minus-mixed-octal"),
    pytest.param("755", 0o2755, id="three-digit-preserves-setgid"),
    pytest.param("0755", 0o2755, id="four-digit-preserves-setgid"),
    pytest.param("+2000", 0o2755, id="plus-setgid-octal"),
    pytest.param("-5022", 0o2755, id="minus-non-setgid-bits"),
    pytest.param("=7777,-5022", 0o2755, id="set-all-then-remove-bits"),
]


def run_bench_chmod(
    args: list[str],
    cwd: Path,
    umask: int | None = None,
) -> tuple[str, str, int]:
    completed = run_candidate(
        BENCH_CHMOD_DLL,
        args,
        cwd=cwd,
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        env=parity_env(),
        preexec_fn=None if umask is None else lambda: os.umask(umask),
        timeout=BENCH_COMMAND_TIMEOUT_SEC,
    )
    return completed.stdout, completed.stderr, completed.returncode


def run_bench_chmod_bytes(args: list[str], cwd: Path) -> tuple[bytes, bytes, int]:
    completed = run_candidate(
        BENCH_CHMOD_DLL,
        args,
        cwd=cwd,
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        env=parity_env(),
        timeout=BENCH_COMMAND_TIMEOUT_SEC,
    )
    return completed.stdout, completed.stderr, completed.returncode


def test_missing_operand_is_exact() -> None:
    # upstream: coreutils/tests/chmod/usage.sh
    # Missing operands produce the deterministic GNU diagnostic and failure status.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert run_bench_chmod([], cwd) == (
            "",
            "chmod: missing operand\nTry 'chmod --help' for more information.\n",
            1,
        )


def test_octal_mode_changes_one_file() -> None:
    # upstream: coreutils/tests/chmod/c-option.sh
    # The supported OCTAL-MODE FILE form changes exactly that file's permission bits.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        target = cwd / "file.txt"
        _ = target.write_text("payload\n", encoding="utf-8")
        target.chmod(0o644)

        result = run_bench_chmod(["600", "file.txt"], cwd)

        assert result == ("", "", 0)
        assert stat.S_IMODE(target.stat().st_mode) == 0o600


def test_reference_mode_changes_one_file() -> None:
    # upstream: none - coreutils/src/chmod.c --reference=RFILE behavior;
    # upstream-reason: no pinned chmod runtime test covers it.
    # The supported --reference=RFILE FILE form copies the reference permission bits.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        ref = cwd / "ref"
        target = cwd / "file.txt"
        _ = ref.write_text("ref\n", encoding="utf-8")
        _ = target.write_text("payload\n", encoding="utf-8")
        ref.chmod(0o640)
        target.chmod(0o600)

        result = run_bench_chmod(["--reference=ref", "file.txt"], cwd)

        assert result == ("", "", 0)
        assert stat.S_IMODE(target.stat().st_mode) == 0o640


def test_silent_missing_file_suppresses_target_diagnostic() -> None:
    # upstream: coreutils/tests/chmod/silent.sh
    # The -f flag suppresses target chmod diagnostics while preserving failure status.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert run_bench_chmod(["-f", "600", "missing"], cwd) == ("", "", 1)


def test_nonrecursive_default_rejects_dangling_symlink() -> None:
    # upstream: coreutils/tests/chmod/symlinks.sh
    # A default-dereferenced dangling operand receives GNU's dedicated diagnostic.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        dangle = cwd / "dangle"
        dangle.symlink_to("missing")

        assert run_bench_chmod(["600", "dangle"], cwd) == (
            "",
            "chmod: cannot operate on dangling symlink 'dangle'\n",
            1,
        )
        assert dangle.is_symlink()


def test_nonrecursive_p_reports_chmod_failure_for_dangling_symlink() -> None:
    # upstream: coreutils/tests/chmod/symlinks.sh
    # Nonrecursive -P reaches chmod on a dangling operand and reports its ENOENT.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        dangle = cwd / "dangle"
        dangle.symlink_to("missing")

        assert run_bench_chmod(["-P", "-7022", "dangle"], cwd) == (
            "",
            "chmod: changing permissions of 'dangle': No such file or directory\n",
            1,
        )
        assert dangle.is_symlink()


def test_nonrecursive_p_explicit_dereference_reports_dangling_failure() -> None:
    # upstream: coreutils/tests/chmod/symlinks.sh
    # Explicit dereference after -P reports GNU's dereference-specific dangling failure.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        dangle = cwd / "dangle"
        dangle.symlink_to("missing")

        assert run_bench_chmod(["-P", "--dereference", "600", "dangle"], cwd) == (
            "",
            "chmod: cannot dereference 'dangle': No such file or directory\n",
            1,
        )
        assert dangle.is_symlink()


# Explicit dereference reports an inaccessible missing operand before attempting chmod.
def test_nonrecursive_p_explicit_dereference_reports_missing_operand() -> None:
    # upstream: none - no pinned chmod runtime test covers this option-order diagnostic.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)

        assert run_bench_chmod(["--dereference", "-P", "600", "missing"], cwd) == (
            "",
            "chmod: cannot access 'missing': No such file or directory\n",
            1,
        )


def test_nonrecursive_p_derives_mode_from_symlink_before_changing_referent() -> None:
    # upstream: coreutils/tests/chmod/symlinks.sh
    # Nonrecursive -P derives the new mode from the link inode before changing its referent.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        target = cwd / "target"
        _ = target.write_text("payload\n", encoding="utf-8")
        target.chmod(0o600)
        link = cwd / "link"
        link.symlink_to("target")

        assert run_bench_chmod(["-P", "u-x", "link"], cwd) == ("", "", 0)
        assert stat.S_IMODE(target.stat().st_mode) == 0o677
        assert link.is_symlink()


def test_nonrecursive_no_dereference_silently_skips_symlink() -> None:
    # upstream: coreutils/tests/chmod/symlinks.sh
    # Nonrecursive -h treats a symlink as a successful no-op without changing either inode.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        target = cwd / "target"
        _ = target.write_text("payload\n", encoding="utf-8")
        target.chmod(0o644)
        link = cwd / "link"
        link.symlink_to("target")
        link_mode = stat.S_IMODE(link.lstat().st_mode)

        assert run_bench_chmod(["--no-dereference", "700", "link"], cwd) == ("", "", 0)
        assert stat.S_IMODE(link.lstat().st_mode) == link_mode
        assert stat.S_IMODE(target.stat().st_mode) == 0o644


def test_nonrecursive_no_dereference_reports_eloop_for_symlink_cycle() -> None:
    # upstream: none - no pinned chmod runtime test covers a nonrecursive symlink cycle.
    # Nonrecursive -h reports GNU's exact access failure without changing a symlink cycle.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        cycle_a = cwd / "cycle-a"
        cycle_b = cwd / "cycle-b"
        cycle_a.symlink_to("cycle-b")
        cycle_b.symlink_to("cycle-a")

        assert run_bench_chmod(["-h", "-7022", "cycle-a"], cwd) == (
            "",
            "chmod: cannot access 'cycle-a': Too many levels of symbolic links\n",
            1,
        )
        assert cycle_a.readlink() == Path("cycle-b")
        assert cycle_b.readlink() == Path("cycle-a")


# Verbose physical mode changes report the attempted transition when chmod hits a symlink cycle.
def test_nonrecursive_physical_verbose_change_failure_reports_attempted_mode() -> None:
    # upstream: none - no pinned chmod runtime test covers this verbose symlink-cycle failure.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        cycle_a = cwd / "chmod-cycle-a"
        cycle_b = cwd / "chmod-cycle-b"
        cycle_a.symlink_to("chmod-cycle-b")
        cycle_b.symlink_to("chmod-cycle-a")
        before = {
            path.name: (path.readlink(), stat.S_IMODE(path.lstat().st_mode))
            for path in (cycle_a, cycle_b)
        }

        assert run_bench_chmod(["-P", "-v", "+2000", "chmod-cycle-b"], cwd) == (
            "failed to change mode of 'chmod-cycle-b' from 0777 (rwxrwxrwx) to 2777 (rwxrwsrwx)\n",
            "chmod: changing permissions of 'chmod-cycle-b': Too many levels of symbolic links\n",
            1,
        )
        assert {
            path.name: (path.readlink(), stat.S_IMODE(path.lstat().st_mode))
            for path in (cycle_a, cycle_b)
        } == before
        assert sorted(path.name for path in cwd.iterdir()) == [
            "chmod-cycle-a",
            "chmod-cycle-b",
        ]


def test_nonrecursive_no_dereference_verbose_reports_symlink_noop() -> None:
    # upstream: coreutils/tests/chmod/symlinks.sh
    # Verbose nonrecursive -h emits GNU's exact neither-changed diagnostic for a symlink.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        target = cwd / "target"
        _ = target.write_text("payload\n", encoding="utf-8")
        target.chmod(0o644)
        (cwd / "link").symlink_to("target")

        assert run_bench_chmod(["--no-dereference", "-v", "700", "link"], cwd) == (
            "neither symbolic link 'link' nor referent has been changed\n",
            "",
            0,
        )
        assert stat.S_IMODE(target.stat().st_mode) == 0o644


def test_nonrecursive_reference_no_dereference_verbose_skips_symlink() -> None:
    # upstream: coreutils/tests/chmod/symlinks.sh
    # Reference mode keeps -h symlinks unchanged and emits the same exact verbose diagnostic.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        reference = cwd / "ref"
        _ = reference.write_text("reference\n", encoding="utf-8")
        reference.chmod(0o700)
        target = cwd / "target"
        _ = target.write_text("payload\n", encoding="utf-8")
        target.chmod(0o644)
        (cwd / "link").symlink_to("target")

        assert run_bench_chmod(["--reference=ref", "--no-dereference", "-v", "link"], cwd) == (
            "neither symbolic link 'link' nor referent has been changed\n",
            "",
            0,
        )
        assert stat.S_IMODE(target.stat().st_mode) == 0o644


def test_nonrecursive_no_dereference_changes_regular_file() -> None:
    # upstream: coreutils/tests/chmod/symlinks.sh
    # Nonrecursive -h still applies the requested mode to an ordinary file.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        target = cwd / "file"
        _ = target.write_text("payload\n", encoding="utf-8")
        target.chmod(0o644)

        assert run_bench_chmod(["--no-dereference", "700", "file"], cwd) == ("", "", 0)
        assert stat.S_IMODE(target.stat().st_mode) == 0o700


def test_symbolic_mode_changes_one_file() -> None:
    # upstream: coreutils/tests/chmod/equal-x.sh
    # Symbolic owner-execute changes the target while preserving every other mode bit.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        target = cwd / "file.txt"
        _ = target.write_text("payload\n", encoding="utf-8")
        target.chmod(0o644)

        assert run_bench_chmod(["u+x", "file.txt"], cwd) == ("", "", 0)
        assert stat.S_IMODE(target.stat().st_mode) == 0o744


def test_omitted_classes_use_one_captured_umask() -> None:
    # upstream: coreutils/tests/chmod/umask-x.sh
    # An omitted class applies the child process umask consistently across the batch.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        for name in ["a", "b"]:
            target = cwd / name
            _ = target.write_text("payload\n", encoding="utf-8")
            target.chmod(0o666)

        assert run_bench_chmod(["--", "-w", "a", "b"], cwd, umask=0o022) == ("", "", 0)
        assert stat.S_IMODE((cwd / "a").stat().st_mode) == 0o466
        assert stat.S_IMODE((cwd / "b").stat().st_mode) == 0o466


def test_option_like_mode_diagnoses_umask_surprise() -> None:
    # upstream: coreutils/tests/chmod/umask-x.sh
    # Recovered -w changes the file but fails with GNU's naive-permission warning.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        target = cwd / "file"
        _ = target.write_text("payload\n", encoding="utf-8")
        target.chmod(0o666)

        assert run_bench_chmod(["-w", "file"], cwd, umask=0o022) == (
            "",
            "chmod: file: new permissions are r--rw-rw-, not r--r--r--\n",
            1,
        )
        assert stat.S_IMODE(target.stat().st_mode) == 0o466


def test_option_like_mode_without_operand_is_generic() -> None:
    # upstream: coreutils/tests/chmod/usage.sh
    # An option-allocated mode without a file uses GNU's generic missing-operand message.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert run_bench_chmod(["-w"], cwd) == (
            "",
            "chmod: missing operand\nTry 'chmod --help' for more information.\n",
            1,
        )


def test_reference_without_operand_is_generic() -> None:
    # upstream: coreutils/tests/chmod/usage.sh
    # --reference without a target uses GNU's generic missing-operand message.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        reference = cwd / "ref"
        _ = reference.write_text("payload\n", encoding="utf-8")
        assert run_bench_chmod(["--reference=ref"], cwd) == (
            "",
            "chmod: missing operand\nTry 'chmod --help' for more information.\n",
            1,
        )


def test_recursive_changes_report_parent_before_child() -> None:
    # upstream: coreutils/tests/chmod/c-option.sh
    # Recursive changes report a directory before its single discovered child.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        tree = cwd / "tree"
        tree.mkdir()
        child = tree / "child"
        _ = child.write_text("payload\n", encoding="utf-8")
        tree.chmod(0o755)
        child.chmod(0o644)

        assert run_bench_chmod(["-c", "-R", "700", "tree"], cwd) == (
            "mode of 'tree' changed from 0755 (rwxr-xr-x) to 0700 (rwx------)\n"
            "mode of 'tree/child' changed from 0644 (rw-r--r--) to 0700 (rwx------)\n",
            "",
            0,
        )
        assert stat.S_IMODE(tree.stat().st_mode) == 0o700
        assert stat.S_IMODE(child.stat().st_mode) == 0o700


def test_recursive_reference_changes_report_parent_before_child() -> None:
    # upstream: none - no pinned chmod runtime test covers recursive reference report order.
    # source-derived: coreutils/src/chmod.c reference plan and pre-order FTS processing.
    # Recursive --reference captures one mode and reports the parent before its child.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        reference = cwd / "ref"
        _ = reference.write_text("reference\n", encoding="utf-8")
        reference.chmod(0o700)
        tree = cwd / "tree"
        tree.mkdir()
        child = tree / "child"
        _ = child.write_text("payload\n", encoding="utf-8")
        tree.chmod(0o755)
        child.chmod(0o644)

        assert run_bench_chmod(["-c", "-R", "--reference=ref", "tree"], cwd) == (
            "mode of 'tree' changed from 0755 (rwxr-xr-x) to 0700 (rwx------)\n"
            "mode of 'tree/child' changed from 0644 (rw-r--r--) to 0700 (rwx------)\n",
            "",
            0,
        )
        assert stat.S_IMODE(tree.stat().st_mode) == 0o700
        assert stat.S_IMODE(child.stat().st_mode) == 0o700


def test_recursive_parent_change_restores_traversal_access() -> None:
    # upstream: coreutils/tests/chmod/inaccessible.sh
    # Changing an unreadable parent before opening it allows its child to be processed.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        tree = cwd / "tree"
        tree.mkdir()
        child = tree / "child"
        _ = child.write_text("payload\n", encoding="utf-8")
        child.chmod(0o600)
        tree.chmod(0o300)

        try:
            assert run_bench_chmod(["-c", "-R", "755", "tree"], cwd) == (
                "mode of 'tree' changed from 0300 (-wx------) to 0755 (rwxr-xr-x)\n"
                "mode of 'tree/child' changed from 0600 (rw-------) to 0755 (rwxr-xr-x)\n",
                "",
                0,
            )
            assert stat.S_IMODE(child.stat().st_mode) == 0o755
        finally:
            tree.chmod(0o700)


def test_upstream_inaccessible_parent_then_child_batch() -> None:
    # upstream: coreutils/tests/chmod/inaccessible.sh
    # An ordered parent-then-child batch restores access before handling the child.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        parent = cwd / "d"
        child = parent / "e"
        child.mkdir(parents=True)
        child.chmod(0)
        parent.chmod(0)

        try:
            assert run_bench_chmod(["u+rwx", "d", "d/e"], cwd) == ("", "", 0)
            assert stat.S_IMODE(parent.stat().st_mode) == 0o700
            assert stat.S_IMODE(child.stat().st_mode) == 0o700
        finally:
            parent.chmod(0o700)
            child.chmod(0o700)


def test_recursive_default_ignores_discovered_file_symlink() -> None:
    # upstream: coreutils/tests/chmod/ignore-symlink.sh
    # A discovered file symlink is ignored without making recursive chmod fail.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        tree = cwd / "dir"
        tree.mkdir()
        target = tree / "f"
        _ = target.write_text("payload\n", encoding="utf-8")
        target.chmod(0o444)
        link = tree / "l"
        link.symlink_to("f")

        assert run_bench_chmod(["u+w", "-R", "dir"], cwd) == ("", "", 0)
        assert stat.S_IMODE(target.stat().st_mode) == 0o644
        assert link.is_symlink()
        assert link.readlink() == Path("f")


def test_recursive_default_follows_top_level_directory_symlink() -> None:
    # upstream: coreutils/tests/chmod/symlinks.sh
    # Default recursive traversal follows a command-line symlink to a directory.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        target = cwd / "target"
        target.mkdir()
        child = target / "child"
        _ = child.write_text("payload\n", encoding="utf-8")
        target.chmod(0o755)
        child.chmod(0o644)
        (cwd / "top").symlink_to("target", target_is_directory=True)

        assert run_bench_chmod(["-R", "700", "top"], cwd) == ("", "", 0)
        assert stat.S_IMODE(target.stat().st_mode) == 0o700
        assert stat.S_IMODE(child.stat().st_mode) == 0o700


def test_recursive_last_h_option_follows_top_level_directory_symlink() -> None:
    # upstream: coreutils/tests/chmod/symlinks.sh
    # A final -H overrides -P and follows a command-line directory symlink.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        target = cwd / "target"
        target.mkdir()
        child = target / "child"
        _ = child.write_text("payload\n", encoding="utf-8")
        target.chmod(0o755)
        child.chmod(0o644)
        (cwd / "top").symlink_to("target", target_is_directory=True)

        assert run_bench_chmod(["-P", "-H", "-R", "700", "top"], cwd) == ("", "", 0)
        assert stat.S_IMODE(target.stat().st_mode) == 0o700
        assert stat.S_IMODE(child.stat().st_mode) == 0o700


def test_recursive_p_rejects_explicit_dereference() -> None:
    # upstream: none - no pinned chmod runtime test covers this recursive option conflict.
    # source-derived: coreutils/src/chmod.c recursive dereference validation.
    # -P with recursive dereference fails before changing any target.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        tree = cwd / "tree"
        tree.mkdir()
        child = tree / "child"
        _ = child.write_text("payload\n", encoding="utf-8")
        tree.chmod(0o755)
        child.chmod(0o644)

        assert run_bench_chmod(["-P", "-R", "--dereference", "700", "tree"], cwd) == (
            "",
            "chmod: -R --dereference requires either -H or -L\n",
            1,
        )
        assert stat.S_IMODE(tree.stat().st_mode) == 0o755
        assert stat.S_IMODE(child.stat().st_mode) == 0o644


def test_recursive_h_accepts_explicit_dereference() -> None:
    # upstream: coreutils/tests/chmod/symlinks.sh
    # source-derived: coreutils/src/chmod.c -H and --dereference interaction.
    # Explicit -H permits recursive dereference of a command-line directory symlink.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        target = cwd / "target"
        target.mkdir()
        child = target / "child"
        _ = child.write_text("payload\n", encoding="utf-8")
        target.chmod(0o755)
        child.chmod(0o644)
        (cwd / "top").symlink_to("target", target_is_directory=True)

        assert run_bench_chmod(["-H", "-R", "--dereference", "700", "top"], cwd) == (
            "",
            "",
            0,
        )
        assert stat.S_IMODE(target.stat().st_mode) == 0o700
        assert stat.S_IMODE(child.stat().st_mode) == 0o700


def test_recursive_h_dereferences_discovered_file_symlink() -> None:
    # upstream: coreutils/tests/chmod/symlinks.sh
    # source-derived: coreutils/src/chmod.c FTS_SL handling with explicit dereference.
    # -H does not traverse a discovered file symlink but --dereference changes its referent.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        tree = cwd / "tree"
        tree.mkdir()
        tree.chmod(0o755)
        referent = cwd / "referent"
        _ = referent.write_text("payload\n", encoding="utf-8")
        referent.chmod(0o644)
        link = tree / "link"
        link.symlink_to("../referent")

        assert run_bench_chmod(["-R", "-H", "--dereference", "700", "tree"], cwd) == (
            "",
            "",
            0,
        )
        assert stat.S_IMODE(tree.stat().st_mode) == 0o700
        assert stat.S_IMODE(referent.stat().st_mode) == 0o700
        assert link.readlink() == Path("../referent")


def test_recursive_h_dereferences_discovered_directory_without_descending() -> None:
    # upstream: coreutils/tests/chmod/symlinks.sh
    # A discovered directory symlink under -H is chmodded through --dereference but not traversed.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        tree = cwd / "tree"
        outside = cwd / "outside"
        tree.mkdir()
        outside.mkdir()
        child = outside / "child"
        _ = child.write_text("payload\n", encoding="utf-8")
        tree.chmod(0o755)
        outside.chmod(0o755)
        child.chmod(0o644)
        (tree / "link").symlink_to("../outside", target_is_directory=True)

        assert run_bench_chmod(["-R", "-H", "--dereference", "700", "tree"], cwd) == ("", "", 0)
        assert stat.S_IMODE(tree.stat().st_mode) == 0o700
        assert stat.S_IMODE(outside.stat().st_mode) == 0o700
        assert stat.S_IMODE(child.stat().st_mode) == 0o644


def test_recursive_h_dangling_failure_continues_to_later_operand() -> None:
    # upstream: coreutils/tests/chmod/symlinks.sh
    # source-derived: coreutils/src/chmod.c FTS_SL dereference failure and process_files.
    # A discovered dangling link fails exact dereference but does not skip the next operand.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        tree = cwd / "tree"
        tree.mkdir()
        tree.chmod(0o755)
        dangle = tree / "dangle"
        dangle.symlink_to("../missing")
        later = cwd / "later"
        _ = later.write_text("payload\n", encoding="utf-8")
        later.chmod(0o600)

        assert run_bench_chmod(["-R", "-H", "--dereference", "700", "tree", "later"], cwd) == (
            "",
            "chmod: cannot dereference 'tree/dangle': No such file or directory\n",
            1,
        )
        assert stat.S_IMODE(tree.stat().st_mode) == 0o700
        assert stat.S_IMODE(later.stat().st_mode) == 0o700
        assert dangle.readlink() == Path("../missing")


def test_recursive_h_verbose_dangling_failure_reports_both_streams() -> None:
    # upstream: coreutils/tests/chmod/symlinks.sh
    # source-derived: coreutils/src/chmod.c verbose FTS_SL failure and continuation.
    # Verbose dereference failure reports access status and still changes the next operand.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        tree = cwd / "tree"
        tree.mkdir()
        tree.chmod(0o755)
        dangle = tree / "dangle"
        dangle.symlink_to("../missing")
        later = cwd / "later"
        _ = later.write_text("payload\n", encoding="utf-8")
        later.chmod(0o600)

        assert run_bench_chmod(
            ["-v", "-R", "-H", "--dereference", "700", "tree", "later"], cwd
        ) == (
            "mode of 'tree' changed from 0755 (rwxr-xr-x) to 0700 (rwx------)\n"
            "'tree/dangle' could not be accessed\n"
            "mode of 'later' changed from 0600 (rw-------) to 0700 (rwx------)\n",
            "chmod: cannot dereference 'tree/dangle': No such file or directory\n",
            1,
        )
        assert stat.S_IMODE(tree.stat().st_mode) == 0o700
        assert stat.S_IMODE(later.stat().st_mode) == 0o700
        assert dangle.readlink() == Path("../missing")


def test_recursive_default_does_not_follow_discovered_directory_symlink() -> None:
    # upstream: coreutils/tests/chmod/symlinks.sh
    # Default recursive traversal leaves a discovered symlink referent unchanged.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        tree = cwd / "tree"
        outside = cwd / "outside"
        tree.mkdir()
        outside.mkdir()
        child = outside / "child"
        _ = child.write_text("payload\n", encoding="utf-8")
        tree.chmod(0o755)
        outside.chmod(0o755)
        child.chmod(0o644)
        (tree / "link").symlink_to("../outside", target_is_directory=True)

        assert run_bench_chmod(["-R", "700", "tree"], cwd) == ("", "", 0)
        assert stat.S_IMODE(tree.stat().st_mode) == 0o700
        assert stat.S_IMODE(outside.stat().st_mode) == 0o755
        assert stat.S_IMODE(child.stat().st_mode) == 0o644


def test_recursive_l_follows_discovered_directory_symlink() -> None:
    # upstream: coreutils/tests/chmod/symlinks.sh
    # -L recursively changes a directory and file reached through a discovered symlink.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        tree = cwd / "tree"
        outside = cwd / "outside"
        tree.mkdir()
        outside.mkdir()
        child = outside / "child"
        _ = child.write_text("payload\n", encoding="utf-8")
        tree.chmod(0o755)
        outside.chmod(0o755)
        child.chmod(0o644)
        (tree / "link").symlink_to("../outside", target_is_directory=True)

        assert run_bench_chmod(["-L", "-R", "700", "tree"], cwd) == ("", "", 0)
        assert stat.S_IMODE(tree.stat().st_mode) == 0o700
        assert stat.S_IMODE(outside.stat().st_mode) == 0o700
        assert stat.S_IMODE(child.stat().st_mode) == 0o700


def test_recursive_l_no_dereference_traverses_symlink_children_only() -> None:
    # upstream: coreutils/tests/chmod/symlinks.sh
    # source-derived: coreutils/src/chmod.c FTS_LOGICAL traversal with dereference disabled.
    # -L traverses a top symlink while --no-dereference leaves its referent directory unchanged.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        target = cwd / "target"
        target.mkdir()
        child = target / "child"
        _ = child.write_text("payload\n", encoding="utf-8")
        target.chmod(0o755)
        child.chmod(0o644)
        top = cwd / "top"
        top.symlink_to("target", target_is_directory=True)

        assert run_bench_chmod(["-R", "-L", "--no-dereference", "700", "top"], cwd) == ("", "", 0)
        assert stat.S_IMODE(target.stat().st_mode) == 0o755
        assert stat.S_IMODE(child.stat().st_mode) == 0o700
        assert top.readlink() == Path("target")


def test_recursive_l_no_dereference_traverses_discovered_directory_children() -> None:
    # upstream: coreutils/tests/chmod/symlinks.sh
    # A discovered directory symlink under -L is not chmodded with -h, but its child is traversed.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        tree = cwd / "tree"
        outside = cwd / "outside"
        tree.mkdir()
        outside.mkdir()
        child = outside / "child"
        _ = child.write_text("payload\n", encoding="utf-8")
        tree.chmod(0o755)
        outside.chmod(0o755)
        child.chmod(0o644)
        (tree / "link").symlink_to("../outside", target_is_directory=True)

        assert run_bench_chmod(["-R", "-L", "--no-dereference", "700", "tree"], cwd) == ("", "", 0)
        assert stat.S_IMODE(tree.stat().st_mode) == 0o700
        assert stat.S_IMODE(outside.stat().st_mode) == 0o755
        assert stat.S_IMODE(child.stat().st_mode) == 0o700


def test_recursive_l_no_dereference_verbose_ignores_discovered_dangling_symlink() -> None:
    # upstream: coreutils/tests/chmod/symlinks.sh
    # source-derived: coreutils/src/chmod.c FTS_SLNONE with logical no-dereference traversal.
    # -L still treats a discovered dangling link as a verbose successful no-op under -h.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        tree = cwd / "tree"
        tree.mkdir()
        tree.chmod(0o700)
        dangle = tree / "dangle"
        dangle.symlink_to("../missing")

        assert run_bench_chmod(["-R", "-L", "--no-dereference", "-v", "700", "tree"], cwd) == (
            "mode of 'tree' retained as 0700 (rwx------)\n"
            "neither symbolic link 'tree/dangle' nor referent has been changed\n",
            "",
            0,
        )
        assert stat.S_IMODE(tree.stat().st_mode) == 0o700
        assert dangle.readlink() == Path("../missing")
        assert not dangle.exists()


def test_recursive_p_verbose_reports_top_level_symlink_not_applied() -> None:
    # upstream: coreutils/tests/chmod/symlinks.sh
    # -P leaves a command-line symlink referent unchanged and reports the no-op exactly.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        target = cwd / "target"
        target.mkdir()
        target.chmod(0o755)
        (cwd / "top").symlink_to("target", target_is_directory=True)

        assert run_bench_chmod(["-v", "-P", "-R", "700", "top"], cwd) == (
            "neither symbolic link 'top' nor referent has been changed\n",
            "",
            0,
        )
        assert stat.S_IMODE(target.stat().st_mode) == 0o755


def test_recursive_default_rejects_top_level_dangling_symlink() -> None:
    # upstream: coreutils/tests/chmod/thru-dangling.sh
    # Default recursive traversal diagnoses a dangling command-line symlink exactly.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        (cwd / "dangle").symlink_to("missing")

        assert run_bench_chmod(["-R", "700", "dangle"], cwd) == (
            "",
            "chmod: cannot operate on dangling symlink 'dangle'\n",
            1,
        )


def test_recursive_p_accepts_top_level_dangling_symlink() -> None:
    # upstream: coreutils/tests/chmod/symlinks.sh
    # -P treats a dangling command-line symlink as a successful no-op.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        dangle = cwd / "dangle"
        dangle.symlink_to("missing")

        assert run_bench_chmod(["-P", "-R", "700", "dangle"], cwd) == ("", "", 0)
        assert dangle.is_symlink()
        assert not dangle.exists()


def test_recursive_default_verbose_ignores_discovered_dangling_symlink() -> None:
    # upstream: coreutils/tests/chmod/symlinks.sh
    # A discovered dangling symlink is a successful verbose no-op under default traversal.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        tree = cwd / "tree"
        tree.mkdir()
        tree.chmod(0o700)
        (tree / "dangle").symlink_to("missing")

        assert run_bench_chmod(["-v", "-R", "700", "tree"], cwd) == (
            "mode of 'tree' retained as 0700 (rwx------)\n"
            "neither symbolic link 'tree/dangle' nor referent has been changed\n",
            "",
            0,
        )


def test_recursive_l_dangling_failure_continues_to_later_operand() -> None:
    # upstream: coreutils/tests/chmod/symlinks.sh
    # -L diagnoses a discovered dangling link but still changes the next operand.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        tree = cwd / "tree"
        tree.mkdir()
        tree.chmod(0o700)
        (tree / "dangle").symlink_to("missing")
        later = cwd / "later"
        _ = later.write_text("payload\n", encoding="utf-8")
        later.chmod(0o600)

        assert run_bench_chmod(["-L", "-R", "700", "tree", "later"], cwd) == (
            "",
            "chmod: cannot operate on dangling symlink 'tree/dangle'\n",
            1,
        )
        assert stat.S_IMODE(later.stat().st_mode) == 0o700


def test_recursive_self_symlink_loop_reports_eloop() -> None:
    # upstream: none - no pinned chmod runtime test covers recursive ELOOP handling.
    # source-derived: coreutils/src/chmod.c FTS_NS retry and errno diagnostic.
    # A command-line self symlink loop reports ELOOP without mutating the link.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        loop = cwd / "loop"
        loop.symlink_to("loop")

        assert run_bench_chmod(["-R", "700", "loop"], cwd) == (
            "",
            "chmod: cannot access 'loop': Too many levels of symbolic links\n",
            1,
        )
        assert loop.is_symlink()


# A recursive -h batch reports a followed symlink cycle after an earlier missing operand.
def test_recursive_no_dereference_cycle_failure_continues_after_missing_operand() -> None:
    # upstream: none - no pinned chmod runtime test covers this recursive symlink-cycle batch.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        cycle_a = cwd / "cycle-a"
        cycle_b = cwd / "cycle-b"
        cycle_a.symlink_to("cycle-b")
        cycle_b.symlink_to("cycle-a")
        before = {
            path.name: (stat.S_IMODE(path.lstat().st_mode), path.readlink())
            for path in (cycle_a, cycle_b)
        }

        assert run_bench_chmod(
            [
                "--no-dereference",
                "-R",
                "-7022",
                "sapze6f/hi91lg8c7n",
                "cycle-a",
            ],
            cwd,
        ) == (
            "",
            "chmod: cannot access 'sapze6f/hi91lg8c7n': No such file or directory\n"
            "chmod: cannot access 'cycle-a': Too many levels of symbolic links\n",
            1,
        )
        assert {
            path.name: (stat.S_IMODE(path.lstat().st_mode), path.readlink())
            for path in (cycle_a, cycle_b)
        } == before
        assert sorted(cwd.iterdir()) == [cycle_a, cycle_b]


def test_recursive_dotdot_after_symlink_uses_referent_parent() -> None:
    # upstream: none - no pinned chmod runtime test covers this symlink component lookup.
    # source-derived: coreutils/src/chmod.c passes the operand through FTS component lookup.
    # Dot-dot after a symlink selects the referent's parent rather than a lexical parent.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        outside = cwd / "outside"
        referent_parent = outside / "inner"
        target = outside / "target"
        target_child = target / "child"
        referent_parent.mkdir(parents=True)
        target.mkdir()
        _ = target_child.write_text("payload\n", encoding="utf-8")
        target.chmod(0o755)
        target_child.chmod(0o644)

        tree = cwd / "tree"
        decoy = tree / "target"
        decoy_child = decoy / "child"
        decoy.mkdir(parents=True)
        _ = decoy_child.write_text("payload\n", encoding="utf-8")
        decoy.chmod(0o755)
        decoy_child.chmod(0o644)
        (tree / "jump").symlink_to("../outside/inner", target_is_directory=True)

        assert run_bench_chmod(["-R", "700", "tree/jump/../target"], cwd) == ("", "", 0)
        assert stat.S_IMODE(target.stat().st_mode) == 0o700
        assert stat.S_IMODE(target_child.stat().st_mode) == 0o700
        assert stat.S_IMODE(decoy.stat().st_mode) == 0o755
        assert stat.S_IMODE(decoy_child.stat().st_mode) == 0o644


def test_recursive_l_two_link_cycle_terminates() -> None:
    # upstream: none - no pinned chmod runtime test covers this logical traversal cycle.
    # source-derived: coreutils/src/chmod.c FTS_DC and gl/lib/xfts.c cycle policy.
    # -L terminates across a two-directory symlink cycle and changes each real node.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        tree = cwd / "tree"
        left = tree / "left"
        right = tree / "right"
        left.mkdir(parents=True)
        right.mkdir()
        left_file = left / "file"
        right_file = right / "file"
        _ = left_file.write_text("left\n", encoding="utf-8")
        _ = right_file.write_text("right\n", encoding="utf-8")
        for path in [tree, left, right]:
            path.chmod(0o755)
        for path in [left_file, right_file]:
            path.chmod(0o644)
        (left / "to-right").symlink_to("../../tree/right", target_is_directory=True)
        (right / "to-left").symlink_to("../../tree/left", target_is_directory=True)

        assert run_bench_chmod(["-L", "-R", "700", "tree"], cwd) == ("", "", 0)
        assert all(
            stat.S_IMODE(path.stat().st_mode) == 0o700
            for path in [tree, left, right, left_file, right_file]
        )


def test_recursive_l_verbose_ancestor_cycle_is_retained() -> None:
    # upstream: none - no pinned chmod runtime test covers this logical ancestor cycle.
    # source-derived: coreutils/src/chmod.c FTS_DC and gl/lib/xfts.c logical-cycle policy.
    # -L reports an ancestor-cycle alias as retained after changing its real directories.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        tree = cwd / "tree"
        child = tree / "sub"
        child.mkdir(parents=True)
        tree.chmod(0o755)
        child.chmod(0o755)
        cycle = child / "up"
        cycle.symlink_to("..", target_is_directory=True)

        assert run_bench_chmod(["-R", "-L", "-v", "700", "tree"], cwd) == (
            "mode of 'tree' changed from 0755 (rwxr-xr-x) to 0700 (rwx------)\n"
            "mode of 'tree/sub' changed from 0755 (rwxr-xr-x) to 0700 (rwx------)\n"
            "mode of 'tree/sub/up' retained as 0700 (rwx------)\n",
            "",
            0,
        )
        assert stat.S_IMODE(tree.stat().st_mode) == 0o700
        assert stat.S_IMODE(child.stat().st_mode) == 0o700
        assert cycle.readlink() == Path("..")


def test_recursive_verbose_silent_failure_continues_to_tree() -> None:
    # upstream: coreutils/tests/chmod/partial-fail.sh
    # -vf suppresses a missing-path diagnostic but continues with later recursive nodes.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        tree = cwd / "tree"
        tree.mkdir()
        child = tree / "child"
        _ = child.write_text("payload\n", encoding="utf-8")
        tree.chmod(0o755)
        child.chmod(0o644)

        assert run_bench_chmod(["-v", "-f", "-R", "700", "missing", "tree"], cwd) == (
            "'missing' could not be accessed\n"
            "mode of 'tree' changed from 0755 (rwxr-xr-x) to 0700 (rwx------)\n"
            "mode of 'tree/child' changed from 0644 (rw-r--r--) to 0700 (rwx------)\n",
            "",
            1,
        )
        assert stat.S_IMODE(tree.stat().st_mode) == 0o700
        assert stat.S_IMODE(child.stat().st_mode) == 0o700


def test_recursive_repeated_operand_reports_changed_then_retained() -> None:
    # upstream: coreutils/tests/chmod/c-option.sh
    # source-derived: coreutils/src/chmod.c argv-order FTS traversal and describe_change.
    # A repeated recursive operand reports changed nodes before retained nodes.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        tree = cwd / "tree"
        tree.mkdir()
        child = tree / "child"
        _ = child.write_text("payload\n", encoding="utf-8")
        tree.chmod(0o755)
        child.chmod(0o644)

        assert run_bench_chmod(["-v", "-R", "700", "tree", "tree"], cwd) == (
            "mode of 'tree' changed from 0755 (rwxr-xr-x) to 0700 (rwx------)\n"
            "mode of 'tree/child' changed from 0644 (rw-r--r--) to 0700 (rwx------)\n"
            "mode of 'tree' retained as 0700 (rwx------)\n"
            "mode of 'tree/child' retained as 0700 (rwx------)\n",
            "",
            0,
        )


def test_recursive_last_changes_option_omits_retained_second_walk() -> None:
    # upstream: coreutils/tests/chmod/c-option.sh
    # A final -c overrides -v and omits retained reports from a repeated recursive walk.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        tree = cwd / "tree"
        tree.mkdir()
        child = tree / "child"
        _ = child.write_text("payload\n", encoding="utf-8")
        tree.chmod(0o755)
        child.chmod(0o644)

        assert run_bench_chmod(["-v", "-c", "-R", "700", "tree", "tree"], cwd) == (
            "mode of 'tree' changed from 0755 (rwxr-xr-x) to 0700 (rwx------)\n"
            "mode of 'tree/child' changed from 0644 (rw-r--r--) to 0700 (rwx------)\n",
            "",
            0,
        )


def test_multi_file_batch_changes_each_operand() -> None:
    # upstream: coreutils/tests/chmod/partial-fail.sh
    # A nonrecursive batch processes each valid operand in command-line order.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        for name in ["a", "b"]:
            path = cwd / name
            _ = path.write_text("payload\n", encoding="utf-8")
            path.chmod(0o644)

        assert run_bench_chmod(["600", "a", "b"], cwd) == ("", "", 0)
        assert stat.S_IMODE((cwd / "a").stat().st_mode) == 0o600
        assert stat.S_IMODE((cwd / "b").stat().st_mode) == 0o600


def test_duplicate_symbolic_operand_is_sequential() -> None:
    # upstream: coreutils/tests/chmod/equal-x.sh
    # A duplicate operand observes the mode written by its preceding occurrence.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        target = cwd / "file"
        _ = target.write_text("payload\n", encoding="utf-8")
        target.chmod(0o640)

        assert run_bench_chmod(["g=u,u=o", "file", "file"], cwd) == ("", "", 0)
        assert stat.S_IMODE(target.stat().st_mode) == 0o000


def test_partial_failure_continues_to_valid_operand() -> None:
    # upstream: coreutils/tests/chmod/partial-fail.sh
    # A missing prefix operand preserves failure while a later valid file is changed.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        target = cwd / "file"
        _ = target.write_text("payload\n", encoding="utf-8")
        target.chmod(0o644)

        assert run_bench_chmod(["0", "missing", "file"], cwd) == (
            "",
            "chmod: cannot access 'missing': No such file or directory\n",
            1,
        )
        assert stat.S_IMODE(target.stat().st_mode) == 0o000


def test_empty_operand_does_not_name_the_working_directory() -> None:
    # upstream: coreutils/tests/chmod/partial-fail.sh
    # An empty raw operand fails as an empty name instead of resolving to cwd.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        before = stat.S_IMODE(cwd.stat().st_mode)

        assert run_bench_chmod(["600", ""], cwd) == (
            "",
            "chmod: cannot access '': No such file or directory\n",
            1,
        )
        assert stat.S_IMODE(cwd.stat().st_mode) == before


def test_regular_file_with_trailing_slash_is_not_a_directory() -> None:
    # upstream: coreutils/tests/chmod/partial-fail.sh
    # A trailing slash retains directory syntax and rejects a regular file.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        target = cwd / "file"
        _ = target.write_text("payload\n", encoding="utf-8")
        target.chmod(0o644)

        assert run_bench_chmod(["600", "file/"], cwd) == (
            "",
            "chmod: cannot access 'file/': Not a directory\n",
            1,
        )
        assert stat.S_IMODE(target.stat().st_mode) == 0o644


def test_two_missing_operands_keep_diagnostic_order() -> None:
    # upstream: coreutils/tests/chmod/partial-fail.sh
    # Two failures are reported once each in original operand order.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert run_bench_chmod(["600", "missing-a", "missing-b"], cwd) == (
            "",
            "chmod: cannot access 'missing-a': No such file or directory\n"
            "chmod: cannot access 'missing-b': No such file or directory\n",
            1,
        )


def test_omitted_equals_respects_umask_when_clearing_classes() -> None:
    # upstream: coreutils/tests/chmod/umask-x.sh
    # An omitted-who equals clause clears and sets only classes allowed by umask.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        target = cwd / "file"
        _ = target.write_text("payload\n", encoding="utf-8")
        target.chmod(0o777)

        assert run_bench_chmod(["=rw", "file"], cwd, umask=0o027) == ("", "", 0)
        assert stat.S_IMODE(target.stat().st_mode) == 0o640


def test_symbolic_copy_chain_uses_each_updated_class() -> None:
    # upstream: coreutils/tests/chmod/equal-x.sh
    # Comma-separated copies observe the mode written by the preceding clause.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        target = cwd / "file"
        _ = target.write_text("payload\n", encoding="utf-8")
        target.chmod(0o640)

        assert run_bench_chmod(["u=rw,g=u,o=g", "file"], cwd) == ("", "", 0)
        assert stat.S_IMODE(target.stat().st_mode) == 0o666


def test_changes_reports_changed_mode_exactly() -> None:
    # upstream: coreutils/tests/chmod/c-option.sh
    # --changes emits one byte-exact report for a changed target.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        target = cwd / "file"
        _ = target.write_text("payload\n", encoding="utf-8")
        target.chmod(0o644)

        assert run_bench_chmod(["-c", "600", "file"], cwd) == (
            "mode of 'file' changed from 0644 (rw-r--r--) to 0600 (rw-------)\n",
            "",
            0,
        )


def test_changes_omits_retained_mode() -> None:
    # upstream: coreutils/tests/chmod/c-option.sh
    # --changes emits nothing for a successful no-op target.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        target = cwd / "file"
        _ = target.write_text("payload\n", encoding="utf-8")
        target.chmod(0o644)

        assert run_bench_chmod(["-c", "644", "file"], cwd) == ("", "", 0)


def test_verbose_reports_changed_mode_exactly() -> None:
    # upstream: coreutils/tests/chmod/c-option.sh
    # --verbose emits one byte-exact changed-mode report for a changed target.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        target = cwd / "file"
        _ = target.write_text("payload\n", encoding="utf-8")
        target.chmod(0o644)

        assert run_bench_chmod(["-v", "600", "file"], cwd) == (
            "mode of 'file' changed from 0644 (rw-r--r--) to 0600 (rw-------)\n",
            "",
            0,
        )
        assert stat.S_IMODE(target.stat().st_mode) == 0o600


# A verbose chmod of the current directory reports the normalized mode after removing search perm.
def test_verbose_reports_changed_mode_for_current_directory_exactly() -> None:
    # upstream: coreutils/tests/chmod/c-option.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        cwd.chmod(0o700)
        try:
            assert run_bench_chmod(["-v", "00644", "."], cwd) == (
                "mode of '.' changed from 0700 (rwx------) to 0644 (rw-r--r--)\n",
                "",
                0,
            )
            assert stat.S_IMODE(cwd.stat().st_mode) == 0o644
        finally:
            cwd.chmod(0o700)


# The iter1900 symbolic mode preserves GNU's post-lookup diagnostics after cwd loses search.
def test_iter1900_current_directory_search_loss_reports_post_lookup_denial() -> None:
    # upstream: none - no pinned chmod runtime test covers this post-lookup authorization loss.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        cwd.chmod(0o700)
        try:
            assert run_bench_chmod(["-v", "a-Xwtrs,ug=xsX,ugo-trX", "."], cwd) == (
                "mode of '.' retained as 6000 (--S--S---)\n",
                "chmod: getting new attributes of '.': Permission denied\n",
                0,
            )
            assert stat.S_IMODE(cwd.stat().st_mode) == 0o6000
        finally:
            cwd.chmod(0o700)


# A named terminal directory remains readable through its parent after the same mode change.
def test_symbolic_mode_for_named_directory_reports_changed_exactly() -> None:
    # upstream: coreutils/tests/chmod/c-option.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        target = cwd / "dir"
        target.mkdir()
        target.chmod(0o700)
        try:
            assert run_bench_chmod(["-v", "a-Xwtrs,ug=xsX,ugo-trX", "dir"], cwd) == (
                "mode of 'dir' changed from 0700 (rwx------) to 6000 (--S--S---)\n",
                "",
                0,
            )
            assert stat.S_IMODE(target.stat().st_mode) == 0o6000
        finally:
            target.chmod(0o700)


def test_verbose_reports_retained_mode_exactly() -> None:
    # upstream: coreutils/tests/chmod/c-option.sh
    # --verbose emits one byte-exact retained-mode report for a no-op target.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        target = cwd / "file"
        _ = target.write_text("payload\n", encoding="utf-8")
        target.chmod(0o644)

        assert run_bench_chmod(["-v", "644", "file"], cwd) == (
            "mode of 'file' retained as 0644 (rw-r--r--)\n",
            "",
            0,
        )


def test_reference_mode_copies_to_multiple_operands() -> None:
    # upstream: coreutils/tests/chmod/equal-x.sh
    # --reference resolves one initial mode and applies it to every later operand.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        reference = cwd / "ref"
        first = cwd / "a"
        second = cwd / "b"
        for path in [reference, first, second]:
            _ = path.write_text("payload\n", encoding="utf-8")
        reference.chmod(0o640)
        first.chmod(0o600)
        second.chmod(0o644)

        assert run_bench_chmod(["--reference=ref", "a", "b"], cwd) == ("", "", 0)
        assert stat.S_IMODE(first.stat().st_mode) == 0o640
        assert stat.S_IMODE(second.stat().st_mode) == 0o640


def test_reference_failure_precedes_recursive_rejection() -> None:
    # upstream: coreutils/tests/chmod/usage.sh
    # A missing reference is diagnosed before the deferred recursive branch is considered.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        target = cwd / "file"
        _ = target.write_text("payload\n", encoding="utf-8")
        target.chmod(0o644)

        assert run_bench_chmod(["-R", "--reference=missing", "file"], cwd) == (
            "",
            "chmod: failed to get attributes of 'missing': No such file or directory\n",
            1,
        )
        assert stat.S_IMODE(target.stat().st_mode) == 0o644


def test_missing_reference_ignores_silent_and_preserves_target() -> None:
    # upstream: coreutils/tests/chmod/usage.sh
    # A missing quoted reference bypasses -f and leaves the target untouched.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        target = cwd / "file"
        _ = target.write_text("payload\n", encoding="utf-8")
        target.chmod(0o644)

        assert run_bench_chmod(["-f", "--reference=a'b", "file"], cwd) == (
            "",
            'chmod: failed to get attributes of "a\'b": No such file or directory\n',
            1,
        )
        assert stat.S_IMODE(target.stat().st_mode) == 0o644


@pytest.mark.parametrize("mode", ["0-anything", "7-anything", "8"])
def test_invalid_octal_like_mode_is_rejected(mode: str) -> None:
    # upstream: coreutils/tests/chmod/octal.sh
    # Each malformed octal-like mode fails before mutating its target.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        target = cwd / "file"
        _ = target.write_text("payload\n", encoding="utf-8")
        target.chmod(0o644)

        assert run_bench_chmod([mode, "file"], cwd) == (
            "",
            f"chmod: invalid mode: '{mode}'\nTry 'chmod --help' for more information.\n",
            1,
        )
        assert stat.S_IMODE(target.stat().st_mode) == 0o644


def test_equal_x_replaces_regular_file_permissions() -> None:
    # upstream: coreutils/tests/chmod/equal-x.sh
    # =x clears non-execute bits and grants execute to every unmasked class.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        target = cwd / "file"
        _ = target.write_text("payload\n", encoding="utf-8")
        target.chmod(0o755)

        assert run_bench_chmod(["=x", "file"], cwd, umask=0o022) == ("", "", 0)
        assert stat.S_IMODE(target.stat().st_mode) == 0o111


def test_capital_x_does_not_add_execute_to_plain_file() -> None:
    # upstream: coreutils/tests/chmod/equal-x.sh
    # X leaves a non-executable regular file without execute bits.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        target = cwd / "file"
        _ = target.write_text("payload\n", encoding="utf-8")
        target.chmod(0o644)

        assert run_bench_chmod(["a+X", "file"], cwd) == ("", "", 0)
        assert stat.S_IMODE(target.stat().st_mode) == 0o644


def test_capital_x_adds_execute_to_directory() -> None:
    # upstream: coreutils/tests/chmod/equal-x.sh
    # X grants execute bits to a directory even when none were initially set.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        target = cwd / "dir"
        target.mkdir()
        target.chmod(0o644)

        assert run_bench_chmod(["a+X", "dir"], cwd) == ("", "", 0)
        assert stat.S_IMODE(target.stat().st_mode) == 0o755


def test_symbolic_setuid_bit_is_applied() -> None:
    # upstream: coreutils/tests/chmod/setgid.sh
    # u+s adds setuid without disturbing the ordinary file permissions.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        target = cwd / "file"
        _ = target.write_text("payload\n", encoding="utf-8")
        target.chmod(0o644)

        assert run_bench_chmod(["u+s", "file"], cwd) == ("", "", 0)
        assert stat.S_IMODE(target.stat().st_mode) == 0o4644


def test_symbolic_sticky_bit_is_applied() -> None:
    # upstream: coreutils/tests/chmod/setgid.sh
    # +t adds the sticky bit without disturbing ordinary directory permissions.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        target = cwd / "dir"
        target.mkdir()
        target.chmod(0o755)

        assert run_bench_chmod(["+t", "dir"], cwd) == ("", "", 0)
        assert stat.S_IMODE(target.stat().st_mode) == 0o1755


def test_symbolic_copy_uses_current_group_bits() -> None:
    # upstream: coreutils/tests/chmod/equal-x.sh
    # u=g copies the current group permission triad into the owner triad.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        target = cwd / "file"
        _ = target.write_text("payload\n", encoding="utf-8")
        target.chmod(0o640)

        assert run_bench_chmod(["u=g", "file"], cwd) == ("", "", 0)
        assert stat.S_IMODE(target.stat().st_mode) == 0o440


def test_valid_prefix_still_reports_later_failure() -> None:
    # upstream: coreutils/tests/chmod/partial-fail.sh
    # A valid prefix is changed before a later missing operand makes the batch fail.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        target = cwd / "file"
        _ = target.write_text("payload\n", encoding="utf-8")
        target.chmod(0o644)

        assert run_bench_chmod(["0", "file", "missing"], cwd) == (
            "",
            "chmod: cannot access 'missing': No such file or directory\n",
            1,
        )
        assert stat.S_IMODE(target.stat().st_mode) == 0o000


def test_option_like_mode_cannot_combine_with_reference() -> None:
    # upstream: coreutils/tests/chmod/usage.sh
    # A recovered option-like mode and --reference fail before touching a target.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        reference = cwd / "ref"
        target = cwd / "file"
        for path in [reference, target]:
            _ = path.write_text("payload\n", encoding="utf-8")
        reference.chmod(0o600)
        target.chmod(0o644)

        assert run_bench_chmod(["-w", "--reference=ref", "file"], cwd) == (
            "",
            "chmod: cannot combine mode and --reference options\n"
            "Try 'chmod --help' for more information.\n",
            1,
        )
        assert stat.S_IMODE(target.stat().st_mode) == 0o644


def test_verbose_missing_file_reports_both_streams() -> None:
    # upstream: coreutils/tests/chmod/partial-fail.sh
    # --verbose emits its access status on stdout and the exact error on stderr.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert run_bench_chmod(["-v", "600", "missing"], cwd) == (
            "'missing' could not be accessed\n",
            "chmod: cannot access 'missing': No such file or directory\n",
            1,
        )


def test_verbose_silent_failure_keeps_stdout_and_status() -> None:
    # upstream: coreutils/tests/chmod/partial-fail.sh
    # -vf suppresses the diagnostic but retains verbose access output and failure status.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert run_bench_chmod(["-v", "-f", "600", "missing"], cwd) == (
            "'missing' could not be accessed\n",
            "",
            1,
        )


def test_last_verbose_option_overrides_changes() -> None:
    # upstream: coreutils/tests/chmod/c-option.sh
    # The last -v occurrence overrides -c and reports a retained mode.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        target = cwd / "file"
        _ = target.write_text("payload\n", encoding="utf-8")
        target.chmod(0o644)

        assert run_bench_chmod(["-c", "-v", "644", "file"], cwd) == (
            "mode of 'file' retained as 0644 (rw-r--r--)\n",
            "",
            0,
        )


def test_last_changes_option_overrides_verbose() -> None:
    # upstream: coreutils/tests/chmod/c-option.sh
    # The last -c occurrence overrides -v and omits a retained-mode report.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        target = cwd / "file"
        _ = target.write_text("payload\n", encoding="utf-8")
        target.chmod(0o644)

        assert run_bench_chmod(["-v", "-c", "644", "file"], cwd) == ("", "", 0)


def test_verbose_apostrophe_path_uses_quoteaf() -> None:
    # upstream: coreutils/tests/chmod/c-option.sh
    # Verbose reports use quoteaf's double-quoted apostrophe form byte-for-byte.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        target = cwd / "a'b"
        _ = target.write_text("payload\n", encoding="utf-8")
        target.chmod(0o644)

        assert run_bench_chmod(["-v", "644", "a'b"], cwd) == (
            'mode of "a\'b" retained as 0644 (rw-r--r--)\n',
            "",
            0,
        )


def test_verbose_tab_path_uses_quoteaf_on_both_streams() -> None:
    # upstream: coreutils/tests/chmod/partial-fail.sh
    # A missing tabbed path is ANSI-C quoted identically on stdout and stderr.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert run_bench_chmod(["-v", "600", "a\tb"], cwd) == (
            "'a'$'\\t''b' could not be accessed\n",
            "chmod: cannot access 'a'$'\\t''b': No such file or directory\n",
            1,
        )


def test_invalid_unicode_mode_uses_c_locale_quote() -> None:
    # upstream: coreutils/tests/chmod/octal.sh
    # Invalid Unicode mode text is emitted as exact C-locale UTF-8 octal escapes.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        target = cwd / "file"
        _ = target.write_text("payload\n", encoding="utf-8")
        target.chmod(0o644)

        assert run_bench_chmod(["é", "file"], cwd) == (
            "",
            "chmod: invalid mode: '\\303\\251'\nTry 'chmod --help' for more information.\n",
            1,
        )
        assert stat.S_IMODE(target.stat().st_mode) == 0o644


def test_surprise_colon_path_uses_colon_forced_quotef() -> None:
    # upstream: coreutils/tests/chmod/umask-x.sh
    # A surprise diagnostic quotes a colon-bearing path before its delimiter.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        target = cwd / "a:b"
        _ = target.write_text("payload\n", encoding="utf-8")
        target.chmod(0o666)

        assert run_bench_chmod(["-w", "a:b"], cwd, umask=0o022) == (
            "",
            "chmod: 'a:b': new permissions are r--rw-rw-, not r--r--r--\n",
            1,
        )
        assert stat.S_IMODE(target.stat().st_mode) == 0o466


def test_mode_without_operand_names_the_mode() -> None:
    # upstream: coreutils/tests/chmod/usage.sh
    # An ordinary positional mode without a file identifies that mode in the diagnostic.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert run_bench_chmod(["755"], cwd) == (
            "",
            "chmod: missing operand after '755'\nTry 'chmod --help' for more information.\n",
            1,
        )


def test_help_output_is_byte_exact() -> None:
    # upstream: none - benchmark pins the CLI help contract beyond upstream shell coverage.
    # Source-derived GNU help is stdout-only and cannot mutate an unrelated file.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        sentinel = cwd / "sentinel"
        _ = sentinel.write_text("payload\n", encoding="utf-8")
        sentinel.chmod(0o640)

        stdout, stderr, exit_code = run_bench_chmod(["--help"], cwd)

        output = stdout.encode("utf-8")
        assert (stdout, stderr, exit_code) == (CHMOD_HELP_TEXT, "", 0)
        assert len(output) == 1945
        assert hashlib.sha256(output).hexdigest() == CHMOD_HELP_SHA256
        assert stat.S_IMODE(sentinel.stat().st_mode) == 0o640


def test_version_output_is_byte_exact() -> None:
    # upstream: none - benchmark pins the CLI version contract beyond upstream shell coverage.
    # The certified GNU oracle fixes exact version bytes without assuming its source version.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        sentinel = cwd / "sentinel"
        _ = sentinel.write_text("payload\n", encoding="utf-8")
        sentinel.chmod(0o640)

        stdout, stderr, exit_code = run_bench_chmod(["--version"], cwd)
        oracle = run_coreutils_utility(COREUTILS_CHMOD, "chmod", ["--version"], cwd)

        output = stdout.encode("utf-8")
        assert (output, stderr.encode("utf-8"), exit_code) == oracle
        assert (stdout, stderr, exit_code) == (CHMOD_VERSION_TEXT, "", 0)
        assert len(output) == 333
        assert hashlib.sha256(output).hexdigest() == CHMOD_VERSION_SHA256
        assert stat.S_IMODE(sentinel.stat().st_mode) == 0o640


def test_reference_option_requires_an_argument_exactly() -> None:
    # upstream: none - no pinned chmod runtime test covers this exact long-option diagnostic.
    # A missing --reference value uses getopt's exact required-argument diagnostic.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert run_bench_chmod(["--reference"], cwd) == (
            "",
            "chmod: option '--reference' requires an argument\n"
            "Try 'chmod --help' for more information.\n",
            1,
        )


@pytest.mark.parametrize("option", ["--help=x", "--version=x"])
def test_no_argument_meta_option_rejects_a_value_exactly(option: str) -> None:
    # upstream: none - no pinned chmod runtime test covers attached meta-option values.
    # Each no-argument meta option rejects an attached value before any filesystem action.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        name = option[2 : option.index("=")]
        assert run_bench_chmod([option], cwd) == (
            "",
            f"chmod: option '--{name}' doesn't allow an argument\n"
            "Try 'chmod --help' for more information.\n",
            1,
        )


def test_ambiguous_reference_prefix_lists_candidates_exactly() -> None:
    # upstream: none - no pinned chmod runtime test covers this long-option ambiguity output.
    # The shared --re prefix names both matching GNU long options in declaration order.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert run_bench_chmod(["--re"], cwd) == (
            "",
            "chmod: option '--re' is ambiguous; possibilities: "
            "'--recursive' '--reference'\n"
            "Try 'chmod --help' for more information.\n",
            1,
        )


def test_bundled_invalid_short_option_names_the_bad_character() -> None:
    # upstream: none - no pinned chmod runtime test covers this bundled-option diagnostic.
    # A valid bundled prefix does not hide the exact later invalid short option.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        target = cwd / "file"
        _ = target.write_text("payload\n", encoding="utf-8")
        target.chmod(0o640)

        assert run_bench_chmod(["-vZ", "600", "file"], cwd) == (
            "",
            "chmod: invalid option -- 'Z'\nTry 'chmod --help' for more information.\n",
            1,
        )
        assert stat.S_IMODE(target.stat().st_mode) == 0o640


def test_empty_reference_is_a_reference_lookup_failure() -> None:
    # upstream: none - no pinned chmod runtime test covers an empty reference operand.
    # --reference= looks up the empty path instead of treating the target as a mode.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        target = cwd / "file"
        _ = target.write_text("payload\n", encoding="utf-8")
        target.chmod(0o640)

        assert run_bench_chmod(["--reference=", "file"], cwd) == (
            "",
            "chmod: failed to get attributes of '': No such file or directory\n",
            1,
        )
        assert stat.S_IMODE(target.stat().st_mode) == 0o640


@pytest.mark.parametrize("option", ["--refe", "--refer", "--referenc"])
def test_reference_abbreviation_requires_an_argument_exactly(option: str) -> None:
    # upstream: none - no pinned chmod runtime test covers abbreviated reference diagnostics.
    # Each unambiguous --reference prefix reports the canonical GNU option name.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert run_bench_chmod([option], cwd) == (
            "",
            "chmod: option '--reference' requires an argument\n"
            "Try 'chmod --help' for more information.\n",
            1,
        )


@pytest.mark.parametrize(
    ("option", "canonical"),
    [
        pytest.param("--he=x", "help", id="help-prefix"),
        pytest.param("--vers=x", "version", id="version-prefix"),
        pytest.param("--rec=x", "recursive", id="recursive-prefix"),
        pytest.param("--q=x", "quiet", id="quiet-prefix"),
    ],
)
def test_no_argument_abbreviation_rejects_a_value_exactly(
    option: str,
    canonical: str,
) -> None:
    # upstream: none - no pinned chmod runtime test covers abbreviated meta-option values.
    # Each unique long-option prefix names its canonical GNU option in the diagnostic.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert run_bench_chmod([option], cwd) == (
            "",
            f"chmod: option '--{canonical}' doesn't allow an argument\n"
            "Try 'chmod --help' for more information.\n",
            1,
        )


@pytest.mark.parametrize(
    ("option", "possibilities"),
    [
        pytest.param("--re=x", "'--recursive' '--reference'", id="recursive-reference"),
        pytest.param("--ver=x", "'--verbose' '--version'", id="verbose-version"),
        pytest.param(
            "--no",
            "'--no-dereference' '--no-preserve-root'",
            id="no-prefix",
        ),
        pytest.param(
            "--=x",
            "'--changes' '--dereference' '--recursive' '--no-dereference' "
            "'--no-preserve-root' '--preserve-root' '--quiet' '--reference' "
            "'--silent' '--verbose' '--help' '--version'",
            id="empty-prefix",
        ),
    ],
)
def test_ambiguous_long_option_lists_all_candidates_exactly(
    option: str,
    possibilities: str,
) -> None:
    # upstream: none - no pinned chmod runtime test covers long-option ambiguity output.
    # Each ambiguous long prefix lists every matching GNU option in declaration order.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert run_bench_chmod([option], cwd) == (
            "",
            f"chmod: option '{option}' is ambiguous; possibilities: {possibilities}\n"
            "Try 'chmod --help' for more information.\n",
            1,
        )


@pytest.mark.parametrize(
    ("args", "expected_stderr"),
    [
        pytest.param(
            ["-w", "--help=x", "file"],
            "chmod: option '--help' doesn't allow an argument\n"
            "Try 'chmod --help' for more information.\n",
            id="unexpected-help-value",
        ),
        pytest.param(
            ["-w", "--re", "file"],
            "chmod: option '--re' is ambiguous; possibilities: "
            "'--recursive' '--reference'\n"
            "Try 'chmod --help' for more information.\n",
            id="ambiguous-long-option",
        ),
        pytest.param(
            ["-w", "-vZ", "file"],
            "chmod: invalid option -- 'Z'\nTry 'chmod --help' for more information.\n",
            id="invalid-bundled-short",
        ),
    ],
)
def test_option_like_mode_does_not_hide_later_parse_error(
    args: list[str],
    expected_stderr: str,
) -> None:
    # upstream: coreutils/tests/chmod/usage.sh
    # A valid option-like mode prefix never converts a later parse failure into an operand.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        target = cwd / "file"
        _ = target.write_text("payload\n", encoding="utf-8")
        target.chmod(0o640)

        assert run_bench_chmod(args, cwd) == ("", expected_stderr, 1)
        assert stat.S_IMODE(target.stat().st_mode) == 0o640


@pytest.mark.parametrize(
    ("args", "expected_stdout", "expected_stderr", "expected_exit"),
    [
        pytest.param(["--help", "-Z"], CHMOD_HELP_TEXT, "", 0, id="help-first"),
        pytest.param(
            ["--help", "--reference"],
            CHMOD_HELP_TEXT,
            "",
            0,
            id="help-before-missing-reference-value",
        ),
        pytest.param(["--version", "-Z"], CHMOD_VERSION_TEXT, "", 0, id="version-first"),
        pytest.param(
            ["-Z", "--help"],
            "",
            "chmod: invalid option -- 'Z'\nTry 'chmod --help' for more information.\n",
            1,
            id="error-before-help",
        ),
        pytest.param(
            ["-Z", "--version"],
            "",
            "chmod: invalid option -- 'Z'\nTry 'chmod --help' for more information.\n",
            1,
            id="error-before-version",
        ),
    ],
)
def test_meta_option_parse_error_precedence(
    args: list[str],
    expected_stdout: str,
    expected_stderr: str,
    expected_exit: int,
) -> None:
    # upstream: none - no pinned chmod runtime test covers these meta-option precedence cases.
    # The first decisive meta request or parse error determines the exact GNU outcome.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert run_bench_chmod(args, cwd) == (
            expected_stdout,
            expected_stderr,
            expected_exit,
        )


@pytest.mark.parametrize(
    ("args", "expected_stdout"),
    [
        pytest.param(["--version", "--help"], CHMOD_VERSION_TEXT, id="version-first"),
        pytest.param(["--help", "--version"], CHMOD_HELP_TEXT, id="help-first"),
    ],
)
def test_meta_option_token_order(args: list[str], expected_stdout: str) -> None:
    # upstream: none - no pinned chmod runtime test covers meta-option token ordering.
    # The first successful meta option determines the exact stdout payload.
    with tempfile.TemporaryDirectory() as tmp_dir:
        assert run_bench_chmod(args, Path(tmp_dir)) == (expected_stdout, "", 0)


def test_non_ascii_long_option_diagnostic_is_exact() -> None:
    # upstream: none - no pinned chmod runtime test covers non-ASCII long-option diagnostics.
    # An unknown Unicode long option survives parsing and diagnostic rendering unchanged.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        result = run_bench_chmod_bytes(["--é"], cwd)
        assert result == run_coreutils_utility(COREUTILS_CHMOD, "chmod", ["--é"], cwd)
        assert result == (
            b"",
            b"chmod: unrecognized option '--\xc3\xa9'\nTry 'chmod --help' for more information.\n",
            1,
        )


def test_non_ascii_short_option_diagnostic_uses_first_utf8_byte() -> None:
    # upstream: none - no pinned chmod runtime test covers non-ASCII short-option diagnostics.
    # GNU identifies an invalid short Unicode rune by its first encoded byte only.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        result = run_bench_chmod_bytes(["-é"], cwd)
        assert result == run_coreutils_utility(COREUTILS_CHMOD, "chmod", ["-é"], cwd)
        assert result == (
            b"",
            b"chmod: invalid option -- '\xc3'\nTry 'chmod --help' for more information.\n",
            1,
        )


@pytest.mark.parametrize(
    ("args", "missing", "expected_files", "expected_mode", "expected_stderr"),
    USAGE_SCENARIOS,
)
def test_upstream_usage_argument_allocation(
    args: list[str],
    missing: str | None,
    expected_files: list[str],
    expected_mode: int,
    expected_stderr: str,
) -> None:
    # upstream: coreutils/tests/chmod/usage.sh
    # Each usage.sh row identifies exactly the operands attempted by one invocation.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        created = ["--", "-w", "f"] if not expected_files else expected_files
        for name in created:
            if name == missing:
                continue
            target = cwd / name
            _ = target.write_text("payload\n", encoding="utf-8")
            target.chmod(0o644)

        stdout, stderr, exit_code = run_bench_chmod(args, cwd, umask=0o022)

        expected_success = bool(expected_files) and missing is None
        assert stdout == ""
        assert stderr == expected_stderr
        assert exit_code == (0 if expected_success else 1)
        for name in ["--", "-w", "f"]:
            target = cwd / name
            if name in expected_files and name != missing:
                assert stat.S_IMODE(target.stat().st_mode) == expected_mode
            elif not expected_files:
                assert stat.S_IMODE(target.stat().st_mode) == 0o644
            else:
                assert not target.exists()


@pytest.mark.parametrize(("source", "destination", "expected_mode"), EQUALS_CASES)
def test_upstream_equals_copies_one_permission_class(
    source: str,
    destination: str,
    expected_mode: int,
) -> None:
    # upstream: coreutils/tests/chmod/equals.sh
    # Each equals.sh direction copies one source triad and clears the source afterward.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        target = cwd / "f"
        _ = target.write_text("payload\n", encoding="utf-8")
        target.chmod(0o644)
        mode = f"a=,{source}=rwx,{destination}={source},{source}="

        assert run_bench_chmod([mode, "f"], cwd) == ("", "", 0)
        assert stat.S_IMODE(target.stat().st_mode) == expected_mode


def test_upstream_omitted_equals_copies_owner_under_umask() -> None:
    # upstream: coreutils/tests/chmod/equals.sh
    # equals.sh =u copies owner bits only to classes allowed by umask 027.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        target = cwd / "f"
        _ = target.write_text("payload\n", encoding="utf-8")

        assert run_bench_chmod(["a=,u=rwx,=u", "f"], cwd, umask=0o027) == (
            "",
            "",
            0,
        )
        assert stat.S_IMODE(target.stat().st_mode) == 0o750


def test_no_x_o_equals_r_pure_mode_semantics() -> None:
    # upstream: coreutils/tests/chmod/no-x.sh
    # The no-x.sh o=r transformation is covered without credential-sensitive traversal.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        target = cwd / "d"
        target.mkdir()
        target.chmod(0o600)

        assert run_bench_chmod(["o=r", "d"], cwd) == ("", "", 0)
        assert stat.S_IMODE(target.stat().st_mode) == 0o604


def test_no_x_a_minus_x_pure_mode_semantics() -> None:
    # upstream: coreutils/tests/chmod/no-x.sh
    # The no-x.sh a-x transformation is covered without cwd search authorization.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        target = cwd / "a"
        target.mkdir()
        target.chmod(0o777)

        assert run_bench_chmod(["a-x", "a"], cwd) == ("", "", 0)
        assert stat.S_IMODE(target.stat().st_mode) == 0o666


@pytest.mark.parametrize("mode", EQUAL_X_MODES)
def test_upstream_equal_x_respects_umask(mode: str) -> None:
    # upstream: coreutils/tests/chmod/equal-x.sh
    # Each equal-x.sh expression leaves only owner and group execute under umask 005.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        target = cwd / "f"
        _ = target.write_text("payload\n", encoding="utf-8")

        assert run_bench_chmod([f"a=r,{mode}", "f"], cwd, umask=0o005) == (
            "",
            "",
            0,
        )
        assert stat.S_IMODE(target.stat().st_mode) == 0o110


@pytest.mark.parametrize(("mode", "expected_mode"), SETGID_CASES)
def test_upstream_directory_setgid_rows(mode: str, expected_mode: int) -> None:
    # upstream: coreutils/tests/chmod/setgid.sh
    # Each setgid.sh row starts from directory mode 2755 and applies one GNU mode expression.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        target = cwd / "d"
        target.mkdir()
        target.chmod(0o2755)
        if stat.S_IMODE(target.stat().st_mode) != 0o2755:
            pytest.skip("filesystem does not retain setgid on this directory")

        assert run_bench_chmod([mode, "d"], cwd, umask=0) == ("", "", 0)
        assert stat.S_IMODE(target.stat().st_mode) == expected_mode


# Verify each affected module and entry independently; builds do not verify dependencies.
@pytest.mark.dafny_verify
@pytest.mark.parametrize(
    "source_name",
    (
        "ChmodSpec.dfy",
        "ChmodCore.dfy",
        "ChmodProof.dfy",
        "ChmodRecursiveSpec.dfy",
        "ChmodRecursiveCore.dfy",
        "ChmodRecursiveProof.dfy",
        "ChmodRecursiveLeafRuntime.dfy",
        "ChmodRecursiveRuntime.dfy",
        "Chmod.dfy",
        "ChmodCli.dfy",
    ),
)
def test_chmod_source_verifies(source_name: str) -> None:
    # upstream: none - repository-local Dafny verification check
    run_dafny_verify(
        ROOT / "bench" / "utils" / "chmod" / source_name,
        extra_flags=("--cores:1", "--verification-time-limit:30"),
    )
