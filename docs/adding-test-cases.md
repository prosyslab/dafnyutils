# Port GNU tests into a utility's Tests.py

Add a test by translating one upstream GNU scenario into a Python test in `bench/utils/<utility>/Tests.py`. Reuse that file's fixture and runner helpers, execute the pinned GNU binary and the Dafny binary, and compare stdout, stderr and exit status.

This guide uses `bench/utils/comm/Tests.py`. Its upstream source is `coreutils/tests/misc/comm.pl`, a Perl test table. The same process applies to shell tests and other utilities. Start with a scenario, preserve its behavior, and express its setup and assertions in Python.

## Contents

- [Prepare the environment and find the source](#prepare-the-environment-and-find-the-source)
- [Start a new utility test file](#start-a-new-utility-test-file)
- [Translate one upstream scenario](#translate-one-upstream-scenario)
  - [Read the upstream case](#read-the-upstream-case)
  - [Reuse the existing adapter helpers](#reuse-the-existing-adapter-helpers)
  - [Add the Python function](#add-the-python-function)
- [Port an error case too](#port-an-error-case-too)
- [Record the upstream source and supported behavior](#record-the-upstream-source-and-supported-behavior)
- [Run the port and inspect its result](#run-the-port-and-inspect-its-result)
  - [Run the new case](#run-the-new-case)
  - [Run the utility suite and record evidence](#run-the-utility-suite-and-record-evidence)
- [When to use the fuzzer guide](#when-to-use-the-fuzzer-guide)

## Prepare the environment and find the source

Use the [setup guide](../README.md#setup). Run commands below in Bash or zsh from `/workspace/dafnyutils`, inside the prepared contributor container. Python tests launch the GNU executable and .NET program through the existing helpers in that environment; they do not start the Rust fuzzer or its Compose service.

```sh
# Expected duration: Estimated < 1 sec; searches the local upstream checkout.
# Success criteria: Exit 0 and the upstream comm test path is listed.
rg --files coreutils/tests | rg '(^|/)comm([./-]|$)'
```

This finds the source even when a utility has no dedicated test directory. For `comm`, the result is:

```text
coreutils/tests/misc/comm.pl
```

Read [comm.pl](../coreutils/tests/misc/comm.pl), [Tests.py](../bench/utils/comm/Tests.py), and the [supported comm scope](../bench/utils/comm/comm.md) together. Check upstream case names against existing Python functions and parameter rows before adding anything. `comm.pl` covers more GNU behavior than this benchmark currently implements.

The current adapter already covers basic columns, delimiters, totals, several NUL modes and operand errors. Its NUL-mode parameter table does not contain the `-z -2` combination used below. If a later revision already covers it, extend or improve the existing test instead of duplicating it.

## Start a new utility test file

`python3 -m benchmarks init --kind coreutils --id base32` creates a `Tests.py`
with shared runner imports, an `executables` fixture, and `assert_parity`.
The fixture builds the pinned GNU binary and the utility DLL. Proof-only tests
do not request this fixture, so they need no executable build.

Replace `test_gnu_parity`, which deliberately fails, with a concrete case. For
the base32 encoding scope, a small stdin case can use the generated helpers:

```python
# Encode one byte from stdin with the default GNU wrapping behavior.
def test_encodes_one_byte(executables: tuple[Path, Path], tmp_path: Path) -> None:
    # upstream: coreutils/tests/basenc/base64.pl
    # Port inout1; this upstream file tests both base32 and base64.
    assert_parity(executables, [], tmp_path, input_data=b"a")
```

Check that upstream path and the accepted scope against your pinned checkout.
`assert_parity` compares stdout, stderr and status exactly, including stderr on
failure. The shared lower-level comparison helper ignores error stderr by default;
pass `ignore_stderr_when_exit_nonzero=False` for a strict comparison.
Add malformed-input and partial-effect cases separately. For filesystem-changing
commands, replace the read-only helper with separate equivalent fixture trees and
compare filesystem effects as well as the returned streams/status.

Keep the generated `test_verify_module` and its `@pytest.mark.dafny_verify` marker.
It verifies Entry, Core and Proof through `run_dafny_verify`. Add any new proof
modules to its parameter list. The final gate runs this selection explicitly:

```sh
python3 -m pytest -q -n0 --import-mode=importlib -m dafny_verify \
  bench/utils/base32/Tests.py
```

Expected summary after completing the three generated proof targets, exit 0:

```text
3 passed, <runtime-case-count> deselected in <seconds>s
```

On an untouched scaffold, expect proof failures and exit 1. If all marked cases
are missing, pytest instead exits 5:

```text
<runtime-case-count> deselected in <seconds>s
```

An unchanged scaffold is expected to fail verification. A completed utility must
pass both this selection and `make -C bench/utils/base32 verify`; selecting no
marked tests exits 5 and is not a pass. Replace the separate placeholder in
`Tests.dfy` with an executable Core behavior case too.

## Translate one upstream scenario

### Read the upstream case

Choose `zopt-2` in `comm.pl`: compare NUL-delimited records and suppress the column unique to the second file. The upstream fixture ends both inputs without a final NUL. Keep that detail; adding a final terminator changes the input being tested.

| Upstream part | Meaning | Python representation |
| --- | --- | --- |
| Case name `zopt-2` | Identity of the scenario being ported | Mention it in a test comment and the PR |
| `@zinputs`, file `za` | First sorted input | `b"1\x003\x003\x003"` |
| `@zinputs`, file `zb` | Second sorted input | `b"2\x002\x003\x003\x003"` |
| `'-z', '-2'` | NUL records; suppress file-2-only output | `["-z", "-2", "za", "zb"]` |
| `OUT` | File-1-only `1`, then three common `3` records | `b"1\x00\t3\x00\t3\x00\t3\x00"` |
| No `ERR` or `EXIT` override | Empty stderr and normal exit 0 | `(expected_stdout, b"", 0)` |

`\x00` is one NUL byte and `\t` is one tab. With column 2 suppressed, common records use one leading tab rather than two. The case can catch a program that removes the wrong column, retains the old indentation, or uses newline output in NUL mode.

Upstream `IN` declarations create named files and supply their names as operands. A Perl table string containing multiple options, such as `'--total --output-delimiter='`, must become separate argv entries in Python. Do not pass it as one argument or introduce `shell=True`.

### Reuse the existing adapter helpers

The complete test below belongs in `bench/utils/comm/Tests.py`, next to the existing NUL-mode tests. That module already imports `Path` and the comparison helper. Its autouse build fixture checks the GNU and Dafny artifacts before a runtime test.

| Existing name | What it does |
| --- | --- |
| `write_comm_nul_inputs(cwd)` | Writes `za` and `zb` with the exact upstream bytes shown above |
| `run_system_comm(args, cwd, input_data=...)` | Runs the pinned `_build/coreutils/src/comm` reference |
| `run_bench_comm(args, cwd, input_data=...)` | Runs `_build/bench/comm_bench.dll` through the shared candidate runner |
| `assert_result_matches_reference(reference, candidate, ignore_stderr_when_exit_nonzero=False)` | Compares the returned stdout/stderr/status tuples, including error stderr |
| `assert_comm_parity(args, cwd, input_data=...)` | Convenience wrapper that runs and compares both programs |

The runners return `(stdout: bytes, stderr: bytes, exit_code: int)` and use the shared C-locale/UTC0 environment and timeout. Do not replace the pinned reference with whatever `comm` happens to be on `PATH`.

This example uses the two runner calls explicitly so it can also check the upstream expected result. When only parity is needed, use `assert_comm_parity(args, tmp_path)` with its default stderr checking.

### Add the Python function

Append this complete function to the existing module; do not replace the file or copy its helpers into a new framework:

```python
# Suppress file-2-only NUL records while preserving common-column tabs and terminators.
def test_zero_terminated_suppress_second_column_matches_coreutils(tmp_path: Path) -> None:
    # upstream: coreutils/tests/misc/comm.pl
    # Port zopt-2, including the final unterminated record in each input.
    write_comm_nul_inputs(tmp_path)
    args = ["-z", "-2", "za", "zb"]

    reference = run_system_comm(args, tmp_path)
    candidate = run_bench_comm(args, tmp_path)

    assert reference == (b"1\x00\t3\x00\t3\x00\t3\x00", b"", 0)
    assert_result_matches_reference(reference, candidate, ignore_stderr_when_exit_nonzero=False)
```

`tmp_path` is pytest's temporary-directory fixture, so this test needs no new import or manual cleanup. Both programs can read the same fixture here because `comm` does not change file contents. For a mutating utility, prepare separate equivalent reference/candidate trees and compare the relevant filesystem effects using that utility's existing helpers.

The first assertion confirms that the reference and ported inputs reproduce the upstream scenario. The second is the differential assertion: it checks the actual Dafny result against the actual GNU result. Keep both streams as bytes; do not decode, strip whitespace, sort lines or discard stderr to make the test pass.

## Port an error case too

Preserve upstream failures as failures, including diagnostic bytes and exit status. `missing-arg2` in `comm.pl` passes no operands and expects an empty stdout, a specific stderr and status 1.

The current `test_operand_count_diagnostics_match_coreutils` already covers `args=[]`. The function below shows the error-port pattern; use it to refine or replace that scenario if exact upstream assertions are wanted. Do not add it as a redundant second permanent test.

```python
# Report the GNU missing-operand diagnostic when neither input file is supplied.
def test_missing_operands_match_upstream_comm(tmp_path: Path) -> None:
    # upstream: coreutils/tests/misc/comm.pl
    # Port missing-arg2; no fixture files or stdin are needed.
    reference = run_system_comm([], tmp_path)
    candidate = run_bench_comm([], tmp_path)

    expected_stderr = (
        b"comm: missing operand\n"
        b"Try 'comm --help' for more information.\n"
    )
    assert reference == (b"", expected_stderr, 1)
    assert_result_matches_reference(reference, candidate, ignore_stderr_when_exit_nonzero=False)
```

Keep success and failure scenarios in separate tests. Use parameterization only for related variants; put the intention comment above the decorators and give variants readable IDs when useful. For stdin scenarios, pass the same `input_data` bytes to both helpers so each process receives its own input.

## Record the upstream source and supported behavior

Place a one-line intention comment above the test. Put the exact `# upstream: coreutils/tests/misc/comm.pl` marker **inside** its body, and put the case name on a separate comment line. The [marker reader](../tools/bench/upstream_markers.py) requires that location and accepts a path, not a path plus a free-text case label.

Record the pinned GNU revision and case name in the PR. Preserve copyright and license notices if copying upstream source; adapting a scenario is not a reason to remove attribution. The example's source revision is `2cf491412c199e2211880ec3f4ba387026638a33`.

Map the parts of any other upstream test in the same way:

| Upstream setup/assertion | Python port |
| --- | --- |
| File bytes, modes, directories or links | Recreate exactly under a temporary fixture, using existing utility helpers |
| Arguments and stdin | Preserve operand order, option spelling and raw input bytes |
| `OUT`, `ERR`, `EXIT`, or shell comparisons | Check expected reference behavior, then compare both actual executions |
| Locale, timezone, user or filesystem prerequisites | Check the shared runner environment and supported scope; document any required setup |
| A named upstream case or shell block | Put the source path inside the test and name the scenario separately |

GNU's `ooo*` sortedness cases and `--check-order`/`--nocheck-order` are deferred in this `comm` slice. Repeated stdin also has a benchmark-specific diagnostic. Do not label those diagnostics as GNU parity or silently rewrite the upstream expected result. Record the gap for maintainer review; a skipped or out-of-scope case is not passing coverage. Use `# upstream: none - <specific reason>` only for a genuinely repository-specific case.

## Run the port and inspect its result

### Run the new case

After adding the success function to `Tests.py`, use the local Make target with a pytest filter:

```sh
# Expected duration: Unknown; may compile Dafny test support and rebuild stale binaries.
# Success criteria: Exit 0; the named Python case runs and passes, with a fresh XML report.
make -C bench/utils/comm test \
  PYTEST_ARGS='-k test_zero_terminated_suppress_second_column_matches_coreutils --junitxml=/tmp/comm-zopt2.xml'
```

Expected Python-stage summary after adding the case, exit 0:

```text
...
1 passed, <count> deselected in <seconds>s
make: Leaving directory '/workspace/dafnyutils/bench/utils/comm'
```

The target runs executable `Tests.dfy` cases first, then `Tests.py`. `PYTEST_ARGS` filters the Python stage only. Build and helper errors must be resolved before interpreting parity. The XML path is supplied explicitly; choose a fresh path for each run to avoid confusing old and new evidence.

For a direct Python-only diagnostic after setup, select the exact pytest node:

```sh
# Expected duration: Unknown on first run; existing build fixture may rebuild the target.
# Success criteria: Exit 0 and exactly the selected Python test passes.
python3 -m pytest -q -n0 --import-mode=importlib \
  bench/utils/comm/Tests.py::test_zero_terminated_suppress_second_column_matches_coreutils
```

Expected summary after adding the case, exit 0:

```text
1 passed in <seconds>s
```

This reuses the module's build fixture and runners. It does not execute `Tests.dfy`. The lowercase `test_` function name makes it discoverable once the explicit `Tests.py` path is selected. Root `make test` targets source tests; use the utility target or explicit adapter path for utility cases.

The example node exists only after you add the function. Record your own result.

### Run the utility suite and record evidence

```sh
# Expected duration: Unknown; includes executable Dafny cases and all comm runtime tests.
# Success criteria: Exit 0, real runtime tests pass, and any skips are explained.
make -C bench/utils/comm test
```

Expected output shape, exit 0:

```text
CommTests.<case>: PASSED
...
<count> passed, <count> deselected in <seconds>s
make: Leaving directory '/workspace/dafnyutils/bench/utils/comm'
```

If existing cases are skipped, the summary includes a skipped count. Report their
reasons; a skipped case is not passing coverage.

Run the broader utility suite after the focused test. This target excludes tests
marked `dafny_verify`; it is not proof verification. Follow
[utility validation](adding-utilities.md#validate-and-submit) for the separate
proof and final contribution checks.

For a PR, report the upstream path/case/revision, Python test name, exact command, tested revision, GNU/Dafny artifact identities, pass/fail/skip counts and an accessible log or JUnit artifact. In `/tmp/comm-zopt2.xml`, look for the named `testcase` and confirm it has no `failure`, `error` or `skipped` child. A collected, deselected or skipped test is not an executed pass.

If GNU disagrees with the upstream expectation, check the fixture bytes, options, reference revision and environment first. If GNU matches but Dafny differs, preserve the failing Python test and investigate the implementation/specification. Keep the original expectation and full diagnostic evidence.

## When to use the fuzzer guide

A Python port is added directly to the utility's `Tests.py`; it requires no JSON case set or Rust generator registration. Use [the fuzzer guide](fuzzing.md) separately for generated campaigns, explicit JSON cases, mismatch bundles and regression suites. Both workflows compare behavior, but only the Python port described here becomes part of that utility's normal test adapter.
