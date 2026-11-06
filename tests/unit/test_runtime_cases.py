from __future__ import annotations

import pytest

from benchmarks.definition import OutputContract
from benchmarks.runtime_cases import RuntimeCase, assert_runtime_observation


# Scalar output accepts the problem's whitespace-insensitive token protocol.
def test_runtime_case_accepts_scalar_output() -> None:
    case = RuntimeCase(input="6\n", output="5\n")

    assert_runtime_observation(case, (b" 5\r\n", b"", 0))


# Integer results preserve numeric equality across valid decimal representations.
def test_runtime_case_accepts_equivalent_integer() -> None:
    case = RuntimeCase(input="6\n", output="5\n")

    assert_runtime_observation(case, (b"+005\n", b"", 0), OutputContract.INTEGER)


# Language-specific digit separators are not part of the command-line integer protocol.
def test_runtime_case_rejects_digit_separator() -> None:
    case = RuntimeCase(input="6\n", output="5\n")

    with pytest.raises(AssertionError, match="decimal integer"):
        assert_runtime_observation(case, (b"0_5\n", b"", 0), OutputContract.INTEGER)


# A candidate's nonzero exit cannot pass even after it prints the expected answer.
def test_runtime_case_rejects_failed_exit() -> None:
    case = RuntimeCase(input="6\n", output="5\n")

    with pytest.raises(AssertionError, match="exited 1"):
        assert_runtime_observation(case, (b"5\n", b"", 1))


# A valid alternative cell is accepted when several cells cover every wall.
def test_runtime_case_accepts_alternative_covering_cell() -> None:
    case = RuntimeCase(input="2 2\n*.\n..\n", output="YES\n1 1\n")

    assert_runtime_observation(case, (b"YES\n1 2\n", b"", 0), OutputContract.COVERING_CELL)


# A claimed feasible cell must actually cover every wall in the source grid.
def test_runtime_case_rejects_uncovered_wall() -> None:
    case = RuntimeCase(input="2 2\n*.\n..\n", output="YES\n1 1\n")

    with pytest.raises(AssertionError, match="uncovered wall"):
        assert_runtime_observation(case, (b"YES\n2 2\n", b"", 0), OutputContract.COVERING_CELL)


# A minimum square may move horizontally while preserving its original white pixels.
def test_runtime_case_accepts_alternative_minimal_frame() -> None:
    case = RuntimeCase(input="2 3\n.w.\n.w.\n", output="+w.\n+w.\n")

    assert_runtime_observation(case, (b".w+\n.w+\n", b"", 0), OutputContract.MINIMAL_FRAME)


# A larger square is rejected even when it covers every white pixel on its boundary.
def test_runtime_case_rejects_nonminimal_frame() -> None:
    case = RuntimeCase(input="3 3\nw..\n...\n...\n", output="w..\n...\n...\n")

    with pytest.raises(AssertionError, match="not minimal"):
        assert_runtime_observation(case, (b"w++\n+.+\n+++\n", b"", 0), OutputContract.MINIMAL_FRAME)
