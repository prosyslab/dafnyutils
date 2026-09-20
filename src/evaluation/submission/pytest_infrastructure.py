"""Keep pytest check failures visible alongside candidate infrastructure failures.

The evaluator loads this plugin through PYTEST_PLUGINS for check commands. If a
command has both a real test failure and a candidate setup failure, separate
failure evidence lets the stage report the failed check and the infrastructure block.
"""

from __future__ import annotations

from collections.abc import Generator
from typing import Any

import pytest

from evaluation.submission.candidate_execution import CandidateInfrastructureError
from evaluation.submission.infrastructure import record_check_failure


@pytest.hookimpl(hookwrapper=True)
def pytest_runtest_makereport(
    item: pytest.Item, call: pytest.CallInfo[None]
) -> Generator[None, Any, None]:
    del item
    outcome = yield
    report = outcome.get_result()
    # CandidateInfrastructureError has its own setup journal. Record other failed
    # phases separately so an infrastructure block cannot hide a real check failure.
    if report.failed and (
        call.excinfo is None or not isinstance(call.excinfo.value, CandidateInfrastructureError)
    ):
        record_check_failure()
