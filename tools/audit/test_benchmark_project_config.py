from __future__ import annotations

import tomllib
from pathlib import Path

import pytest

from benchmarks.profiles import is_algorithm_utility, utility_paths
from tests.evaluation.evaluation_test_support import benchmark_utility_configs

ROOT = Path(__file__).resolve().parents[2]
UTILITIES = benchmark_utility_configs()


def _utility_id(utility: object) -> str:
    return str(getattr(utility, "name"))


# Every benchmark item owns one complete and exact Dafny build configuration.
@pytest.mark.parametrize("utility", UTILITIES, ids=_utility_id)
def test_benchmark_item_owns_exact_project_config(utility: object) -> None:
    name = _utility_id(utility)
    paths = utility_paths(utility, name)
    config_path = ROOT / paths["project_config"]

    build_entry = paths["wrapper"] if is_algorithm_utility(name) else paths["cli"]
    assert tomllib.loads(config_path.read_text(encoding="utf-8")) == {
        "includes": [Path(build_entry).name],
        "options": {
            "target": "cs",
            "no-verify": True,
            "standard-libraries": False,
        },
    }
