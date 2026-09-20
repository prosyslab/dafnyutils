"""Audit manifest-backed benchmark discovery without a fixed item count."""

from pathlib import Path

import pytest

from benchmarks.definition import BenchmarkKind
from benchmarks.generated_profile import generate_task_profile
from benchmarks.repository import BenchmarkRepository
from benchmarks.task import TaskProfile

ROOT = Path(__file__).resolve().parents[2]


@pytest.fixture(scope="module")
def generated_profiles() -> dict[str, TaskProfile]:
    repository = BenchmarkRepository.open(ROOT)
    return {
        definition.task_id: generate_task_profile(definition, repository_root=ROOT).profile
        for definition in repository.definitions()
    }


# Every discovered public contract and project config belongs to one canonical manifest ID.
def test_all_benchmark_items_are_discovered_from_versioned_definitions(
    generated_profiles: dict[str, TaskProfile],
) -> None:
    repository = BenchmarkRepository.open(ROOT)
    definitions = repository.definitions()

    assert definitions
    assert len(definitions) == len({definition.task_id for definition in definitions})
    for definition in definitions:
        assert (ROOT / definition.project_config_path).is_file()
        profile = generated_profiles[definition.task_id]
        assert profile.task_id == definition.task_id


# Every coreutils public contract declares its C locale and UTC0 timezone without
# constraining algorithms.
def test_coreutils_profiles_declare_c_diagnostic_locale(
    generated_profiles: dict[str, TaskProfile],
) -> None:
    repository = BenchmarkRepository.open(ROOT)

    for definition in repository.definitions():
        profile = generated_profiles[definition.task_id]
        rules = {rule.rule_id: rule for rule in profile.public_rules}
        if definition.kind is BenchmarkKind.COREUTILS:
            locale = rules["diagnostic-locale"]
            assert locale.title == "Use the C diagnostic locale"
            assert locale.description == (
                "Coreutils behavior is specified and evaluated with LC_ALL=C; LANG=C is also "
                "supplied. Locale-dependent behavior outside the C locale is outside this task "
                "contract."
            )
            timezone = rules["time-zone"]
            assert timezone.title == "Use the UTC0 timezone"
            assert timezone.description == (
                "Coreutils behavior is specified and evaluated with TZ=UTC0. "
                "Timezone-dependent behavior outside UTC0 is outside this task contract."
            )
        else:
            assert "diagnostic-locale" not in rules
            assert "time-zone" not in rules
