from __future__ import annotations

import shutil
import subprocess
from pathlib import Path
from types import SimpleNamespace

import pytest

import verification
from benchmarks import checks as benchmark_checks
from benchmarks.checks import EvaluationName
from benchmarks.contribution import (
    check_commands,
    run_benchmark_checks,
    validate_pytest_report,
)
from benchmarks.definition import BenchmarkDefinition, BenchmarkKind, BenchmarkSource
from benchmarks.generated_profile import generate_task_profile
from benchmarks.repository import BenchmarkRepository
from benchmarks.scaffold import scaffold_benchmark
from benchmarks.selection import affected_task_ids
from benchmarks.validation import load_validated_benchmark, validate_benchmark
from benchmarks.verify import local_verification_contract, verify_project

ROOT = Path(__file__).resolve().parents[2]


def _write(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


# Registered definitions preserve canonical IDs across utility and algorithm directory layouts.
def test_repository_round_trips_every_registered_task() -> None:
    repository = BenchmarkRepository.open(ROOT)

    for task_id in repository.task_ids():
        definition = repository.load_definition(task_id)
        assert definition.task_id == task_id
        assert repository.definition_path(task_id) == (
            ROOT / definition.item_directory / "benchmark.yaml"
        )

    assert "cat" in repository.task_ids(BenchmarkKind.COREUTILS)
    assert "algorithm-1" in repository.task_ids(BenchmarkKind.ALGORITHM)
    assert "1" not in repository.task_ids()


# A generated scaffold is visibly incomplete and cannot pass registration validation.
@pytest.mark.parametrize(
    ("kind", "task_id", "relative_directory"),
    (
        (BenchmarkKind.COREUTILS, "sample", Path("bench/utils/sample")),
        (BenchmarkKind.ALGORITHM, "algorithm-999", Path("bench/algorithm/999")),
    ),
)
def test_scaffold_is_incomplete_for_both_families(
    tmp_path: Path,
    kind: BenchmarkKind,
    task_id: str,
    relative_directory: Path,
) -> None:
    (tmp_path / "bench").mkdir()
    source_templates = ROOT / "tools/benchmark_templates"
    target_templates = tmp_path / "tools/benchmark_templates"
    target_templates.parent.mkdir(parents=True)
    target_templates.symlink_to(source_templates, target_is_directory=True)

    result = scaffold_benchmark(root=tmp_path, kind=kind, task_id=task_id)
    repository = BenchmarkRepository.open(tmp_path)

    assert result.directory == tmp_path / relative_directory
    assert (result.directory / "benchmark.yaml").is_file()
    assert (result.directory / "Makefile").is_file()
    if kind is BenchmarkKind.COREUTILS:
        assert (result.directory / "Tests.py").is_file()
        assert (result.directory / "Tests.dfy").is_file()
    assert any(
        "source provenance is incomplete" in issue.message
        for issue in validate_benchmark(repository, task_id)
    )


# Hyphenated utility IDs produce valid PascalCase Dafny source and module names.
def test_coreutils_scaffold_normalizes_hyphenated_class_name(tmp_path: Path) -> None:
    (tmp_path / "bench").mkdir()
    target_templates = tmp_path / "tools/benchmark_templates"
    target_templates.parent.mkdir(parents=True)
    target_templates.symlink_to(ROOT / "tools/benchmark_templates", target_is_directory=True)

    result = scaffold_benchmark(
        root=tmp_path,
        kind=BenchmarkKind.COREUTILS,
        task_id="sample-tool",
    )

    assert (result.directory / "SampleTool.dfy").is_file()
    assert "module SampleTool" in (result.directory / "SampleTool.dfy").read_text(encoding="utf-8")


# Scaffolding never overwrites an existing contribution directory.
def test_scaffold_refuses_existing_directory(tmp_path: Path) -> None:
    (tmp_path / "bench/utils/sample").mkdir(parents=True)

    with pytest.raises(FileExistsError, match="already exists"):
        scaffold_benchmark(root=tmp_path, kind=BenchmarkKind.COREUTILS, task_id="sample")


# Invalid scaffold IDs are rejected before any path or template is created.
@pytest.mark.parametrize(
    "task_id", ("../escaped", "/absolute", "bad/name", ".", "Bad", "bad-", "bad--id")
)
def test_scaffold_rejects_malformed_id_without_writing(tmp_path: Path, task_id: str) -> None:
    with pytest.raises(ValueError, match="task_id"):
        scaffold_benchmark(root=tmp_path, kind=BenchmarkKind.COREUTILS, task_id=task_id)

    assert not (tmp_path / "bench").exists()


# An existing family-directory symlink cannot redirect scaffold writes outside the repository.
def test_scaffold_rejects_parent_symlink_escape(tmp_path: Path) -> None:
    root = tmp_path / "repository"
    outside = tmp_path / "outside"
    (root / "bench").mkdir(parents=True)
    outside.mkdir()
    (root / "bench/utils").symlink_to(outside, target_is_directory=True)

    with pytest.raises(ValueError, match="escapes repository root"):
        scaffold_benchmark(root=root, kind=BenchmarkKind.COREUTILS, task_id="sample")

    assert not (outside / "sample").exists()


# Only the fixed migration baseline can use unknown legacy provenance.
def test_new_definition_cannot_claim_legacy_provenance() -> None:
    payload = {
        "schema_version": "benchmark.definition.v2",
        "task_id": "new-task",
        "kind": "coreutils",
        "source": {
            "status": "legacy-unverified",
            "name": "Unknown",
        },
    }

    with pytest.raises(ValueError, match="migration baseline"):
        BenchmarkDefinition.model_validate(payload)


# Unsupported contributor schema versions require an explicit migration.
@pytest.mark.parametrize("schema_version", ("benchmark.definition.v1", "benchmark.definition.v3"))
def test_definition_rejects_unsupported_schema_version(schema_version: str) -> None:
    payload = {
        "schema_version": schema_version,
        "task_id": "sample",
        "kind": "coreutils",
        "source": {
            "status": "verified",
            "name": "Sample source",
            "url": "https://example.com/sample",
            "license": "MIT",
        },
    }

    with pytest.raises(ValueError, match="benchmark.definition.v2"):
        BenchmarkDefinition.model_validate(payload)


# A copied v1 path cannot override the evaluator path derived from the v2 task ID.
def test_definition_rejects_legacy_path_override() -> None:
    payload = {
        "schema_version": "benchmark.definition.v2",
        "task_id": "sample",
        "kind": "coreutils",
        "source": {
            "status": "verified",
            "name": "Sample source",
            "url": "https://example.com/sample",
            "license": "MIT",
        },
        "evaluation": {"test_path": "tools/bench/other.py"},
    }

    with pytest.raises(ValueError, match="evaluation"):
        BenchmarkDefinition.model_validate(payload)


# A valid definition cannot be moved to another utility directory under the same family.
def test_definition_location_rejects_wrong_item_directory(tmp_path: Path) -> None:
    item = tmp_path / "bench/utils/other"
    item.mkdir(parents=True)
    shutil.copyfile(ROOT / "bench/utils/cat/benchmark.yaml", item / "benchmark.yaml")

    with pytest.raises(ValueError, match="expected"):
        BenchmarkRepository.open(tmp_path).task_ids()


# Verified provenance requires normalized human-readable fields and an HTTP(S) URL.
@pytest.mark.parametrize(
    "source",
    (
        {"status": "verified", "name": " Source", "url": "https://example.com", "license": "MIT"},
        {"status": "verified", "name": "Source", "url": "file:///tmp/source", "license": "MIT"},
        {"status": "verified", "name": "Source", "url": "https://example.com", "license": " TODO "},
    ),
)
def test_verified_provenance_rejects_placeholder_or_malformed_fields(
    source: dict[str, object],
) -> None:
    with pytest.raises(ValueError):
        BenchmarkSource.model_validate(source)


# Shared changes expand selection; item changes stay focused and algorithms use canonical IDs.
def test_affected_task_selection_uses_manifest_families() -> None:
    repository = BenchmarkRepository.open(ROOT)

    assert affected_task_ids(repository, ("bench/utils/cat/CatSpec.dfy",)) == ("cat",)
    assert affected_task_ids(repository, ("bench/algorithm/1/Spec.dfy",)) == ("algorithm-1",)
    assert set(affected_task_ids(repository, ("tools/coreutils_fuzzer/src/lib.rs",))) == set(
        repository.task_ids(BenchmarkKind.COREUTILS)
    )


# Editing either algorithm execution component must select every algorithm for checking.
@pytest.mark.parametrize(
    "path",
    ("tools/bench/test_bench_algorithm.py", "tools/fixtures/algorithm/OutputCapture.cs"),
)
def test_affected_selection_tracks_algorithm_execution_components(path: str) -> None:
    repository = BenchmarkRepository.open(ROOT)

    assert affected_task_ids(repository, (path,)) == repository.task_ids(BenchmarkKind.ALGORITHM)


# Shared benchmark tests affect every item rather than naming a nonexistent task.
@pytest.mark.parametrize(
    "path",
    (
        "tools/bench/test_bench_functional.py",
        "tools/bench/test_bench_stream_filesystem_models.py",
        "tools/bench/bench_test_support.py",
        "tools/audit/test_coreutils_entry_contract.py",
    ),
)
def test_affected_selection_includes_all_tasks_for_shared_benchmark_tests(path: str) -> None:
    repository = BenchmarkRepository.open(ROOT)

    assert affected_task_ids(repository, (path,)) == repository.task_ids()


# Changes to shared analysis, verifier, and candidate execution select every item.
@pytest.mark.parametrize(
    "path",
    (
        "src/analysis/client.py",
        "src/dafny_cli.py",
        "dafny",
        "dafny/Source/DafnyCore/AST/Expressions/Expression.cs",
    ),
)
def test_affected_selection_includes_all_tasks_for_shared_execution(path: str) -> None:
    repository = BenchmarkRepository.open(ROOT)

    assert affected_task_ids(repository, (path,)) == repository.task_ids()


# Deleted and renamed item paths remain selected so CI fails closed on missing definitions.
def test_affected_selection_retains_missing_deleted_or_renamed_ids() -> None:
    repository = BenchmarkRepository.open(ROOT)

    assert affected_task_ids(
        repository,
        (
            "bench/utils/deleted/benchmark.yaml",
            "bench/utils/replacement/benchmark.yaml",
            "bench/algorithm/999/benchmark.yaml",
        ),
    ) == ("algorithm-999", "deleted", "replacement")


# Each family keeps its prerequisite, test, fuzz, and proof command order.
@pytest.mark.parametrize("task_id", ("cat", "algorithm-1"))
def test_check_plan_keeps_required_family_checks(task_id: str) -> None:
    repository = BenchmarkRepository.open(ROOT)
    commands = check_commands(ROOT, repository.load_definition(task_id))

    expected = (
        (
            "build",
            "coreutils-reference",
            "implementation-tests",
            "fuzzer",
            "dafny-verify",
            "utility-proof-tests",
        )
        if task_id == "cat"
        else ("build", "implementation-tests", "dafny-verify")
    )
    assert tuple(command.name for command in commands) == expected
    proof = next(command for command in commands if command.name == "dafny-verify")
    assert proof.argv == (
        "make", "-C", repository.load_definition(task_id).item_directory, "verify"
    )
    if task_id == "cat":
        assert commands[-1].argv[1:] == (
            "-m", "pytest", "-q", "-n0", "--import-mode=importlib",
            "-m", "dafny_verify", "bench/utils/cat/Tests.py",
        )


# A newly required check cannot silently disappear from contributor validation.
def test_check_plan_rejects_unimplemented_required_check(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    repository = BenchmarkRepository.open(ROOT)
    monkeypatch.setattr(
        benchmark_checks,
        "MANDATORY_CHECKS",
        (
            *benchmark_checks.MANDATORY_CHECKS,
            benchmark_checks.MandatoryCheck("security_scan", EvaluationName.VERIFICATION),
        ),
    )

    with pytest.raises(ValueError, match="missing contributor commands.*security_scan"):
        check_commands(ROOT, repository.load_definition("cat"))


# The verification gate enumerates included Core and Proof files, not only the wrapper entry.
def test_verification_session_includes_algorithm_core_and_proof() -> None:
    contract = local_verification_contract(ROOT / "bench/algorithm/1")

    sources = {path.name for path in contract.verification_sources}

    assert {"Algorithm1.dfy", "Core.dfy", "Proof.dfy"} <= sources


# A verifier failure in an included proof makes the canonical benchmark proof gate fail.
def test_verification_gate_rejects_invalid_included_proof(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    project = ROOT / "bench/algorithm/1"
    visited: list[str] = []

    def verify_command(command: list[str], *, cwd: Path) -> subprocess.CompletedProcess[bytes]:
        _ = cwd
        source_filter = next(arg for arg in command if arg.startswith("--filter-position="))
        visited.append(source_filter)
        if source_filter.endswith("Proof.dfy"):
            return subprocess.CompletedProcess(command, 1, b"proof failed\n", b"")
        report_arg = next(arg for arg in command if arg.startswith("trx;LogFileName="))
        report_path = Path(report_arg.removeprefix("trx;LogFileName="))
        report_path.write_text(
            '<TestRun><Results><UnitTestResult outcome="Passed" /></Results></TestRun>',
            encoding="utf-8",
        )
        return subprocess.CompletedProcess(command, 0, b"", b"")

    monkeypatch.setattr(verification, "_run_verification_command", verify_command)

    assert verify_project(project, (), dafny="test-dafny") == 1
    assert any(item.endswith("Proof.dfy") for item in visited)


# A failed mandatory command stops the check and is never reported as success.
def test_check_fails_on_first_failed_mandatory_command(monkeypatch: pytest.MonkeyPatch) -> None:
    repository = BenchmarkRepository.open(ROOT)
    validated = load_validated_benchmark(repository, "cat")
    monkeypatch.setattr(
        "benchmarks.contribution.load_validated_benchmark",
        lambda _repository, _task_id: validated,
    )
    calls: list[tuple[str, ...]] = []

    def failed_run(argv: tuple[str, ...], **_kwargs: object) -> SimpleNamespace:
        calls.append(argv)
        return SimpleNamespace(returncode=7)

    monkeypatch.setattr("benchmarks.contribution.subprocess.run", failed_run)

    with pytest.raises(RuntimeError, match="build.*exit code 7"):
        run_benchmark_checks(repository, "cat")
    assert len(calls) == 1


# Moving the principal Spec call into a precondition cannot satisfy the final proof obligation.
def test_validation_rejects_principal_spec_moved_out_of_postcondition(tmp_path: Path) -> None:
    shutil.copytree(ROOT / "bench/algorithm/1", tmp_path / "bench/algorithm/1")
    shutil.copytree(ROOT / "bench/core", tmp_path / "bench/core")
    evaluation_test = tmp_path / "tools/bench/test_bench_algorithm.py"
    _write(evaluation_test, "# trusted evaluator placeholder for structural validation\n")
    entry = tmp_path / "bench/algorithm/1/Algorithm1.dfy"
    entry.write_text(
        entry.read_text(encoding="utf-8").replace(
            "ensures Spec.Spec(x, result)",
            "requires Spec.Spec(x, x)\n    ensures result == result",
        ),
        encoding="utf-8",
    )

    repository = BenchmarkRepository.open(tmp_path)
    definition = repository.load_definition("algorithm-1")
    with pytest.raises(ValueError, match="principal specification in a postcondition"):
        generate_task_profile(definition, repository_root=repository.root)

    issues = validate_benchmark(repository, "algorithm-1")

    assert any("principal specification in a postcondition" in issue.message for issue in issues)


# A generated profile rejects a missing natural specification before publication.
def test_generated_profile_rejects_missing_resource(tmp_path: Path) -> None:
    shutil.copytree(ROOT / "bench/algorithm/1", tmp_path / "bench/algorithm/1")
    shutil.copytree(ROOT / "bench/core", tmp_path / "bench/core")
    (tmp_path / "bench/algorithm/1/algorithm-1.md").unlink()
    repository = BenchmarkRepository.open(tmp_path)
    definition = repository.load_definition("algorithm-1")

    with pytest.raises(FileNotFoundError, match="task resource is missing"):
        generate_task_profile(definition, repository_root=repository.root)


# A real pytest artifact containing only skipped cases is not valid mandatory-test evidence.
def test_pytest_evidence_rejects_all_skipped_suite(tmp_path: Path) -> None:
    test_path = tmp_path / "test_skipped.py"
    report_path = tmp_path / "report.xml"
    _write(
        test_path,
        """import pytest

pytestmark = pytest.mark.skip(reason="not configured")

def test_semantics():
    pass
""",
    )
    subprocess.run(
        [
            "python3",
            "-m",
            "pytest",
            "-q",
            "-n0",
            str(test_path),
            f"--junitxml={report_path}",
        ],
        check=True,
        capture_output=True,
    )

    with pytest.raises(RuntimeError, match="executed no tests"):
        validate_pytest_report(report_path)


# A real pytest artifact remains valid when at least one case executes beside allowed skips.
def test_pytest_evidence_accepts_executed_case_with_skip(tmp_path: Path) -> None:
    test_path = tmp_path / "test_mixed.py"
    report_path = tmp_path / "report.xml"
    _write(
        test_path,
        """import pytest

def test_semantics():
    assert 1 + 1 == 2

@pytest.mark.skip(reason="optional platform case")
def test_optional():
    pass
""",
    )
    subprocess.run(
        [
            "python3",
            "-m",
            "pytest",
            "-q",
            "-n0",
            str(test_path),
            f"--junitxml={report_path}",
        ],
        check=True,
        capture_output=True,
    )

    validate_pytest_report(report_path)
