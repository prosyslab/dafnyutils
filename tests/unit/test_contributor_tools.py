"""Exercise independent contributor commands with bounded in-memory boundaries."""

from __future__ import annotations

import xml.etree.ElementTree as ElementTree
from pathlib import Path
from types import SimpleNamespace

import pytest

from benchmarks.definition import BenchmarkDefinition
from tools.contribution import __main__ as cli
from tools.contribution import checks, make_tasks, validation, verify

ROOT = Path("/benchmark")


def _definition(*, fuzzer: bool = False, source_status: str = "verified") -> BenchmarkDefinition:
    return BenchmarkDefinition.model_validate(
        {
            "schema_version": "benchmark.definition.v2",
            "task_id": "sample",
            "kind": "coreutils",
            "source": {
                "status": source_status,
                "name": "Sample source",
                "url": "https://example.com/sample",
                "license": "MIT",
            },
            "capabilities": {"gnu_reference": True, "fuzzer": fuzzer},
        }
    )


# Local contributor checks retain runtime, reference, fuzzer and full proof test steps.
def test_check_plan_preserves_required_capability_checks() -> None:
    commands = checks.check_commands(ROOT, _definition(fuzzer=True))
    assert tuple(command.name for command in commands) == (
        "build",
        "coreutils-reference",
        "implementation-tests",
        "fuzzer",
        "dafny-verify",
        "benchmark-proof-tests",
    )
    assert commands[0].argv[1:4] == ("-m", "tools.contribution.make_tasks", "build")
    assert commands[-1].argv[-2:] == ("dafny_verify", "bench/utils/sample/Tests.py")
    implementation = commands[2]
    assert (
        implementation.pytest_report == "_build/contribution_checks/sample/implementation-tests.xml"
    )
    assert dict(implementation.environment)["EVAL_BENCH_DLL"] == "_build/bench/sample_bench.dll"


# Unsupported output paths fail before the gate can test stale default artifacts or helpers.
@pytest.mark.parametrize("directory", ("custom-build", "/selected/build"))
def test_check_plan_rejects_custom_build_directory(
    monkeypatch: pytest.MonkeyPatch, directory: str
) -> None:
    monkeypatch.setenv("BUILD_DIR", directory)
    with pytest.raises(ValueError, match="require the default BUILD_DIR=_build"):
        checks.check_commands(ROOT, _definition(fuzzer=True))


# Failed commands stop the local check before any subsequent mandatory step runs.
def test_check_executor_stops_on_failure(monkeypatch: pytest.MonkeyPatch) -> None:
    calls = []
    monkeypatch.setattr(checks, "_prepare_pytest_report", lambda *_args: None)
    monkeypatch.setattr(
        checks.subprocess,
        "run",
        lambda argv, **kwargs: calls.append((argv, kwargs)) or SimpleNamespace(returncode=7),
    )
    commands = (checks.CheckCommand("build", ("build",)), checks.CheckCommand("test", ("test",)))
    with pytest.raises(RuntimeError, match="build.*exit code 7"):
        checks.run_check_commands(ROOT, commands)
    assert len(calls) == 1
    assert calls[0][1]["cwd"] == ROOT


# Successful command exits still require implementation-test execution evidence.
def test_check_executor_validates_report(monkeypatch: pytest.MonkeyPatch) -> None:
    report = ROOT / "report.xml"
    validated = []
    monkeypatch.setattr(checks, "_prepare_pytest_report", lambda *_args: report)
    monkeypatch.setattr(checks.subprocess, "run", lambda *_a, **_k: SimpleNamespace(returncode=0))
    monkeypatch.setattr(checks, "validate_pytest_report", validated.append)
    checks.run_check_commands(ROOT, (checks.CheckCommand("implementation-tests", ("test",)),))
    assert validated == [report]


# An all-skipped implementation suite cannot satisfy the mandatory runtime check.
def test_pytest_report_rejects_all_skipped_tests(monkeypatch: pytest.MonkeyPatch) -> None:
    tree = ElementTree.ElementTree(
        ElementTree.fromstring(
            '<testsuites><testsuite><testcase name="sample"><skipped/></testcase>'
            "</testsuite></testsuites>"
        )
    )
    monkeypatch.setattr(checks.ElementTree, "parse", lambda _path: tree)
    with pytest.raises(RuntimeError, match="executed no tests"):
        checks.validate_pytest_report(ROOT / "report.xml")


# One executed implementation case is sufficient evidence for a successful command.
def test_pytest_report_accepts_executed_test(monkeypatch: pytest.MonkeyPatch) -> None:
    tree = ElementTree.ElementTree(
        ElementTree.fromstring(
            '<testsuites><testsuite><testcase name="sample"/></testsuite></testsuites>'
        )
    )
    monkeypatch.setattr(checks.ElementTree, "parse", lambda _path: tree)
    checks.validate_pytest_report(ROOT / "report.xml")


# Metadata validation requires provenance completeness without invoking source analysis.
def test_basic_validation_rejects_incomplete_source(monkeypatch: pytest.MonkeyPatch) -> None:
    repository = SimpleNamespace(
        root=ROOT, load_definition=lambda _id: _definition(source_status="incomplete")
    )
    monkeypatch.setattr(Path, "is_file", lambda _path: True)
    issues = validation.validate_benchmark(repository, "sample")
    assert tuple(issue.message for issue in issues) == ("source details are incomplete",)


# Declared local files remain required even when metadata is otherwise valid.
def test_basic_validation_reports_missing_declared_file(monkeypatch: pytest.MonkeyPatch) -> None:
    repository = SimpleNamespace(root=ROOT, load_definition=lambda _id: _definition())
    monkeypatch.setattr(Path, "is_file", lambda path: path.name != "Tests.py")
    issues = validation.validate_benchmark(repository, "sample")
    assert tuple(issue.message for issue in issues) == (
        "missing evaluation test: bench/utils/sample/Tests.py",
    )


# Valid metadata and declared files can be checked without any installed analysis service.
def test_basic_validation_accepts_complete_local_task(monkeypatch: pytest.MonkeyPatch) -> None:
    repository = SimpleNamespace(root=ROOT, load_definition=lambda _id: _definition())
    monkeypatch.setattr(Path, "is_file", lambda _path: True)
    result = validation.load_validated_benchmark(repository, "sample")
    assert result.definition.task_id == "sample"
    assert result.configuration.item_directory == "bench/utils/sample"


# Build dispatch uses ordinary Dafny by default and preserves an explicit compiler override.
@pytest.mark.parametrize("compiler", (None, "/selected/dafny"))
def test_build_uses_selected_native_dafny(
    monkeypatch: pytest.MonkeyPatch, compiler: str | None
) -> None:
    monkeypatch.delenv("DAFNY_BENCHMARK", raising=False)
    if compiler:
        monkeypatch.setenv("DAFNY_BENCHMARK", compiler)
    monkeypatch.setattr(Path, "mkdir", lambda *_a, **_k: None)
    calls = []
    monkeypatch.setattr(
        make_tasks, "_run", lambda argv, **kwargs: calls.append((argv, kwargs)) or 0
    )
    assert make_tasks._build(ROOT, _definition()) == 0
    assert calls[0][0][0] == (compiler or "dafny")
    assert calls[0][0][-1] == "bench/core/IOExtern.cs"


# Implementation checks use owner-owned failure evidence even when a runner injects plugins.
def test_implementation_tests_select_local_plugin(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setenv("PYTEST_PLUGINS", "evaluation.submission.pytest_infrastructure")
    calls = []
    monkeypatch.setattr(
        make_tasks, "_run", lambda argv, **kwargs: calls.append((argv, kwargs)) or 0
    )

    assert make_tasks._test(ROOT, _definition()) == 0

    assert calls[0][1]["env"]["PYTEST_PLUGINS"] == "tools.pytest_infrastructure"


# Explicit file enumeration covers standalone proof sources without making core a proof root.
def test_verification_sources_include_unreferenced_proof(monkeypatch: pytest.MonkeyPatch) -> None:
    project = ROOT / "bench/utils/sample"
    library = ROOT / "bench/core"
    files = {
        project: (project / "Impl/Sample.dfy", project / "Proof/UnreferencedProof.dfy"),
        library: (library / "IO.dfy",),
    }
    monkeypatch.setattr(Path, "rglob", lambda path, _pattern: iter(files[path]))
    assert verify.verification_sources(project) == tuple(
        sorted(
            (
                project / "Impl/Sample.dfy",
                project / "Proof/UnreferencedProof.dfy",
            )
        )
    )


# Native proof invocation verifies all project files and keeps explicit core support as a library.
@pytest.mark.parametrize("with_library", (False, True))
def test_verify_invokes_all_sources_directly(
    monkeypatch: pytest.MonkeyPatch, with_library: bool
) -> None:
    source = ROOT / "Proof/UnreferencedProof.dfy"
    monkeypatch.setattr(Path, "is_dir", lambda _path: True)
    monkeypatch.setattr(Path, "is_symlink", lambda _path: False)
    monkeypatch.setattr(verify, "_source_snapshot", lambda *_a: ((source, "fixed"),))
    monkeypatch.setattr(verify, "verification_sources", lambda *_a: (source,))
    calls = []
    monkeypatch.setattr(
        verify.subprocess,
        "run",
        lambda argv, **kwargs: calls.append((argv, kwargs)) or SimpleNamespace(returncode=0),
    )
    libraries = (ROOT / "bench/core",) if with_library else ()
    assert verify.verify_project(ROOT, libraries, dafny="/selected/dafny") == 0
    assert calls[0][0] == [
        "/selected/dafny",
        "verify",
        "--standard-libraries:false",
        *(("--library:/benchmark/bench/core", "--allow-warnings") if with_library else ()),
        "--verify-included-files",
        "--boogie=/randomSeed:42",
        "--isolate-assertions",
        "--verification-time-limit:30",
        "--allow-external-contracts",
        str(source),
    ]


# Source mutation during native verification invalidates an otherwise successful result.
def test_verify_rejects_changed_sources(monkeypatch: pytest.MonkeyPatch) -> None:
    source = ROOT / "Sample.dfy"
    snapshots = iter((((source, "before"),), ((source, "after"),)))
    monkeypatch.setattr(Path, "is_dir", lambda _path: True)
    monkeypatch.setattr(verify, "_source_snapshot", lambda *_a: next(snapshots))
    monkeypatch.setattr(verify, "verification_sources", lambda *_a: (source,))
    monkeypatch.setattr(verify.subprocess, "run", lambda *_a, **_k: SimpleNamespace(returncode=0))
    with pytest.raises(RuntimeError, match="sources changed"):
        verify.verify_project(ROOT, (), dafny="dafny")


# Unrelated changed paths select no tasks instead of accidentally checking every registered task.
def test_cli_keeps_empty_changed_path_selection(monkeypatch: pytest.MonkeyPatch) -> None:
    repository = SimpleNamespace(task_ids=lambda: ("sample",))
    monkeypatch.setattr(cli.BenchmarkRepository, "open", lambda _root: repository)
    monkeypatch.setattr(cli, "affected_task_ids", lambda *_a: ())
    monkeypatch.setattr(cli, "run_benchmark_checks", lambda *_a: pytest.fail("unexpected check"))
    assert cli.main(["check", "--changed-path", "README.md"]) == 0


# Source snapshots cover explicit trusted library inputs as well as project sources and metadata.
def test_snapshot_tracks_library_source_changes(monkeypatch: pytest.MonkeyPatch) -> None:
    project = ROOT / "bench/utils/sample"
    library = ROOT / "bench/core"
    project_source = project / "Proof/SampleProof.dfy"
    support_source = library / "IO.dfy"
    contents = {
        project_source: b"project",
        support_source: b"support-before",
        project / "benchmark.yaml": b"definition",
        project / "dfyconfig.toml": b"configuration",
    }
    monkeypatch.setattr(verify, "verification_sources", lambda _project: (project_source,))
    monkeypatch.setattr(Path, "rglob", lambda _path, _pattern: iter((support_source,)))
    monkeypatch.setattr(Path, "read_bytes", lambda path: contents[path])
    before = verify._source_snapshot(project, (library,))
    contents[support_source] = b"support-after"
    after = verify._source_snapshot(project, (library,))
    assert tuple(path for path, _digest in before) == tuple(sorted(contents))
    assert before != after
