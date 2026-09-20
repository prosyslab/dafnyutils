"""Verify candidate-editable Dafny sources and validate their TRX results."""

from __future__ import annotations

import argparse
import os
import subprocess
import sys
import tempfile
import xml.etree.ElementTree as ElementTree
from collections.abc import Callable, Sequence
from pathlib import Path

from analysis.kinds import DefinitionKind
from dafny_cli import dafny_command
from entry_contract import (
    EntryContractCheckSession,
    EntryContractManifest,
    EntryValidationFailure,
    ValidatedEntryContract,
)
from standard_library import (
    DAFNY_BENCH_CORE_LIBRARY_OPTION,
    DAFNY_STANDARD_LIBRARY_OPTION,
    dafny_bench_core_library_options,
    has_dafny_warning,
    without_expected_dafny_library_warnings,
    without_expected_library_warnings,
)

DAFNY_VERIFICATION_TIME_LIMIT_SEC = 30


def _verification_options(workspace_root: Path) -> tuple[str, ...]:
    return verification_options(dafny_bench_core_library_options(workspace_root))


def verification_options(library_options: Sequence[str] = ()) -> tuple[str, ...]:
    """Keep proof batching and limits consistent for local and evaluator verification."""
    return (
        DAFNY_STANDARD_LIBRARY_OPTION,
        *library_options,
        "--verify-included-files",
        "--isolate-assertions",
        f"--verification-time-limit:{DAFNY_VERIFICATION_TIME_LIMIT_SEC}",
        "--allow-external-contracts",
    )


def _trx_counts(report_path: Path) -> tuple[int, int]:
    results = ElementTree.parse(report_path).getroot().findall(".//{*}UnitTestResult")
    return len(results), sum(item.get("outcome") != "Passed" for item in results)


def _emit_outcome(outcome: str, phase: str) -> None:
    print(f"DAFNY_VERIFICATION_OUTCOME={outcome} phase={phase}")


def _run_verification_command(
    command: list[str],
    *,
    cwd: Path,
) -> subprocess.CompletedProcess[bytes]:
    return subprocess.run(
        command,
        cwd=cwd,
        env={**os.environ, "TMPDIR": "/tmp"},
        check=False,
        capture_output=True,
    )


def _stream_text(stream: str | bytes | None) -> str:
    if isinstance(stream, bytes):
        return stream.decode(errors="replace")
    return stream or ""


def _emit_process_output(stdout: str, stderr: str) -> None:
    if stdout:
        print(stdout, end="", file=sys.stdout)
    if stderr:
        print(stderr, end="", file=sys.stderr)


def _run_build_command(
    command: Sequence[str],
    *,
    cwd: Path,
) -> subprocess.CompletedProcess[bytes]:
    return subprocess.run(command, cwd=cwd, env={**os.environ, "TMPDIR": "/tmp"}, check=False)


def _verify_sources(
    contract: ValidatedEntryContract,
    workspace_root: Path,
    dafny: str,
    report_dir: Path,
    verification_options: tuple[str, ...],
    libraries: tuple[Path, ...] = (),
) -> tuple[int, int] | None:
    if any(
        definition.body_start is None and definition.kind is not DefinitionKind.DATATYPE
        for definition in contract.verification_definitions
    ):
        _emit_outcome("verification_failure", "verify")
        return None
    total = 0
    failed = 0
    sources = contract.verification_sources
    print(f"Verification targets ({len(sources)} files):", flush=True)
    for source in sources:
        print(f"  {source.relative_to(workspace_root).as_posix()}", flush=True)
    for index, source in enumerate(sources):
        progress = f"[{index + 1}/{len(sources)}]"
        source_path = source.relative_to(workspace_root).as_posix()
        print(f"{progress} Verifying {source_path}", flush=True)
        report_path = report_dir / f"{index}.trx"
        try:
            result = _run_verification_command(
                [
                    dafny,
                    "verify",
                    verification_options[0],
                    str(contract.execution_source),
                    *verification_options[1:],
                    f"--filter-position={source_path}",
                    "--log-format",
                    f"trx;LogFileName={report_path}",
                ],
                cwd=workspace_root,
            )
        except OSError:
            _emit_outcome("infrastructure_failure", "build")
            return None
        stdout = _stream_text(result.stdout)
        stderr = _stream_text(result.stderr)
        if DAFNY_BENCH_CORE_LIBRARY_OPTION in verification_options:
            stdout = without_expected_dafny_library_warnings(stdout, workspace_root)
            stderr = without_expected_dafny_library_warnings(stderr, workspace_root)
        if libraries:
            stdout = without_expected_library_warnings(stdout, libraries)
            stderr = without_expected_library_warnings(stderr, libraries)
        _emit_process_output(stdout, stderr)
        if has_dafny_warning(stdout) or has_dafny_warning(stderr):
            _emit_outcome("verification_failure", "verify")
            return None
        if result.returncode != 0:
            _emit_outcome("verification_failure", "verify")
            return None
        try:
            report_total, report_failed = _trx_counts(report_path)
        except (OSError, ElementTree.ParseError):
            _emit_outcome("infrastructure_failure", "evidence")
            return None
        total += report_total
        failed += report_failed
        print(
            f"{progress} Completed {source_path}: total={report_total} failed={report_failed}",
            flush=True,
        )
    return total, failed


def verify_session(session: EntryContractCheckSession, dafny: str) -> int:
    """Verify one already-bound contract session using one explicit Dafny tool."""
    verification_options = _verification_options(session.workspace_root)
    try:
        if session.tool_identity is not None and session.tool_identity != dafny:
            raise EntryValidationFailure("contract session Dafny tool does not match verifier tool")
        if session.verification_options and session.verification_options != verification_options:
            raise EntryValidationFailure("contract session verifier options do not match")
        contract = session.validate()
    except (EntryValidationFailure, OSError, ValueError):
        _emit_outcome("infrastructure_failure", "evidence")
        return 1

    return verify_contract(
        contract, session.workspace_root, dafny, verification_options, validate=session.validate
    )


def verify_contract(
    contract: ValidatedEntryContract,
    working_directory: Path,
    dafny: str,
    options: tuple[str, ...],
    *,
    validate: Callable[[], object],
    libraries: tuple[Path, ...] = (),
) -> int:
    """Verify a resolved proof surface and recheck its source identity before success."""
    try:
        reports = tempfile.TemporaryDirectory()
    except OSError:
        _emit_outcome("infrastructure_failure", "evidence")
        return 1
    with reports as report_dir:
        counts = _verify_sources(
            contract,
            working_directory,
            dafny,
            Path(report_dir),
            options,
            libraries,
        )
    if counts is None:
        return 1
    try:
        validate()
    except (EntryValidationFailure, OSError, ValueError):
        _emit_outcome("infrastructure_failure", "evidence")
        return 1
    total, failed = counts

    if total == 0:
        _emit_outcome("infrastructure_failure", "evidence")
        return 1
    if failed:
        _emit_outcome("verification_failure", "verify")
        return 1
    _emit_outcome("verified", "verify")
    print(f"DAFNY_VERIFICATION_RESULT total={total} failed=0")
    return 0


def run_full_session(
    session: EntryContractCheckSession,
    dafny: str,
    build_command: Sequence[str],
) -> int:
    """Run build, proof-layout, and verification phases through one session."""
    try:
        session.validate()
    except (EntryValidationFailure, OSError, ValueError):
        _emit_outcome("infrastructure_failure", "build")
        return 1

    try:
        build_result = _run_build_command(build_command, cwd=session.workspace_root)
    except OSError:
        _emit_outcome("infrastructure_failure", "build")
        return 1
    if build_result.returncode != 0:
        _emit_outcome("infrastructure_failure", "build")
        return 1

    try:
        session.validate()
    except (EntryValidationFailure, OSError, ValueError):
        _emit_outcome("infrastructure_failure", "proof_layout")
        return 1
    return verify_session(session, dafny)


def _load_session(
    workspace_root: Path,
    utility_root: Path,
    manifest_path: Path,
    dafny: str,
) -> EntryContractCheckSession:
    workspace_root = workspace_root.resolve()
    utility_root = (workspace_root / utility_root).resolve()
    manifest = EntryContractManifest.model_validate_json(manifest_path.read_text(encoding="utf-8"))
    return EntryContractCheckSession(
        workspace_root,
        utility_root,
        manifest,
        tool_identity=dafny,
        verification_options=_verification_options(workspace_root),
    )


def run(
    workspace_root: Path,
    utility_root: Path,
    manifest_path: Path,
    dafny: str,
) -> int:
    """Verify every entry-reachable candidate source from one execution root."""
    try:
        session = _load_session(workspace_root, utility_root, manifest_path, dafny)
    except (OSError, ValueError):
        _emit_outcome("infrastructure_failure", "evidence")
        return 1
    return verify_session(session, dafny)


def run_full(
    workspace_root: Path,
    utility_root: Path,
    manifest_path: Path,
    dafny: str,
    build_command: Sequence[str],
) -> int:
    """Load one manifest and run every public verification phase in one process."""
    try:
        session = _load_session(workspace_root, utility_root, manifest_path, dafny)
    except (OSError, ValueError):
        _emit_outcome("infrastructure_failure", "build")
        return 1
    return run_full_session(session, dafny, build_command)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--workspace-root", default=".", type=Path)
    parser.add_argument("--utility-root", required=True, type=Path)
    parser.add_argument("--manifest", required=True, type=Path)
    parser.add_argument("--dafny", default=dafny_command())
    parser.add_argument("--full", action="store_true")
    parser.add_argument("--build-arg", action="append", default=[])
    arguments = parser.parse_args()
    if arguments.full:
        if not arguments.build_arg:
            parser.error("--full requires at least one --build-arg")
        raise SystemExit(
            run_full(
                arguments.workspace_root,
                arguments.utility_root,
                arguments.manifest,
                arguments.dafny,
                arguments.build_arg,
            )
        )
    raise SystemExit(
        run(
            arguments.workspace_root,
            arguments.utility_root,
            arguments.manifest,
            arguments.dafny,
        )
    )
