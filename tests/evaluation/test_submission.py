"""Receive controlled archives using only the public submission contract."""

import gzip
import hashlib
import io
import os
import tarfile
from pathlib import Path

import pytest

from evaluation.submission.archive import SubmissionError, receive_submission
from evaluation.task.release import ArchiveLimits, TaskReleaseManifest, publish_release


@pytest.fixture(scope="module")
def release(tmp_path_factory: pytest.TempPathFactory) -> tuple[Path, TaskReleaseManifest]:
    directory = tmp_path_factory.mktemp("archive-release") / "release"
    return directory, publish_release(("algorithm-1",), directory)


def _archive(path: Path, entries: list[tuple[str, bytes, bytes]]) -> Path:
    with tarfile.open(path, "w:gz", format=tarfile.USTAR_FORMAT) as archive:
        for name, payload, kind in entries:
            member = tarfile.TarInfo(name)
            member.type = kind
            member.size = len(payload) if kind == tarfile.REGTYPE else 0
            member.linkname = "../../outside" if kind in (tarfile.SYMTYPE, tarfile.LNKTYPE) else ""
            archive.addfile(member, io.BytesIO(payload) if kind == tarfile.REGTYPE else None)
    return path


def _outputs(directory: Path, manifest: TaskReleaseManifest) -> list[tuple[str, bytes, bytes]]:
    return [
        (p, (directory / "workspace" / p).read_bytes(), tarfile.REGTYPE)
        for p in manifest.files
        if any(Path(p).is_relative_to(root) for root in manifest.task_roots)
    ]


# Utility test files stay out of releases and candidate archives cannot supply replacements.
def test_utility_release_rejects_evaluator_test_submission(tmp_path: Path) -> None:
    release_dir = tmp_path / "release"
    manifest = publish_release(("cat",), release_dir)
    reserved = "bench/utils/cat/Tests.dfy"
    assert reserved in manifest.excluded_paths
    assert reserved not in manifest.files
    archive = _archive(
        tmp_path / "submission.tar.gz",
        [*_outputs(release_dir, manifest), (reserved, b"module FakeTests {}", tarfile.REGTYPE)],
    )

    with pytest.raises(SubmissionError, match="excluded archive path"):
        receive_submission(archive, manifest=manifest, run_directory=tmp_path / "run")


# Extra candidate sources survive reception and provenance hashes the exact compressed bytes.
def test_receive_preserves_extra_candidate_sources(tmp_path: Path, release) -> None:
    directory, manifest = release
    extra = ("bench/algorithm/1/helpers/Arithmetic.dfy", b"module Arithmetic {}", tarfile.REGTYPE)
    archive = _archive(tmp_path / "submission.tar.gz", [*_outputs(directory, manifest), extra])
    expected = hashlib.sha256(archive.read_bytes()).hexdigest()
    received = receive_submission(archive, manifest=manifest, run_directory=tmp_path / "run")
    archive.unlink()
    assert (received.workspace / extra[0]).read_bytes() == extra[1]
    assert received.archive_sha256 == expected
    assert hashlib.sha256(received.archive_path.read_bytes()).hexdigest() == expected


# Unsafe names are rejected before any path outside the staging directory is written.
@pytest.mark.parametrize(
    "name",
    [
        "../outside",
        "/outside",
        "bench/algorithm/1/../../outside",
        "bench//algorithm/1/x",
        "bench/algorithm/1/./x",
        "bench\\algorithm\\1\\x",
    ],
)
def test_receive_rejects_unsafe_paths(tmp_path: Path, release, name: str) -> None:
    _, manifest = release
    archive = _archive(tmp_path / "submission.tar.gz", [(name, b"x", tarfile.REGTYPE)])
    with pytest.raises(SubmissionError, match="unsafe archive path"):
        receive_submission(archive, manifest=manifest, run_directory=tmp_path / "run")
    assert not (tmp_path / "outside").exists()


# Links and special entries cannot change archive restoration semantics.
@pytest.mark.parametrize(
    "kind", [tarfile.SYMTYPE, tarfile.LNKTYPE, tarfile.FIFOTYPE, tarfile.CHRTYPE]
)
def test_receive_rejects_nonregular_entries(tmp_path: Path, release, kind: bytes) -> None:
    _, manifest = release
    archive = _archive(tmp_path / "submission.tar.gz", [("bench/algorithm/1/x", b"", kind)])
    with pytest.raises(SubmissionError, match="unsupported archive entry"):
        receive_submission(archive, manifest=manifest, run_directory=tmp_path / "run")


# Duplicate paths cannot hide conflicting candidate content.
def test_receive_rejects_duplicate_entries(tmp_path: Path, release) -> None:
    _, manifest = release
    entry = ("bench/algorithm/1/x", b"x", tarfile.REGTYPE)
    archive = _archive(tmp_path / "submission.tar.gz", [entry, entry])
    with pytest.raises(SubmissionError, match="duplicate archive entry"):
        receive_submission(archive, manifest=manifest, run_directory=tmp_path / "run")


# Candidate archives cannot modify immutable formal specifications.
def test_receive_rejects_changed_fixed_material(tmp_path: Path, release) -> None:
    _, manifest = release
    archive = _archive(
        tmp_path / "submission.tar.gz",
        [("bench/algorithm/1/Spec.dfy", b"altered", tarfile.REGTYPE)],
    )
    with pytest.raises(SubmissionError, match="fixed release file changed"):
        receive_submission(archive, manifest=manifest, run_directory=tmp_path / "run")


# Archives cannot add shared-core or checker files outside task roots.
@pytest.mark.parametrize(
    "name", ["bench/core/Functional.dfy", "eval_support/algorithm-1/verify.sh"]
)
def test_receive_rejects_non_candidate_roots(tmp_path: Path, release, name: str) -> None:
    _, manifest = release
    archive = _archive(tmp_path / "submission.tar.gz", [(name, b"x", tarfile.REGTYPE)])
    with pytest.raises(SubmissionError, match="outside task roots"):
        receive_submission(archive, manifest=manifest, run_directory=tmp_path / "run")


# Missing mandatory output paths prevent an incomplete archive from reaching the evaluator.
def test_receive_rejects_missing_required_outputs(tmp_path: Path, release) -> None:
    _, manifest = release
    archive = _archive(tmp_path / "submission.tar.gz", [])
    with pytest.raises(SubmissionError, match="required outputs missing"):
        receive_submission(archive, manifest=manifest, run_directory=tmp_path / "run")


# Compressed input size is bounded before parsing or extraction.
def test_receive_enforces_compressed_limit(tmp_path: Path, release) -> None:
    _, manifest = release
    limited = manifest.model_copy(update={"limits": ArchiveLimits(compressed_bytes=10)})
    archive = _archive(tmp_path / "submission.tar.gz", [])
    with pytest.raises(SubmissionError, match="compressed archive size limit"):
        receive_submission(archive, manifest=limited, run_directory=tmp_path / "run")


# Highly compressible payloads cannot exceed the expansion budget.
def test_receive_enforces_expansion_limit(tmp_path: Path, release) -> None:
    _, manifest = release
    limited = manifest.model_copy(update={"limits": ArchiveLimits(expanded_bytes=100)})
    archive = tmp_path / "submission.tar.gz"
    archive.write_bytes(gzip.compress(b"0" * 1000))
    with pytest.raises(SubmissionError, match="expanded archive size limit"):
        receive_submission(archive, manifest=limited, run_directory=tmp_path / "run")


# Per-file payloads cannot evade the manifest's file budget.
def test_receive_enforces_file_limit(tmp_path: Path, release) -> None:
    _, manifest = release
    limited = manifest.model_copy(update={"limits": ArchiveLimits(file_bytes=2)})
    archive = _archive(
        tmp_path / "submission.tar.gz", [("bench/algorithm/1/x", b"123", tarfile.REGTYPE)]
    )
    with pytest.raises(SubmissionError, match="file size limit"):
        receive_submission(archive, manifest=limited, run_directory=tmp_path / "run")


# Many small entries cannot exceed the manifest's entry count budget.
def test_receive_enforces_entry_limit(tmp_path: Path, release) -> None:
    _, manifest = release
    limited = manifest.model_copy(update={"limits": ArchiveLimits(entries=1)})
    archive = _archive(
        tmp_path / "submission.tar.gz",
        [(f"bench/algorithm/1/{n}", b"", tarfile.REGTYPE) for n in range(2)],
    )
    with pytest.raises(SubmissionError, match="entry count limit"):
        receive_submission(archive, manifest=limited, run_directory=tmp_path / "run")


# Missing immutable task files violate the complete task-directory submission contract.
def test_receive_requires_fixed_task_files(tmp_path: Path, release) -> None:
    directory, manifest = release
    entries = [
        entry for entry in _outputs(directory, manifest) if entry[0] != "bench/algorithm/1/Spec.dfy"
    ]
    archive = _archive(tmp_path / "submission.tar.gz", entries)
    with pytest.raises(SubmissionError, match="Spec.dfy"):
        receive_submission(archive, manifest=manifest, run_directory=tmp_path / "run")


# PAX extended path names cannot carry embedded NULs into filesystem operations.
def test_receive_rejects_nul_pax_path(tmp_path: Path, release) -> None:
    _, manifest = release
    path = tmp_path / "submission.tar.gz"
    with tarfile.open(path, "w:gz", format=tarfile.PAX_FORMAT) as archive:
        member = tarfile.TarInfo("bench/algorithm/1/x")
        member.pax_headers = {"path": "bench/algorithm/1/x\x00evil"}
        member.size = 1
        archive.addfile(member, io.BytesIO(b"x"))
    with pytest.raises(SubmissionError, match="unsafe archive path"):
        receive_submission(path, manifest=manifest, run_directory=tmp_path / "run")


# A FIFO supplied as the archive is rejected without waiting for a writer.
def test_receive_rejects_fifo_archive(tmp_path: Path, release) -> None:
    _, manifest = release
    path = tmp_path / "submission.tar.gz"
    os.mkfifo(path)
    with pytest.raises(SubmissionError, match="regular archive file"):
        receive_submission(path, manifest=manifest, run_directory=tmp_path / "run")


# A final-path symlink is rejected even when it points to a valid regular archive.
def test_receive_rejects_symlink_archive(tmp_path: Path, release) -> None:
    _, manifest = release
    target = _archive(tmp_path / "target.tar.gz", [])
    path = tmp_path / "submission.tar.gz"
    path.symlink_to(target)
    with pytest.raises(SubmissionError, match="regular archive file"):
        receive_submission(path, manifest=manifest, run_directory=tmp_path / "run")


# Appended tar members cannot evade entry validation behind an earlier tar end marker.
def test_receive_rejects_concatenated_tar_payload(tmp_path: Path, release) -> None:
    directory, manifest = release
    first = _archive(tmp_path / "first.tar.gz", _outputs(directory, manifest))
    second = _archive(tmp_path / "second.tar.gz", [("../outside", b"x", tarfile.REGTYPE)])
    path = tmp_path / "submission.tar.gz"
    path.write_bytes(
        gzip.compress(gzip.decompress(first.read_bytes()) + gzip.decompress(second.read_bytes()))
    )
    with pytest.raises(SubmissionError, match="trailing data"):
        receive_submission(path, manifest=manifest, run_directory=tmp_path / "run")


# Oversized extended names are bounded before allocating path component structures.
def test_receive_rejects_oversized_pax_path(tmp_path: Path, release) -> None:
    _, manifest = release
    path = tmp_path / "submission.tar.gz"
    with tarfile.open(path, "w:gz", format=tarfile.PAX_FORMAT) as archive:
        member = tarfile.TarInfo("bench/algorithm/1/x")
        member.pax_headers = {"path": "bench/algorithm/1/" + "nested/" * 1000}
        member.size = 1
        archive.addfile(member, io.BytesIO(b"x"))
    with pytest.raises(SubmissionError, match="path length limit"):
        receive_submission(path, manifest=manifest, run_directory=tmp_path / "run")


# Directory entries cannot carry undisclosed payload bytes.
def test_receive_rejects_directory_payload(tmp_path: Path, release) -> None:
    _, manifest = release
    path = tmp_path / "submission.tar.gz"
    with tarfile.open(path, "w:gz") as archive:
        member = tarfile.TarInfo("bench/algorithm/1/new-directory")
        member.type = tarfile.DIRTYPE
        member.size = 1
        archive.addfile(member, io.BytesIO(b"x"))
    with pytest.raises(SubmissionError, match="directory entry carries payload"):
        receive_submission(path, manifest=manifest, run_directory=tmp_path / "run")
