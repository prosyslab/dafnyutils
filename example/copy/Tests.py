"""Check the tutorial's observable IO behavior on Linux."""

import os
import subprocess
from pathlib import Path

PROGRAM = Path(__file__).resolve().parents[2] / "_build/tutorial-copy/copy.dll"


# Empty input must produce no output and succeed.
def test_empty_input() -> None:
    result = subprocess.run(
        ["dotnet", str(PROGRAM)], input=b"", capture_output=True, timeout=10, check=False
    )
    assert (result.stdout, result.stderr, result.returncode) == (b"", b"", 0)


# All byte values must survive unchanged, including NUL and non-UTF-8 bytes.
def test_binary_input() -> None:
    data = bytes(range(256))
    result = subprocess.run(
        ["dotnet", str(PROGRAM)], input=data, capture_output=True, timeout=10, check=False
    )
    assert (result.stdout, result.stderr, result.returncode) == (data, b"", 0)


# A failed stdout write must return failure instead of claiming a successful copy.
def test_full_output_device() -> None:
    with open("/dev/full", "wb") as output:
        result = subprocess.run(
            ["dotnet", str(PROGRAM)], input=b"hello\n", stdout=output,
            stderr=subprocess.PIPE, timeout=10, check=False,
        )
    assert (result.stderr, result.returncode) == (b"", 1)


# Reading a directory as stdin must return failure without emitting data.
def test_directory_input(tmp_path: Path) -> None:
    descriptor = os.open(tmp_path, os.O_RDONLY | os.O_DIRECTORY)
    try:
        result = subprocess.run(
            ["dotnet", str(PROGRAM)], stdin=descriptor, capture_output=True,
            timeout=10, check=False,
        )
    finally:
        os.close(descriptor)
    assert (result.stdout, result.stderr, result.returncode) == (b"", b"", 1)
