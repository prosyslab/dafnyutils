"""Build the fuzzer's optional native observation libraries."""

from __future__ import annotations

import argparse
import os
import shlex
import subprocess
from dataclasses import dataclass
from pathlib import Path

FUZZER_ROOT = Path(__file__).resolve().parents[1]
REPO_ROOT = FUZZER_ROOT.parents[1]
COMMON_FLAGS = (
    "-std=c11",
    "-O2",
    "-fPIC",
    "-fvisibility=hidden",
    "-Wall",
    "-Wextra",
    "-Werror",
)


@dataclass(frozen=True)
class NativeLibrary:
    source: Path
    filename: str
    options: tuple[str, ...]
    libraries: tuple[str, ...] = ()


LIBRARIES = {
    "clock-observer": NativeLibrary(
        source=FUZZER_ROOT / "native" / "clock_syscall.c",
        filename="libclock_syscall.so",
        options=("-shared", "-Wl,-z,defs"),
    ),
    "startup-reference": NativeLibrary(
        source=REPO_ROOT / "bench" / "core" / "IOStartup.c",
        filename="libdafnyutils_reference_startup.so",
        options=(
            "-DDFY_STARTUP_COMPILE_PROFILE=1",
            "-shared",
            "-Wl,-z,defs",
            "-Wl,-soname,libdafnyutils_reference_startup.so",
        ),
        libraries=("-ldl",),
    ),
}


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("library", choices=LIBRARIES)
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=FUZZER_ROOT / "target" / "native",
        help="directory for the compiled shared library",
    )
    args = parser.parse_args(argv)
    compiler = shlex.split(os.environ.get("CC", "cc"))
    if not compiler:
        parser.error("CC must name a C compiler")

    library = LIBRARIES[args.library]
    args.output_dir.mkdir(parents=True, exist_ok=True)
    output = args.output_dir / library.filename
    command = [
        *compiler,
        *COMMON_FLAGS,
        *library.options,
        "-o",
        str(output),
        str(library.source),
        *library.libraries,
    ]
    result = subprocess.run(command, check=False)
    if result.returncode == 0:
        print(output)
    return result.returncode


if __name__ == "__main__":
    raise SystemExit(main())
