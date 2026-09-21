#!/usr/bin/env bash
set -euo pipefail

cd /workspace/dafnyutils
mkdir -p _build/setup
setup_log="_build/setup/post-create-$(date -u +%Y%m%dT%H%M%SZ)-$$.log"
exec > >(tee "$setup_log") 2>&1
trap 'printf "Setup failed at line %s. Log: %s\nRetry: bash .devcontainer/post-create.sh\n" "$LINENO" "$setup_log" >&2' ERR
printf 'Setup log: %s\n' "$setup_log"
python3 -m venv .venv
.venv/bin/python -m pip install -e '.[dev,contributor]'
git submodule update --init --recursive
# Ignore only this known GNU bootstrap output, without changing the pinned source.
exclude_file=$(git -C coreutils rev-parse --path-format=absolute --git-path info/exclude)
mkdir -p "$(dirname "$exclude_file")"
if [[ ! -f "$exclude_file" ]] || ! grep -Fxq '/m4/extern-inline.m4' "$exclude_file"; then
    printf '\n/m4/extern-inline.m4\n' >> "$exclude_file"
fi
export PATH="/workspace/dafnyutils/.venv/bin:$PATH"
make build-dafny
make check-environment

versions_log="${setup_log%.log}-versions.txt"
{
    printf 'Recorded at: '
    date -u +%Y-%m-%dT%H:%M:%SZ
    printf '\nRepository revision\n'
    git rev-parse HEAD
    git submodule status --recursive
    printf '\nDafny\n'
    dafny-benchmark --version
    printf '\n.NET SDKs and runtimes\n'
    dotnet --list-sdks
    dotnet --list-runtimes
    printf '\nRust toolchain\n'
    rustup show active-toolchain
    rustc --version
    cargo --version
    printf '\nPython packages\n'
    python3 --version
    python3 -m pip freeze --all
    printf '\nSystem packages\n'
    dpkg-query -W -f='${binary:Package}\t${Version}\n'
} > "$versions_log"
printf 'Dependency versions: %s\n' "$versions_log"
