#!/usr/bin/env bash
set -euo pipefail

cd /workspace/dafnyutils
python3 -m venv .venv
.venv/bin/python -m pip install -e '.[dev,contributor]'
git submodule update --init --recursive
make build-dafny
.venv/bin/python -c 'import benchmarks; print("dafnyutils import OK")'
