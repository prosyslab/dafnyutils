#!/usr/bin/env bash
set -euo pipefail
@{BUILD_ENVIRONMENT}
cleanup_dotnet_build_servers() {
  dotnet build-server shutdown >/dev/null 2>&1 || true
}
trap cleanup_dotnet_build_servers EXIT
workspace_root="${EVAL_WORKSPACE_DIR:-$PWD}"
cd "$workspace_root"
python3 -m entry_contract check \
  --workspace-root "$workspace_root" \
  --utility-root @{UTILITY_ROOT} \
  --manifest @{MANIFEST_PATH}
mkdir -p _build/bench
TMPDIR=/tmp "${DAFNY_BENCHMARK:-dafny-benchmark}" @{RUNTIME_BUILD_ARGS}
