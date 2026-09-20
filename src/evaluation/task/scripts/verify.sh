#!/usr/bin/env bash
set -euo pipefail
verification_infrastructure_failure() {
  printf 'DAFNY_VERIFICATION_OUTCOME=infrastructure_failure phase=%s\n' "$1"
  exit 1
}
script_path="${BASH_SOURCE[0]}"
case "$script_path" in
  */*) script_dir="${script_path%/*}" ;;
  *) script_dir="." ;;
esac
script_dir="$(cd "$script_dir" && pwd)" ||
  verification_infrastructure_failure build
if [[ -n "${EVAL_WORKSPACE_DIR:-}" ]]; then
  workspace_root="$EVAL_WORKSPACE_DIR"
else
  workspace_root="$(cd "$script_dir/@{SCRIPT_PARENT}" && pwd)" ||
    verification_infrastructure_failure build
fi
cd "$workspace_root" || verification_infrastructure_failure build
@{BUILD_ENVIRONMENT}
cleanup_dotnet_build_servers() {
  dotnet build-server shutdown >/dev/null 2>&1 || true
}
trap cleanup_dotnet_build_servers EXIT
mkdir -p _build/bench ||
  verification_infrastructure_failure build
command -v python3 >/dev/null 2>&1 ||
  verification_infrastructure_failure evidence
python3 -c 'import verification' ||
  verification_infrastructure_failure evidence
python3 -m verification \
  --workspace-root "$workspace_root" \
  --utility-root @{UTILITY_ROOT} \
  --manifest "$script_dir/entry_contract.json" \
  --dafny "${DAFNY_BENCHMARK:-dafny-benchmark}" \
  --full \
  --build-arg="${DAFNY_BENCHMARK:-dafny-benchmark}" \
  @{FULL_BUILD_ARGS}
