#!/usr/bin/env bash
set -euo pipefail
script_path="${BASH_SOURCE[0]}"
case "$script_path" in
  */*) script_dir="${script_path%/*}" ;;
  *) script_dir="." ;;
esac
script_dir="$(cd "$script_dir" && pwd)"
workspace_root="${EVAL_WORKSPACE_DIR:-$(cd "$script_dir/@{SCRIPT_PARENT}" && pwd)}"
cd "$workspace_root"
python3 -m entry_contract check \
  --workspace-root "$workspace_root" \
  --utility-root @{UTILITY_ROOT} \
  --manifest @{MANIFEST_PATH}
