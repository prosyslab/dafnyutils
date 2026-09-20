#!/usr/bin/env bash
set -euo pipefail

blocked_utility="${EVAL_BLOCKED_COREUTIL:-}"
if [[ -n "$blocked_utility" ]]; then
  if [[ ! "$blocked_utility" =~ ^[a-z0-9][a-z0-9-]*$ ]]; then
    printf 'error: invalid blocked coreutils utility: %s\n' "$blocked_utility" >&2
    exit 126
  fi

  canonical_path="/usr/bin/$blocked_utility"
  bin_alias="/bin/$blocked_utility"
  if [[ ( -f "$canonical_path" && -x "$canonical_path" ) ||
        ( -f "$bin_alias" && -x "$bin_alias" ) ]]; then
    printf 'error: coreutils oracle remains executable: %s\n' "$blocked_utility" >&2
    exit 126
  fi
  if [[ ! "$canonical_path" -ef "$bin_alias" ]]; then
    printf 'error: coreutils oracle aliases are not covered by one mount: %s\n' \
      "$blocked_utility" >&2
    exit 126
  fi

  old_ifs="$IFS"
  IFS=:
  for path_dir in ${PATH:-}; do
    [[ -n "$path_dir" ]] || path_dir="."
    candidate="$path_dir/$blocked_utility"
    if [[ -f "$candidate" && -x "$candidate" ]]; then
      printf 'error: alternate coreutils oracle remains on PATH: %s\n' "$candidate" >&2
      exit 126
    fi
  done
  IFS="$old_ifs"

  if ! package_paths="$(dpkg-query -L coreutils)"; then
    printf 'error: unable to inspect the installed coreutils package\n' >&2
    exit 126
  fi
  while IFS= read -r package_path; do
    package_name="${package_path##*/}"
    if [[ "$package_name" == "$blocked_utility" &&
          -f "$package_path" && -x "$package_path" ]]; then
      printf 'error: package-owned coreutils oracle remains executable: %s\n' \
        "$package_path" >&2
      exit 126
    fi
    if [[ "$package_name" == "coreutils" &&
          -f "$package_path" && -x "$package_path" ]]; then
      printf 'error: coreutils multi-call oracle remains executable: %s\n' \
        "$package_path" >&2
      exit 126
    fi
  done <<< "$package_paths"
fi

exec "$@"
