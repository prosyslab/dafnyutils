#!/usr/bin/env bash
set -u

container_name=$1
project_name=$2
service=$3
command=$4
infrastructure_report_env=$5
shift 5

compose_args=(docker compose)
if [[ -n "$project_name" ]]; then
  compose_args+=(-p "$project_name")
fi
for compose_file in "$@"; do
  compose_args+=(-f "$compose_file")
done
compose_args+=(run --no-TTY --interactive=false)
if [[ "$service" == evaluator ]]; then
  compose_args+=(--env "$infrastructure_report_env" --env PYTEST_PLUGINS)
fi
compose_args+=(--name "$container_name" "$service" bash -lc "$command")

capture_dir=$(mktemp -d)
temp_status=$?
if [[ $temp_status -ne 0 ]]; then
  exit "$temp_status"
fi
compose_output="$capture_dir/compose"
container_stdout="$capture_dir/stdout"
container_stderr="$capture_dir/stderr"
trap 'rm -f "$compose_output" "$container_stdout" "$container_stderr"; rmdir "$capture_dir"' EXIT

if docker inspect "$container_name" >/dev/null 2>&1; then
  printf '[docker inspect] evaluator container already exists: %s\n' "$container_name" >&2
  exit 1
fi

"${compose_args[@]}" >"$compose_output" 2>&1
run_status=$?
docker logs "$container_name" >"$container_stdout" 2>"$container_stderr"
logs_status=$?
if [[ $logs_status -ne 0 ]]; then
  sed 's/^/[docker compose] /' "$compose_output" >&2
  sed 's/^/[docker logs] /' "$container_stderr" >&2
fi
docker rm -f "$container_name" >"$compose_output" 2>&1
rm_status=$?
if [[ $rm_status -ne 0 ]]; then
  sed 's/^/[docker rm] /' "$compose_output" >&2
fi
if [[ $logs_status -eq 0 && $rm_status -eq 0 ]]; then
  cat "$container_stdout"
  cat "$container_stderr" >&2
fi
if [[ $logs_status -ne 0 ]]; then
  exit "$logs_status"
fi
if [[ $rm_status -ne 0 ]]; then
  exit "$rm_status"
fi
exit "$run_status"
