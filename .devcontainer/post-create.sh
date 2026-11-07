#!/usr/bin/env bash
# Prepare the development container: Python and Rust tooling, submodules, a smoke test
# and a record of tool versions. Run it again after a failure; finished steps are reused.
set -Eeuo pipefail

readonly REPO=/workspace/dafnyutils
# The nested gnulib submodule lives on git.savannah.gnu.org, which often answers HTTP 500.
# The GitHub mirror serves the same pinned commit, and git verifies its hash.
readonly GNULIB_URL=https://git.savannah.gnu.org/git/gnulib.git
readonly GNULIB_MIRROR_URL=https://github.com/coreutils/gnulib.git

# Run a command up to $1 times, waiting 10, 20, 40... seconds between attempts.
retry() {
    local attempts=$1 delay=10 attempt
    shift
    for ((attempt = 1; attempt < attempts; attempt++)); do
        "$@" && return
        printf 'Attempt %s of %s failed: %s\nRetrying in %s seconds.\n' \
            "$attempt" "$attempts" "$*" "$delay" >&2
        sleep "$delay"
        delay=$((delay * 2))
    done
    "$@"
}

report_failure() {
    printf 'Setup failed at line %s. Log: %s\nRetry: bash .devcontainer/post-create.sh\n' \
        "$1" "$setup_log" >&2
}

install_python_tools() {
    python3 -m venv .venv
    .venv/bin/python -m pip install -e '.[dev,contributor]'
    export PATH="$REPO/.venv/bin:$PATH"
}

checkout_submodules() {
    local update=(submodule update --init --recursive)
    git "${update[@]}" && return
    printf 'Submodule download failed; retrying gnulib through %s\n' "$GNULIB_MIRROR_URL" >&2
    retry 3 git -c "url.${GNULIB_MIRROR_URL}.insteadOf=${GNULIB_URL}" "${update[@]}"
}

# Ignore only this known GNU bootstrap output, without changing the pinned source.
ignore_bootstrap_output() {
    local exclude_file
    exclude_file=$(git -C coreutils rev-parse --path-format=absolute --git-path info/exclude)
    mkdir -p "$(dirname "$exclude_file")"
    grep -Fxqs '/m4/extern-inline.m4' "$exclude_file" ||
        printf '\n/m4/extern-inline.m4\n' >> "$exclude_file"
}

smoke_test() {
    python3 -m benchmarks --help
    python3 -m tools.contribution --help
    make test
}

# The fuzzer and the `final-check` task target start containers on the host Docker.
warn_if_docker_unreachable() {
    docker info > /dev/null 2>&1 && return
    printf '%s\n' \
        'Warning: the host Docker daemon is not reachable from this container.' \
        'Fuzzing needs it; see "Set up your checkout" in CONTRIBUTING.md.' >&2
}

section() {
    printf '\n%s\n' "$1"
}

record_versions() {
    local versions_log="${setup_log%.log}-versions.txt"
    {
        printf 'Recorded at: %s\n' "$(date -u +%Y-%m-%dT%H:%M:%SZ)"
        section 'Repository revision'
        git rev-parse HEAD
        git submodule status --recursive
        section 'Rust toolchain'
        rustup show active-toolchain
        rustc --version
        cargo --version
        section '.NET SDK and Dafny'
        dotnet --list-sdks
        dafny --version
        section 'Docker CLI'
        docker --version
        docker compose version
        section 'Python packages'
        python3 --version
        python3 -m pip freeze --all
        section 'System packages'
        dpkg-query -W -f='${binary:Package}\t${Version}\n'
    } > "$versions_log"
    printf 'Dependency versions: %s\n' "$versions_log"
}

cd "$REPO"
mkdir -p _build/setup
setup_log="_build/setup/post-create-$(date -u +%Y%m%dT%H%M%SZ)-$$.log"
exec > >(tee "$setup_log") 2>&1
trap 'report_failure "$LINENO"' ERR
printf 'Setup log: %s\n' "$setup_log"

install_python_tools
checkout_submodules
ignore_bootstrap_output
smoke_test
warn_if_docker_unreachable
record_versions
