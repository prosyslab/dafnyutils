# Standalone benchmark checks and local toolchain builds.

.PHONY: test test-unit test-integration test-final scaffold fmt build-coreutils clean

test:
	@$(MAKE) --no-print-directory test-unit

test-unit:
	@python3 -m pytest -q

test-integration:
	@python3 -m pytest -q -m integration

test-final:
	@$(MAKE) --no-print-directory test-unit && $(MAKE) --no-print-directory test-integration

scaffold:
	@test -n "$(KIND)" -a -n "$(ID)" || \
		{ echo 'usage: make scaffold KIND=<coreutils|algorithm> ID=<task-id>' >&2; exit 2; }
	@python3 -m tools.scaffold --kind "$(KIND)" --id "$(ID)"

# Python and Rust are formatted everywhere because CI enforces both. Dafny is not enforced,
# so only the .dfy files you changed or added are formatted, as the pre-commit hook does.
fmt:
	ruff format .
	ruff check --fix --exit-zero .
	cargo fmt --manifest-path tools/coreutils_fuzzer/Cargo.toml --all
	{ git diff -z --name-only --diff-filter=ACMR HEAD -- '*.dfy'; \
		git ls-files -z --others --exclude-standard -- '*.dfy'; } | xargs -0 -r dafny format

build-coreutils:
	@tools/build-coreutils

clean:
	@test "$(abspath $(or $(BUILD_DIR),_build))" = "$(CURDIR)/_build" || \
		{ echo 'clean only removes the default _build directory' >&2; exit 2; }
	rm -rf -- "$(CURDIR)/_build"
