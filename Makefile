# Standalone benchmark checks and local toolchain builds.

.PHONY: test test-unit test-integration test-final scaffold build-coreutils clean

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

build-coreutils:
	@tools/build-coreutils

clean:
	@test "$(abspath $(or $(BUILD_DIR),_build))" = "$(CURDIR)/_build" || \
		{ echo 'clean only removes the default _build directory' >&2; exit 2; }
	rm -rf -- "$(CURDIR)/_build"
