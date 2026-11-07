# Shared contributor targets for benchmark task directories.
#
# The including Makefile must define PROJECT_DIR and LOCAL_TASK before the include.
# Define PROJECT_DIR there, not here: inside this file, the last entry of
# MAKEFILE_LIST is this file instead of the task Makefile.
REPO_ROOT := $(abspath $(PROJECT_DIR)/../../..)

.PHONY: build verify test lint final-check

build:
	python3 -m tools.contribution.make_tasks build --root "$(REPO_ROOT)" --task "$(LOCAL_TASK)"

verify:
	python3 -m tools.contribution.verify --project "$(PROJECT_DIR)" --library "$(PROJECT_DIR)/../../core"

test:
	python3 -m tools.contribution.make_tasks test --root "$(REPO_ROOT)" --task "$(LOCAL_TASK)"

lint:
	python3 -m tools.contribution --root "$(REPO_ROOT)" validate "$(LOCAL_TASK)"

final-check:
	python3 -m tools.contribution --root "$(REPO_ROOT)" check "$(LOCAL_TASK)"
