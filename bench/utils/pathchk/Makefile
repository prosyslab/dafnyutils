PROJECT_DIR := $(abspath $(dir $(lastword $(MAKEFILE_LIST))))
REPO_ROOT := $(abspath $(PROJECT_DIR)/../../..)
LOCAL_TASK := pathchk

.PHONY: build verify test

build:
	python3 -m evaluation.contribution.make_tasks build --root "$(REPO_ROOT)" --task "$(LOCAL_TASK)"

verify:
	python3 -m evaluation.contribution.verify --project "$(PROJECT_DIR)" --library "$(PROJECT_DIR)/../../core"

test:
	python3 -m evaluation.contribution.make_tasks test --root "$(REPO_ROOT)" --task "$(LOCAL_TASK)"
