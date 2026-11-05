PROJECT_DIR := $(abspath $(dir $(lastword $(MAKEFILE_LIST))))
REPO_ROOT := $(abspath $(PROJECT_DIR)/../../..)
LOCAL_TASK := join

.PHONY: build verify test

build:
	python3 -m benchmark_tools.contribution.make_tasks build --root "$(REPO_ROOT)" --task "$(LOCAL_TASK)"

verify:
	python3 -m benchmark_tools.contribution.verify --project "$(PROJECT_DIR)" --library "$(PROJECT_DIR)/../../core"

test:
	python3 -m benchmark_tools.contribution.make_tasks test --root "$(REPO_ROOT)" --task "$(LOCAL_TASK)"
