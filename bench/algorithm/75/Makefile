PROJECT_DIR := $(abspath $(dir $(lastword $(MAKEFILE_LIST))))
REPO_ROOT := $(abspath $(PROJECT_DIR)/../../..)
LOCAL_TASK := algorithm-$(notdir $(PROJECT_DIR))

.PHONY: build verify test

build:
	python3 -m benchmarks.make_tasks build --root "$(REPO_ROOT)" --task "$(LOCAL_TASK)"

verify:
	python3 -m benchmarks.verify --project "$(PROJECT_DIR)"

test:
	python3 -m benchmarks.make_tasks test --root "$(REPO_ROOT)" --task "$(LOCAL_TASK)"
