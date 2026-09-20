PROJECT_DIR := $(abspath $(dir $(lastword $(MAKEFILE_LIST))))
REPO_ROOT := $(abspath $(PROJECT_DIR)/../../..)
LOCAL_TASK := $(notdir $(PROJECT_DIR))
BUILD_DIR ?= _build
ROOT_BUILD_DIR := $(if $(filter /%,$(BUILD_DIR)),$(BUILD_DIR),$(REPO_ROOT)/$(BUILD_DIR))
COREUTILS_BUILD_DIR := $(ROOT_BUILD_DIR)/coreutils
TOUCH_TIME_PARSER := $(ROOT_BUILD_DIR)/bench/touch_time_parser

.PHONY: build verify test build-time-parser

build:
	python3 -m benchmarks.make_tasks build --root "$(REPO_ROOT)" --task "$(LOCAL_TASK)"

verify:
	python3 -m benchmarks.verify --project "$(PROJECT_DIR)" --library "$(PROJECT_DIR)/../../core"

test:
	python3 -m benchmarks.make_tasks test --root "$(REPO_ROOT)" --task "$(LOCAL_TASK)"

build-time-parser:
	$(MAKE) -C "$(REPO_ROOT)" build-coreutils BUILD_DIR="$(BUILD_DIR)"
	$(MAKE) "$(TOUCH_TIME_PARSER)"

$(TOUCH_TIME_PARSER): $(REPO_ROOT)/bench/core/TouchTimeParser.c \
		$(COREUTILS_BUILD_DIR)/lib/config.h $(COREUTILS_BUILD_DIR)/lib/libcoreutils.a
	mkdir -p "$(dir $@)"
	$(CC) -std=c11 -O2 -Wall -Wextra -Werror \
		-I"$(COREUTILS_BUILD_DIR)/lib" -I"$(REPO_ROOT)/coreutils/gnulib/lib" \
		-Wl,--wrap=rpl_time -o "$@" "$<" "$(COREUTILS_BUILD_DIR)/lib/libcoreutils.a"
