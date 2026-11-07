PROJECT_DIR := $(abspath $(dir $(lastword $(MAKEFILE_LIST))))
LOCAL_TASK := date
include $(PROJECT_DIR)/../../../tools/task.mk

BUILD_DIR ?= _build
ROOT_BUILD_DIR := $(if $(filter /%,$(BUILD_DIR)),$(BUILD_DIR),$(REPO_ROOT)/$(BUILD_DIR))
COREUTILS_BUILD_DIR := $(ROOT_BUILD_DIR)/coreutils
TOUCH_TIME_PARSER ?= $(ROOT_BUILD_DIR)/bench/touch_time_parser

.PHONY: build-time-parser

# Reuse the canonical gnulib companion target; GNU prerequisites are built separately.
build-time-parser:
	@test -f "$(COREUTILS_BUILD_DIR)/lib/config.h" -a -f "$(COREUTILS_BUILD_DIR)/lib/libcoreutils.a"
	$(MAKE) -C "$(REPO_ROOT)/bench/utils/touch" "$(TOUCH_TIME_PARSER)" BUILD_DIR="$(ROOT_BUILD_DIR)" TOUCH_TIME_PARSER="$(TOUCH_TIME_PARSER)"
