DAFNY := dafny-benchmark
PROJECT_DIR := $(abspath $(dir $(lastword $(MAKEFILE_LIST))))
REPO_ROOT := $(abspath $(PROJECT_DIR)/../..)
OUTPUT_DIR := $(REPO_ROOT)/_build/tutorial-copy
FLAGS := --standard-libraries:false

.PHONY: verify build test

verify:
	$(DAFNY) verify $(FLAGS) --verify-included-files \
		--library:$(REPO_ROOT)/bench/core --allow-warnings CopyCli.dfy

build:
	mkdir -p "$(OUTPUT_DIR)"
	$(DAFNY) build $(FLAGS) --no-verify --output "$(OUTPUT_DIR)/copy.dll" \
		CopyCli.dfy "$(REPO_ROOT)/bench/core/IOExtern.cs"

test: build
	python3 -m pytest -q -n0 Tests.py
