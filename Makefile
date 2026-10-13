# cborg
#
# Lake does the building; this file runs the test suites. Run from the
# repository root: the suites load their vectors from testdata/ by relative path.

SHELL := /bin/bash
LAKE  ?= lake
BIN   := .lake/build/bin

# Test executables, as declared in lakefile.toml. Lake names each binary after
# its module with the dots turned into dashes.
TESTS := \
	Cborg.Tests.Reference

.PHONY: all build test clean

all: build

build:
	$(LAKE) build

test:
	$(LAKE) build $(TESTS)
	@set -e; for t in $(TESTS); do LEAN_ABORT_ON_PANIC=1 ./$(BIN)/$${t//./-}; done

clean:
	$(LAKE) clean
