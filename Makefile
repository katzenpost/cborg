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
	Cborg.Tests.Reference \
	Cborg.Tests.Encoding \
	Cborg.Tests.Properties \
	Cborg.Tests.ThinClient

.PHONY: all build test interop vectors clean

all: build

build:
	$(LAKE) build

test:
	$(LAKE) build $(TESTS)
	@set -e; for t in $(TESTS); do LEAN_ABORT_ON_PANIC=1 ./$(BIN)/$${t//./-}; done

# Check that Go decodes Lean's thin client requests into the expected values.
# Needs Go and a katzenpost checkout next to this repository.
interop: test
	cd scripts/gen-vectors && go run . verify ../../.lake/thinclient

# Regenerate testdata/thinclient from the Go daemon's types.
vectors:
	cd scripts/gen-vectors && go run . gen ../../testdata/thinclient

clean:
	$(LAKE) clean
