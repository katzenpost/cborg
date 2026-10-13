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

.PHONY: all build test interop pycheck vectors clean

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

# Check Lean against Python's cbor2, which the Python thin client uses.
# Needs a virtualenv: python3 -m venv .venv && .venv/bin/pip install 'cbor2>=5.6.5,<7'
PYTHON ?= .venv/bin/python
pycheck: test
	$(LAKE) build Cborg.Tests.Corpus
	$(PYTHON) -I scripts/cbor2_check.py corpus .lake/cbor2-corpus
	./$(BIN)/Cborg-Tests-Corpus .lake/cbor2-corpus
	$(PYTHON) -I scripts/cbor2_check.py check

# Regenerate testdata/thinclient from the Go daemon's types.
vectors:
	cd scripts/gen-vectors && go run . gen ../../testdata/thinclient

clean:
	$(LAKE) clean
