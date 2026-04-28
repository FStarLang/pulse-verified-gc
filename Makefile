# Root Makefile for pulse-verified-gc
#
# The mark-and-sweep/ Makefile builds all modules (common/ + mark-and-sweep/)
# in a single incremental build via `fstar.exe --dep full`.
#
# Run `./setup.sh` once after cloning to build the F* toolchain from source.
#
# Usage:
#   ./setup.sh      Build F* from source (one-time)
#   make            Verify all modules (common/ + mark-and-sweep/)
#   make extract    Verify + extract mark-and-sweep to C
#   make snapshot   Verify + extract + create snapshot/
#   make clean      Clean all build artifacts

FSTAR_HOME ?= $(CURDIR)/fstar
KRML_HOME  ?= $(FSTAR_HOME)/karamel

.PHONY: all verify extract snapshot clean

all: verify

verify:
	+$(MAKE) -C mark-and-sweep FSTAR_HOME=$(FSTAR_HOME)

extract:
	+$(MAKE) -C mark-and-sweep extract FSTAR_HOME=$(FSTAR_HOME) KRML_HOME=$(KRML_HOME)

snapshot:
	+$(MAKE) -C mark-and-sweep snapshot FSTAR_HOME=$(FSTAR_HOME) KRML_HOME=$(KRML_HOME)

clean:
	+$(MAKE) -C mark-and-sweep clean
	+$(MAKE) -C common clean 2>/dev/null || true
