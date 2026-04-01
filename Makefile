# Root Makefile for pulse-verified-gc
#
# The mark-and-sweep/ Makefile builds all modules (common/ + mark-and-sweep/)
# in a single incremental build via `fstar.exe --dep full`.
#
# The FStar/ submodule (fstar2 branch) provides F*, Pulse, and KaRaMeL.
# Run `make prep` once after cloning to build the toolchain.
#
# Usage:
#   make prep       Build fstar.exe (stage3) and KaRaMeL
#   make            Verify all modules (common/ + mark-and-sweep/)
#   make extract    Verify + extract mark-and-sweep to C
#   make snapshot   Verify + extract + create snapshot/
#   make clean      Clean all build artifacts

FSTAR_HOME ?= $(CURDIR)/FStar
KRML_HOME  ?= $(FSTAR_HOME)/karamel

.PHONY: all prep verify extract snapshot clean

all: verify

# Build the fstar2 toolchain: stage3 F*+Pulse and KaRaMeL
prep:
	+$(MAKE) -C $(FSTAR_HOME) -j8
	+$(MAKE) -C $(FSTAR_HOME) karamel

verify:
	+$(MAKE) -C mark-and-sweep FSTAR_HOME=$(FSTAR_HOME)

extract:
	+$(MAKE) -C mark-and-sweep extract FSTAR_HOME=$(FSTAR_HOME) KRML_HOME=$(KRML_HOME)

snapshot:
	+$(MAKE) -C mark-and-sweep snapshot FSTAR_HOME=$(FSTAR_HOME) KRML_HOME=$(KRML_HOME)

clean:
	+$(MAKE) -C mark-and-sweep clean
	+$(MAKE) -C common clean 2>/dev/null || true
