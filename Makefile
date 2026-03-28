# Root Makefile for pulse-verified-gc
#
# Orchestrates builds across all subdirectories.
# common/ is built first; mark-and-sweep/ depends on it.
#
# The FStar/ submodule (fstar2 branch) provides F*, Pulse, and KaRaMeL.
# Run `make prep` once after cloning to build the toolchain.
#
# Usage:
#   make prep       Build fstar.exe (stage3) and KaRaMeL
#   make            Verify common/ then mark-and-sweep/
#   make extract    Verify + extract mark-and-sweep to C
#   make snapshot   Verify + extract + create snapshot/
#   make clean      Clean all subdirectories

FSTAR_HOME ?= $(CURDIR)/FStar
KRML_HOME  ?= $(FSTAR_HOME)/karamel

SUBDIRS = common mark-and-sweep

.PHONY: all prep verify extract snapshot clean $(SUBDIRS)

all: verify

# Build the fstar2 toolchain: stage3 F*+Pulse and KaRaMeL
prep:
	+$(MAKE) -C $(FSTAR_HOME) -j8
	+$(MAKE) -C $(FSTAR_HOME) karamel

verify: common
	+$(MAKE) -C mark-and-sweep FSTAR_HOME=$(FSTAR_HOME)

common:
	+$(MAKE) -C common FSTAR_HOME=$(FSTAR_HOME)

mark-and-sweep: common
	+$(MAKE) -C mark-and-sweep FSTAR_HOME=$(FSTAR_HOME)

extract: common
	+$(MAKE) -C mark-and-sweep extract FSTAR_HOME=$(FSTAR_HOME) KRML_HOME=$(KRML_HOME)

snapshot: common
	+$(MAKE) -C mark-and-sweep snapshot FSTAR_HOME=$(FSTAR_HOME) KRML_HOME=$(KRML_HOME)

clean:
	@for d in $(SUBDIRS); do $(MAKE) -C $$d clean; done
