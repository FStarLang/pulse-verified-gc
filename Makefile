# Root Makefile for pulse-verified-gc
#
# Orchestrates builds across all subdirectories.
# common/ is built first; mark-and-sweep/ depends on it.
#
# The FStar/ submodule (fstar2 branch) provides both F* and Pulse.
# Run `make prep` once to build it.

FSTAR_HOME ?= $(CURDIR)/FStar

SUBDIRS = common mark-and-sweep

.PHONY: all prep verify clean $(SUBDIRS)

all: verify

# Build the FStar submodule (stage 3 = F* with Pulse baked in)
prep:
	+$(MAKE) -C $(FSTAR_HOME) -j8

verify: common
	$(MAKE) -C mark-and-sweep FSTAR_HOME=$(FSTAR_HOME)

common:
	$(MAKE) -C common FSTAR_HOME=$(FSTAR_HOME)

mark-and-sweep: common
	$(MAKE) -C mark-and-sweep FSTAR_HOME=$(FSTAR_HOME)

clean:
	@for d in $(SUBDIRS); do $(MAKE) -C $$d clean; done
