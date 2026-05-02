# Root Makefile for pulse-verified-gc
#
# Builds all sub-projects: common/, mark-and-sweep/, generational/.
# Each sub-directory has its own Makefile; this orchestrates the full build.
#
# Run `./setup.sh` once after cloning to install the F* toolchain.
#
# Usage:
#   ./setup.sh          Install F* binary release
#   make                Verify all modules (common + mark-and-sweep + generational)
#   make common         Verify common/ only
#   make mark-and-sweep Verify mark-and-sweep/ (includes common/)
#   make generational   Verify generational/ (includes common/ + mark-and-sweep/)
#   make extract        Verify + extract both GCs to C
#   make snapshot       Verify + extract mark-and-sweep + create snapshot/
#   make clean          Clean all build artifacts

FSTAR_HOME ?= $(CURDIR)/fstar
KRML_HOME  ?= $(FSTAR_HOME)/karamel

.PHONY: all verify common mark-and-sweep generational extract snapshot clean

all: verify

# --- Verification targets ---------------------------------------------------

verify: common mark-and-sweep generational

common:
	+$(MAKE) -C common FSTAR_HOME=$(FSTAR_HOME)

mark-and-sweep: common
	+$(MAKE) -C mark-and-sweep FSTAR_HOME=$(FSTAR_HOME)

generational: mark-and-sweep
	+$(MAKE) -C generational FSTAR_HOME=$(FSTAR_HOME)

# --- Extraction targets -----------------------------------------------------

extract: extract-mark-and-sweep extract-generational

.PHONY: extract-mark-and-sweep extract-generational

extract-mark-and-sweep: mark-and-sweep
	+$(MAKE) -C mark-and-sweep extract FSTAR_HOME=$(FSTAR_HOME) KRML_HOME=$(KRML_HOME)

extract-generational: generational
	+$(MAKE) -C generational extract FSTAR_HOME=$(FSTAR_HOME) KRML_HOME=$(KRML_HOME)

# --- Snapshot (mark-and-sweep only) -----------------------------------------

snapshot: extract-mark-and-sweep
	+$(MAKE) -C mark-and-sweep snapshot FSTAR_HOME=$(FSTAR_HOME) KRML_HOME=$(KRML_HOME)

# --- Clean ------------------------------------------------------------------

clean:
	+$(MAKE) -C common clean
	+$(MAKE) -C mark-and-sweep clean
	+$(MAKE) -C generational clean
