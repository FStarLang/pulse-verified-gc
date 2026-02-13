# Makefile for Parallel On-the-Fly GC (fly/)
#
# Per-thread parallel mark with Dijkstra write barriers.
# Depends on common/ (Base, Heap, Object, Fields, Graph, DFS, HeapGraph, HeapModel)
# and concurrent/ (TriColor 4-color spec, AtomicColor, ShadowStack, WriteBarrier).

.PHONY: all verify verify-spec verify-lib lax extract clean help

# ------------------------------------------------------------------------------
# Configuration
# ------------------------------------------------------------------------------

PULSE_HOME ?= $(HOME)/pulse
KRML_HOME ?= $(shell opam var prefix)/lib/karamel

# Pulse includes
PULSE_INCLUDES = \
  --include $(PULSE_HOME)/lib/pulse/lib \
  --include $(PULSE_HOME)/out/lib/pulse

# Common and concurrent infrastructure
COMMON_DIR = ../common
CONCURRENT_DIR = ../concurrent

# F* base options
FSTAR_BASE = fstar.exe \
  --cache_checked_modules \
  --warn_error -321-331

# SMT options
SMT_OPTIONS = \
  --z3rlimit 100 \
  --max_fuel 2 \
  --max_ifuel 1

# For Spec modules (pure F*, no Pulse)
FSTAR_SPEC = $(FSTAR_BASE) $(SMT_OPTIONS) \
  --include $(COMMON_DIR)/Spec \
  --include $(COMMON_DIR)/Lib \
  --include $(CONCURRENT_DIR)/Spec \
  --include .

# For Lib modules (Pulse)
FSTAR_LIB = $(FSTAR_BASE) $(SMT_OPTIONS) $(PULSE_INCLUDES) \
  --include $(COMMON_DIR)/Spec \
  --include $(COMMON_DIR)/Lib \
  --include $(COMMON_DIR)/Pulse.Lib.GC \
  --include $(CONCURRENT_DIR)/Spec \
  --include $(CONCURRENT_DIR)/Pulse.Lib.GC \
  --include . \
  --load_cmxs pulse

# ------------------------------------------------------------------------------
# Source files
# ------------------------------------------------------------------------------

# Fly-specific spec modules (pure F*)
SPEC_MODULES = \
  Pulse.Spec.GC.GraySet.fst \
  Pulse.Spec.GC.CASPreservation.fst \
  Pulse.Spec.GC.GraphBridge.fst \
  Pulse.Spec.GC.ColorLemmas.fst \
  Pulse.Spec.GC.Correctness.fst

# Fly-specific implementation modules (Pulse)
LIB_MODULES = \
  Pulse.Lib.GC.RootScanning.fst \
  Pulse.Lib.GC.ConcurrentMark.fst \
  Pulse.Lib.GC.Sweep.fst \
  Pulse.Lib.GC.fst

# ------------------------------------------------------------------------------
# Targets
# ------------------------------------------------------------------------------

all: verify

verify: verify-spec verify-lib

verify-spec:
	@echo "=== Verifying Parallel GC Specs ==="
	@for f in $(SPEC_MODULES); do \
	  if [ -f "$$f" ]; then \
	    echo "  $$f"; \
	    $(FSTAR_SPEC) $$f || exit 1; \
	  fi; \
	done
	@echo "=== Spec verification complete ==="

verify-lib:
	@echo "=== Verifying Parallel GC Implementations ==="
	@for f in $(LIB_MODULES); do \
	  if [ -f "$$f" ]; then \
	    echo "  $$f"; \
	    $(FSTAR_LIB) $$f || exit 1; \
	  fi; \
	done
	@echo "=== Lib verification complete ==="

lax:
	@echo "=== Lax checking all modules ==="
	@for f in $(SPEC_MODULES); do \
	  if [ -f "$$f" ]; then \
	    echo "  [lax] $$f"; \
	    $(FSTAR_SPEC) --lax $$f || exit 1; \
	  fi; \
	done
	@for f in $(LIB_MODULES); do \
	  if [ -f "$$f" ]; then \
	    echo "  [lax] $$f"; \
	    $(FSTAR_LIB) --lax $$f || exit 1; \
	  fi; \
	done
	@echo "=== Lax check complete ==="

# ------------------------------------------------------------------------------
# Extraction to C via KaRaMeL
# ------------------------------------------------------------------------------

EXTRACT_DIR = dist

extract: verify
	@echo "=== Extracting to C ==="
	@mkdir -p $(EXTRACT_DIR)
	krml \
	  -tmpdir $(EXTRACT_DIR) \
	  -skip-linking \
	  -bundle 'Pulse.Lib.GC.*' \
	  -bundle 'Pulse.Spec.GC.*' \
	  -minimal \
	  -add-include '"krml/internal/target.h"' \
	  $(LIB_MODULES)
	@echo "=== Extraction complete: $(EXTRACT_DIR)/ ==="

# ------------------------------------------------------------------------------
# Cleanup
# ------------------------------------------------------------------------------

clean:
	rm -rf .cache $(EXTRACT_DIR)
	rm -f *.checked *.checked.lax .depend

# ------------------------------------------------------------------------------
# Help
# ------------------------------------------------------------------------------

help:
	@echo "Parallel On-the-Fly GC Makefile"
	@echo ""
	@echo "Targets:"
	@echo "  make              - Verify all (default)"
	@echo "  make verify-spec  - Verify spec modules only"
	@echo "  make verify-lib   - Verify Pulse lib modules only"
	@echo "  make lax          - Lax check all modules (fast)"
	@echo "  make extract      - Extract to C via KaRaMeL"
	@echo "  make clean        - Remove generated files"
	@echo ""
	@echo "Spec modules:  GraySet, CASPreservation, GraphBridge, Correctness"
	@echo "Lib modules:   RootScanning, ConcurrentMark, Sweep, GC"
	@echo ""
	@echo "Dependencies:"
	@echo "  ../common/     - Base, Heap, Object, Fields, Graph, DFS, HeapGraph, HeapModel"
	@echo "  ../concurrent/ - TriColor (4-color), AtomicColor, ShadowStack, WriteBarrier"
