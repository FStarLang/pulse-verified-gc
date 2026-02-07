# Makefile for Concurrent On-the-Fly GC
# 
# This Makefile supports:
# - F* verification of Pulse modules
# - KaRaMeL extraction to C
# - Building the extracted C code

# Find F* and Pulse paths
FSTAR_HOME ?= $(shell opam var prefix)/.opam-switch/build/fstar.*
PULSE_HOME ?= $(HOME)/pulse/lib/pulse/lib
KRML_HOME  ?= $(shell opam var prefix)/.opam-switch/build/karamel.*

# F* executable
FSTAR_EXE = fstar.exe

# Common infrastructure path
COMMON_DIR = ../common

# Include paths
FSTAR_INCLUDES = \
  --include $(PULSE_HOME) \
  --include $(COMMON_DIR)/Spec \
  --include $(COMMON_DIR)/Lib \
  --include .

# Common F* options
FSTAR_OPTIONS = \
  --cache_checked_modules \
  --warn_error -331

# SMT solver options
SMT_OPTIONS = \
  --z3rlimit 100 \
  --max_fuel 2 \
  --max_ifuel 1

# Common modules (from ../common/Spec - verified there, imported here)
COMMON_MODULES = \
  Pulse.Spec.GC.Base \
  Pulse.Spec.GC.Heap \
  Pulse.Spec.GC.Object \
  Pulse.Spec.GC.Graph \
  Pulse.Spec.GC.DFS

# Fly-specific spec modules (verification only)
SPEC_MODULES = \
  Pulse.Spec.GC.Fields \
  Pulse.Spec.GC.TriColor \
  Pulse.Spec.GC.GraySet \
  Pulse.Spec.GC.CASPreservation \
  Pulse.Spec.GC.Correctness \
  Pulse.Spec.GC.GraphBridge

# Implementation modules (require Pulse tooling - verify with lax for now)
LIB_MODULES = \
  Pulse.Lib.GC.ConcurrentMark \
  Pulse.Lib.GC.RootScanning \
  Pulse.Lib.GC.Sweep \
  Pulse.Lib.GC

# Test modules (verification only, not extracted)
TEST_MODULES = \
  Test.Atomics \
  Test.Concurrent

# Modules for standard verification (Spec only - Lib needs Pulse extension)
ALL_MODULES = $(SPEC_MODULES)
ALL_WITH_TESTS = $(ALL_MODULES) $(TEST_MODULES)

# Source files
SPEC_FILES = $(addsuffix .fst,$(SPEC_MODULES))
LIB_FILES = $(addsuffix .fst,$(LIB_MODULES))
TEST_FILES = $(addsuffix .fst,$(TEST_MODULES))
ALL_FILES = $(SPEC_FILES)
ALL_FILES_WITH_TESTS = $(ALL_FILES) $(TEST_FILES)

# Checked files
CHECKED_FILES = $(addsuffix .checked,$(ALL_FILES))

# Output directories
DIST_DIR = dist
CACHE_DIR = .cache

# ============================================================================
# Phony targets
# ============================================================================

.PHONY: all verify verify-tests extract clean

all: verify

# ============================================================================
# Verification targets
# ============================================================================

# Full verification (strict mode)
verify: $(CHECKED_FILES)
	@echo "All modules verified successfully."

# Verify test modules
verify-tests:
	@for f in $(TEST_FILES); do \
		echo "Lax checking $$f..."; \
		$(FSTAR_EXE) --lax $(FSTAR_INCLUDES) $$f || exit 1; \
	done
	@echo "All test modules lax-checked successfully."

# Individual module verification
%.fst.checked: %.fst
	@echo "Verifying $<..."
	@mkdir -p $(CACHE_DIR)
	$(FSTAR_EXE) $(FSTAR_INCLUDES) $(FSTAR_OPTIONS) $(SMT_OPTIONS) \
		--cache_dir $(CACHE_DIR) \
		$<
	@touch $@

# ============================================================================
# Extraction targets
# ============================================================================

# KaRaMeL extraction options
KRML_OPTIONS = \
  -bundle Pulse.Lib.GC=* \
  -bundle FStar.*,Pulse.* \
  -no-prefix Pulse.Lib.GC \
  -skip-compilation \
  -tmpdir $(DIST_DIR) \
  -add-include '"kremlib.h"' \
  -add-include '"prims.h"'

# Extract all implementation modules to C
extract: verify
	@echo "Extracting to C..."
	@mkdir -p $(DIST_DIR)
	krml $(KRML_OPTIONS) \
		$(FSTAR_INCLUDES) \
		--admit_smt_queries true \
		$(LIB_FILES)
	@echo "C code generated in $(DIST_DIR)/"

# ============================================================================
# Cleanup
# ============================================================================

clean:
	rm -rf $(CACHE_DIR) $(DIST_DIR)
	rm -f *.checked
	rm -f .depend

# ============================================================================
# Dependencies (auto-generated)
# ============================================================================

# Generate dependencies
.depend: $(ALL_FILES)
	$(FSTAR_EXE) --dep full $(FSTAR_INCLUDES) $(ALL_FILES) > $@

-include .depend
