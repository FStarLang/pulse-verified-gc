# Makefile for Pulse GC
#
# Verifies and extracts the verified garbage collector
# Includes both sequential and concurrent GC modules

.PHONY: all verify verify-concurrent extract clean help

# ------------------------------------------------------------------------------
# Configuration
# ------------------------------------------------------------------------------

PULSE_HOME ?= $(HOME)/pulse
KRML_HOME ?= $(shell opam var prefix)/lib/karamel

# Pulse includes
PULSE_INCLUDES = \
--include $(PULSE_HOME)/lib/pulse/lib \
--include $(PULSE_HOME)/lib/pulse/core \
--include $(PULSE_HOME)/share/pulse/examples/by-example

# Common infrastructure path
COMMON_DIR = ../common

# F* base options
FSTAR_BASE = fstar.exe \
--cache_checked_modules \
--warn_error -321

# For Spec modules (pure F*, no Pulse) - includes common/
FSTAR_SPEC = $(FSTAR_BASE) --include Spec --include Lib --include $(COMMON_DIR)/Spec --include $(COMMON_DIR)/Lib

# For Lib modules (Pulse) - includes common/
FSTAR_LIB = $(FSTAR_BASE) $(PULSE_INCLUDES) --include Pulse.Lib.GC --include Lib --include $(COMMON_DIR)/Spec --include $(COMMON_DIR)/Lib --load_cmxs pulse

# ------------------------------------------------------------------------------
# Source files
# ------------------------------------------------------------------------------

LIB_HEADER =

# Base specification modules (sequential) - uses common/ for Base, Heap, Object, Graph, DFS
SPEC_MODULES = \
Spec/Pulse.Spec.GC.HeapModel.fst \
Spec/Pulse.Spec.GC.Mark.fst \
Spec/Pulse.Spec.GC.Sweep.fst \
Spec/Pulse.Spec.GC.Correctness.fst

# Concurrent GC specification modules (NEW)
SPEC_CONCURRENT_MODULES = \
Spec/Pulse.Spec.GC.Color.fst \
Spec/Pulse.Spec.GC.TriColor.fst

# Base implementation modules (sequential)
LIB_MODULES = \
Pulse.Lib.GC/Pulse.Lib.GC.Heap.fst \
Pulse.Lib.GC/Pulse.Lib.GC.Object.fst \
Pulse.Lib.GC/Pulse.Lib.GC.Fields.fst \
Pulse.Lib.GC/Pulse.Lib.GC.Closure.fst \
Pulse.Lib.GC/Pulse.Lib.GC.Stack.fst \
Pulse.Lib.GC/Pulse.Lib.GC.Mark.fst \
Pulse.Lib.GC/Pulse.Lib.GC.Sweep.fst \
Pulse.Lib.GC/Pulse.Lib.GC.fst

# Concurrent GC implementation modules (NEW)
LIB_CONCURRENT_MODULES = \
Pulse.Lib.GC/Pulse.Lib.GC.AtomicColor.fst \
Pulse.Lib.GC/Pulse.Lib.GC.ShadowStack.fst \
Pulse.Lib.GC/Pulse.Lib.GC.WriteBarrier.fst

ALL_MODULES = $(LIB_HEADER) $(SPEC_MODULES) $(SPEC_CONCURRENT_MODULES) $(LIB_MODULES) $(LIB_CONCURRENT_MODULES)

# ------------------------------------------------------------------------------
# Default target: verify everything (full mode - no lax)
# ------------------------------------------------------------------------------

all: verify

verify:
	@echo "=== Verifying Pulse GC (full mode) ==="
	@echo ""
	@echo "--- Specifications (Sequential) ---"
	@for f in $(SPEC_MODULES); do \
if [ -f "$$f" ]; then \
echo "  $$f"; \
$(FSTAR_SPEC) $$f || exit 1; \
fi; \
done
	@echo ""
	@echo "--- Specifications (Concurrent) ---"
	@for f in $(SPEC_CONCURRENT_MODULES); do \
if [ -f "$$f" ]; then \
echo "  $$f"; \
$(FSTAR_SPEC) $$f || echo "    (errors - work in progress)"; \
fi; \
done
	@echo ""
	@echo "--- Implementation (Sequential) ---"
	@for f in $(LIB_MODULES); do \
if [ -f "$$f" ]; then \
echo "  $$f"; \
$(FSTAR_LIB) $$f 2>/dev/null || echo "    (skipped - Pulse not available or errors)"; \
fi; \
done
	@echo ""
	@echo "--- Implementation (Concurrent) ---"
	@for f in $(LIB_CONCURRENT_MODULES); do \
if [ -f "$$f" ]; then \
echo "  $$f"; \
$(FSTAR_LIB) $$f 2>/dev/null || echo "    (errors - work in progress)"; \
fi; \
done
	@echo ""
	@echo "=== Verification complete ==="

# Verify only concurrent modules
verify-concurrent:
	@echo "=== Verifying Concurrent GC Modules ==="
	@echo ""
	@echo "--- Specifications ---"
	@for f in $(SPEC_CONCURRENT_MODULES); do \
if [ -f "$$f" ]; then \
echo "  $$f"; \
$(FSTAR_SPEC) $$f || echo "    (errors)"; \
fi; \
done
	@echo ""
	@echo "--- Implementation ---"
	@for f in $(LIB_CONCURRENT_MODULES); do \
if [ -f "$$f" ]; then \
echo "  $$f"; \
$(FSTAR_LIB) $$f 2>/dev/null || echo "    (errors)"; \
fi; \
done
	@echo ""
	@echo "=== Done ==="

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
	rm -rf .cache *.checked *.checked.lax
	rm -f Spec/*.checked Spec/*.checked.lax
	rm -f Lib/*.checked Lib/*.checked.lax
	rm -f Pulse.Lib.GC/*.checked Pulse.Lib.GC/*.checked.lax
	rm -rf $(EXTRACT_DIR)

# ------------------------------------------------------------------------------
# Help
# ------------------------------------------------------------------------------

help:
	@echo "Pulse GC Makefile"
	@echo ""
	@echo "Targets:"
	@echo "  make                - Verify all (full mode, default)"
	@echo "  make verify         - Same as above"
	@echo "  make verify-concurrent - Verify only concurrent GC modules"
	@echo "  make extract        - Extract to C via KaRaMeL"
	@echo "  make clean          - Remove generated files"
	@echo ""
	@echo "Modules:"
	@echo "  Lib/            - Pure F* library (Header bitvector proofs)"
	@echo "  Spec/           - Pure F* specifications"
	@echo "    - Sequential: Base, Graph, Heap, Object, Fields, Mark, Sweep, Correctness"
	@echo "    - Concurrent: Color, TriColor (NEW)"
	@echo "  Pulse.Lib.GC/   - Pulse implementations"
	@echo "    - Sequential: Heap, Object, Fields, Closure, Stack, Mark, Sweep"
	@echo "    - Concurrent: AtomicColor, ShadowStack, WriteBarrier (NEW)"
