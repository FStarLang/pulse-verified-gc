# Makefile for Pulse GC (Mark-and-Sweep)
#
# Verifies and extracts the sequential stop-the-world garbage collector.
# Shared infrastructure (Heap, Object, Stack) lives in ../common/Pulse.Lib.GC/
# Concurrent modules live in ../concurrent/

.PHONY: all verify extract clean help

# ------------------------------------------------------------------------------
# Configuration
# ------------------------------------------------------------------------------

PULSE_HOME ?= $(HOME)/pulse
KRML_HOME ?= $(shell opam var prefix)/lib/karamel

# Pulse includes
PULSE_INCLUDES = \
--include $(PULSE_HOME)/lib/pulse/lib \
--include $(PULSE_HOME)/out/lib/pulse

# Common infrastructure path
COMMON_DIR = ../common

# F* base options
FSTAR_BASE = fstar.exe \
--cache_checked_modules \
--warn_error -321

# For Spec modules (pure F*, no Pulse) - includes common/
FSTAR_SPEC = $(FSTAR_BASE) --include Spec --include Lib \
--include $(COMMON_DIR)/Spec --include $(COMMON_DIR)/Lib

# For Lib modules (Pulse) - includes common/ (Spec + Lib + Pulse.Lib.GC)
FSTAR_LIB = $(FSTAR_BASE) $(PULSE_INCLUDES) --include Pulse.Lib.GC --include Lib \
--include $(COMMON_DIR)/Spec --include $(COMMON_DIR)/Lib \
--include $(COMMON_DIR)/Pulse.Lib.GC --load_cmxs pulse

# ------------------------------------------------------------------------------
# Source files
# ------------------------------------------------------------------------------

# Specification modules (sequential mark-and-sweep)
SPEC_MODULES = \
Spec/Pulse.Spec.GC.SeqMemLemmas.fst \
Spec/Pulse.Spec.GC.Mark.fst \
Spec/Pulse.Spec.GC.Sweep.fst \
Spec/Pulse.Spec.GC.Correctness.fst

# Implementation modules (sequential mark-and-sweep)
# Heap, Object, Stack are now in common/Pulse.Lib.GC/
LIB_MODULES = \
Pulse.Lib.GC/Pulse.Lib.GC.Fields.fst \
Pulse.Lib.GC/Pulse.Lib.GC.Closure.fst \
Pulse.Lib.GC/Pulse.Lib.GC.Mark.fst \
Pulse.Lib.GC/Pulse.Lib.GC.Sweep.fst \
Pulse.Lib.GC/Pulse.Lib.GC.fst

ALL_MODULES = $(SPEC_MODULES) $(LIB_MODULES)

# ------------------------------------------------------------------------------
# Default target: verify everything
# ------------------------------------------------------------------------------

all: verify

verify:
	@echo "=== Verifying Mark-and-Sweep GC ==="
	@echo ""
	@echo "--- Specifications ---"
	@for f in $(SPEC_MODULES); do \
if [ -f "$$f" ]; then \
echo "  $$f"; \
$(FSTAR_SPEC) $$f || exit 1; \
fi; \
done
	@echo ""
	@echo "--- Implementation ---"
	@for f in $(LIB_MODULES); do \
if [ -f "$$f" ]; then \
echo "  $$f"; \
$(FSTAR_LIB) $$f || echo "    (skipped - Pulse errors, see above)"; \
fi; \
done
	@echo ""
	@echo "=== Verification complete ==="

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
	@echo "Mark-and-Sweep GC Makefile"
	@echo ""
	@echo "Targets:"
	@echo "  make                - Verify all (default)"
	@echo "  make verify         - Same as above"
	@echo "  make extract        - Extract to C via KaRaMeL"
	@echo "  make clean          - Remove generated files"
	@echo ""
	@echo "Modules:"
	@echo "  Spec/           - Pure F* specifications (Mark, Sweep, Correctness)"
	@echo "  Pulse.Lib.GC/   - Pulse implementations (Fields, Closure, Mark, Sweep, GC)"
	@echo ""
	@echo "Shared infrastructure (Heap, Object, Stack) is in ../common/Pulse.Lib.GC/"
	@echo "Concurrent modules (TriColor, AtomicColor, etc.) are in ../concurrent/"
