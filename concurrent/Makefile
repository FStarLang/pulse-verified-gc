# Makefile for Concurrent GC Extensions
#
# Concurrent tri-color marking modules (Dijkstra-style on-the-fly GC).
# Depends on common/ for shared infrastructure.

.PHONY: all verify verify-spec verify-lib clean help

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
FSTAR_SPEC = $(FSTAR_BASE) --include Spec \
--include $(COMMON_DIR)/Spec --include $(COMMON_DIR)/Lib

# For Lib modules (Pulse) - includes common/ (Spec + Lib + Pulse.Lib.GC)
FSTAR_LIB = $(FSTAR_BASE) $(PULSE_INCLUDES) --include Pulse.Lib.GC \
--include $(COMMON_DIR)/Spec --include $(COMMON_DIR)/Lib \
--include $(COMMON_DIR)/Pulse.Lib.GC --load_cmxs pulse

# ------------------------------------------------------------------------------
# Source files
# ------------------------------------------------------------------------------

# Concurrent specification modules
SPEC_MODULES = \
Spec/Pulse.Spec.GC.TriColor.fst

# Concurrent implementation modules
LIB_MODULES = \
Pulse.Lib.GC/Pulse.Lib.GC.AtomicColor.fst \
Pulse.Lib.GC/Pulse.Lib.GC.ShadowStack.fst \
Pulse.Lib.GC/Pulse.Lib.GC.WriteBarrier.fst

ALL_MODULES = $(SPEC_MODULES) $(LIB_MODULES)

# ------------------------------------------------------------------------------
# Targets
# ------------------------------------------------------------------------------

all: verify

verify: verify-spec verify-lib

verify-spec:
	@echo "=== Verifying Concurrent GC Specs ==="
	@for f in $(SPEC_MODULES); do \
if [ -f "$$f" ]; then \
echo "  $$f"; \
$(FSTAR_SPEC) $$f || echo "    (errors)"; \
fi; \
done

verify-lib:
	@echo "=== Verifying Concurrent GC Implementations ==="
	@for f in $(LIB_MODULES); do \
if [ -f "$$f" ]; then \
echo "  $$f"; \
$(FSTAR_LIB) $$f 2>/dev/null || echo "    (errors)"; \
fi; \
done

clean:
	rm -f Spec/*.checked Spec/*.checked.lax
	rm -f Pulse.Lib.GC/*.checked Pulse.Lib.GC/*.checked.lax

help:
	@echo "Concurrent GC Makefile"
	@echo ""
	@echo "Targets:"
	@echo "  make            - Verify all (default)"
	@echo "  make verify-spec - Verify spec modules only"
	@echo "  make verify-lib  - Verify Pulse lib modules only"
	@echo "  make clean       - Remove generated files"
	@echo ""
	@echo "Modules:"
	@echo "  Spec/           - TriColor invariant (4-color: black|white|gray|blue)"
	@echo "  Pulse.Lib.GC/   - AtomicColor, ShadowStack, WriteBarrier"
	@echo ""
	@echo "Depends on ../common/ for shared infrastructure."
