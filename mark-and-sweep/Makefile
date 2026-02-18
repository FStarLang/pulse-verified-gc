# Makefile for Pulse GC (Mark-and-Sweep)
#
# Verifies and extracts the sequential stop-the-world garbage collector.
# Uses F*'s --dep full for dependency tracking and incremental builds.
# Shared infrastructure (Heap, Object, Stack) lives in ../common/

FSTAR ?= fstar.exe
PULSE_HOME ?= $(HOME)/pulse
KRML_HOME ?= $(shell opam var prefix)/lib/karamel

COMMON_DIR = ../common
COMMON_ABS = $(abspath $(COMMON_DIR))

# Include paths (shared between spec and lib)
COMMON_INCLUDES = \
  --include Spec \
  --include $(COMMON_DIR)/Spec \
  --include $(COMMON_DIR)/Lib

# Spec: pure F*, no Pulse plugin needed
FSTAR_SPEC_INCLUDES = $(COMMON_INCLUDES)

# Lib: needs Pulse plugin and includes
FSTAR_LIB_INCLUDES = $(COMMON_INCLUDES) \
  --include Pulse.Lib.GC \
  --include $(COMMON_DIR)/Pulse.Lib.GC \
  --include $(PULSE_HOME)/lib/pulse/lib \
  --include $(PULSE_HOME)/out/lib/pulse

# F* base options
FSTAR_BASE = \
  --cache_checked_modules \
  --warn_error -321

FSTAR_SPEC_FLAGS = $(FSTAR_BASE) \
  --already_cached 'FStar -Pulse.Spec.GC'

FSTAR_LIB_FLAGS = $(FSTAR_BASE) \
  --load_cmxs pulse \
  --already_cached 'FStar Pulse -Pulse.Spec.GC -Pulse.Lib.GC -Pulse.Lib.Header -Pulse.Lib.Address -Pulse.Lib.Bitvec'

# Source files
SPEC_FILES = $(wildcard Spec/*.fst Spec/*.fsti)
LIB_FILES  = $(wildcard Pulse.Lib.GC/*.fst)

# ------------------------------------------------------------------------------
# Targets
# ------------------------------------------------------------------------------

.PHONY: all verify verify-spec verify-lib extract clean

all: verify

# Spec dependency tracking (pure F*, no Pulse plugin)
.depend.spec: $(SPEC_FILES)
	$(FSTAR) --dep full $(FSTAR_SPEC_INCLUDES) $(FSTAR_SPEC_FLAGS) $^ > $@

# Lib dependency tracking (requires Pulse plugin)
.depend.lib: $(LIB_FILES)
	$(FSTAR) --dep full $(FSTAR_LIB_INCLUDES) $(FSTAR_LIB_FLAGS) $^ > $@

-include .depend.spec
-include .depend.lib

# Filter out external (absolute-path) entries — only build local modules
LOCAL_CHECKED = $(filter-out /%, $(ALL_CHECKED_FILES))

# Verify all local modules
verify: verify-spec

# Verify spec modules only (pure F*, no Pulse needed)
verify-spec: .depend.spec
	@$(MAKE) --no-print-directory $(filter Spec/%, $(LOCAL_CHECKED))
	@echo "=== mark-and-sweep: spec modules verified ==="

# Verify lib modules (requires Pulse plugin)
verify-lib: .depend.lib verify-spec
	@$(MAKE) --no-print-directory $(filter Pulse.Lib.GC/%, $(LOCAL_CHECKED))
	@echo "=== mark-and-sweep: lib modules verified ==="

# Delegate common module builds to ../common/
$(COMMON_ABS)/%.checked:
	$(MAKE) -C $(COMMON_DIR)

# Pattern rules for incremental verification
Spec/%.fst.checked: Spec/%.fst
	$(FSTAR) $(FSTAR_SPEC_INCLUDES) $(FSTAR_SPEC_FLAGS) $<

Spec/%.fsti.checked: Spec/%.fsti
	$(FSTAR) $(FSTAR_SPEC_INCLUDES) $(FSTAR_SPEC_FLAGS) $<

Pulse.Lib.GC/%.fst.checked: Pulse.Lib.GC/%.fst
	$(FSTAR) $(FSTAR_LIB_INCLUDES) $(FSTAR_LIB_FLAGS) $<

# ------------------------------------------------------------------------------
# Extraction to C via KaRaMeL
# ------------------------------------------------------------------------------

EXTRACT_DIR = dist

LIB_MODULES = \
  Pulse.Lib.GC/Pulse.Lib.GC.Fields.fst \
  Pulse.Lib.GC/Pulse.Lib.GC.Closure.fst \
  Pulse.Lib.GC/Pulse.Lib.GC.Mark.fst \
  Pulse.Lib.GC/Pulse.Lib.GC.Sweep.fst \
  Pulse.Lib.GC/Pulse.Lib.GC.fst

extract: verify-lib
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
	rm -f Spec/*.checked* Pulse.Lib.GC/*.checked*
	rm -f .depend.spec .depend.lib
	rm -rf $(EXTRACT_DIR)
