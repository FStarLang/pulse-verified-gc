# Makefile for common GC infrastructure
#
# Uses F*'s --dep full for dependency tracking and incremental builds.
# Default target: verify all modules.

FSTAR ?= fstar.exe
PULSE_HOME ?= $(HOME)/pulse

# Include paths (shared)
COMMON_INCLUDES = \
  --include Lib \
  --include Spec

# Spec/Lib: pure F*, no Pulse plugin needed
FSTAR_SPEC_INCLUDES = $(COMMON_INCLUDES)

# Pulse.Lib.GC: needs Pulse plugin
FSTAR_PULSE_INCLUDES = $(COMMON_INCLUDES) \
  --include Pulse.Lib.GC \
  --include $(PULSE_HOME)/lib/pulse/lib \
  --include $(PULSE_HOME)/out/lib/pulse

# F* base options
FSTAR_BASE = --cache_checked_modules

FSTAR_SPEC_FLAGS = $(FSTAR_BASE) \
  --already_cached 'FStar -Pulse.Spec.GC -Pulse.Lib.Header -Pulse.Lib.Address'

FSTAR_PULSE_FLAGS = $(FSTAR_BASE) \
  --load_cmxs pulse \
  --already_cached 'FStar Pulse -Pulse.Spec.GC -Pulse.Lib.GC -Pulse.Lib.Header -Pulse.Lib.Address'

# Source files
SPEC_FILES  = $(wildcard Spec/*.fst Spec/*.fsti Lib/*.fst)
PULSE_FILES = $(wildcard Pulse.Lib.GC/*.fst)

# ------------------------------------------------------------------------------
# Targets
# ------------------------------------------------------------------------------

.PHONY: all verify verify-spec verify-pulse clean

all: verify

# Spec dependency tracking (pure F*, no Pulse plugin)
.depend.spec: $(SPEC_FILES)
	$(FSTAR) --dep full $(FSTAR_SPEC_INCLUDES) $(FSTAR_SPEC_FLAGS) $^ > $@

# Pulse dependency tracking (requires Pulse plugin)
.depend.pulse: $(PULSE_FILES)
	$(FSTAR) --dep full $(FSTAR_PULSE_INCLUDES) $(FSTAR_PULSE_FLAGS) $^ > $@

-include .depend.spec
-include .depend.pulse

# Filter out external (absolute-path) entries — only build local modules
LOCAL_CHECKED = $(filter-out /%, $(ALL_CHECKED_FILES))

# Verify all modules (spec always, pulse if plugin available)
verify: verify-spec
	@echo "=== common: all modules verified ==="

# Verify spec modules only (pure F*, no Pulse needed)
verify-spec: .depend.spec
	@$(MAKE) --no-print-directory $(filter Spec/% Lib/%, $(LOCAL_CHECKED))

# Verify Pulse modules (requires Pulse plugin)
verify-pulse: .depend.pulse verify-spec
	@$(MAKE) --no-print-directory $(filter Pulse.Lib.GC/%, $(LOCAL_CHECKED))
	@echo "=== common: Pulse modules verified ==="

# Pattern rules for incremental verification
Spec/%.fst.checked: Spec/%.fst
	$(FSTAR) $(FSTAR_SPEC_INCLUDES) $(FSTAR_SPEC_FLAGS) $<

Spec/%.fsti.checked: Spec/%.fsti
	$(FSTAR) $(FSTAR_SPEC_INCLUDES) $(FSTAR_SPEC_FLAGS) $<

Lib/%.fst.checked: Lib/%.fst
	$(FSTAR) $(FSTAR_SPEC_INCLUDES) $(FSTAR_SPEC_FLAGS) $<

Pulse.Lib.GC/%.fst.checked: Pulse.Lib.GC/%.fst
	$(FSTAR) $(FSTAR_PULSE_INCLUDES) $(FSTAR_PULSE_FLAGS) $<

clean:
	rm -f Spec/*.checked* Lib/*.checked* Pulse.Lib.GC/*.checked*
	rm -f .depend.spec .depend.pulse
