# Makefile for common GC infrastructure
#
# Hand-written dependency graph for parallel-safe builds (make -j8).
# Default target: verify all spec+lib modules.

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
FSTAR_BASE = --cache_checked_modules --report_assumes warn

FSTAR_SPEC_FLAGS = $(FSTAR_BASE) \
  --already_cached 'FStar -Pulse.Spec.GC -Pulse.Lib.Header -Pulse.Lib.Address'

FSTAR_PULSE_FLAGS = $(FSTAR_BASE) \
  --load_cmxs pulse \
  --already_cached 'FStar Pulse -Pulse.Spec.GC -Pulse.Lib.GC -Pulse.Lib.Header -Pulse.Lib.Address'

# Spec+Lib checked files (explicit list)
SPEC_CHECKED = \
  Lib/Pulse.Lib.Header.fst.checked \
  Lib/Pulse.Lib.Address.fst.checked \
  Spec/Pulse.Spec.GC.Base.fsti.checked \
  Spec/Pulse.Spec.GC.Base.fst.checked \
  Spec/Pulse.Spec.GC.Heap.fsti.checked \
  Spec/Pulse.Spec.GC.Heap.fst.checked \
  Spec/Pulse.Spec.GC.Object.fsti.checked \
  Spec/Pulse.Spec.GC.Object.fst.checked \
  Spec/Pulse.Spec.GC.Graph.fst.checked \
  Spec/Pulse.Spec.GC.Fields.fst.checked \
  Spec/Pulse.Spec.GC.DFS.fst.checked \
  Spec/Pulse.Spec.GC.HeapGraph.fst.checked \
  Spec/Pulse.Spec.GC.HeapModel.fst.checked

# Pulse checked files (explicit list)
PULSE_CHECKED = \
  Pulse.Lib.GC/Pulse.Lib.GC.Heap.fst.checked \
  Pulse.Lib.GC/Pulse.Lib.GC.Object.fst.checked \
  Pulse.Lib.GC/Pulse.Lib.GC.Stack.fst.checked

# ------------------------------------------------------------------------------
# Targets
# ------------------------------------------------------------------------------

.PHONY: all verify verify-spec verify-pulse clean

all: verify

verify: verify-spec
	@echo "=== common: all modules verified ==="

verify-spec: $(SPEC_CHECKED)

verify-pulse: verify-spec $(PULSE_CHECKED)
	@echo "=== common: Pulse modules verified ==="

# ------------------------------------------------------------------------------
# Spec+Lib module dependencies (from module graph, validated against --dep full)
# ------------------------------------------------------------------------------

Lib/Pulse.Lib.Header.fst.checked: \
	Lib/Pulse.Lib.Header.fst

Lib/Pulse.Lib.Address.fst.checked: \
	Lib/Pulse.Lib.Address.fst \
	Spec/Pulse.Spec.GC.Base.fsti.checked

Spec/Pulse.Spec.GC.Base.fsti.checked: \
	Spec/Pulse.Spec.GC.Base.fsti

Spec/Pulse.Spec.GC.Base.fst.checked: \
	Spec/Pulse.Spec.GC.Base.fst \
	Spec/Pulse.Spec.GC.Base.fsti.checked

Spec/Pulse.Spec.GC.Heap.fsti.checked: \
	Spec/Pulse.Spec.GC.Heap.fsti \
	Lib/Pulse.Lib.Header.fst.checked \
	Spec/Pulse.Spec.GC.Base.fsti.checked

Spec/Pulse.Spec.GC.Heap.fst.checked: \
	Spec/Pulse.Spec.GC.Heap.fst \
	Spec/Pulse.Spec.GC.Heap.fsti.checked \
	Lib/Pulse.Lib.Header.fst.checked \
	Spec/Pulse.Spec.GC.Base.fsti.checked

Spec/Pulse.Spec.GC.Object.fsti.checked: \
	Spec/Pulse.Spec.GC.Object.fsti \
	Lib/Pulse.Lib.Header.fst.checked \
	Spec/Pulse.Spec.GC.Heap.fsti.checked \
	Spec/Pulse.Spec.GC.Base.fsti.checked

Spec/Pulse.Spec.GC.Object.fst.checked: \
	Spec/Pulse.Spec.GC.Object.fst \
	Spec/Pulse.Spec.GC.Object.fsti.checked \
	Lib/Pulse.Lib.Header.fst.checked \
	Spec/Pulse.Spec.GC.Heap.fsti.checked \
	Spec/Pulse.Spec.GC.Base.fsti.checked

Spec/Pulse.Spec.GC.Graph.fst.checked: \
	Spec/Pulse.Spec.GC.Graph.fst \
	Spec/Pulse.Spec.GC.Base.fsti.checked

Spec/Pulse.Spec.GC.Fields.fst.checked: \
	Spec/Pulse.Spec.GC.Fields.fst \
	Lib/Pulse.Lib.Header.fst.checked \
	Spec/Pulse.Spec.GC.Object.fsti.checked \
	Spec/Pulse.Spec.GC.Heap.fsti.checked \
	Spec/Pulse.Spec.GC.Base.fsti.checked

Spec/Pulse.Spec.GC.DFS.fst.checked: \
	Spec/Pulse.Spec.GC.DFS.fst \
	Spec/Pulse.Spec.GC.Graph.fst.checked

Spec/Pulse.Spec.GC.HeapGraph.fst.checked: \
	Spec/Pulse.Spec.GC.HeapGraph.fst \
	Lib/Pulse.Lib.Address.fst.checked \
	Spec/Pulse.Spec.GC.Graph.fst.checked \
	Spec/Pulse.Spec.GC.Object.fsti.checked \
	Spec/Pulse.Spec.GC.Heap.fsti.checked \
	Spec/Pulse.Spec.GC.Base.fsti.checked

Spec/Pulse.Spec.GC.HeapModel.fst.checked: \
	Spec/Pulse.Spec.GC.HeapModel.fst \
	Spec/Pulse.Spec.GC.HeapGraph.fst.checked \
	Spec/Pulse.Spec.GC.Fields.fst.checked \
	Spec/Pulse.Spec.GC.Graph.fst.checked \
	Spec/Pulse.Spec.GC.Object.fsti.checked \
	Spec/Pulse.Spec.GC.Heap.fsti.checked \
	Spec/Pulse.Spec.GC.Base.fsti.checked

# ------------------------------------------------------------------------------
# Pulse module dependencies (from module graph, validated against --dep full)
# ------------------------------------------------------------------------------

Pulse.Lib.GC/Pulse.Lib.GC.Heap.fst.checked: \
	Pulse.Lib.GC/Pulse.Lib.GC.Heap.fst \
	Spec/Pulse.Spec.GC.Heap.fsti.checked \
	Spec/Pulse.Spec.GC.Base.fsti.checked

Pulse.Lib.GC/Pulse.Lib.GC.Object.fst.checked: \
	Pulse.Lib.GC/Pulse.Lib.GC.Object.fst \
	Lib/Pulse.Lib.Header.fst.checked \
	Spec/Pulse.Spec.GC.Object.fsti.checked \
	Pulse.Lib.GC/Pulse.Lib.GC.Heap.fst.checked

Pulse.Lib.GC/Pulse.Lib.GC.Stack.fst.checked: \
	Pulse.Lib.GC/Pulse.Lib.GC.Stack.fst \
	Pulse.Lib.GC/Pulse.Lib.GC.Object.fst.checked \
	Pulse.Lib.GC/Pulse.Lib.GC.Heap.fst.checked

# ------------------------------------------------------------------------------
# Pattern rules (recipes for verification)
# ------------------------------------------------------------------------------

Spec/%.fst.checked: Spec/%.fst
	$(FSTAR) $(FSTAR_SPEC_INCLUDES) $(FSTAR_SPEC_FLAGS) $<

Spec/%.fsti.checked: Spec/%.fsti
	$(FSTAR) $(FSTAR_SPEC_INCLUDES) $(FSTAR_SPEC_FLAGS) $<

Lib/%.fst.checked: Lib/%.fst
	$(FSTAR) $(FSTAR_SPEC_INCLUDES) $(FSTAR_SPEC_FLAGS) $<

Pulse.Lib.GC/%.fst.checked: Pulse.Lib.GC/%.fst
	$(FSTAR) $(FSTAR_PULSE_INCLUDES) $(FSTAR_PULSE_FLAGS) $<

# ------------------------------------------------------------------------------
# Cleanup
# ------------------------------------------------------------------------------

clean:
	rm -f Spec/*.checked* Lib/*.checked* Pulse.Lib.GC/*.checked*
	rm -f .depend .depend.spec .depend.pulse
