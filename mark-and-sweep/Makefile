# Makefile for Pulse GC (Mark-and-Sweep)
#
# Verifies and extracts the sequential stop-the-world garbage collector.
# Hand-written dependency graph for parallel-safe builds (make -j8).
# Shared infrastructure (Heap, Object, Stack) lives in ../common/

FSTAR ?= fstar.exe
PULSE_HOME ?= $(HOME)/pulse
KRML_HOME ?= $(shell opam var prefix)/lib/karamel

C = ../common

# Include paths (shared between spec and lib)
COMMON_INCLUDES = \
  --include Spec \
  --include $(C)/Spec \
  --include $(C)/Lib

# Spec: pure F*, no Pulse plugin needed
FSTAR_SPEC_INCLUDES = $(COMMON_INCLUDES)

# Lib: needs Pulse plugin and includes
FSTAR_LIB_INCLUDES = $(COMMON_INCLUDES) \
  --include Pulse.Lib.GC \
  --include $(C)/Pulse.Lib.GC \
  --include $(PULSE_HOME)/lib/pulse/lib \
  --include $(PULSE_HOME)/out/lib/pulse

# F* base options
FSTAR_BASE = \
  --cache_checked_modules \
  --warn_error -321 \
  --report_assumes warn

FSTAR_SPEC_FLAGS = $(FSTAR_BASE) \
  --already_cached 'FStar -Pulse.Spec.GC'

FSTAR_LIB_FLAGS = $(FSTAR_BASE) \
  --load_cmxs pulse \
  --split_queries always \
  --already_cached 'FStar Pulse -Pulse.Spec.GC -Pulse.Lib.GC -Pulse.Lib.Header -Pulse.Lib.Address -Pulse.Lib.Bitvec'

# Spec checked files (explicit list)
SPEC_CHECKED = \
  Spec/Pulse.Spec.GC.SeqMemLemmas.fst.checked \
  Spec/Pulse.Spec.GC.SweepInv.fsti.checked \
  Spec/Pulse.Spec.GC.SweepInv.fst.checked \
  Spec/Pulse.Spec.GC.Mark.fst.checked \
  Spec/Pulse.Spec.GC.MarkInv.fsti.checked \
  Spec/Pulse.Spec.GC.MarkInv.fst.checked \
  Spec/Pulse.Spec.GC.Sweep.fst.checked \
  Spec/Pulse.Spec.GC.Correctness.fsti.checked \
  Spec/Pulse.Spec.GC.Correctness.fst.checked

# Lib checked files (explicit list)
LIB_CHECKED = \
  Pulse.Lib.GC/Pulse.Lib.GC.Fields.fst.checked \
  Pulse.Lib.GC/Pulse.Lib.GC.Closure.fst.checked \
  Pulse.Lib.GC/Pulse.Lib.GC.Mark.fst.checked \
  Pulse.Lib.GC/Pulse.Lib.GC.Sweep.fst.checked \
  Pulse.Lib.GC/Pulse.Lib.GC.fst.checked

# ------------------------------------------------------------------------------
# Targets
# ------------------------------------------------------------------------------

.PHONY: all verify verify-spec verify-lib extract clean

all: verify

verify: verify-lib

verify-spec: $(SPEC_CHECKED)
	@echo "=== mark-and-sweep: spec modules verified ==="

verify-lib: verify-spec $(LIB_CHECKED)
	@echo "=== mark-and-sweep: lib modules verified ==="

# ------------------------------------------------------------------------------
# Common/ build: parallel-safe via sentinel files
# ------------------------------------------------------------------------------

COMMON_SPEC_SOURCES = $(wildcard $(C)/Spec/*.fst $(C)/Spec/*.fsti $(C)/Lib/*.fst)
COMMON_PULSE_SOURCES = $(wildcard $(C)/Pulse.Lib.GC/*.fst)

# Build common/ spec+lib modules once (for verify-spec)
.common-stamp: $(COMMON_SPEC_SOURCES)
	+$(MAKE) -C $(C)
	@touch $@

# Build common/ Pulse modules once (for verify-lib)
.common-pulse-stamp: .common-stamp $(COMMON_PULSE_SOURCES)
	+$(MAKE) -C $(C) verify-pulse
	@touch $@

# Common checked files are produced by common/Makefile via stamps
$(C)/Spec/%.checked: | .common-stamp
	@true

$(C)/Lib/%.checked: | .common-stamp
	@true

$(C)/Pulse.Lib.GC/%.checked: | .common-pulse-stamp
	@true

# ------------------------------------------------------------------------------
# Spec module dependencies (from module graph, validated against --dep full)
# ------------------------------------------------------------------------------

Spec/Pulse.Spec.GC.SeqMemLemmas.fst.checked: \
	Spec/Pulse.Spec.GC.SeqMemLemmas.fst

Spec/Pulse.Spec.GC.Correctness.fsti.checked: \
	Spec/Pulse.Spec.GC.Correctness.fsti \
	Spec/Pulse.Spec.GC.Sweep.fst.checked \
	Spec/Pulse.Spec.GC.Mark.fst.checked \
	$(C)/Spec/Pulse.Spec.GC.HeapGraph.fst.checked \
	$(C)/Spec/Pulse.Spec.GC.DFS.fst.checked \
	$(C)/Spec/Pulse.Spec.GC.HeapModel.fst.checked \
	$(C)/Spec/Pulse.Spec.GC.Fields.fst.checked \
	$(C)/Spec/Pulse.Spec.GC.Graph.fst.checked \
	$(C)/Spec/Pulse.Spec.GC.Object.fsti.checked \
	$(C)/Spec/Pulse.Spec.GC.Heap.fsti.checked \
	$(C)/Spec/Pulse.Spec.GC.Base.fsti.checked

Spec/Pulse.Spec.GC.Correctness.fst.checked: \
	Spec/Pulse.Spec.GC.Correctness.fst \
	Spec/Pulse.Spec.GC.Correctness.fsti.checked \
	Spec/Pulse.Spec.GC.Sweep.fst.checked \
	Spec/Pulse.Spec.GC.Mark.fst.checked \
	$(C)/Spec/Pulse.Spec.GC.HeapGraph.fst.checked \
	$(C)/Spec/Pulse.Spec.GC.DFS.fst.checked \
	$(C)/Spec/Pulse.Spec.GC.HeapModel.fst.checked \
	$(C)/Spec/Pulse.Spec.GC.Fields.fst.checked \
	$(C)/Spec/Pulse.Spec.GC.Graph.fst.checked \
	$(C)/Spec/Pulse.Spec.GC.Object.fsti.checked \
	$(C)/Spec/Pulse.Spec.GC.Heap.fsti.checked \
	$(C)/Spec/Pulse.Spec.GC.Base.fsti.checked

Spec/Pulse.Spec.GC.SweepInv.fsti.checked: \
	Spec/Pulse.Spec.GC.SweepInv.fsti \
	$(C)/Spec/Pulse.Spec.GC.HeapGraph.fst.checked \
	$(C)/Spec/Pulse.Spec.GC.Fields.fst.checked \
	$(C)/Spec/Pulse.Spec.GC.Object.fsti.checked \
	$(C)/Spec/Pulse.Spec.GC.Heap.fsti.checked \
	$(C)/Spec/Pulse.Spec.GC.Base.fsti.checked

Spec/Pulse.Spec.GC.SweepInv.fst.checked: \
	Spec/Pulse.Spec.GC.SweepInv.fst \
	Spec/Pulse.Spec.GC.SweepInv.fsti.checked \
	$(C)/Spec/Pulse.Spec.GC.HeapGraph.fst.checked \
	$(C)/Spec/Pulse.Spec.GC.Fields.fst.checked \
	$(C)/Spec/Pulse.Spec.GC.Object.fsti.checked \
	$(C)/Spec/Pulse.Spec.GC.Heap.fsti.checked \
	$(C)/Spec/Pulse.Spec.GC.Base.fsti.checked

Spec/Pulse.Spec.GC.Mark.fst.checked: \
	Spec/Pulse.Spec.GC.Mark.fst \
	Spec/Pulse.Spec.GC.SweepInv.fsti.checked \
	$(C)/Lib/Pulse.Lib.Header.fst.checked \
	$(C)/Spec/Pulse.Spec.GC.HeapGraph.fst.checked \
	$(C)/Spec/Pulse.Spec.GC.DFS.fst.checked \
	$(C)/Spec/Pulse.Spec.GC.HeapModel.fst.checked \
	$(C)/Spec/Pulse.Spec.GC.Fields.fst.checked \
	$(C)/Spec/Pulse.Spec.GC.Graph.fst.checked \
	$(C)/Spec/Pulse.Spec.GC.Object.fsti.checked \
	$(C)/Spec/Pulse.Spec.GC.Heap.fsti.checked \
	$(C)/Spec/Pulse.Spec.GC.Base.fsti.checked

Spec/Pulse.Spec.GC.MarkInv.fsti.checked: \
	Spec/Pulse.Spec.GC.MarkInv.fsti \
	Spec/Pulse.Spec.GC.SweepInv.fsti.checked \
	Spec/Pulse.Spec.GC.Mark.fst.checked \
	$(C)/Spec/Pulse.Spec.GC.Fields.fst.checked \
	$(C)/Spec/Pulse.Spec.GC.Object.fsti.checked \
	$(C)/Spec/Pulse.Spec.GC.Base.fsti.checked

Spec/Pulse.Spec.GC.MarkInv.fst.checked: \
	Spec/Pulse.Spec.GC.MarkInv.fst \
	Spec/Pulse.Spec.GC.MarkInv.fsti.checked \
	Spec/Pulse.Spec.GC.SweepInv.fsti.checked \
	Spec/Pulse.Spec.GC.Mark.fst.checked \
	$(C)/Spec/Pulse.Spec.GC.Fields.fst.checked \
	$(C)/Spec/Pulse.Spec.GC.Object.fsti.checked \
	$(C)/Spec/Pulse.Spec.GC.Base.fsti.checked

Spec/Pulse.Spec.GC.Sweep.fst.checked: \
	Spec/Pulse.Spec.GC.Sweep.fst \
	Spec/Pulse.Spec.GC.Mark.fst.checked \
	$(C)/Lib/Pulse.Lib.Header.fst.checked \
	$(C)/Spec/Pulse.Spec.GC.HeapGraph.fst.checked \
	$(C)/Spec/Pulse.Spec.GC.HeapModel.fst.checked \
	$(C)/Spec/Pulse.Spec.GC.Fields.fst.checked \
	$(C)/Spec/Pulse.Spec.GC.Graph.fst.checked \
	$(C)/Spec/Pulse.Spec.GC.Object.fsti.checked \
	$(C)/Spec/Pulse.Spec.GC.Heap.fsti.checked \
	$(C)/Spec/Pulse.Spec.GC.Base.fsti.checked


# ------------------------------------------------------------------------------
# Lib module dependencies (from module graph, validated against --dep full)
# ------------------------------------------------------------------------------

Pulse.Lib.GC/Pulse.Lib.GC.Fields.fst.checked: \
	Pulse.Lib.GC/Pulse.Lib.GC.Fields.fst \
	$(C)/Pulse.Lib.GC/Pulse.Lib.GC.Object.fst.checked \
	$(C)/Pulse.Lib.GC/Pulse.Lib.GC.Heap.fst.checked

Pulse.Lib.GC/Pulse.Lib.GC.Closure.fst.checked: \
	Pulse.Lib.GC/Pulse.Lib.GC.Closure.fst \
	Pulse.Lib.GC/Pulse.Lib.GC.Fields.fst.checked \
	$(C)/Pulse.Lib.GC/Pulse.Lib.GC.Object.fst.checked \
	$(C)/Pulse.Lib.GC/Pulse.Lib.GC.Heap.fst.checked

Pulse.Lib.GC/Pulse.Lib.GC.Mark.fst.checked: \
	Pulse.Lib.GC/Pulse.Lib.GC.Mark.fst \
	Pulse.Lib.GC/Pulse.Lib.GC.Fields.fst.checked \
	Spec/Pulse.Spec.GC.MarkInv.fsti.checked \
	Spec/Pulse.Spec.GC.Mark.fst.checked \
	$(C)/Spec/Pulse.Spec.GC.HeapGraph.fst.checked \
	$(C)/Spec/Pulse.Spec.GC.Fields.fst.checked \
	$(C)/Spec/Pulse.Spec.GC.Object.fsti.checked \
	$(C)/Spec/Pulse.Spec.GC.Heap.fsti.checked \
	$(C)/Spec/Pulse.Spec.GC.Base.fsti.checked \
	$(C)/Lib/Pulse.Lib.Header.fst.checked \
	$(C)/Pulse.Lib.GC/Pulse.Lib.GC.Stack.fst.checked \
	$(C)/Pulse.Lib.GC/Pulse.Lib.GC.Object.fst.checked \
	$(C)/Pulse.Lib.GC/Pulse.Lib.GC.Heap.fst.checked

Pulse.Lib.GC/Pulse.Lib.GC.Sweep.fst.checked: \
	Pulse.Lib.GC/Pulse.Lib.GC.Sweep.fst \
	Pulse.Lib.GC/Pulse.Lib.GC.Fields.fst.checked \
	Spec/Pulse.Spec.GC.Correctness.fsti.checked \
	Spec/Pulse.Spec.GC.SweepInv.fsti.checked \
	Spec/Pulse.Spec.GC.Sweep.fst.checked \
	Spec/Pulse.Spec.GC.Mark.fst.checked \
	$(C)/Spec/Pulse.Spec.GC.HeapGraph.fst.checked \
	$(C)/Spec/Pulse.Spec.GC.Fields.fst.checked \
	$(C)/Spec/Pulse.Spec.GC.Object.fsti.checked \
	$(C)/Spec/Pulse.Spec.GC.Heap.fsti.checked \
	$(C)/Spec/Pulse.Spec.GC.Base.fsti.checked \
	$(C)/Lib/Pulse.Lib.Header.fst.checked \
	$(C)/Pulse.Lib.GC/Pulse.Lib.GC.Object.fst.checked \
	$(C)/Pulse.Lib.GC/Pulse.Lib.GC.Heap.fst.checked

Pulse.Lib.GC/Pulse.Lib.GC.fst.checked: \
	Pulse.Lib.GC/Pulse.Lib.GC.fst \
	Pulse.Lib.GC/Pulse.Lib.GC.Mark.fst.checked \
	Pulse.Lib.GC/Pulse.Lib.GC.Sweep.fst.checked \
	Spec/Pulse.Spec.GC.SweepInv.fsti.checked \
	Spec/Pulse.Spec.GC.MarkInv.fsti.checked \
	Spec/Pulse.Spec.GC.Correctness.fsti.checked \
	$(C)/Spec/Pulse.Spec.GC.Object.fsti.checked \
	$(C)/Spec/Pulse.Spec.GC.Fields.fst.checked \
	$(C)/Pulse.Lib.GC/Pulse.Lib.GC.Stack.fst.checked \
	$(C)/Pulse.Lib.GC/Pulse.Lib.GC.Object.fst.checked \
	$(C)/Pulse.Lib.GC/Pulse.Lib.GC.Heap.fst.checked

# ------------------------------------------------------------------------------
# Pattern rules (recipes for verification)
# ------------------------------------------------------------------------------

Spec/%.fst.checked: Spec/%.fst
	$(FSTAR) $(FSTAR_SPEC_INCLUDES) $(FSTAR_SPEC_FLAGS) $<

Spec/%.fsti.checked: Spec/%.fsti
	$(FSTAR) $(FSTAR_SPEC_INCLUDES) $(FSTAR_SPEC_FLAGS) $<

Pulse.Lib.GC/%.fst.checked: Pulse.Lib.GC/%.fst
	$(FSTAR) $(FSTAR_LIB_INCLUDES) $(FSTAR_LIB_FLAGS) --z3refresh $<

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
	rm -f .depend .depend.spec .depend.lib .common-stamp .common-pulse-stamp
	rm -rf $(EXTRACT_DIR)
