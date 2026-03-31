# Makefile for Pulse GC (Mark-and-Sweep)
#
# Verifies and extracts the sequential stop-the-world garbage collector.
# Hand-written dependency graph for parallel-safe builds (make -j8).
# Shared infrastructure (Heap, Object, Stack) lives in ../common/

FSTAR_HOME ?= $(CURDIR)/../FStar
FSTAR      ?= $(FSTAR_HOME)/bin/fstar.exe
KRML_HOME  ?= $(FSTAR_HOME)/karamel
KRML       ?= $(KRML_HOME)/krml

C = ../common

# Include paths (shared between spec and lib)
COMMON_INCLUDES = \
  --include spec \
  --include $(C)/spec \
  --include $(C)/lib

# Spec: pure F*, no Pulse plugin needed
FSTAR_SPEC_INCLUDES = $(COMMON_INCLUDES)

# Lib: fstar2 stage3 has Pulse baked in
PULSE_LIB ?= $(FSTAR_HOME)/pulse/lib/pulse/lib
FSTAR_IMPL_INCLUDES = $(COMMON_INCLUDES) \
  --include impl \
  --include $(C)/impl \
  --include $(PULSE_LIB)

# F* base options
FSTAR_BASE = \
  --cache_checked_modules \
  --warn_error -321 \
  --report_assumes warn

FSTAR_SPEC_FLAGS = $(FSTAR_BASE) \
  --already_cached 'FStar -GC'

FSTAR_IMPL_FLAGS = $(FSTAR_BASE) \
  --split_queries always \
  --already_cached 'FStar Pulse -GC'

# Spec checked files (explicit list)
SPEC_CHECKED = \
  spec/GC.Spec.SeqMemLemmas.fst.checked \
  spec/GC.Spec.SweepInv.fsti.checked \
  spec/GC.Spec.SweepInv.fst.checked \
  spec/GC.Spec.Mark.fst.checked \
  spec/GC.Spec.MarkInv.fsti.checked \
  spec/GC.Spec.MarkInv.fst.checked \
  spec/GC.Spec.Sweep.fst.checked \
  spec/GC.Spec.Correctness.fsti.checked \
  spec/GC.Spec.Correctness.fst.checked

# Lib checked files (explicit list)
IMPL_CHECKED = \
  impl/GC.Impl.Fields.fst.checked \
  impl/GC.Impl.Closure.fst.checked \
  impl/GC.Impl.Mark.fst.checked \
  impl/GC.Impl.Sweep.Lemmas.fst.checked \
  impl/GC.Impl.Sweep.fst.checked \
  impl/GC.Impl.fst.checked

# ------------------------------------------------------------------------------
# Targets
# ------------------------------------------------------------------------------

.PHONY: all verify verify-spec verify-impl extract snapshot clean

all: verify

verify: verify-impl

verify-spec: $(SPEC_CHECKED)
	@echo "=== mark-and-sweep: spec modules verified ==="

verify-impl: verify-spec $(IMPL_CHECKED)
	@echo "=== mark-and-sweep: impl modules verified ==="

# ------------------------------------------------------------------------------
# Common/ build: parallel-safe via sentinel files
# ------------------------------------------------------------------------------

COMMON_SPEC_SOURCES = $(wildcard $(C)/spec/*.fst $(C)/spec/*.fsti $(C)/lib/*.fst)
COMMON_PULSE_SOURCES = $(wildcard $(C)/impl/*.fst)

# Build common/ spec+lib modules once (for verify-spec)
.common-stamp: $(COMMON_SPEC_SOURCES)
	+$(MAKE) -C $(C)
	@touch $@

# Build common/ Pulse modules once (for verify-impl)
.common-impl-stamp: .common-stamp $(COMMON_PULSE_SOURCES)
	+$(MAKE) -C $(C) verify-impl
	@touch $@

# Common checked files are produced by common/Makefile via stamps
$(C)/spec/%.checked: | .common-stamp
	@true

$(C)/lib/%.checked: | .common-stamp
	@true

$(C)/impl/%.checked: | .common-impl-stamp
	@true

# ------------------------------------------------------------------------------
# Spec module dependencies (from module graph, validated against --dep full)
# ------------------------------------------------------------------------------

spec/GC.Spec.SeqMemLemmas.fst.checked: \
	spec/GC.Spec.SeqMemLemmas.fst

spec/GC.Spec.Correctness.fsti.checked: \
	spec/GC.Spec.Correctness.fsti \
	spec/GC.Spec.Sweep.fst.checked \
	spec/GC.Spec.Mark.fst.checked \
	$(C)/spec/GC.Spec.HeapGraph.fst.checked \
	$(C)/spec/GC.Spec.DFS.fst.checked \
	$(C)/spec/GC.Spec.HeapModel.fst.checked \
	$(C)/spec/GC.Spec.Fields.fst.checked \
	$(C)/spec/GC.Spec.Graph.fst.checked \
	$(C)/spec/GC.Spec.Object.fsti.checked \
	$(C)/spec/GC.Spec.Heap.fsti.checked \
	$(C)/spec/GC.Spec.Base.fsti.checked

spec/GC.Spec.Correctness.fst.checked: \
	spec/GC.Spec.Correctness.fst \
	spec/GC.Spec.Correctness.fsti.checked \
	spec/GC.Spec.Sweep.fst.checked \
	spec/GC.Spec.Mark.fst.checked \
	$(C)/spec/GC.Spec.HeapGraph.fst.checked \
	$(C)/spec/GC.Spec.DFS.fst.checked \
	$(C)/spec/GC.Spec.HeapModel.fst.checked \
	$(C)/spec/GC.Spec.Fields.fst.checked \
	$(C)/spec/GC.Spec.Graph.fst.checked \
	$(C)/spec/GC.Spec.Object.fsti.checked \
	$(C)/spec/GC.Spec.Heap.fsti.checked \
	$(C)/spec/GC.Spec.Base.fsti.checked

spec/GC.Spec.SweepInv.fsti.checked: \
	spec/GC.Spec.SweepInv.fsti \
	$(C)/spec/GC.Spec.HeapGraph.fst.checked \
	$(C)/spec/GC.Spec.Fields.fst.checked \
	$(C)/spec/GC.Spec.Object.fsti.checked \
	$(C)/spec/GC.Spec.Heap.fsti.checked \
	$(C)/spec/GC.Spec.Base.fsti.checked

spec/GC.Spec.SweepInv.fst.checked: \
	spec/GC.Spec.SweepInv.fst \
	spec/GC.Spec.SweepInv.fsti.checked \
	$(C)/spec/GC.Spec.HeapGraph.fst.checked \
	$(C)/spec/GC.Spec.Fields.fst.checked \
	$(C)/spec/GC.Spec.Object.fsti.checked \
	$(C)/spec/GC.Spec.Heap.fsti.checked \
	$(C)/spec/GC.Spec.Base.fsti.checked

spec/GC.Spec.Mark.fst.checked: \
	spec/GC.Spec.Mark.fst \
	spec/GC.Spec.SweepInv.fsti.checked \
	$(C)/lib/GC.Lib.Header.fst.checked \
	$(C)/spec/GC.Spec.HeapGraph.fst.checked \
	$(C)/spec/GC.Spec.DFS.fst.checked \
	$(C)/spec/GC.Spec.HeapModel.fst.checked \
	$(C)/spec/GC.Spec.Fields.fst.checked \
	$(C)/spec/GC.Spec.Graph.fst.checked \
	$(C)/spec/GC.Spec.Object.fsti.checked \
	$(C)/spec/GC.Spec.Heap.fsti.checked \
	$(C)/spec/GC.Spec.Base.fsti.checked

spec/GC.Spec.MarkInv.fsti.checked: \
	spec/GC.Spec.MarkInv.fsti \
	spec/GC.Spec.SweepInv.fsti.checked \
	spec/GC.Spec.Mark.fst.checked \
	$(C)/spec/GC.Spec.Fields.fst.checked \
	$(C)/spec/GC.Spec.Object.fsti.checked \
	$(C)/spec/GC.Spec.Base.fsti.checked

spec/GC.Spec.MarkInv.fst.checked: \
	spec/GC.Spec.MarkInv.fst \
	spec/GC.Spec.MarkInv.fsti.checked \
	spec/GC.Spec.SweepInv.fsti.checked \
	spec/GC.Spec.Mark.fst.checked \
	$(C)/spec/GC.Spec.Fields.fst.checked \
	$(C)/spec/GC.Spec.Object.fsti.checked \
	$(C)/spec/GC.Spec.Base.fsti.checked

spec/GC.Spec.Sweep.fst.checked: \
	spec/GC.Spec.Sweep.fst \
	spec/GC.Spec.Mark.fst.checked \
	$(C)/lib/GC.Lib.Header.fst.checked \
	$(C)/spec/GC.Spec.HeapGraph.fst.checked \
	$(C)/spec/GC.Spec.HeapModel.fst.checked \
	$(C)/spec/GC.Spec.Fields.fst.checked \
	$(C)/spec/GC.Spec.Graph.fst.checked \
	$(C)/spec/GC.Spec.Object.fsti.checked \
	$(C)/spec/GC.Spec.Heap.fsti.checked \
	$(C)/spec/GC.Spec.Base.fsti.checked


# ------------------------------------------------------------------------------
# Impl module dependencies (from module graph, validated against --dep full)
# ------------------------------------------------------------------------------

impl/GC.Impl.Fields.fst.checked: \
	impl/GC.Impl.Fields.fst \
	$(C)/impl/GC.Impl.Object.fst.checked \
	$(C)/impl/GC.Impl.Heap.fst.checked

impl/GC.Impl.Closure.fst.checked: \
	impl/GC.Impl.Closure.fst \
	impl/GC.Impl.Fields.fst.checked \
	$(C)/impl/GC.Impl.Object.fst.checked \
	$(C)/impl/GC.Impl.Heap.fst.checked

impl/GC.Impl.Mark.fst.checked: \
	impl/GC.Impl.Mark.fst \
	impl/GC.Impl.Fields.fst.checked \
	spec/GC.Spec.MarkInv.fsti.checked \
	spec/GC.Spec.Mark.fst.checked \
	$(C)/spec/GC.Spec.HeapGraph.fst.checked \
	$(C)/spec/GC.Spec.Fields.fst.checked \
	$(C)/spec/GC.Spec.Object.fsti.checked \
	$(C)/spec/GC.Spec.Heap.fsti.checked \
	$(C)/spec/GC.Spec.Base.fsti.checked \
	$(C)/lib/GC.Lib.Header.fst.checked \
	$(C)/impl/GC.Impl.Stack.fst.checked \
	$(C)/impl/GC.Impl.Object.fst.checked \
	$(C)/impl/GC.Impl.Heap.fst.checked

impl/GC.Impl.Sweep.Lemmas.fsti.checked: \
	impl/GC.Impl.Sweep.Lemmas.fsti \
	impl/GC.Impl.Fields.fst.checked \
	spec/GC.Spec.Correctness.fsti.checked \
	spec/GC.Spec.SweepInv.fsti.checked \
	spec/GC.Spec.Sweep.fst.checked \
	spec/GC.Spec.Mark.fst.checked \
	$(C)/spec/GC.Spec.HeapGraph.fst.checked \
	$(C)/spec/GC.Spec.Fields.fst.checked \
	$(C)/spec/GC.Spec.Object.fsti.checked \
	$(C)/spec/GC.Spec.Heap.fsti.checked \
	$(C)/spec/GC.Spec.Base.fsti.checked \
	$(C)/lib/GC.Lib.Header.fst.checked \
	$(C)/impl/GC.Impl.Object.fst.checked \
	$(C)/impl/GC.Impl.Heap.fst.checked

impl/GC.Impl.Sweep.Lemmas.fst.checked: \
	impl/GC.Impl.Sweep.Lemmas.fst \
	impl/GC.Impl.Sweep.Lemmas.fsti.checked \
	impl/GC.Impl.Fields.fst.checked \
	spec/GC.Spec.Correctness.fsti.checked \
	spec/GC.Spec.SweepInv.fsti.checked \
	spec/GC.Spec.Sweep.fst.checked \
	spec/GC.Spec.Mark.fst.checked \
	$(C)/spec/GC.Spec.HeapGraph.fst.checked \
	$(C)/spec/GC.Spec.Fields.fst.checked \
	$(C)/spec/GC.Spec.Object.fsti.checked \
	$(C)/spec/GC.Spec.Heap.fsti.checked \
	$(C)/spec/GC.Spec.Base.fsti.checked \
	$(C)/lib/GC.Lib.Header.fst.checked \
	$(C)/impl/GC.Impl.Object.fst.checked \
	$(C)/impl/GC.Impl.Heap.fst.checked

impl/GC.Impl.Sweep.fst.checked: \
	impl/GC.Impl.Sweep.fst \
	impl/GC.Impl.Sweep.Lemmas.fst.checked \
	impl/GC.Impl.Fields.fst.checked \
	spec/GC.Spec.Correctness.fsti.checked \
	spec/GC.Spec.SweepInv.fsti.checked \
	spec/GC.Spec.Sweep.fst.checked \
	spec/GC.Spec.Mark.fst.checked \
	$(C)/spec/GC.Spec.HeapGraph.fst.checked \
	$(C)/spec/GC.Spec.Fields.fst.checked \
	$(C)/spec/GC.Spec.Object.fsti.checked \
	$(C)/spec/GC.Spec.Heap.fsti.checked \
	$(C)/spec/GC.Spec.Base.fsti.checked \
	$(C)/lib/GC.Lib.Header.fst.checked \
	$(C)/impl/GC.Impl.Object.fst.checked \
	$(C)/impl/GC.Impl.Heap.fst.checked

impl/GC.Impl.fst.checked: \
	impl/GC.Impl.fst \
	impl/GC.Impl.Mark.fst.checked \
	impl/GC.Impl.Sweep.fst.checked \
	spec/GC.Spec.SweepInv.fsti.checked \
	spec/GC.Spec.MarkInv.fsti.checked \
	spec/GC.Spec.Correctness.fsti.checked \
	$(C)/spec/GC.Spec.Object.fsti.checked \
	$(C)/spec/GC.Spec.Fields.fst.checked \
	$(C)/impl/GC.Impl.Stack.fst.checked \
	$(C)/impl/GC.Impl.Object.fst.checked \
	$(C)/impl/GC.Impl.Heap.fst.checked

# ------------------------------------------------------------------------------
# Pattern rules (recipes for verification)
# ------------------------------------------------------------------------------

spec/%.checked: spec/%
	$(FSTAR) $(FSTAR_SPEC_INCLUDES) $(FSTAR_SPEC_FLAGS) $<

impl/%.checked: impl/%
	$(FSTAR) $(FSTAR_IMPL_INCLUDES) $(FSTAR_IMPL_FLAGS) --z3refresh $<

# ------------------------------------------------------------------------------
# Extraction to C via KaRaMeL (two-phase pipeline)
#
# Phase 1: fstar.exe --codegen krml → .krml  (one per module)
# Phase 2: krml .krml → GC_Impl.c/.h    (bundle into single C file)
# ------------------------------------------------------------------------------

KRML_OUTPUT_DIR = _output
EXTRACT_DIR     = _extract

# F* flags for extraction (reuses lib flags + codegen)
FSTAR_EXTRACT_FLAGS = $(FSTAR_BASE) \
  --split_queries always \
  --already_cached 'FStar Pulse -GC'

# KaRaMeL flags
KRML_FLAGS = \
  -tmpdir $(EXTRACT_DIR) \
  -skip-compilation \
  -skip-linking \
  -library GC.Spec.Base \
  -library GC.Spec.Heap \
  -library GC.Spec.Object \
  -library GC.Lib.Header \
  -library GC.Lib.Address \
  -bundle 'GC.Impl=GC.Impl.*' \
  -bundle 'FStar.Pervasives.Native' \
  -bundle 'GC.Spec.*,GC.Lib.Header,GC.Lib.Address' \
  -no-prefix GC.Impl \
  -no-prefix GC.Impl.Mark \
  -no-prefix GC.Impl.Sweep \
  -no-prefix GC.Impl.Fields \
  -no-prefix GC.Impl.Closure \
  -no-prefix GC.Impl.Heap \
  -no-prefix GC.Impl.Object \
  -no-prefix GC.Impl.Stack \
  -warn-error -2-9-15

# .krml files from mark-and-sweep GC.Impl modules
MS_KRML = \
  $(KRML_OUTPUT_DIR)/GC_Impl_Fields.krml \
  $(KRML_OUTPUT_DIR)/GC_Impl_Closure.krml \
  $(KRML_OUTPUT_DIR)/GC_Impl_Mark.krml \
  $(KRML_OUTPUT_DIR)/GC_Impl_Sweep.krml \
  $(KRML_OUTPUT_DIR)/GC_Impl.krml

# .krml files from common/ GC.Impl modules
COMMON_KRML = \
  $(KRML_OUTPUT_DIR)/GC_Impl_Heap.krml \
  $(KRML_OUTPUT_DIR)/GC_Impl_Object.krml \
  $(KRML_OUTPUT_DIR)/GC_Impl_Stack.krml

# .krml files for dependencies (spec types, FStar.Pervasives.Native)
DEP_KRML = \
  $(KRML_OUTPUT_DIR)/FStar_Pervasives_Native.krml \
  $(KRML_OUTPUT_DIR)/GC_Spec_Base.krml \
  $(KRML_OUTPUT_DIR)/GC_Spec_Heap.krml \
  $(KRML_OUTPUT_DIR)/GC_Spec_Object.krml \
  $(KRML_OUTPUT_DIR)/GC_Lib_Header.krml \
  $(KRML_OUTPUT_DIR)/GC_Lib_Address.krml

ALL_KRML = $(MS_KRML) $(COMMON_KRML) $(DEP_KRML)

$(KRML_OUTPUT_DIR):
	@mkdir -p $@

$(EXTRACT_DIR):
	@mkdir -p $@

# Phase 1a: extract mark-and-sweep modules to .krml
$(KRML_OUTPUT_DIR)/GC_Impl_Fields.krml: impl/GC.Impl.Fields.fst | $(KRML_OUTPUT_DIR)
	$(FSTAR) $(FSTAR_IMPL_INCLUDES) $(FSTAR_EXTRACT_FLAGS) \
	  --codegen krml --extract_module GC.Impl.Fields --odir $(KRML_OUTPUT_DIR) $<

$(KRML_OUTPUT_DIR)/GC_Impl_Closure.krml: impl/GC.Impl.Closure.fst | $(KRML_OUTPUT_DIR)
	$(FSTAR) $(FSTAR_IMPL_INCLUDES) $(FSTAR_EXTRACT_FLAGS) \
	  --codegen krml --extract_module GC.Impl.Closure --odir $(KRML_OUTPUT_DIR) $<

$(KRML_OUTPUT_DIR)/GC_Impl_Mark.krml: impl/GC.Impl.Mark.fst | $(KRML_OUTPUT_DIR)
	$(FSTAR) $(FSTAR_IMPL_INCLUDES) $(FSTAR_EXTRACT_FLAGS) \
	  --codegen krml --extract_module GC.Impl.Mark --odir $(KRML_OUTPUT_DIR) $<

$(KRML_OUTPUT_DIR)/GC_Impl_Sweep.krml: impl/GC.Impl.Sweep.fst | $(KRML_OUTPUT_DIR)
	$(FSTAR) $(FSTAR_IMPL_INCLUDES) $(FSTAR_EXTRACT_FLAGS) \
	  --codegen krml --extract_module GC.Impl.Sweep --odir $(KRML_OUTPUT_DIR) $<

$(KRML_OUTPUT_DIR)/GC_Impl.krml: impl/GC.Impl.fst | $(KRML_OUTPUT_DIR)
	$(FSTAR) $(FSTAR_IMPL_INCLUDES) $(FSTAR_EXTRACT_FLAGS) \
	  --codegen krml --extract_module GC.Impl --odir $(KRML_OUTPUT_DIR) $<

# Phase 1b: extract common/ GC.Impl modules to .krml
$(KRML_OUTPUT_DIR)/GC_Impl_Heap.krml: $(C)/impl/GC.Impl.Heap.fst | $(KRML_OUTPUT_DIR)
	$(FSTAR) $(FSTAR_IMPL_INCLUDES) $(FSTAR_EXTRACT_FLAGS) \
	  --codegen krml --extract_module GC.Impl.Heap --odir $(KRML_OUTPUT_DIR) $<

$(KRML_OUTPUT_DIR)/GC_Impl_Object.krml: $(C)/impl/GC.Impl.Object.fst | $(KRML_OUTPUT_DIR)
	$(FSTAR) $(FSTAR_IMPL_INCLUDES) $(FSTAR_EXTRACT_FLAGS) \
	  --codegen krml --extract_module GC.Impl.Object --odir $(KRML_OUTPUT_DIR) $<

$(KRML_OUTPUT_DIR)/GC_Impl_Stack.krml: $(C)/impl/GC.Impl.Stack.fst | $(KRML_OUTPUT_DIR)
	$(FSTAR) $(FSTAR_IMPL_INCLUDES) $(FSTAR_EXTRACT_FLAGS) \
	  --codegen krml --extract_module GC.Impl.Stack --odir $(KRML_OUTPUT_DIR) $<

# Phase 1c: extract dependency modules to .krml
$(KRML_OUTPUT_DIR)/FStar_Pervasives_Native.krml: | $(KRML_OUTPUT_DIR)
	$(FSTAR) --cache_checked_modules --warn_error -321 \
	  --codegen krml --extract_module FStar.Pervasives.Native --odir $(KRML_OUTPUT_DIR) \
	  $(FSTAR_HOME)/ulib/FStar.Pervasives.Native.fst

$(KRML_OUTPUT_DIR)/GC_Spec_Base.krml: $(C)/spec/GC.Spec.Base.fst | $(KRML_OUTPUT_DIR)
	$(FSTAR) $(COMMON_INCLUDES) $(FSTAR_BASE) --already_cached 'FStar -GC' \
	  --codegen krml --extract_module GC.Spec.Base --odir $(KRML_OUTPUT_DIR) $<

$(KRML_OUTPUT_DIR)/GC_Spec_Heap.krml: $(C)/spec/GC.Spec.Heap.fst | $(KRML_OUTPUT_DIR)
	$(FSTAR) $(COMMON_INCLUDES) $(FSTAR_BASE) --already_cached 'FStar -GC.Spec -GC.Lib.Header' \
	  --codegen krml --extract_module GC.Spec.Heap --odir $(KRML_OUTPUT_DIR) $<

$(KRML_OUTPUT_DIR)/GC_Spec_Object.krml: $(C)/spec/GC.Spec.Object.fst | $(KRML_OUTPUT_DIR)
	$(FSTAR) $(COMMON_INCLUDES) $(FSTAR_BASE) --already_cached 'FStar -GC.Spec -GC.Lib.Header' \
	  --codegen krml --extract_module GC.Spec.Object --odir $(KRML_OUTPUT_DIR) $<

$(KRML_OUTPUT_DIR)/GC_Lib_Header.krml: $(C)/lib/GC.Lib.Header.fst | $(KRML_OUTPUT_DIR)
	$(FSTAR) $(COMMON_INCLUDES) $(FSTAR_BASE) --already_cached 'FStar -GC.Lib.Header' \
	  --codegen krml --extract_module GC.Lib.Header --odir $(KRML_OUTPUT_DIR) $<

$(KRML_OUTPUT_DIR)/GC_Lib_Address.krml: $(C)/lib/GC.Lib.Address.fst | $(KRML_OUTPUT_DIR)
	$(FSTAR) $(COMMON_INCLUDES) $(FSTAR_BASE) --already_cached 'FStar -GC.Spec -GC.Lib.Address' \
	  --codegen krml --extract_module GC.Lib.Address --odir $(KRML_OUTPUT_DIR) $<

# Phase 2: .krml → C via KaRaMeL
$(EXTRACT_DIR)/GC_Impl.c: $(ALL_KRML) | $(EXTRACT_DIR)
	$(KRML) $(KRML_FLAGS) $(ALL_KRML)

extract: verify-impl $(EXTRACT_DIR)/GC_Impl.c
	@echo "=== Extraction complete: $(EXTRACT_DIR)/GC_Impl.{c,h} ==="

# ------------------------------------------------------------------------------
# Snapshot: self-contained extracted C for CI without F*/KaRaMeL
# ------------------------------------------------------------------------------

SNAPSHOT_DIR = snapshot

snapshot: extract
	@echo "=== Creating snapshot ==="
	@mkdir -p $(SNAPSHOT_DIR)/krmllib/krml/internal $(SNAPSHOT_DIR)/internal
	@cp $(EXTRACT_DIR)/GC_Impl.c $(SNAPSHOT_DIR)/
	@cp $(EXTRACT_DIR)/GC_Impl.h $(SNAPSHOT_DIR)/
	@cp $(EXTRACT_DIR)/GC_Spec_GC_Lib_Header_GC_Lib_Address.h $(SNAPSHOT_DIR)/ 2>/dev/null || true
	@cp $(EXTRACT_DIR)/internal/*.h $(SNAPSHOT_DIR)/internal/ 2>/dev/null || true
	@cp $(EXTRACT_DIR)/krmlinit.c $(SNAPSHOT_DIR)/ 2>/dev/null || true
	@cp $(EXTRACT_DIR)/krmlinit.h $(SNAPSHOT_DIR)/ 2>/dev/null || true
	@cp $(KRML_HOME)/include/krmllib.h $(SNAPSHOT_DIR)/krmllib/ 2>/dev/null || true
	@cp -r $(KRML_HOME)/krmllib/dist/minimal/* $(SNAPSHOT_DIR)/krmllib/ 2>/dev/null || true
	@cp $(KRML_HOME)/include/krml/*.h $(SNAPSHOT_DIR)/krmllib/krml/ 2>/dev/null || true
	@cp $(KRML_HOME)/include/krml/internal/*.h $(SNAPSHOT_DIR)/krmllib/krml/internal/ 2>/dev/null || true
	@if ! grep -q '^#include "pulsegc_compat.h"' $(SNAPSHOT_DIR)/GC_Impl.c 2>/dev/null; then \
	  sed -i '/#include "internal\/GC_Spec_GC_Lib_Header_GC_Lib_Address.h"/a #include "pulsegc_compat.h"' $(SNAPSHOT_DIR)/GC_Impl.c; \
	fi
	@echo "=== Snapshot updated: $(SNAPSHOT_DIR)/ ==="
	@echo "    Hand-maintained: pulsegc_compat.h, pulsegc_runtime.c, Makefile"

# ------------------------------------------------------------------------------
# Cleanup
# ------------------------------------------------------------------------------

clean:
	rm -f spec/*.checked* impl/*.checked*
	rm -f .depend .depend.spec .depend.lib .common-stamp .common-impl-stamp
	rm -rf $(KRML_OUTPUT_DIR) $(EXTRACT_DIR)
