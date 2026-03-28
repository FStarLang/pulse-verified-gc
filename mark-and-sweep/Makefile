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
  --include Spec \
  --include $(C)/Spec \
  --include $(C)/Lib

# Spec: pure F*, no Pulse plugin needed
FSTAR_SPEC_INCLUDES = $(COMMON_INCLUDES)

# Lib: fstar2 stage3 has Pulse baked in
PULSE_LIB ?= $(FSTAR_HOME)/pulse/lib/pulse/lib
FSTAR_LIB_INCLUDES = $(COMMON_INCLUDES) \
  --include Pulse.Lib.GC \
  --include $(C)/Pulse.Lib.GC \
  --include $(PULSE_LIB)

# F* base options
FSTAR_BASE = \
  --cache_checked_modules \
  --warn_error -321 \
  --report_assumes warn

FSTAR_SPEC_FLAGS = $(FSTAR_BASE) \
  --already_cached 'FStar -Pulse.Spec.GC'

FSTAR_LIB_FLAGS = $(FSTAR_BASE) \
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

.PHONY: all verify verify-spec verify-lib extract snapshot clean

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
# Extraction to C via KaRaMeL (two-phase pipeline)
#
# Phase 1: fstar.exe --codegen krml → .krml  (one per module)
# Phase 2: krml .krml → Pulse_Lib_GC.c/.h    (bundle into single C file)
# ------------------------------------------------------------------------------

KRML_OUTPUT_DIR = _output
EXTRACT_DIR     = _extract

# F* flags for extraction (reuses lib flags + codegen)
FSTAR_EXTRACT_FLAGS = $(FSTAR_BASE) \
  --split_queries always \
  --already_cached 'FStar Pulse -Pulse.Spec.GC -Pulse.Lib.GC -Pulse.Lib.Header -Pulse.Lib.Address -Pulse.Lib.Bitvec'

# KaRaMeL flags
KRML_FLAGS = \
  -tmpdir $(EXTRACT_DIR) \
  -skip-compilation \
  -skip-linking \
  -library Pulse.Spec.GC.Base \
  -library Pulse.Spec.GC.Heap \
  -library Pulse.Spec.GC.Object \
  -library Pulse.Lib.Header \
  -library Pulse.Lib.Address \
  -bundle 'Pulse.Lib.GC=Pulse.Lib.GC.*,Pulse.Lib.LinkedList' \
  -bundle 'Pulse.Spec.GC.*,Pulse.Lib.Header,Pulse.Lib.Address' \
  -no-prefix Pulse.Lib.GC \
  -no-prefix Pulse.Lib.GC.Mark \
  -no-prefix Pulse.Lib.GC.Sweep \
  -no-prefix Pulse.Lib.GC.Fields \
  -no-prefix Pulse.Lib.GC.Closure \
  -no-prefix Pulse.Lib.GC.Heap \
  -no-prefix Pulse.Lib.GC.Object \
  -no-prefix Pulse.Lib.GC.Stack \
  -no-prefix Pulse.Lib.LinkedList \
  -warn-error -2-9-15

# .krml files from mark-and-sweep Pulse.Lib.GC modules
MS_KRML = \
  $(KRML_OUTPUT_DIR)/Pulse_Lib_GC_Fields.krml \
  $(KRML_OUTPUT_DIR)/Pulse_Lib_GC_Closure.krml \
  $(KRML_OUTPUT_DIR)/Pulse_Lib_GC_Mark.krml \
  $(KRML_OUTPUT_DIR)/Pulse_Lib_GC_Sweep.krml \
  $(KRML_OUTPUT_DIR)/Pulse_Lib_GC.krml

# .krml files from common/ Pulse.Lib.GC modules
COMMON_KRML = \
  $(KRML_OUTPUT_DIR)/Pulse_Lib_GC_Heap.krml \
  $(KRML_OUTPUT_DIR)/Pulse_Lib_GC_Object.krml \
  $(KRML_OUTPUT_DIR)/Pulse_Lib_GC_Stack.krml

# .krml files for dependencies (LinkedList, spec types, FStar.Pervasives.Native)
DEP_KRML = \
  $(KRML_OUTPUT_DIR)/Pulse_Lib_LinkedList.krml \
  $(KRML_OUTPUT_DIR)/FStar_Pervasives_Native.krml \
  $(KRML_OUTPUT_DIR)/Pulse_Spec_GC_Base.krml \
  $(KRML_OUTPUT_DIR)/Pulse_Spec_GC_Heap.krml \
  $(KRML_OUTPUT_DIR)/Pulse_Spec_GC_Object.krml \
  $(KRML_OUTPUT_DIR)/Pulse_Lib_Header.krml \
  $(KRML_OUTPUT_DIR)/Pulse_Lib_Address.krml

ALL_KRML = $(MS_KRML) $(COMMON_KRML) $(DEP_KRML)

$(KRML_OUTPUT_DIR):
	@mkdir -p $@

$(EXTRACT_DIR):
	@mkdir -p $@

# Phase 1a: extract mark-and-sweep modules to .krml
$(KRML_OUTPUT_DIR)/Pulse_Lib_GC_Fields.krml: Pulse.Lib.GC/Pulse.Lib.GC.Fields.fst | $(KRML_OUTPUT_DIR)
	$(FSTAR) $(FSTAR_LIB_INCLUDES) $(FSTAR_EXTRACT_FLAGS) \
	  --codegen krml --extract_module Pulse.Lib.GC.Fields --odir $(KRML_OUTPUT_DIR) $<

$(KRML_OUTPUT_DIR)/Pulse_Lib_GC_Closure.krml: Pulse.Lib.GC/Pulse.Lib.GC.Closure.fst | $(KRML_OUTPUT_DIR)
	$(FSTAR) $(FSTAR_LIB_INCLUDES) $(FSTAR_EXTRACT_FLAGS) \
	  --codegen krml --extract_module Pulse.Lib.GC.Closure --odir $(KRML_OUTPUT_DIR) $<

$(KRML_OUTPUT_DIR)/Pulse_Lib_GC_Mark.krml: Pulse.Lib.GC/Pulse.Lib.GC.Mark.fst | $(KRML_OUTPUT_DIR)
	$(FSTAR) $(FSTAR_LIB_INCLUDES) $(FSTAR_EXTRACT_FLAGS) \
	  --codegen krml --extract_module Pulse.Lib.GC.Mark --odir $(KRML_OUTPUT_DIR) $<

$(KRML_OUTPUT_DIR)/Pulse_Lib_GC_Sweep.krml: Pulse.Lib.GC/Pulse.Lib.GC.Sweep.fst | $(KRML_OUTPUT_DIR)
	$(FSTAR) $(FSTAR_LIB_INCLUDES) $(FSTAR_EXTRACT_FLAGS) \
	  --codegen krml --extract_module Pulse.Lib.GC.Sweep --odir $(KRML_OUTPUT_DIR) $<

$(KRML_OUTPUT_DIR)/Pulse_Lib_GC.krml: Pulse.Lib.GC/Pulse.Lib.GC.fst | $(KRML_OUTPUT_DIR)
	$(FSTAR) $(FSTAR_LIB_INCLUDES) $(FSTAR_EXTRACT_FLAGS) \
	  --codegen krml --extract_module Pulse.Lib.GC --odir $(KRML_OUTPUT_DIR) $<

# Phase 1b: extract common/ Pulse.Lib.GC modules to .krml
$(KRML_OUTPUT_DIR)/Pulse_Lib_GC_Heap.krml: $(C)/Pulse.Lib.GC/Pulse.Lib.GC.Heap.fst | $(KRML_OUTPUT_DIR)
	$(FSTAR) $(FSTAR_LIB_INCLUDES) $(FSTAR_EXTRACT_FLAGS) \
	  --codegen krml --extract_module Pulse.Lib.GC.Heap --odir $(KRML_OUTPUT_DIR) $<

$(KRML_OUTPUT_DIR)/Pulse_Lib_GC_Object.krml: $(C)/Pulse.Lib.GC/Pulse.Lib.GC.Object.fst | $(KRML_OUTPUT_DIR)
	$(FSTAR) $(FSTAR_LIB_INCLUDES) $(FSTAR_EXTRACT_FLAGS) \
	  --codegen krml --extract_module Pulse.Lib.GC.Object --odir $(KRML_OUTPUT_DIR) $<

$(KRML_OUTPUT_DIR)/Pulse_Lib_GC_Stack.krml: $(C)/Pulse.Lib.GC/Pulse.Lib.GC.Stack.fst | $(KRML_OUTPUT_DIR)
	$(FSTAR) $(FSTAR_LIB_INCLUDES) $(FSTAR_EXTRACT_FLAGS) \
	  --codegen krml --extract_module Pulse.Lib.GC.Stack --odir $(KRML_OUTPUT_DIR) $<

# Phase 1c: extract dependency modules to .krml
$(KRML_OUTPUT_DIR)/Pulse_Lib_LinkedList.krml: $(PULSE_LIB)/Pulse.Lib.LinkedList.fst | $(KRML_OUTPUT_DIR)
	$(FSTAR) $(FSTAR_LIB_INCLUDES) $(FSTAR_EXTRACT_FLAGS) \
	  --codegen krml --extract_module Pulse.Lib.LinkedList --odir $(KRML_OUTPUT_DIR) $<

$(KRML_OUTPUT_DIR)/FStar_Pervasives_Native.krml: | $(KRML_OUTPUT_DIR)
	$(FSTAR) --cache_checked_modules --warn_error -321 \
	  --codegen krml --extract_module FStar.Pervasives.Native --odir $(KRML_OUTPUT_DIR) \
	  $(FSTAR_HOME)/ulib/FStar.Pervasives.Native.fst

$(KRML_OUTPUT_DIR)/Pulse_Spec_GC_Base.krml: $(C)/Spec/Pulse.Spec.GC.Base.fst | $(KRML_OUTPUT_DIR)
	$(FSTAR) $(COMMON_INCLUDES) $(FSTAR_BASE) --already_cached 'FStar -Pulse.Spec.GC' \
	  --codegen krml --extract_module Pulse.Spec.GC.Base --odir $(KRML_OUTPUT_DIR) $<

$(KRML_OUTPUT_DIR)/Pulse_Spec_GC_Heap.krml: $(C)/Spec/Pulse.Spec.GC.Heap.fst | $(KRML_OUTPUT_DIR)
	$(FSTAR) $(COMMON_INCLUDES) $(FSTAR_BASE) --already_cached 'FStar -Pulse.Spec.GC -Pulse.Lib.Header' \
	  --codegen krml --extract_module Pulse.Spec.GC.Heap --odir $(KRML_OUTPUT_DIR) $<

$(KRML_OUTPUT_DIR)/Pulse_Spec_GC_Object.krml: $(C)/Spec/Pulse.Spec.GC.Object.fst | $(KRML_OUTPUT_DIR)
	$(FSTAR) $(COMMON_INCLUDES) $(FSTAR_BASE) --already_cached 'FStar -Pulse.Spec.GC -Pulse.Lib.Header' \
	  --codegen krml --extract_module Pulse.Spec.GC.Object --odir $(KRML_OUTPUT_DIR) $<

$(KRML_OUTPUT_DIR)/Pulse_Lib_Header.krml: $(C)/Lib/Pulse.Lib.Header.fst | $(KRML_OUTPUT_DIR)
	$(FSTAR) $(COMMON_INCLUDES) $(FSTAR_BASE) --already_cached 'FStar -Pulse.Lib.Header' \
	  --codegen krml --extract_module Pulse.Lib.Header --odir $(KRML_OUTPUT_DIR) $<

$(KRML_OUTPUT_DIR)/Pulse_Lib_Address.krml: $(C)/Lib/Pulse.Lib.Address.fst | $(KRML_OUTPUT_DIR)
	$(FSTAR) $(COMMON_INCLUDES) $(FSTAR_BASE) --already_cached 'FStar -Pulse.Spec.GC -Pulse.Lib.Address' \
	  --codegen krml --extract_module Pulse.Lib.Address --odir $(KRML_OUTPUT_DIR) $<

# Phase 2: .krml → C via KaRaMeL
$(EXTRACT_DIR)/Pulse_Lib_GC.c: $(ALL_KRML) | $(EXTRACT_DIR)
	$(KRML) $(KRML_FLAGS) $(ALL_KRML)

extract: verify-lib $(EXTRACT_DIR)/Pulse_Lib_GC.c
	@echo "=== Extraction complete: $(EXTRACT_DIR)/Pulse_Lib_GC.{c,h} ==="

# ------------------------------------------------------------------------------
# Snapshot: self-contained extracted C for CI without F*/KaRaMeL
# ------------------------------------------------------------------------------

SNAPSHOT_DIR = snapshot

snapshot: extract
	@echo "=== Creating snapshot ==="
	@mkdir -p $(SNAPSHOT_DIR)/krmllib/krml/internal $(SNAPSHOT_DIR)/internal
	@cp $(EXTRACT_DIR)/Pulse_Lib_GC.c $(SNAPSHOT_DIR)/
	@cp $(EXTRACT_DIR)/Pulse_Lib_GC.h $(SNAPSHOT_DIR)/
	@cp $(EXTRACT_DIR)/Pulse_Spec_GC_Pulse_Lib_Header_Pulse_Lib_Address.h $(SNAPSHOT_DIR)/ 2>/dev/null || true
	@cp $(EXTRACT_DIR)/internal/*.h $(SNAPSHOT_DIR)/internal/ 2>/dev/null || true
	@cp $(EXTRACT_DIR)/krmlinit.c $(SNAPSHOT_DIR)/ 2>/dev/null || true
	@cp $(EXTRACT_DIR)/krmlinit.h $(SNAPSHOT_DIR)/ 2>/dev/null || true
	@cp $(KRML_HOME)/include/krmllib.h $(SNAPSHOT_DIR)/krmllib/ 2>/dev/null || true
	@cp -r $(KRML_HOME)/krmllib/dist/minimal/* $(SNAPSHOT_DIR)/krmllib/ 2>/dev/null || true
	@cp $(KRML_HOME)/include/krml/*.h $(SNAPSHOT_DIR)/krmllib/krml/ 2>/dev/null || true
	@cp $(KRML_HOME)/include/krml/internal/*.h $(SNAPSHOT_DIR)/krmllib/krml/internal/ 2>/dev/null || true
	@if ! grep -q '^#include "pulsegc_compat.h"' $(SNAPSHOT_DIR)/Pulse_Lib_GC.c 2>/dev/null; then \
	  sed -i '/#include "internal\/Pulse_Lib_GC.h"/a #include "pulsegc_compat.h"' $(SNAPSHOT_DIR)/Pulse_Lib_GC.c; \
	fi
	@echo "=== Snapshot updated: $(SNAPSHOT_DIR)/ ==="
	@echo "    Hand-maintained: pulsegc_compat.h, pulsegc_runtime.c, Makefile"

# ------------------------------------------------------------------------------
# Cleanup
# ------------------------------------------------------------------------------

clean:
	rm -f Spec/*.checked* Pulse.Lib.GC/*.checked*
	rm -f .depend .depend.spec .depend.lib .common-stamp .common-pulse-stamp
	rm -rf $(KRML_OUTPUT_DIR) $(EXTRACT_DIR) $(SNAPSHOT_DIR)
